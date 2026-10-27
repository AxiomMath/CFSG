module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

section General

variable {A : Type*} [Group A]

theorem isKleinFour_of_mulEquiv {B C : Type*} [Group B] [Group C] (e : B ≃* C)
    (h : IsKleinFour C) : IsKleinFour B where
  card_four := by rw [Nat.card_congr e.toEquiv]; exact h.card_four
  exponent_two := by rw [Monoid.exponent_eq_of_mulEquiv e]; exact h.exponent_two

theorem not_two_dvd_index {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) : ¬ 2 ∣ S.index := by
  have h := hS.2.2
  rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h

theorem isPGroup_zpowers {g : A} {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨k, Subtype.ext ?_⟩
  change (g ^ m) ^ 2 ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

theorem mem_of_mem_normalizer_of_pow [Finite A] {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) {g : A}
    (hg : g ∈ Subgroup.normalizer (S : Set A)) {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Sylow 2 A := hS.2.1.toSylow (not_two_dvd_index hS) with hQ
  have h := (isPGroup_zpowers hk).inf_normalizer_sylow Q
  have hmem := h.le ⟨Subgroup.mem_zpowers g, hg⟩
  exact hmem.2

theorem eq_one_of_mem_normalizer [Finite A] {S Y : Subgroup A} (hS4 : Nat.card S = 4)
    (hCS : Subgroup.centralizer (S : Set A) = S) (hY : Nat.card Y = 3)
    (hSY : S ≤ Subgroup.normalizer (Y : Set A)) {a : A} (haY : a ∈ Y)
    (haS : a ∈ Subgroup.normalizer (S : Set A)) : a = 1 := by
  have hbot : S ⊓ Y = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hS4, hY]; norm_num)).eq_bot
  have hcomm : ∀ s ∈ S, s * a = a * s := by
    intro s hs
    have h1 : s * a * s⁻¹ * a⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSY hs) a).mp haY) (Y.inv_mem haY)
    have h2 : s * a * s⁻¹ * a⁻¹ ∈ S := by
      have h3 : a * s⁻¹ * a⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp haS s⁻¹).mp (S.inv_mem hs)
      have e : s * a * s⁻¹ * a⁻¹ = s * (a * s⁻¹ * a⁻¹) := by group
      rw [e]
      exact S.mul_mem hs h3
    have h4 : s * a * s⁻¹ * a⁻¹ ∈ S ⊓ Y := ⟨h2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h4
    calc s * a = s * a * s⁻¹ * a⁻¹ * (a * s) := by group
      _ = a * s := by rw [h4, one_mul]
  have haC : a ∈ Subgroup.centralizer (S : Set A) :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => hcomm s hs
  rw [hCS] at haC
  have h5 : a ∈ S ⊓ Y := ⟨haC, haY⟩
  rwa [hbot, Subgroup.mem_bot] at h5

theorem dihedral_commute_of_odd {m : ℕ} {x y : DihedralGroup m} (hx : Odd (orderOf x))
    (hy : Odd (orderOf y)) : x * y = y * x := by
  rcases x with i | i
  · rcases y with j | j
    · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    · rw [DihedralGroup.orderOf_sr] at hy
      exact absurd hy (by decide)
  · rw [DihedralGroup.orderOf_sr] at hx
    exact absurd hx (by decide)

end General

variable {A : Type*} [Group A] {p : ℕ} [hp : Fact p.Prime]

theorem isKleinFour_of_sylow [Finite A] (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : A ≃* PSL(2, ZMod p)) {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) : IsKleinFour ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  set S' : Subgroup (PSL(2, ZMod p)) := S.map (e : A →* PSL(2, ZMod p)) with hS'
  have h2 : IsPGroup 2 ↥S' := hS.2.1.map _
  have hidx : ¬ 2 ∣ S'.index := by
    rw [hS', Subgroup.index_map_equiv]
    exact not_two_dvd_index hS
  have hK := CFSG.Walter.psl2_sylow_two_isKleinFour (ZMod p) (p := p) (f := 1)
    (by rw [Nat.card_zmod, pow_one]) hpo one_pos (by rw [pow_one]; exact h8) (h2.toSylow hidx)
  exact isKleinFour_of_mulEquiv
    (Subgroup.equivMapOfInjective S (e : A →* PSL(2, ZMod p)) e.injective) hK


theorem centralizer_sylow_eq [Finite A] (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : A ≃* PSL(2, ZMod p)) {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) :
    Subgroup.centralizer (S : Set A) = S :=
  C10P34.centralizer_eq_of_kleinFour (by rintro rfl; omega) e (isKleinFour_of_sylow h8 e hS)

theorem pow_three_eq_one_of_mem_normalizer [Finite A] (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (e : A ≃* PSL(2, ZMod p)) {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) {a : A}
    (ha : a ∈ Subgroup.normalizer (S : Set A)) (hodd : Odd (orderOf a)) : a ^ 3 = 1 := by
  have hK := isKleinFour_of_sylow h8 e hS
  have h24 := C10P34.card_normalizer_dvd hK.card_four (centralizer_sylow_eq h8 e hS)
  have hdvd : orderOf a ∣ 24 := by
    have h1 : orderOf (⟨a, ha⟩ : ↥(Subgroup.normalizer (S : Set A))) ∣
        Nat.card ↥(Subgroup.normalizer (S : Set A)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans h24
  have hcop : Nat.Coprime (orderOf a) 8 :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
  have h3 : orderOf a ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem commute_of_mem_centralizer_involution (hp2 : p ≠ 2) (e : A ≃* PSL(2, ZMod p)) {z a b : A}
    (hz : orderOf z = 2) (ha : a * z = z * a) (hb : b * z = z * b) (hao : Odd (orderOf a))
    (hbo : Odd (orderOf b)) : a * b = b * a := by
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  have hez : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  have hC := CFSG.Walter.psl2_centralizer_involution (ZMod p) (p := p) (f := 1)
    (by rw [Nat.card_zmod, pow_one]) hpo one_pos hez
  set C := Subgroup.centralizer ({e z} : Set PSL(2, ZMod p)) with hCdef
  have hmem : ∀ x : A, x * z = z * x → e x ∈ C := fun x hx => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hx]
  obtain ⟨m, ⟨d⟩⟩ : ∃ m : ℕ, Nonempty (↥C ≃* DihedralGroup m) := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with h4 | h4
    · exact ⟨_, (hC.1 (by rw [pow_one]; exact h4)).2⟩
    · exact ⟨_, (hC.2 (by rw [pow_one]; exact h4)).2⟩
  have hoa : Odd (orderOf (d ⟨e a, hmem a ha⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, MulEquiv.orderOf_eq]
    exact hao
  have hob : Odd (orderOf (d ⟨e b, hmem b hb⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, MulEquiv.orderOf_eq]
    exact hbo
  have h := dihedral_commute_of_odd hoa hob
  rw [← map_mul, ← map_mul] at h
  have h' := congrArg Subtype.val (d.injective h)
  simp only [Subgroup.coe_mul] at h'
  rw [← map_mul, ← map_mul] at h'
  exact e.injective h'

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
