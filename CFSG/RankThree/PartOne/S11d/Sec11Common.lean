module

public import CFSG.RankThree.PartOne.S11b.Sec11Five
public import CFSG.RankThree.PartOne.S11d.FieldCase

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem coords_eq_one_of_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} {a c d : G} (haA : a ∈ A) (hcA : c ∈ A) (hdA : d ∈ A)
    (ha : a ^ p = 1) (hc : c ^ p = 1) (hd : d ^ p = 1) (hcard : Nat.card A = p ^ 3)
    (hgen : ∀ g ∈ A, ∃ x y z : ℤ, g = a ^ x * c ^ y * d ^ z) {x y z : ℤ}
    (h : a ^ x * c ^ y * d ^ z = 1) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hred : ∀ (e : G), e ^ p = 1 → ∀ m : ℤ, ∃ k : Fin p, e ^ m = e ^ (k : ℕ) := by
    intro e he m
    have hz : e ^ (p : ℤ) = 1 := by rw [zpow_natCast, he]
    have h1 := Int.emod_nonneg m (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos m (by exact_mod_cast hp0 : (0 : ℤ) < p)
    refine ⟨⟨(m % (p : ℤ)).toNat, by omega⟩, ?_⟩
    simp only
    rw [zpow_eq_zpow_emod m hz, ← zpow_natCast, Int.toNat_of_nonneg h1]
  let φ : Fin p × Fin p × Fin p → A := fun t =>
    ⟨a ^ (t.1 : ℕ) * c ^ (t.2.1 : ℕ) * d ^ (t.2.2 : ℕ),
      A.mul_mem (A.mul_mem (A.pow_mem haA _) (A.pow_mem hcA _)) (A.pow_mem hdA _)⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨x', y', z', rfl⟩ := hgen g hg
    obtain ⟨kx, hkx⟩ := hred a ha x'
    obtain ⟨ky, hky⟩ := hred c hc y'
    obtain ⟨kz, hkz⟩ := hred d hd z'
    refine ⟨(kx, ky, kz), Subtype.ext ?_⟩
    simp only [φ]
    rw [hkx, hky, hkz]
  have : Fintype A := Fintype.ofFinite A
  have hcardeq : Fintype.card (Fin p × Fin p × Fin p) = Fintype.card A := by
    have h1 : Fintype.card A = p ^ 3 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [h1, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    ring
  have hbij := (Fintype.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcardeq⟩
  have hp1 : 1 < p := hp.one_lt
  let z0 : Fin p := ⟨0, hp0⟩
  let o0 : Fin p := ⟨1, hp1⟩
  have ho0 : o0 ≠ z0 := fun h' => by
    have := congrArg Fin.val h'
    simp [o0, z0] at this
  have hord : ∀ e : G, e ^ p = 1 → e ≠ 1 → ∀ m : ℤ, e ^ m = 1 → (p : ℤ) ∣ m := by
    intro e he he1 m hm
    have h1 : orderOf e = p := orderOf_eq_prime he he1
    have := (orderOf_dvd_iff_zpow_eq_one (x := e) (i := m)).mpr hm
    rwa [h1] at this
  have ha1 : a ≠ 1 := by
    intro ha1
    have hinj := hbij.1 (a₁ := (o0, z0, z0)) (a₂ := (z0, z0, z0))
      (Subtype.ext (by simp [φ, z0, o0, ha1]))
    exact ho0 (Prod.ext_iff.mp hinj).1
  have hc1 : c ≠ 1 := by
    intro hc1
    have hinj := hbij.1 (a₁ := (z0, o0, z0)) (a₂ := (z0, z0, z0))
      (Subtype.ext (by simp [φ, z0, o0, hc1]))
    exact ho0 (Prod.ext_iff.mp (Prod.ext_iff.mp hinj).2).1
  have hd1 : d ≠ 1 := by
    intro hd1
    have hinj := hbij.1 (a₁ := (z0, z0, o0)) (a₂ := (z0, z0, z0))
      (Subtype.ext (by simp [φ, z0, o0, hd1]))
    exact ho0 (Prod.ext_iff.mp (Prod.ext_iff.mp hinj).2).2
  obtain ⟨kx, hkx⟩ := hred a ha x
  obtain ⟨ky, hky⟩ := hred c hc y
  obtain ⟨kz, hkz⟩ := hred d hd z
  have heq : φ (kx, ky, kz) = φ (z0, z0, z0) := by
    apply Subtype.ext
    simp only [φ, z0]
    rw [← hkx, ← hky, ← hkz, h]
    simp
  have hinj := hbij.1 heq
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨h1, h2, h3⟩ := hinj
  have hax : a ^ x = 1 := by rw [hkx, h1]; simp [z0]
  have hcy : c ^ y = 1 := by rw [hky, h2]; simp [z0]
  have hdz : d ^ z = 1 := by rw [hkz, h3]; simp [z0]
  exact ⟨hord a ha ha1 x hax, hord c hc hc1 y hcy, hord d hd hd1 z hdz⟩

theorem InducesFieldAut.zpow {G : Type} [Group G] {p : ℕ} {a : G} {J : Subgroup G}
    (hp : p.Prime) (h : InducesFieldAut p a J) (hap : a ^ p = 1) {i : ℤ} (hi : ¬ (p : ℤ) ∣ i) :
    InducesFieldAut p (a ^ i) J := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hN, hnot, -, t, n, f, hf, hmodel, hfix⟩ := h
  have hcent := S11d.centralizer_zpow_eq (G := G) hp hap hi
  have hzpow : ∀ n : ℤ, (p : ℤ) ∣ n → a ^ n = 1 := fun n hn => by
    obtain ⟨t', rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, hap, one_zpow]
  have hEq : J ⊓ centralizer ({a ^ i} : Set G) = J ⊓ centralizer ({a} : Set G) := by
    rw [hcent]
  refine ⟨Subgroup.zpow_mem _ hN i, ?_, ?_, t, n, f, hf, hmodel, ?_⟩
  · intro hmem
    apply hnot
    obtain ⟨m, hm⟩ := Sec11Indeed.exists_nat_mul_add_dvd (p := p) hi (-1)
    have h1 : (a ^ i) ^ (m : ℤ) = a := by
      rw [← zpow_mul]
      have h2 : a ^ (i * (m : ℤ) + -1) = 1 := hzpow _ hm
      calc a ^ (i * (m : ℤ)) = a ^ (i * (m : ℤ) + -1) * a := by
            rw [zpow_add, zpow_neg_one]
            group
        _ = a := by rw [h2, one_mul]
    rw [← h1]
    exact Subgroup.zpow_mem _ hmem _
  · have : (a ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    rw [this]
    exact Subgroup.one_mem _
  · let P : Subgroup G → Prop := fun X =>
      LieModel (↥(inSubgroup perfectResidual X) ⧸ Subgroup.center ↥(inSubgroup perfectResidual X))
        t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        LieModel (↥(inSubgroup perfectResidual X) ⧸
          Subgroup.center ↥(inSubgroup perfectResidual X)) .Tits 0 2 1)
    have key : ∀ X Y : Subgroup G, X = Y → P X → P Y := by
      intro X Y hXY
      subst hXY
      exact id
    exact key _ _ hEq.symm hfix

theorem exists_zpow_coords_of_sup {G : Type} [Group G] {A : Subgroup G} {u v w : G}
    (hA : A = zpowers u ⊔ zpowers v ⊔ zpowers w) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hwA : w ∈ A) {g : G} (hg : g ∈ A) : ∃ x y z : ℤ, g = u ^ x * v ^ y * w ^ z := by
  have hcommw : ∀ β ∈ zpowers u ⊔ zpowers v, Commute β w := by
    intro β hβ
    have hβA : β ∈ A := by
      rw [hA]
      exact Subgroup.mem_sup_left hβ
    exact hcomm β hβA w hwA
  have hg' : g ∈ (zpowers u ⊔ zpowers v) ⊔ zpowers w := by
    rw [← hA]
    exact hg
  obtain ⟨β, hβ, z, hz⟩ := (S11d.mem_sup_zpowers_iff hcommw).mp hg'
  have huv : Commute u v := by
    have hu : u ∈ A := by
      rw [hA]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
    have hv : v ∈ A := by
      rw [hA]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
    exact hcomm u hu v hv
  obtain ⟨x, y, hxy⟩ := (S11d.mem_zpowers_sup_zpowers_iff huv).mp hβ
  exact ⟨x, y, z, by rw [hz, hxy]⟩

namespace Sec11Indeed

namespace Sit

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}
  {a d : G}

theorem A_elem (sit : Sit p A c L a d) : IsElementaryAbelian p A := sit.setup.2.2.2.2.2.2.1

theorem prime (sit : Sit p A c L a d) : p.Prime := sectionTenSetup_prime sit.setup

theorem three_lt (sit : Sit p A c L a d) : 3 < p := sectionTenSetup_three_lt sit.setup

theorem five_le (sit : Sit p A c L a d) : 5 ≤ p := by
  have hp := sit.prime
  have h3 := sit.three_lt
  by_contra hlt
  have h4 : p = 4 := by omega
  rw [h4] at hp
  exact absurd hp (by decide)

theorem A_comm (sit : Sit p A c L a d) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  have hAe : IsElementaryAbelian p A := sit.A_elem
  exact congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem pow_eq_one (sit : Sit p A c L a d) {x : G} (hx : x ∈ A) : x ^ p = 1 := by
  have : IsElementaryAbelian p A := sit.A_elem
  exact elemPow_eq_one_of_isElementaryAbelian (p := p) x hx

theorem L_le_centralizer (sit : Sit p A c L a d) : L ≤ centralizer ({c} : Set G) :=
  (mem_thetaComponentsAt_iff.mp sit.L_mem.2).1

theorem comm_c_L (sit : Sit p A c L a d) {x : G} (hx : x ∈ L) : x * c = c * x :=
  mem_centralizer_singleton_iff.mp (sit.L_le_centralizer hx)

theorem d_mem_L (sit : Sit p A c L a d) : d ∈ L :=
  (Subgroup.mem_inf.mp (sit.d_gen ▸ Subgroup.mem_zpowers d)).2

theorem zpow_c_mem_centralizer (sit : Sit p A c L a d) (j : ℤ) :
    c ^ j ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro g hg
  exact (Commute.zpow_right (show Commute g c from sit.comm_c_L hg) j).eq

theorem inducesFieldAut_mul (sit : Sit p A c L a d) {i : ℤ} (j : ℤ) (hi : ¬ (p : ℤ) ∣ i) :
    InducesFieldAut p (a ^ i * c ^ j) L := by
  have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
  have hcp : c ^ p = 1 := sit.pow_eq_one sit.c_mem
  have hai : InducesFieldAut p (a ^ i) L := sit.a_field.zpow sit.prime hap hi
  refine hai.mul_centralizer (sit.zpow_c_mem_centralizer j) ?_
  have hcomm : Commute (a ^ i) (c ^ j) :=
    (Commute.zpow_zpow (show Commute a c from sit.A_comm sit.a_mem sit.c_mem) i j)
  have h1 : (a ^ i) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
  have h2 : (c ^ j) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  rw [hcomm.mul_pow, h1, h2, one_mul]
  exact Subgroup.one_mem _

theorem exists_zpow_mul (sit : Sit p A c L a d) {f : G} (hf : f ∈ zpowers a ⊔ zpowers c) :
    ∃ i j : ℤ, f = a ^ i * c ^ j :=
  S11d.mem_zpowers_sup_zpowers_iff
    (show Commute a c from sit.A_comm sit.a_mem sit.c_mem) |>.mp hf


theorem exists_zpow_coords (sit : Sit p A c L a d) {g : G} (hg : g ∈ A) :
    ∃ x y z : ℤ, g = a ^ x * c ^ y * d ^ z :=
  exists_zpow_coords_of_sup sit.A_eq (fun _ hx _ hy => sit.A_comm hx hy) sit.d_mem hg

theorem coords_eq_one (sit : Sit p A c L a d) {x y z : ℤ} (h : a ^ x * c ^ y * d ^ z = 1) :
    (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z :=
  coords_eq_one_of_card sit.prime sit.a_mem sit.c_mem sit.d_mem (sit.pow_eq_one sit.a_mem)
    (sit.pow_eq_one sit.c_mem) (sit.pow_eq_one sit.d_mem) sit.setup.2.2.2.2.2.2.2.1
    (fun _ hg => sit.exists_zpow_coords hg) h

theorem c_not_mem_sup (sit : Sit p A c L a d) {i : ℤ} (j : ℤ) (hi : ¬ (p : ℤ) ∣ i) :
    c ∉ zpowers (a ^ i * c ^ j) ⊔ zpowers d := by
  intro hc
  have hfd : Commute (a ^ i * c ^ j) d := by
    have h1 : Commute a d := sit.A_comm sit.a_mem sit.d_mem
    have h2 : Commute c d := sit.A_comm sit.c_mem sit.d_mem
    exact ((h1.zpow_left i).mul_left (h2.zpow_left j))
  obtain ⟨x, z, hxz⟩ := (S11d.mem_zpowers_sup_zpowers_iff hfd).mp hc
  have hac : Commute a c := sit.A_comm sit.a_mem sit.c_mem
  have hcomm : Commute (a ^ i) (c ^ j) := hac.zpow_zpow i j
  have hcd : Commute c d := sit.A_comm sit.c_mem sit.d_mem
  have e1 : (a ^ i * c ^ j) ^ x = a ^ (i * x) * c ^ (j * x) := by
    rw [hcomm.mul_zpow, ← zpow_mul, ← zpow_mul]
  have hcdz : c⁻¹ * d ^ z = d ^ z * c⁻¹ := ((hcd.zpow_right z).inv_left).eq
  have h1 : a ^ (i * x) * c ^ (j * x - 1) * d ^ z = 1 := by
    calc a ^ (i * x) * c ^ (j * x - 1) * d ^ z
        = a ^ (i * x) * c ^ (j * x) * (c⁻¹ * d ^ z) := by rw [zpow_sub_one]; group
      _ = a ^ (i * x) * c ^ (j * x) * (d ^ z * c⁻¹) := by rw [hcdz]
      _ = (a ^ (i * x) * c ^ (j * x) * d ^ z) * c⁻¹ := by group
      _ = 1 := by rw [← e1, ← hxz]; group
  obtain ⟨h1p, h2p, -⟩ := sit.coords_eq_one h1
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp sit.prime
  have hx : (p : ℤ) ∣ x := by
    rcases hpZ.dvd_mul.mp h1p with h | h
    · exact absurd h hi
    · exact h
  have h3 : (p : ℤ) ∣ j * x := Dvd.dvd.mul_left hx j
  have h4 : (p : ℤ) ∣ 1 := by
    have := dvd_sub h3 h2p
    simpa using this
  have h5 := Int.eq_one_of_dvd_one (by positivity) h4
  have : p = 1 := by exact_mod_cast h5
  exact sit.prime.one_lt.ne' this

end Sit

end Sec11Indeed

end CFSG.RankThree.PartOne
