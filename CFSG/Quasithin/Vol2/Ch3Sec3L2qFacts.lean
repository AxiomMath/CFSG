module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.Quasithin.H13.L2q

open CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F] {q : ℕ}

omit [Field F] [Finite F] in
theorem isOddPrimePower (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) :
    IsOddPrimePower (Nat.card F) :=
  ⟨q, 1, hq, hq.odd_of_ne_two (by omega), le_rfl, by rw [hF, pow_one]⟩

theorem card_psl2 (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) :
    Nat.card (PSL2 F) = q * (q ^ 2 - 1) / 2 := by
  rw [psl2_card_formula F (isOddPrimePower hF hq hq5), hF]

theorem gcd_two (hq : q.Prime) (hq5 : 5 ≤ q) : (q - 1).gcd 2 = 2 := by
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  have : q - 1 = 2 * k := by omega
  rw [this, Nat.gcd_comm, Nat.gcd_mul_right_right]

theorem dickson (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (H : Subgroup (PSL2 F)) :
    CFSG.IsElementaryAbelian q ↥H ∨
      (∃ z : ℕ, (z ∣ (q - 1) / 2 ∨ z ∣ (q + 1) / 2) ∧ Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ, (z ∣ (q - 1) / 2 ∨ z ∣ (q + 1) / 2) ∧ Nat.card H = 2 * z ∧
        Nonempty (H ≃* DihedralGroup z)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      (16 ∣ q ^ 2 - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
      (∃ N C : Subgroup H, N.Normal ∧ CFSG.IsElementaryAbelian q N ∧ IsCyclic C ∧
        Disjoint N C ∧ N ⊔ C = ⊤) ∨
      H = ⊤ := by
  have : Fact q.Prime := ⟨hq⟩
  have hF1 : Nat.card F = q ^ 1 := by rw [hF, pow_one]
  have hg := gcd_two hq hq5
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF1 H with
    h | ⟨z, hz, hc, hcyc⟩ | ⟨z, hz, hc, hd⟩ | ⟨-, h⟩ | ⟨h16, h⟩ | ⟨-, h⟩ |
      ⟨m, t, -, -, N, C, hN, hNe, -, hC, -, hdisj, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, -⟩
  · exact Or.inl h
  · rw [hF, hg] at hz
    exact Or.inr (Or.inl ⟨z, hz, hc, hcyc⟩)
  · rw [hF, hg] at hz
    exact Or.inr (Or.inr (Or.inl ⟨z, hz, hc, hd⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [mul_one] at h16
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h16, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨N, C, hN, hNe, hC, hdisj,
      hsup⟩))))))
  ·
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hmf
    subst hm1
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
    apply Subgroup.eq_top_of_card_eq
    have hGF : Nat.card (GaloisField q 1) = q := by
      rw [GaloisField.card q 1 (by norm_num), pow_one]
    rw [Nat.card_congr e.toEquiv, card_psl2 hGF hq hq5, card_psl2 hF hq hq5]
  · exfalso
    have : 2 * m ∣ 1 := hmf
    have h1 := Nat.le_of_dvd (by norm_num) this
    omega

theorem eight_dvd_card_sylow (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (h8 : q % 8 = 1 ∨ q % 8 = 7) {S : Subgroup (PSL2 F)} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : 8 ∣ Nat.card S := by
  have hG := card_psl2 hF hq hq5
  have hmul := Subgroup.card_mul_index S
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
  have h8G : 8 ∣ q * (q ^ 2 - 1) / 2 := by
    have : 16 ∣ q ^ 2 - 1 := by
      rcases h8 with h | h
      · obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + 1 := ⟨q / 8, by omega⟩
        subst hk
        refine ⟨k * (4 * k + 1), ?_⟩
        have : (8 * k + 1) ^ 2 = 64 * k ^ 2 + 16 * k + 1 := by ring
        rw [this]
        ring_nf
        omega
      · obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + 7 := ⟨q / 8, by omega⟩
        subst hk
        refine ⟨4 * k ^ 2 + 7 * k + 3, ?_⟩
        have : (8 * k + 7) ^ 2 = 64 * k ^ 2 + 112 * k + 49 := by ring
        rw [this]
        ring_nf
        omega
    obtain ⟨m, hm⟩ := this
    refine ⟨q * m, ?_⟩
    rw [hm]
    have : q * (16 * m) = 2 * (8 * (q * m)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [← hG, ← hmul, hn] at h8G
  rw [hn]
  have hodd : Odd S.index := Nat.odd_iff.mpr (by omega)
  have hcop : Nat.Coprime 8 S.index := by
    have : Nat.Coprime (2 ^ 3) S.index :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  exact hcop.dvd_of_dvd_mul_right h8G

theorem card_sylow_eq_four (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (h3 : q % 8 = 3 ∨ q % 8 = 5) {S : Subgroup (PSL2 F)} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : Nat.card S = 4 := by
  have hG := card_psl2 hF hq hq5
  have hmul := Subgroup.card_mul_index S
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
  obtain ⟨u, hu, hGu⟩ : ∃ u, Odd u ∧ q * (q ^ 2 - 1) / 2 = 4 * u := by
    have hqo : Odd q := hq.odd_of_ne_two (by omega)
    rcases h3 with h | h
    · obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
      subst hk
      refine ⟨(8 * k + 3) * (8 * k ^ 2 + 6 * k + 1), ?_, ?_⟩
      · refine Nat.odd_mul.mpr ⟨hqo, ⟨4 * k ^ 2 + 3 * k, by ring⟩⟩
      · have : (8 * k + 3) ^ 2 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by
          have : (8 * k + 3) ^ 2 = 64 * k ^ 2 + 48 * k + 9 := by ring
          rw [this]
          omega
        rw [this]
        have : (8 * k + 3) * (8 * (8 * k ^ 2 + 6 * k + 1)) =
            2 * (4 * ((8 * k + 3) * (8 * k ^ 2 + 6 * k + 1))) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    · obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + 5 := ⟨q / 8, by omega⟩
      subst hk
      refine ⟨(8 * k + 5) * (8 * k ^ 2 + 10 * k + 3), ?_, ?_⟩
      · refine Nat.odd_mul.mpr ⟨hqo, ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩⟩
      · have : (8 * k + 5) ^ 2 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by
          have : (8 * k + 5) ^ 2 = 64 * k ^ 2 + 80 * k + 25 := by ring
          rw [this]
          omega
        rw [this]
        have : (8 * k + 5) * (8 * (8 * k ^ 2 + 10 * k + 3)) =
            2 * (4 * ((8 * k + 5) * (8 * k ^ 2 + 10 * k + 3))) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hGu, ← hmul, hn] at hG
  rw [hn]
  have hodd : Odd S.index := Nat.odd_iff.mpr (by omega)
  have h1 : 2 ^ n ∣ 4 * u := ⟨S.index, hG.symm⟩
  have h2 : 4 ∣ 2 ^ n * S.index := ⟨u, hG⟩
  have hcop4 : Nat.Coprime 4 S.index := by
    have : Nat.Coprime (2 ^ 2) S.index :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have h4 : 4 ∣ 2 ^ n := hcop4.dvd_of_dvd_mul_right h2
  have hcopu : Nat.Coprime (2 ^ n) u :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hu)
  have h5 : 2 ^ n ∣ 4 := hcopu.dvd_of_dvd_mul_right h1
  exact Nat.dvd_antisymm h5 h4

theorem alt4_pow_four (x : alternatingGroup (Fin 4)) (h : x ^ 4 = 1) : x ^ 2 = 1 := by
  revert x
  decide +kernel

theorem alt4_card_sq :
    (Finset.univ.filter fun x : alternatingGroup (Fin 4) => x ^ 2 = 1).card = 4 := by
  decide +kernel

theorem alt4_conj (x y : alternatingGroup (Fin 4)) (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ^ 3 = 1)
    (hy1 : y ≠ 1) : ∃ g : alternatingGroup (Fin 4), g * x * g⁻¹ = y ∨ g * x⁻¹ * g⁻¹ = y := by
  revert x y
  decide +kernel

theorem alt4_card_cube :
    (Finset.univ.filter fun x : alternatingGroup (Fin 4) => x ^ 3 = 1).card = 9 := by
  decide +kernel

theorem perm4_card_two :
    (Finset.univ.filter fun x : Equiv.Perm (Fin 4) => x ^ 8 = 1).card = 16 := by
  decide +kernel

theorem dihedral2_sq (x : DihedralGroup 2) : x ^ 2 = 1 := by
  revert x
  decide +kernel

section General

variable {G : Type*} [Group G]

theorem eq_bot_of_le_elemAb {H S : Subgroup G} {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hH : CFSG.IsElementaryAbelian p ↥H) (hS : S ≤ H) (hSr : IsPGroup r S) :
    S = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hSr) ⟨x, hx⟩
  have h1 : orderOf (⟨x, hS hx⟩ : ↥H) ∣ p :=
    (Monoid.order_dvd_exponent _).trans hH.exponent_dvd_p
  rw [Subgroup.orderOf_mk] at h1
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at h1
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · exfalso
    have hrp : r ∣ p := (dvd_pow_self r (Nat.succ_ne_zero k)).trans h1
    exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp hrp).symm

theorem exists_sr_mem {z : ℕ} [NeZero z] {S : Subgroup (DihedralGroup z)} (hS : ¬ IsCyclic S) :
    ∃ i, DihedralGroup.sr i ∈ S := by
  by_contra h
  simp only [not_exists] at h
  apply hS
  have hle : S ≤ Subgroup.zpowers (DihedralGroup.r 1) := by
    intro x hx
    rcases x with j | j
    · refine ⟨(j.val : ℤ), ?_⟩
      show DihedralGroup.r 1 ^ ((j.val : ℕ) : ℤ) = DihedralGroup.r j
      rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    · exact absurd hx (h j)
  exact Subgroup.isCyclic_of_le hle

theorem pow_two_of_normal {z : ℕ} [NeZero z] {S : Subgroup (DihedralGroup z)} (hS : S.Normal)
    (hS2 : IsPGroup 2 S) {i : ZMod z} (hi : DihedralGroup.sr i ∈ S) : ∃ k, z = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : DihedralGroup.sr (i - 2) ∈ S := by
    have := hS.conj_mem _ hi (DihedralGroup.r 1)
    rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at this
    convert this using 2
    ring
  have h2 : DihedralGroup.r 2 ∈ S := by
    have := S.mul_mem h1 hi
    rw [DihedralGroup.sr_mul_sr] at this
    convert this using 2
    ring
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨_, h2⟩
  rw [Subgroup.orderOf_mk, DihedralGroup.orderOf_r] at ha
  rcases Nat.lt_or_ge z 3 with hz | hz
  · have hz0 : z ≠ 0 := NeZero.ne z
    interval_cases z
    · exact absurd rfl hz0
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
  · have hv : (2 : ZMod z).val = 2 := by
      rw [ZMod.val_ofNat_of_lt hz]
    rw [hv] at ha
    rcases Nat.even_or_odd z with he | ho
    · have hg : z.gcd 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp he)
      rw [hg] at ha
      refine ⟨a + 1, ?_⟩
      have := Nat.div_mul_cancel (even_iff_two_dvd.mp he)
      rw [ha] at this
      rw [← this, pow_succ]
    · have hg : z.gcd 2 = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr ho)
      rw [hg, Nat.div_one] at ha
      exact ⟨a, ha⟩

theorem isCyclic_of_semidirect [Finite G] {N C : Subgroup G} (hNn : N.Normal) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : CFSG.IsElementaryAbelian p ↥N) (hC : IsCyclic C)
    (hsup : N ⊔ C = ⊤) {S : Subgroup G} (hS2 : IsPGroup 2 S) : IsCyclic S := by
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective (π.comp C.subtype) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hg : g ∈ N ⊔ C := hsup ▸ Subgroup.mem_top g
    obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨c, hc⟩, ?_⟩
    have hn1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show π c = π (n * c)
    rw [map_mul, hn1, one_mul]
  have : IsCyclic (G ⧸ N) := isCyclic_of_surjective _ hsurj
  have hSN : S ⊓ N = ⊥ :=
    eq_bot_of_le_elemAb hp Nat.prime_two hp2 hN inf_le_right (hS2.to_inf_left)
  refine isCyclic_of_injective (π.comp S.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
  have h2 : (x : G) ∈ S ⊓ N := ⟨x.2, h1⟩
  rw [hSN, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

end General

theorem card_alt4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_perm4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_psl2_facts (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) :
    2 ∣ Nat.card (PSL2 F) ∧ 60 ≤ Nat.card (PSL2 F) ∧ q ∣ Nat.card (PSL2 F) := by
  rw [card_psl2 hF hq hq5]
  have hqo : Odd q := hq.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hqo
  subst hk
  have e : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [e]
  have e2 : (2 * k + 1) * (4 * (k * (k + 1))) / 2 = (2 * k + 1) * (2 * (k * (k + 1))) := by
    have : (2 * k + 1) * (4 * (k * (k + 1))) = 2 * ((2 * k + 1) * (2 * (k * (k + 1)))) := by
      ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [e2]
  refine ⟨⟨(2 * k + 1) * (k * (k + 1)), by ring⟩, ?_, ⟨2 * (k * (k + 1)), rfl⟩⟩
  have hk2 : 2 ≤ k := by omega
  have : 5 * (2 * (2 * 3)) ≤ (2 * k + 1) * (2 * (k * (k + 1))) := by
    apply Nat.mul_le_mul (by omega)
    apply Nat.mul_le_mul le_rfl
    exact Nat.mul_le_mul hk2 (by omega)
  omega

theorem not_isCyclic_sylow (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    {S : Subgroup (PSL2 F)} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) : ¬ IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    psl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower hF hq hq5) (hS2.toSylow hSi)
  have : IsCyclic ↥((hS2.toSylow hSi : Subgroup (PSL2 F))) := hcyc
  have : IsCyclic (DihedralGroup (2 ^ m)) := isCyclic_of_surjective e.toMonoidHom e.surjective
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · have hm1 : m = 1 := by omega
    subst hm1
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := DihedralGroup (2 ^ 1))
    have h4 : Nat.card (DihedralGroup (2 ^ 1)) = 4 := by
      rw [DihedralGroup.nat_card]
      norm_num
    have hg2 : g ^ 2 = 1 := dihedral2_sq g
    have := orderOf_le_of_pow_eq_one (by norm_num) hg2
    omega
  · have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2
    exact DihedralGroup.not_commutative (n := 2 ^ m) (by omega) (by omega)
      IsCyclic.isMulCommutative

theorem isCyclic_of_eq_bot {G : Type*} [Group G] {H : Subgroup G} (h : H = ⊥) : IsCyclic H := by
  subst h
  exact Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (1 : G)) bot_le

theorem isCyclic_of_isPGroup_three (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (H : Subgroup (PSL2 F)) (h3 : IsPGroup 3 H) : IsCyclic H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h3
  have hodd : Odd (Nat.card H) := hk ▸ (by decide : Odd 3).pow
  have hq3 : q ≠ 3 := by omega
  rcases dickson hF hq hq5 H with h | ⟨z, -, -, hcyc⟩ | ⟨z, -, hc, -⟩ | ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨⟨e⟩⟩ |
      ⟨N, C, hN, hNe, hC, -, hsup⟩ | htop
  · exact isCyclic_of_eq_bot (eq_bot_of_le_elemAb hq Nat.prime_three hq3 h le_rfl h3)
  · exact hcyc
  · rw [hc] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega
  · rw [Nat.card_congr e.toEquiv, card_alt4] at hodd
    exact absurd hodd (by decide)
  · rw [Nat.card_congr e.toEquiv, card_perm4] at hodd
    exact absurd hodd (by decide)
  · rw [Nat.card_congr e.toEquiv, card_alt5] at hodd
    exact absurd hodd (by decide)
  · have hN3 : IsPGroup 3 N := h3.to_subgroup N
    have hNb : N = ⊥ := eq_bot_of_le_elemAb hq Nat.prime_three hq3 hNe le_rfl hN3
    rw [hNb, bot_sup_eq] at hsup
    have hCs : Function.Surjective C.subtype := by
      intro x
      exact ⟨⟨x, hsup ▸ Subgroup.mem_top x⟩, rfl⟩
    exact isCyclic_of_surjective C.subtype hCs
  · exfalso
    rw [htop, Subgroup.card_top] at hodd
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨c, hc⟩ := (card_psl2_facts hF hq hq5).1
    omega

theorem false_of_normal_perm4 {K : Subgroup (Equiv.Perm (Fin 4))} (hK : K.Normal)
    (hc : Nat.card K = 8) : False := by
  classical
  have hidx : K.index = 3 := by
    have := Subgroup.card_mul_index K
    rw [hc, card_perm4] at this
    omega
  have hmem : ∀ x : Equiv.Perm (Fin 4), x ^ 8 = 1 → x ∈ K := by
    intro x hx
    have h3 : (x : Equiv.Perm (Fin 4) ⧸ K) ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (x : Equiv.Perm (Fin 4) ⧸ K))
      rwa [← Subgroup.index_eq_card, hidx] at this
    have h8 : (x : Equiv.Perm (Fin 4) ⧸ K) ^ 8 = 1 := by
      rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
    have h1 : (x : Equiv.Perm (Fin 4) ⧸ K) = 1 := by
      have e : (x : Equiv.Perm (Fin 4) ⧸ K) =
          ((x : Equiv.Perm (Fin 4) ⧸ K) ^ 3) ^ 3 * ((x : Equiv.Perm (Fin 4) ⧸ K) ^ 8)⁻¹ := by
        group
      rw [e, h3, h8]
      simp
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hsub : ((Finset.univ.filter fun x : Equiv.Perm (Fin 4) => x ^ 8 = 1 :
      Finset (Equiv.Perm (Fin 4))) : Set (Equiv.Perm (Fin 4))) ⊆
        (K : Set (Equiv.Perm (Fin 4))) := by
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hx
    exact hmem x hx
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, perm4_card_two, ← Nat.card_coe_set_eq] at h1
  have h2 : Nat.card (K : Set (Equiv.Perm (Fin 4))) = 8 := hc
  omega

theorem card_pow_two_of_dihedral {X : Type*} [Group X] [Finite X] {z : ℕ}
    (e : X ≃* DihedralGroup z) {S : Subgroup X} (hS : S.Normal) (hS2 : IsPGroup 2 S)
    (hc : ¬ IsCyclic S) : ∃ a, Nat.card X = 2 ^ a := by
  have hz : z ≠ 0 := by
    intro h0
    subst h0
    have := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at this
    have : 0 < Nat.card X := Nat.card_pos
    omega
  have : NeZero z := ⟨hz⟩
  set K := S.map e.toMonoidHom with hK
  have hKn : K.Normal := hS.map _ e.surjective
  have hK2 : IsPGroup 2 K := hS2.map _
  have hKc : ¬ IsCyclic K := fun h =>
    hc ((MulEquiv.isCyclic (S.equivMapOfInjective e.toMonoidHom e.injective)).mpr h)
  obtain ⟨i, hi⟩ := exists_sr_mem hKc
  obtain ⟨k, hk⟩ := pow_two_of_normal hKn hK2 hi
  refine ⟨k + 1, ?_⟩
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk, pow_succ]
  ring

theorem normalizer_sylow_eq (hF : Nat.card F = q) (hq : q.Prime)
    (hq5 : 5 ≤ q) (h8 : q % 8 = 1 ∨ q % 8 = 7) {S : Subgroup (PSL2 F)} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : Subgroup.normalizer (S : Set (PSL2 F)) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (S : Set (PSL2 F)) with hNdef
  have hSN : S ≤ N := Subgroup.le_normalizer
  have hS8 := eight_dvd_card_sylow hF hq hq5 h8 hS2 hSi
  have hnc := not_isCyclic_sylow hF hq hq5 hS2 hSi
  have hq2 : q ≠ 2 := by omega
  set S' := S.subgroupOf N with hS'
  have hS'n : S'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr le_rfl
  have eS : ↥S' ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSN
  have hS'2 : IsPGroup 2 S' := hS2.of_equiv eS.symm
  have hS'c : ¬ IsCyclic S' := fun h => hnc ((MulEquiv.isCyclic eS).mp h)
  have hcS' : Nat.card S' = Nat.card S := Nat.card_congr eS.toEquiv
  have hSne : S ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hS8
    omega
  suffices h2N : ∃ a, Nat.card N = 2 ^ a by
    obtain ⟨a, ha⟩ := h2N
    have hdvd : Nat.card N ∣ Nat.card (PSL2 F) := Subgroup.card_subgroup_dvd_card N
    rw [← Subgroup.card_mul_index S] at hdvd
    have hodd : Odd S.index := Nat.odd_iff.mpr (by omega)
    have hcop : Nat.Coprime (Nat.card N) S.index := by
      rw [ha]
      exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
    have h1 : Nat.card N ∣ Nat.card S := hcop.dvd_of_dvd_mul_right hdvd
    exact (Subgroup.eq_of_le_of_card_ge hSN (Nat.le_of_dvd Nat.card_pos h1)).symm
  rcases dickson hF hq hq5 N with h | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨⟨e⟩⟩ | ⟨N₁, C, hN₁, hNe, hC, -, hsup⟩ | htop
  · exact absurd (eq_bot_of_le_elemAb hq Nat.prime_two hq2 h hSN hS2) hSne
  · exact absurd (Subgroup.isCyclic S') hS'c
  · exact card_pow_two_of_dihedral e hS'n hS'2 hS'c
  · exfalso
    have h1 := Subgroup.card_dvd_of_le hSN
    rw [Nat.card_congr e.toEquiv, card_alt4] at h1
    have := hS8.trans h1
    omega
  · exfalso
    have h1 := Subgroup.card_dvd_of_le hSN
    rw [Nat.card_congr e.toEquiv, card_perm4] at h1
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
    have hb8 : Nat.card S = 8 := by
      rw [hb] at h1 hS8 ⊢
      have hcop : Nat.Coprime (2 ^ b) 3 := Nat.Coprime.pow_left b (by norm_num)
      have h2 : 2 ^ b ∣ 8 := hcop.dvd_of_dvd_mul_right (by simpa using h1)
      exact Nat.dvd_antisymm h2 hS8
    have hmap : Nat.card ↥(S'.map e.toMonoidHom) = 8 := by
      rw [← hb8, ← hcS']
      exact (Nat.card_congr (S'.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
    exact false_of_normal_perm4 (hS'n.map _ e.surjective) hmap
  · exfalso
    have h1 := Subgroup.card_dvd_of_le hSN
    rw [Nat.card_congr e.toEquiv, card_alt5] at h1
    have := hS8.trans h1
    omega
  · exact absurd (isCyclic_of_semidirect hN₁ hq hq2 hNe hC hsup hS'2) hS'c
  · exfalso
    have hnorm : S.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hsimp : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    rcases hsimp.eq_bot_or_eq_top_of_normal S with hb | ht
    · exact hSne hb
    · obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
      have h1 : q ∣ Nat.card S := by
        rw [ht, Subgroup.card_top]
        exact (card_psl2_facts hF hq hq5).2.2
      rw [hb] at h1
      have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1)
      exact hq2 this

theorem normal_of_card_four_alt4 {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 4)) {S : Subgroup X} (hS : Nat.card S = 4) : S.Normal := by
  classical
  set K := S.map e.toMonoidHom with hK
  have hKc : Nat.card K = 4 :=
    ((Nat.card_congr (S.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm).trans hS
  have hKsq : ∀ x ∈ K, x ^ 2 = 1 := by
    intro x hx
    apply alt4_pow_four
    have := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥K))
    rw [hKc] at this
    exact congrArg Subtype.val this
  have hsub : (K : Set (alternatingGroup (Fin 4))) ⊆
      ((Finset.univ.filter fun x : alternatingGroup (Fin 4) => x ^ 2 = 1 :
        Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))) := by
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact hKsq x hx
  have hcard : ((Finset.univ.filter fun x : alternatingGroup (Fin 4) => x ^ 2 = 1 :
      Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))).ncard ≤
      (K : Set (alternatingGroup (Fin 4))).ncard := by
    rw [Set.ncard_coe_finset, alt4_card_sq, ← Nat.card_coe_set_eq]
    exact hKc.ge
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  constructor
  intro s hs g
  have hx : e s ∈ K := ⟨s, hs, rfl⟩
  have h1 : e (g * s * g⁻¹) ∈ (K : Set (alternatingGroup (Fin 4))) := by
    rw [heq]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    rw [map_mul, map_mul, map_inv]
    have := hKsq _ hx
    calc (e g * e s * (e g)⁻¹) ^ 2 = e g * (e s) ^ 2 * (e g)⁻¹ := by
          rw [pow_two, pow_two]
          group
      _ = 1 := by rw [this, mul_one, mul_inv_cancel]
  obtain ⟨s', hs', e'⟩ := h1
  have : s' = g * s * g⁻¹ := e.injective e'
  exact this ▸ hs'

theorem eq_top_of_normal_alt4 {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 4)) {N : Subgroup X} (hN : N.Normal)
    (h3 : 3 ∣ Nat.card N) : N = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := N.map e.toMonoidHom with hK
  have hKn : K.Normal := hN.map _ e.surjective
  have hKc : Nat.card K = Nat.card N :=
    (Nat.card_congr (N.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥K) 3
    (by rw [← Nat.card_eq_fintype_card, hKc]; exact h3)
  have hx3 : (x : alternatingGroup (Fin 4)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : (x : alternatingGroup (Fin 4)) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  have hmem : ∀ y : alternatingGroup (Fin 4), y ^ 3 = 1 → y ∈ K := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact K.one_mem
    obtain ⟨g, hg | hg⟩ := alt4_conj _ y hx3 hx1 hy hy1
    · rw [← hg]
      exact hKn.conj_mem _ x.2 g
    · rw [← hg]
      exact hKn.conj_mem _ (K.inv_mem x.2) g
  have hsub : ((Finset.univ.filter fun y : alternatingGroup (Fin 4) => y ^ 3 = 1 :
      Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))) ⊆
      (K : Set (alternatingGroup (Fin 4))) := by
    intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy
    exact hmem y hy
  have h9 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, alt4_card_cube, ← Nat.card_coe_set_eq] at h9
  have hdvd : Nat.card K ∣ 12 := by
    rw [← card_alt4]
    exact Subgroup.card_subgroup_dvd_card K
  have h12 : Nat.card K = 12 := by
    have h9' : 9 ≤ Nat.card K := h9
    have hle : Nat.card K ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ := hdvd
    generalize Nat.card K = k at h9' hc hle ⊢
    interval_cases k <;> omega
  have hKt : K = ⊤ := Subgroup.eq_top_of_card_eq K (by rw [h12, card_alt4])
  rw [eq_top_iff]
  intro n _
  have : e n ∈ K := hKt ▸ Subgroup.mem_top _
  obtain ⟨n', hn', e'⟩ := this
  exact e.injective e' ▸ hn'

theorem sylow_sub_data (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    {S W : Subgroup (PSL2 F)} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hSW : S ≤ W) :
    IsPGroup 2 (S.subgroupOf W) ∧ ¬ IsCyclic (S.subgroupOf W) ∧
      Nat.card (S.subgroupOf W) = Nat.card S ∧ S ≠ ⊥ := by
  have eS : ↥(S.subgroupOf W) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSW
  have hnc := not_isCyclic_sylow hF hq hq5 hS2 hSi
  refine ⟨hS2.of_equiv eS.symm, fun h => hnc ((MulEquiv.isCyclic eS).mp h),
    Nat.card_congr eS.toEquiv, fun hb => hnc ?_⟩
  rw [hb]
  exact isCyclic_of_eq_bot rfl

theorem not_normal_sylow (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    {S : Subgroup (PSL2 F)} (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥) (hn : S.Normal) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  rcases hsimp.eq_bot_or_eq_top_of_normal S with hb | ht
  · exact hSne hb
  · obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS2
    have h1 : q ∣ Nat.card S := by
      rw [ht, Subgroup.card_top]
      exact (card_psl2_facts hF hq hq5).2.2
    rw [hb] at h1
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1)
    omega

theorem normalizer_eq_of_twelve (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (h3 : q % 8 = 3 ∨ q % 8 = 5) {S W : Subgroup (PSL2 F)}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hSW : S ≤ W) (hW : Nat.card W = 12)
    (hWN : W ≤ Subgroup.normalizer (S : Set (PSL2 F))) :
    Subgroup.normalizer (S : Set (PSL2 F)) = W ∧ Nonempty (W ≃* alternatingGroup (Fin 4)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : q ≠ 2 := by omega
  have hS4 := card_sylow_eq_four hF hq hq5 h3 hS2 hSi
  obtain ⟨hS'2, hS'c, hcS', hSne⟩ := sylow_sub_data hF hq hq5 hS2 hSi hSW
  have hS'n : (S.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSW).mpr hWN
  have hpow12 : ∀ a, 12 ≠ 2 ^ a := by
    intro a ha
    have : 3 ∣ 2 ^ a := ha ▸ (by norm_num : 3 ∣ 12)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow this)
    omega
  have hA4 : Nonempty (W ≃* alternatingGroup (Fin 4)) := by
    rcases dickson hF hq hq5 W with h | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
        ⟨⟨e⟩⟩ | ⟨N₁, C, hN₁, hNe, hC, -, hsup⟩ | htop
    · exact absurd (eq_bot_of_le_elemAb hq Nat.prime_two hq2 h hSW hS2) hSne
    · exact absurd (Subgroup.isCyclic (S.subgroupOf W)) hS'c
    · obtain ⟨a, ha⟩ := card_pow_two_of_dihedral e hS'n hS'2 hS'c
      exact absurd (hW ▸ ha) (hpow12 a)
    · exact ⟨e⟩
    · exfalso
      have := Nat.card_congr e.toEquiv
      rw [hW, card_perm4] at this
      omega
    · exfalso
      have := Nat.card_congr e.toEquiv
      rw [hW, card_alt5] at this
      omega
    · exact absurd (isCyclic_of_semidirect hN₁ hq hq2 hNe hC hsup hS'2) hS'c
    · exfalso
      rw [htop, Subgroup.card_top] at hW
      have := (card_psl2_facts hF hq hq5).2.1
      omega
  refine ⟨?_, hA4⟩
  set N := Subgroup.normalizer (S : Set (PSL2 F)) with hNdef
  have hSN : S ≤ N := Subgroup.le_normalizer
  obtain ⟨hS''2, hS''c, hcS'', -⟩ := sylow_sub_data hF hq hq5 hS2 hSi hSN
  have hS''n : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr le_rfl
  have h12N : 12 ∣ Nat.card N := hW ▸ Subgroup.card_dvd_of_le hWN
  rcases dickson hF hq hq5 N with h | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨⟨e⟩⟩ | ⟨N₁, C, hN₁, hNe, hC, -, hsup⟩ | htop
  · exact absurd (eq_bot_of_le_elemAb hq Nat.prime_two hq2 h hSN hS2) hSne
  · exact absurd (Subgroup.isCyclic (S.subgroupOf N)) hS''c
  · exfalso
    obtain ⟨a, ha⟩ := card_pow_two_of_dihedral e hS''n hS''2 hS''c
    rw [ha] at h12N
    have : 3 ∣ 2 ^ a := (by norm_num : 3 ∣ 12).trans h12N
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow this)
    omega
  · have hN12 : Nat.card N = 12 := by rw [Nat.card_congr e.toEquiv, card_alt4]
    exact (Subgroup.eq_of_le_of_card_ge hWN (by rw [hN12, hW])).symm
  · exfalso
    have h24 : Nat.card N = 24 := by rw [Nat.card_congr e.toEquiv, card_perm4]
    have h8 : 8 ∣ Nat.card (PSL2 F) := by
      have := Subgroup.card_subgroup_dvd_card N
      rw [h24] at this
      exact (by norm_num : 8 ∣ 24).trans this
    rw [← Subgroup.card_mul_index S, hS4] at h8
    have hodd : Odd S.index := Nat.odd_iff.mpr (by omega)
    obtain ⟨m, hm⟩ := hodd
    rw [hm] at h8
    omega
  · exfalso
    have hsimp : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hn := hS''n.map e.toMonoidHom e.surjective
    have hc : Nat.card ↥((S.subgroupOf N).map e.toMonoidHom) = 4 := by
      rw [← hS4, ← hcS'']
      exact (Nat.card_congr ((S.subgroupOf N).equivMapOfInjective e.toMonoidHom
        e.injective).toEquiv).symm
    have := hn
    rcases hsimp.eq_bot_or_eq_top_of_normal ((S.subgroupOf N).map e.toMonoidHom) with hb | ht
    · rw [hb, Subgroup.card_bot] at hc
      omega
    · rw [ht, Subgroup.card_top, card_alt5] at hc
      omega
  · exact absurd (isCyclic_of_semidirect hN₁ hq hq2 hNe hC hsup hS''2) hS''c
  · exfalso
    exact not_normal_sylow hF hq hq5 hS2 hSne (Subgroup.normalizer_eq_top_iff.mp htop)

theorem center_eq_bot (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) :
    Subgroup.center (PSL2 F) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2 F)) with h | h
  · exact h
  · exfalso
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (PSL2 F)))
    have hS2 : IsPGroup 2 (S : Subgroup (PSL2 F)) := S.isPGroup'
    have hSi : ¬ 2 ∣ (S : Subgroup (PSL2 F)).index := S.not_dvd_index
    obtain ⟨-, -, -, hSne⟩ :=
      sylow_sub_data hF hq hq5 hS2 hSi (le_top : (S : Subgroup (PSL2 F)) ≤ ⊤)
    refine not_normal_sylow hF hq hq5 hS2 hSne ⟨fun s _ g => ?_⟩
    have hg : g ∈ Subgroup.center (PSL2 F) := h ▸ Subgroup.mem_top g
    rwa [(Subgroup.mem_center_iff.mp hg s).symm, mul_inv_cancel_right]

theorem exists_conj_of_odd (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (α : MulAut (PSL2 F)) (hα : Odd (orderOf α)) :
    ∃ x : PSL2 F, Odd (orderOf x) ∧ ∀ y, α y = x * y * x⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  have hodd := isOddPrimePower hF hq hq5
  have h4 : 3 < Nat.card F := by omega
  have hsurj := pGammaL2ToMulAutPSL2_surjective F (p := q) (f := 1) (by rw [hF, pow_one]) hodd h4
  let eA := pGammaL2EquivMulAutPSL2 F hodd h4 hsurj
  obtain ⟨-, -, -, -, h1, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := F) hq le_rfl (by rw [hF, pow_one])
  have hev : 2 ∣ q * (q ^ 2 - 1) := by
    have h := (card_psl2_facts hF hq hq5).1
    rw [card_psl2 hF hq hq5] at h
    have hqo : Odd q := hq.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ := hqo
    subst hk
    exact ⟨(2 * k + 1) * (2 * (k * (k + 1))), by
      have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
        have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
        omega
      rw [this]
      ring⟩
  have hAut : Nat.card (MulAut (PSL2 F)) = 2 * Nat.card (PSL2 F) := by
    rw [← Nat.card_congr eA.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      pgl2_card_formula, h1, card_psl2 hF hq hq5, hF, mul_one, Nat.mul_div_cancel' hev]
  have hZ := center_eq_bot hF hq hq5
  have hinj : Function.Injective (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxz : x ∈ Subgroup.center (PSL2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut (PSL2 F) => φ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [hZ, Subgroup.mem_bot] at hxz
    exact hxz
  set I := (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range with hI
  have hIc : Nat.card I = Nat.card (PSL2 F) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : I.index = 2 := by
    have := Subgroup.card_mul_index I
    rw [hIc, hAut] at this
    have hpos : 0 < Nat.card (PSL2 F) := Nat.card_pos
    nlinarith
  have hαI : α ∈ I := by
    obtain ⟨k, hk⟩ := hα
    have hsq : α * α ∈ I := (Subgroup.mul_mem_iff_of_index_two hidx).mpr Iff.rfl
    have h1 : α ^ orderOf α ∈ I := by rw [pow_orderOf_eq_one]; exact I.one_mem
    rw [hk, pow_succ, pow_mul, sq] at h1
    exact (Subgroup.mul_mem_cancel_left I (I.pow_mem hsq k)).mp h1
  obtain ⟨x, rfl⟩ := hαI
  refine ⟨x, ?_, fun y => MulAut.conj_apply x y⟩
  rw [← orderOf_injective _ hinj x]
  exact hα

section Transport

variable {X : Type*} [Group X]

omit [Finite F] in
theorem isPGroup_map (e : X ≃* PSL2 F) {p : ℕ} {H : Subgroup X} (h : IsPGroup p H) :
    IsPGroup p (H.map e.toMonoidHom) := h.map _

omit [Finite F] in
theorem index_map (e : X ≃* PSL2 F) (H : Subgroup X) : (H.map e.toMonoidHom).index = H.index :=
  Subgroup.index_map_equiv H e

omit [Finite F] in
theorem card_map (e : X ≃* PSL2 F) (H : Subgroup X) : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
  (Nat.card_congr (H.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm

omit [Finite F] in
theorem normalizer_map (e : X ≃* PSL2 F) (H : Subgroup X) :
    (Subgroup.normalizer (H : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup (PSL2 F)) : Set (PSL2 F)) :=
  Subgroup.map_equiv_normalizer_eq H e

theorem isCyclic_three (e : X ≃* PSL2 F) (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (H : Subgroup X) (h3 : IsPGroup 3 H) : IsCyclic H := by
  have := isCyclic_of_isPGroup_three hF hq hq5 _ (isPGroup_map e h3)
  exact (MulEquiv.isCyclic (H.equivMapOfInjective e.toMonoidHom e.injective)).mpr this

theorem normalizer_sylow (e : X ≃* PSL2 F) (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (h8 : q % 8 = 1 ∨ q % 8 = 7) {S : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) : Subgroup.normalizer (S : Set X) = S := by
  have h := normalizer_sylow_eq hF hq hq5 h8 (isPGroup_map e hS2) (by rwa [index_map])
  rw [← normalizer_map] at h
  exact Subgroup.map_injective e.injective h

theorem card_sylow_four (e : X ≃* PSL2 F) (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (h3 : q % 8 = 3 ∨ q % 8 = 5) {S : Subgroup X} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    Nat.card S = 4 := by
  rw [← card_map e]
  exact card_sylow_eq_four hF hq hq5 h3 (isPGroup_map e hS2) (by rwa [index_map])

theorem normalizer_twelve_X (e : X ≃* PSL2 F)
    (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) (h3 : q % 8 = 3 ∨ q % 8 = 5)
    {S W : Subgroup X} (hS2 : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) (hSW : S ≤ W) (hW : Nat.card W = 12)
    (hWN : W ≤ Subgroup.normalizer (S : Set X)) :
    Subgroup.normalizer (S : Set X) = W ∧ Nonempty (W ≃* alternatingGroup (Fin 4)) := by
  have hWN' : W.map e.toMonoidHom ≤
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
    rw [← normalizer_map]
    exact Subgroup.map_mono hWN
  obtain ⟨h1, ⟨f⟩⟩ := normalizer_eq_of_twelve hF hq hq5 h3 (isPGroup_map e hS2)
    (by rwa [index_map]) (Subgroup.map_mono hSW) (by rwa [card_map]) hWN'
  rw [← normalizer_map] at h1
  exact ⟨Subgroup.map_injective e.injective h1,
    ⟨(W.equivMapOfInjective e.toMonoidHom e.injective).trans f⟩⟩

theorem exists_conj_X (e : X ≃* PSL2 F) (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (α : MulAut X) (hα : Odd (orderOf α)) :
    ∃ x : X, Odd (orderOf x) ∧ ∀ y, α y = x * y * x⁻¹ := by
  set α' := MulAut.congr e α with hα'
  have hord : orderOf α' = orderOf α :=
    orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α
  obtain ⟨x', hx', hconj⟩ := exists_conj_of_odd hF hq hq5 α' (hord ▸ hα)
  refine ⟨e.symm x', ?_, fun y => ?_⟩
  · have := orderOf_injective e.symm.toMonoidHom e.symm.injective x'
    rw [show e.symm.toMonoidHom x' = e.symm x' from rfl] at this
    rw [this]
    exact hx'
  · have h1 := hconj (e y)
    have h2 : α' (e y) = e (α y) := by
      rw [hα']
      simp [MulAut.congr_apply]
    rw [h2] at h1
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_of_card_four_alt4' (f : X ≃* alternatingGroup (Fin 4)) {K K' : Subgroup X}
    (hK : Nat.card K = 4) (hK' : Nat.card K' = 4) : K = K' := by
  classical
  have key : ∀ {L : Subgroup X}, Nat.card L = 4 → ∀ x : X, x ∈ L ↔ f x ^ 2 = 1 := by
    intro L hL
    set M := L.map f.toMonoidHom with hM
    have hMc : Nat.card M = 4 :=
      ((Nat.card_congr (L.equivMapOfInjective f.toMonoidHom f.injective).toEquiv).symm).trans hL
    have hMsq : ∀ y ∈ M, y ^ 2 = 1 := by
      intro y hy
      apply alt4_pow_four
      have := pow_card_eq_one' (x := (⟨y, hy⟩ : ↥M))
      rw [hMc] at this
      exact congrArg Subtype.val this
    have hsub : (M : Set (alternatingGroup (Fin 4))) ⊆
        ((Finset.univ.filter fun y : alternatingGroup (Fin 4) => y ^ 2 = 1 :
          Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))) := by
      intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      exact hMsq y hy
    have hcard : ((Finset.univ.filter fun y : alternatingGroup (Fin 4) => y ^ 2 = 1 :
        Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))).ncard ≤
        (M : Set (alternatingGroup (Fin 4))).ncard := by
      rw [Set.ncard_coe_finset, alt4_card_sq, ← Nat.card_coe_set_eq]
      exact hMc.ge
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
    intro x
    constructor
    · intro hx
      exact hMsq _ ⟨x, hx, rfl⟩
    · intro hx
      have : f x ∈ (M : Set (alternatingGroup (Fin 4))) := by
        rw [heq]
        simp only [Finset.coe_filter, Finset.mem_univ, true_and]
        exact hx
      obtain ⟨x', hx', e'⟩ := this
      exact f.injective e' ▸ hx'
  ext x
  rw [key hK x, key hK' x]

theorem dickson_X (e : X ≃* PSL2 F) (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (H : Subgroup X) :
    CFSG.IsElementaryAbelian q ↥H ∨
      (∃ z : ℕ, (z ∣ (q - 1) / 2 ∨ z ∣ (q + 1) / 2) ∧ Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ, (z ∣ (q - 1) / 2 ∨ z ∣ (q + 1) / 2) ∧ Nat.card H = 2 * z ∧
        Nonempty (H ≃* DihedralGroup z)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      (16 ∣ q ^ 2 - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) ∨
      (∃ N C : Subgroup H, N.Normal ∧ CFSG.IsElementaryAbelian q N ∧ IsCyclic C ∧
        Disjoint N C ∧ N ⊔ C = ⊤) ∨
      H = ⊤ := by
  set g := H.equivMapOfInjective e.toMonoidHom e.injective with hg
  rcases dickson hF hq hq5 (H.map e.toMonoidHom) with h | ⟨z, hz, hc, hcyc⟩ |
      ⟨z, hz, hc, ⟨d⟩⟩ | ⟨⟨a⟩⟩ | ⟨h16, ⟨s⟩⟩ | ⟨⟨a⟩⟩ | ⟨N, C, hN, hNe, hC, hdisj, hsup⟩ | htop
  · left
    have : IsMulCommutative ↥H := ⟨⟨fun a b => g.injective (by
      rw [map_mul, map_mul]
      exact h.toIsMulCommutative.is_comm.comm _ _)⟩⟩
    exact ⟨by
      rw [Monoid.exponent_eq_of_mulEquiv g]
      exact h.exponent_dvd_p⟩
  · exact Or.inr (Or.inl ⟨z, hz, by rw [← hc]; exact Nat.card_congr g.toEquiv,
      (MulEquiv.isCyclic g).mpr hcyc⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨z, hz, by rw [← hc]; exact Nat.card_congr g.toEquiv,
      ⟨g.trans d⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g.trans a⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h16, ⟨g.trans s⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g.trans a⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    refine ⟨N.map g.symm.toMonoidHom, C.map g.symm.toMonoidHom, hN.map _ g.symm.surjective, ?_,
      (MulEquiv.isCyclic (C.equivMapOfInjective _ g.symm.injective)).mp hC, ?_, ?_⟩
    · have hiso := N.equivMapOfInjective g.symm.toMonoidHom g.symm.injective
      have : IsMulCommutative ↥(N.map g.symm.toMonoidHom) := ⟨⟨fun a b => hiso.symm.injective (by
        rw [map_mul, map_mul]
        exact hNe.toIsMulCommutative.is_comm.comm _ _)⟩⟩
      exact ⟨by
        rw [← Monoid.exponent_eq_of_mulEquiv hiso]
        exact hNe.exponent_dvd_p⟩
    · exact Subgroup.disjoint_map g.symm.injective hdisj
    · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ g.symm.surjective]
  · right; right; right; right; right; right; right
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]

omit [Finite F] in
theorem no_large_prime [Finite X] {U : Subgroup X} (hUo : ∀ u ∈ U, ∃ k, u ^ (3 * 2 ^ k) = 1)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrU : r ∣ Nat.card U) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype ↥U := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥U) r
    (by rw [← Nat.card_eq_fintype_card]; exact hrU)
  obtain ⟨k, hk⟩ := hUo u u.2
  have h1 : orderOf (u : X) = r := by rw [Subgroup.orderOf_coe]; exact hu
  have h2 : r ∣ 3 * 2 ^ k := h1 ▸ orderOf_dvd_of_pow_eq_one hk
  rcases (Nat.Prime.dvd_mul hr).mp h2 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
    omega

theorem lemma_U (e : X ≃* PSL2 F) [Finite X] (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (h3 : q % 8 = 3 ∨ q % 8 = 5) {S U : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hSU : S ≤ Subgroup.normalizer (U : Set X))
    (hU3 : 3 ∣ Nat.card U) (hUo : ∀ u ∈ U, ∃ k, u ^ (3 * 2 ^ k) = 1) :
    (q % 24 = 11 ∨ q % 24 = 13) ∨
      (U = Subgroup.normalizer (S : Set X) ∧ Nonempty (U ≃* alternatingGroup (Fin 4))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : q ≠ 2 := by omega
  have hS4 := card_sylow_four e hF hq hq5 h3 hS2 hSi
  set W := U ⊔ S with hWdef
  have hUW : U ≤ W := le_sup_left
  have hSW : S ≤ W := le_sup_right
  have hWU : W ≤ Subgroup.normalizer (U : Set X) := sup_le Subgroup.le_normalizer hSU
  have hUn : (U.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW).mpr hWU
  have hncX : ¬ IsCyclic S := fun h =>
    (not_isCyclic_sylow hF hq hq5 (isPGroup_map e hS2) (by rwa [index_map]))
      ((MulEquiv.isCyclic (S.equivMapOfInjective e.toMonoidHom e.injective)).mp h)
  have eS : ↥(S.subgroupOf W) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSW
  have hS'2 : IsPGroup 2 (S.subgroupOf W) := hS2.of_equiv eS.symm
  have hS'c : ¬ IsCyclic (S.subgroupOf W) := fun h => hncX ((MulEquiv.isCyclic eS).mp h)
  have hS'card : Nat.card (S.subgroupOf W) = 4 := (Nat.card_congr eS.toEquiv).trans hS4
  have h4W : 4 ∣ Nat.card W := hS4 ▸ Subgroup.card_dvd_of_le hSW
  have h3W : 3 ∣ Nat.card W := hU3.trans (Subgroup.card_dvd_of_le hUW)
  have hUne : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU3
    omega
  have hsX : IsSimpleGroup X := by
    have : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact e.isSimpleGroup
  have hcX : Nat.card X = Nat.card (PSL2 F) := Nat.card_congr e.toEquiv
  rcases dickson_X e hF hq hq5 W with h | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hc, -⟩ | ⟨⟨f⟩⟩ | ⟨-, ⟨f⟩⟩ |
      ⟨⟨f⟩⟩ | ⟨N₁, C, hN₁, hNe, hC, -, hsup⟩ | htop
  · exfalso
    have := eq_bot_of_le_elemAb hq Nat.prime_two hq2 h hSW hS2
    rw [this, Subgroup.card_bot] at hS4
    omega
  · exact absurd (Subgroup.isCyclic (S.subgroupOf W)) hS'c
  · left
    rw [hc] at h4W h3W
    have h6 : 6 ∣ z := by omega
    rcases hz with hz | hz
    · have := h6.trans hz
      omega
    · have := h6.trans hz
      omega
  · right
    have hWc : Nat.card W = 12 := by rw [Nat.card_congr f.toEquiv, card_alt4]
    have hSn : (S.subgroupOf W).Normal := normal_of_card_four_alt4 f hS'card
    have hWN : W ≤ Subgroup.normalizer (S : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSW).mp hSn
    obtain ⟨hN, -⟩ := normalizer_twelve_X e hF hq hq5 h3 hS2 hSi hSW hWc hWN
    have hU3' : 3 ∣ Nat.card (U.subgroupOf W) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv]
      exact hU3
    have htop := eq_top_of_normal_alt4 f hUn hU3'
    have hUeq : U = W := by
      refine le_antisymm hUW fun w hw => ?_
      have : (⟨w, hw⟩ : ↥W) ∈ U.subgroupOf W := htop ▸ Subgroup.mem_top _
      exact this
    refine ⟨hUeq.trans hN.symm, ?_⟩
    rw [hUeq]
    exact ⟨f⟩
  · exfalso
    have h24 : Nat.card W = 24 := by rw [Nat.card_congr f.toEquiv, card_perm4]
    have h8 : 8 ∣ Nat.card X := by
      have := Subgroup.card_subgroup_dvd_card W
      rw [h24] at this
      exact (by norm_num : 8 ∣ 24).trans this
    rw [← Subgroup.card_mul_index S, hS4] at h8
    have hodd : Odd S.index := Nat.odd_iff.mpr (by omega)
    obtain ⟨m, hm⟩ := hodd
    rw [hm] at h8
    omega
  · exfalso
    have hsimp : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hn := hUn.map f.toMonoidHom f.surjective
    have := hn
    have hcU : Nat.card ↥((U.subgroupOf W).map f.toMonoidHom) = Nat.card U := by
      rw [← Nat.card_congr ((U.subgroupOf W).equivMapOfInjective f.toMonoidHom
        f.injective).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
    rcases hsimp.eq_bot_or_eq_top_of_normal ((U.subgroupOf W).map f.toMonoidHom) with hb | ht
    · rw [hb, Subgroup.card_bot] at hcU
      rw [← hcU] at hU3
      omega
    · rw [ht, Subgroup.card_top, card_alt5] at hcU
      exact no_large_prime hUo Nat.prime_five le_rfl (by rw [← hcU]; norm_num)
  · exact absurd (isCyclic_of_semidirect hN₁ hq hq2 hNe hC hsup hS'2) hS'c
  · exfalso
    have hUnX : U.Normal := by
      constructor
      intro u hu g
      have hg : g ∈ W := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.mp (hWU hg) u).mp hu
    rcases hsX.eq_bot_or_eq_top_of_normal U with hb | ht
    · exact hUne hb
    · have hqU : q ∣ Nat.card U := by
        rw [ht, Subgroup.card_top, hcX]
        exact (card_psl2_facts hF hq hq5).2.2
      exact no_large_prime hUo hq hq5 hqU

end Transport

end CFSG.Quasithin.H13.L2q
