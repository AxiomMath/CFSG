module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLinearTwo
public import CFSG.Quasithin.Vol2.Ch10SecQ3CR

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_dvd_card_fsuL0 (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrL : ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L))
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ¬ r ∣ Nat.card (fsuL0 T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : ¬ r ∣ Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
    intro h
    rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
    · exact hrL h1
    · obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hj] at h1
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
  have hLt : Nat.card (CFSG.conjugate L t) = Nat.card L :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hN : L ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
    SecA.le_normalizer_conjugate hyp.fsu.maximal.1 (SecA.le_fsuM T L ht)
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [← SecA.fsuL0_eq_sup h37 h38 hyp ht htn, hLt] at h1
  intro h
  have h2 : r ∣ Nat.card L * Nat.card L := h1 ▸ Dvd.dvd.mul_right h _
  rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3 <;> exact hL h3

theorem eq_one_of_mem_hall_pair
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Case10_1_1One T L I n)
    (hn3 : 3 ≤ n) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hfaith : HallFaithful T L I H) {B D : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) (hDB : D ≤ Subgroup.normalizer (B : Set G))
    {y : G} (hy : y ∈ B) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1)
    (hrL : ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) : y = 1 := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  have hK := (bender_of_cases (Or.inl ⟨n, h1⟩)).1
  have hXB0 := inf_fsuM_le_normalizer_B0 hF6 h37 h38 h331 hyp hK hH
  have hyX := hB.1 hy
  have hrB0 : ¬ r ∣ Nat.card (B0 T L) := fun h => not_dvd_card_fsuL0 hyp ht hr hr2 hrL h37 h38
    htn (h.trans (Subgroup.card_dvd_of_le ((oTwoUpper_le _).trans inf_le_left)))
  have hyD : ∀ d ∈ D, y * d = d * y := fun d hd =>
    commute_of_mem_hall_pair hBc (hB.1.trans hXB0) hD.1 hDB hy hr hyr hrB0 hd
  obtain ⟨hUab, F, _, _, _, -, hF, ⟨c⟩⟩ := SecA.exists_natCoord hyp h1
  have hrq : ¬ r ∣ 2 ^ n - 1 := by
    obtain ⟨-, ⟨F', _, _, hF', ⟨e⟩⟩, -⟩ := h1
    rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF'] at hrL
    intro h
    apply hrL
    refine h.trans (Dvd.dvd.mul_left ?_ _)
    have h4 : 4 ^ n - 1 = (2 ^ n) ^ 2 - 1 ^ 2 := by
      rw [one_pow, ← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4]
    exact Nat.sub_dvd_pow_sub_pow _ _ _
  have hyM := hyX.2
  have hodd := hr.odd_of_ne_two hr2
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_pow_prime h37 h38 hyp hyM hodd hyr
  have hyU : y ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator
      (Subgroup.zpowers_le.mpr (SecA.fsuM_le_normalizer_fsuVM T L I hyM))
      (Subgroup.zpowers_le.mpr hyL) (Subgroup.mem_zpowers y)
  obtain ⟨d₁, hd₁, hd₁N, μ₁, x₁, hμ₁, hd₁'⟩ := exists_mem_hall_torus h37 h38 hyp hF
    (by omega) c hD
  have hfix1 := commutator_fix_of_torus hF hn3 c hyU hyL hr hr2 hyr hrq hd₁N (hyD d₁ hd₁)
    hμ₁ hd₁'
  have htB0 : t ∈ Subgroup.normalizer (B0 T L : Set G) := SecA.le_normalizer_B0 T L ht
  obtain ⟨d', hd', hd'N, μ₂, x₂, hμ₂, hd''⟩ := exists_mem_hall_torus h37 h38 hyp hF
    (by omega) c (isHallTwoPrimeOf_map_conj htB0 hD)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hd'
  set z := t * y * t⁻¹ with hz
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have hzM : z ∈ fsuM T L :=
    (fsuM T L).mul_mem ((fsuM T L).mul_mem htM hyM) ((fsuM T L).inv_mem htM)
  have hzr : z ^ r = 1 := by rw [hz, conj_pow, hyr, mul_one, mul_inv_cancel]
  have hzL : z ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_pow_prime h37 h38 hyp hzM hodd hzr
  have hzU : z ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator
      (Subgroup.zpowers_le.mpr (SecA.fsuM_le_normalizer_fsuVM T L I hzM))
      (Subgroup.zpowers_le.mpr hzL) (Subgroup.mem_zpowers z)
  have hzd : z * d' = d' * z := by
    rw [← hd₂']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz]
    calc t * y * t⁻¹ * (t * d₂ * t⁻¹) = t * (y * d₂) * t⁻¹ := by group
      _ = t * (d₂ * y) * t⁻¹ := by rw [hyD d₂ hd₂]
      _ = t * d₂ * t⁻¹ * (t * y * t⁻¹) := by group
  have hfix2 := commutator_fix_of_torus hF hn3 c hzU hzL hr hr2 hzr hrq hd'N hzd hμ₂ hd''
  have hC1 : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro l hl
    have hc : y * l * y⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hyL l).mp hl) (L.inv_mem hl)
    exact mem_centralizer_of_fix h37 h38 hyp ht htn hc fun u hu => hfix1 l hl u hu
  have htC : t⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
    SecA.le_normalizer_centralizer (SecA.le_normalizer_fsuVM T L I) (T.inv_mem ht)
  have hC2 : ∀ l ∈ CFSG.conjugate L t,
      y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro l hl
    have hl' : t * l * t⁻¹ ∈ L := SecA.mem_conjugate_iff.mp hl
    have hc : z * (t * l * t⁻¹) * z⁻¹ * (t * l * t⁻¹)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hzL _).mp hl') (L.inv_mem hl')
    have h1 := mem_centralizer_of_fix h37 h38 hyp ht htn hc fun u hu => hfix2 _ hl' u hu
    have h2 := (Subgroup.mem_normalizer_iff.mp htC _).mp h1
    have e : t⁻¹ * (z * (t * l * t⁻¹) * z⁻¹ * (t * l * t⁻¹)⁻¹) * t⁻¹⁻¹ =
        y * l * y⁻¹ * l⁻¹ := by rw [hz]; group
    rwa [e] at h2
  have hyC : y ∈ cenL0 T L I :=
    mem_cenL0_of_sup hyM (SecA.fsuL0_eq_sup h37 h38 hyp ht htn) hC1 hC2
  exact eq_one_of_mem_cenL0 hfaith hB hyX hr hr2 hyr hyC

theorem eq_one_of_prime_not_dvd
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (hDHB : Ch11.SecB.DerivedHallBorel)
    (hB0K : Obl10_2_3B0K) (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Case10_1_1One T L I n)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) (hfaith : HallFaithful T L I H)
    {K : Subgroup G} {m : ℕ} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    {y : G} (hy : y ∈ H ⊓ fsuM T L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hyr : y ^ r = 1)
    (hrL : ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) : y = 1 := by
  obtain ⟨B, D, hB, hBc, hD, -, hDB⟩ :=
    exists_hall_pair hF6 h37 h38 h331 hDHB hB0K hyp h1 hH hn1 hZH hKc hHK hKF
  rcases Nat.lt_or_ge n 3 with hn | hn3
  ·
    have hn2 : n = 2 := by have := h1.1; omega
    subst hn2
    obtain ⟨-, ⟨F, _, _, hF, ⟨e⟩⟩, -⟩ := h1
    obtain ⟨f⟩ := CFSG.QuasithinUnique.Setup.Family.SL_two_four_equiv_alternating_five hF
    refine eq_one_of_pow_prime h37 h38 h322 hyp hfaith hB hy hr hr2 hyr ?_
    rw [card_mulAut_of_equiv_A5 (e.trans f)]
    rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF] at hrL
    intro h
    apply hrL
    rcases (Nat.Prime.dvd_mul hr).mp (show r ∣ 2 * 60 from h) with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h') hr2
    · exact h'
  ·
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, -, hle⟩ := Ch11.SecB.exists_conj_le_hall hr2 hB (Subgroup.zpowers_le.mpr hy)
      (isPGroup_zpowers_of_pow_eq_one hr hyr)
    have hy' : x⁻¹ * y * x ∈ B := A1b.mem_conjSub_iff.mp (hle (Subgroup.mem_zpowers y))
    have hy'r : (x⁻¹ * y * x) ^ r = 1 := by
      rw [show x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ by rw [inv_inv], conj_pow, hyr, mul_one,
        mul_inv_cancel]
    have h' := eq_one_of_mem_hall_pair hF6 h37 h38 h331 hyp h1 hn3 hH hfaith hB hBc hD hDB hy'
      hr hr2 hy'r hrL
    rwa [show x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ by rw [inv_inv], conj_eq_one_iff] at h'

theorem oTwoUpper_inf_le_B0
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3)
    (hDHB : Ch11.SecB.DerivedHallBorel) (hB0K : Obl10_2_3B0K) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Case10_1_1One T L I n) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hn1 : 1 < E1.nParam H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hfaith : HallFaithful T L I H) {K : Subgroup G} {m : ℕ} (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T)
    (hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    oTwoUpper (H ⊓ fsuM T L) ≤ B0 T L := by
  have hK := (bender_of_cases (Or.inl ⟨n, h1⟩)).1
  have hkill : ∀ y ∈ H ⊓ fsuM T L, ∀ r : ℕ, r.Prime → r ≠ 2 → y ^ r = 1 →
      ¬ r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) → y = 1 :=
    fun y hy r hr hr2 hyr hrL => eq_one_of_prime_not_dvd hF6 h37 h38 h322 h331 hDHB hB0K hyp
      h1 hH hn1 hZH hfaith hKc hHK hKF hy hr hr2 hyr hrL
  have hN := inf_le_normalizer_T0 hF6 h37 h38 h331 hyp hK hH
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hx0 := mem_fsuL0_of_kill h1013 hyp inf_le_right hkill hx.1 hx.2
  exact mem_oTwoUpper_of_odd ⟨hx0, hN ⟨hx.1, hx0⟩⟩ hx.2

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
