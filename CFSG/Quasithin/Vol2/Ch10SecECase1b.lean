module

public import CFSG.Quasithin.Vol2.Ch10SecECase1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem oTwoUpper_eq_self_of_isL2Natural {W : Type*} [CommGroup W] [Finite W]
    {K : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ} (h : E2.IsL2Natural K C m) (hm : 2 ≤ m) :
    oTwoUpper K = K := by
  obtain ⟨-, F, hF, hFt, hcard, e, -⟩ := h
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have h2 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, hcard]; exact h2)
    exact ⟨s, hs⟩
  have hP := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    have h2 : (⊤ : Subgroup ↥K) = (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map
        e.symm.toMonoidHom :=
      (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective).symm
    rw [h2, ← Subgroup.map_commutator]
    have h3 := hP.commutator_eq_top
    rw [commutator_def] at h3
    rw [h3]
  have hKK : ⁅K, K⁆ = K := by
    rw [← htop, ← Subgroup.map_commutator, h1]
  exact (eq_oTwoUpper_of_perfect hKK).symm

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem card_autI_L
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) :
    Nat.card ↥(autI (SecA.isElemAbelian_fsuVM hyp) L) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
  Nat.card_congr (SecA.autOnEquivQuot h37 h38 h322 hyp).toEquiv

omit [Finite G] in
theorem card_autI_conjugate {t : G} (ht : t ∈ T) :
    Nat.card ↥(autOn (CFSG.conjugate L t) (fsuVM T L I)) = Nat.card ↥(autOn L (fsuVM T L I)) := by
  have htN : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) := SecA.le_normalizer_fsuVM T L I ht
  rw [SecA.autOn_conjugate htN, Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem sixty_le_card_autI_L_case1 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n) : 60 ≤ Nat.card ↥(autI (SecA.isElemAbelian_fsuVM hyp) L) := by
  obtain ⟨hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ := h1
  rw [card_autI_L h37 h38 h322 hyp, Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hK]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ 4 ^ n := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc 60 = 4 * 15 := by norm_num
    _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h4 (by omega)

theorem two_le_of_isL2Natural_of_le {W : Type*} [CommGroup W] {K A : Subgroup (MulAut W)}
    {C : Subgroup W} {m : ℕ} (h : E2.IsL2Natural K C m) (hAK : A ≤ K) (h60 : 60 ≤ Nat.card ↥A) :
    2 ≤ m := by
  have hc := SecA.card_of_isL2Natural h
  obtain ⟨hm, F, _, _, -, e, -⟩ := h
  have : Finite ↥K := Finite.of_equiv _ e.symm.toEquiv
  have hle : Nat.card ↥A ≤ Nat.card ↥K := Subgroup.card_le_of_le hAK
  by_contra h2
  have hm1 : m = 1 := by omega
  rw [hc, hm1] at hle
  norm_num at hle
  omega

theorem autI_thompsonJ_eq_case1 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n)
    {I' : Finset (Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))))}
    (hKJ : twoResidual (fsuL0 T L ⊔ T) ≤ thompsonJ (fsuL0 T L ⊔ T))
    (hcard : I'.card = 1 ∨ I'.card = 2)
    (hJeq : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = ⨆ K ∈ I', K)
    (hcomm : ∀ K ∈ I', ∀ K' ∈ I', K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hind : ∀ K ∈ I', K ⊓ ⨆ K' ∈ I', ⨆ (_ : K' ≠ K), K' = ⊥)
    (htrans : ∀ K ∈ I', ∀ K' ∈ I',
      ∃ s ∈ autI (SecA.isElemAbelian_fsuVM hyp) T, B1.conjAut s K = K')
    (htype : ∀ K ∈ I', (∃ m, E2.IsL2Natural K (fixV (autI (SecA.isElemAbelian_fsuVM hyp)
      (twoResidual (fsuL0 T L ⊔ T)))) m) ∨ E2.IsA5Module K) :
    autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) =
      autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hL2 := isL2Natural_of_case1 h37 h38 h322 hyp h1 hKJ hcard hJeq hcomm hind htrans htype
  have h60 := sixty_le_card_autI_L_case1 h37 h38 h322 hyp h1
  have h60' : 60 ≤ Nat.card ↥(autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t)) :=
    (card_autI_conjugate (I := I) ht).symm ▸ h60
  rw [autI_fsuL0 h37 h38 hyp ht htn]
  rcases ident_L0T h37 h38 h322 hyp ht htn hKJ hcard hJeq hcomm hind htrans with
    ⟨K, hK, -, hJK, hO⟩ | ⟨K₁, hK₁, K₂, hK₂, -, -, hJK, hO₁, hO₂, -, -⟩
  · obtain ⟨m, hm⟩ := hL2 K hK
    have hAK : autI (SecA.isElemAbelian_fsuVM hyp) L ≤ K :=
      le_sup_left.trans (hO.symm.le.trans (oTwoUpper_le K))
    rw [hJK, ← hO, oTwoUpper_eq_self_of_isL2Natural hm (two_le_of_isL2Natural_of_le hm hAK h60)]
  · obtain ⟨m₁, hm₁⟩ := hL2 K₁ hK₁
    obtain ⟨m₂, hm₂⟩ := hL2 K₂ hK₂
    have hA₁ : autI (SecA.isElemAbelian_fsuVM hyp) L ≤ K₁ := hO₁ ▸ oTwoUpper_le K₁
    have hA₂ : autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t) ≤ K₂ :=
      hO₂ ▸ oTwoUpper_le K₂
    rw [hJK, ← hO₁, ← hO₂,
      oTwoUpper_eq_self_of_isL2Natural hm₁ (two_le_of_isL2Natural_of_le hm₁ hA₁ h60),
      oTwoUpper_eq_self_of_isL2Natural hm₂ (two_le_of_isL2Natural_of_le hm₂ hA₂ h60')]

theorem inf_centralizer_le_T
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) :
    (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hquot := B6.isTwoQuotient_of_sup_eq hT2
    (sup_le Subgroup.le_normalizer (SecA.le_fsuM T L)) (sup_comm T (fsuL0 T L))
  have hO := SecA.fsuL0_inf_centralizer_le h37 h38 hyp
  have hP : IsPGroup 2 ↥((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
    intro y
    obtain ⟨k, hk⟩ := hquot (y : G) y.2.1
    have hk' : (y : G) ^ 2 ^ k ∈ pCoreOf 2 (fsuL0 T L) :=
      hO ⟨hk, Subgroup.pow_mem _ y.2.2 _⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (fsuL0 T L) ⟨_, hk'⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((y : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
    exact hj'
  have hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer
      (((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      SecA.le_normalizer_centralizer (fsuL0_sup_le_normalizer T L I) hx⟩
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    hN hP).trans (SecA.pCoreOf_le_of_sylow hyp.fsu.sylow le_sup_right)

theorem le_T0_sup_of_autI_le
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {X : Subgroup G} (hXT : X ≤ T)
    (hX : autI (SecA.isElemAbelian_fsuVM hyp) X ≤ autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L)) :
    X ≤ Ch10.T0 T L ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.le_normalizer_fsuVM T L I (hXT hx)
  obtain ⟨l, hlL, hl⟩ := (mem_autI _).mp (hX (convI_mem_autI _ hx hxN))
  set c : Subgroup.normalizer (fsuVM T L I : Set G) := l⁻¹ * ⟨x, hxN⟩
  have hc1 : convI (SecA.isElemAbelian_fsuVM hyp) c = 1 := by
    rw [map_mul, map_inv, hl, inv_mul_cancel]
  have hcC := (convI_eq_one_iff _ c).mp hc1
  have hcH : (c : G) ∈ fsuL0 T L ⊔ T :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hlL))
      (Subgroup.mem_sup_right (hXT hx))
  have hcT : (c : G) ∈ T := inf_centralizer_le_T h37 h38 hyp ⟨hcH, hcC⟩
  have hlT : (l : G) ∈ T := by
    have e : (l : G) = x * (c : G)⁻¹ := by
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact T.mul_mem (hXT hx) (T.inv_mem hcT)
  have e : x = (l : G) * c := by
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlT, hlL⟩)
    (Subgroup.mem_sup_right ⟨hcT, hcC⟩)

end CFSG.Quasithin.Vol2.Ch10.SecE
