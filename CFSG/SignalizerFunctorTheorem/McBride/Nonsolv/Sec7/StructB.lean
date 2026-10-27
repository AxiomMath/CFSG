module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.Struct
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Ind
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Wreath

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K : Subgroup G}

theorem isRegFam_line_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    IsRegFam A (thetaOf θ F) (lcal (thetaOf θ F)) (E ⊔ F) := by
  have h1 := h.isRegFam_lcal hF.1 (h.ne_bot_of_mem_E1 hF) (kOf_line_of_typeB h hB hF hFE)
  rwa [hB.bN_eq F hF, sup_comm F E] at h1

theorem card_lcal_line_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Nat.card (lcal (thetaOf θ F)) = p := by
  have h1 := (isRegFam_line_of_typeB h hB hF hFE).card_mul_card
  rw [(h.sup_mem_E2_of_ne hB.mem hF hFE.symm).2, h.card] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) (h1.trans (by ring))

theorem nonempty_mulEquiv_line_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {L : Subgroup G}
    (hL : L ∈ lcal (thetaOf θ F)) : Nonempty (↥L ≃* ↥K) := by
  obtain ⟨L₁, C, hW, ⟨e⟩⟩ := hB.wreath_F F hF hFE
  have hLs : IsSimpleGroup L₁ := e.isSimpleGroup_congr.mpr hB.simple_K.1
  have hnc : ¬ IsMulCommutative L₁ := fun hc => hB.simple_K.2 ((isMulCommutative_congr e).mp hc)
  have hL₁ : L₁ ∈ lcal (thetaOf θ F) :=
    T61.mem_lcal_of_isWreath (h.isFunctor.normalizes_thetaOf hF.1) hW hLs hnc
  obtain ⟨a, -, rfl⟩ := h.exists_conj_eq_of_mem_lcal hF.1 (h.ne_bot_of_mem_E1 hF) hL₁ hL
  exact ⟨(Subgroup.equivMapOfInjective L₁ _ (MulAut.conj a).injective).symm.trans e⟩

theorem ind_eq_lcal_line_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Ind (thetaOf θ F) = lcal (thetaOf θ F) := by
  have hΩ := isRegFam_line_of_typeB h hB hF hFE
  exact IsDirectProduct.ind_eq hΩ.isDirectProduct (h.sol_thetaOf hF.1 (h.ne_bot_of_mem_E1 hF))
    hΩ.ne_bot fun L hL => card_lcal_eq_one_of_isFStarSimple (isFStarSimple_of_mem_lcal hL)

theorem le_normalizer_of_mem_lcal_line_of_typeB
    (h : Counterexample p A θ)
    (hB : TypeBCore p A θ E K) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : F ≠ E) {L : Subgroup G} (hL : L ∈ lcal (thetaOf θ F)) :
    E ≤ Subgroup.normalizer (L : Set G) :=
  le_sup_left.trans (((isRegFam_line_of_typeB h hB hF hFE).stabilizer L hL).symm.le.trans
    inf_le_right)

theorem card_line_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Nat.card (thetaOf θ F) = Nat.card K ^ p := by
  rw [(isRegFam_line_of_typeB h hB hF hFE).card_eq_pow (m := Nat.card K) fun L hL =>
    Nat.card_congr (nonempty_mulEquiv_line_of_typeB h hB hF hFE hL).some.toEquiv,
    card_lcal_line_of_typeB h hB hF hFE]

theorem isRegFam_ind_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) :
    IsRegFam A (thetaOf θ E) (Ind (thetaOf θ E)) E := by
  obtain ⟨Ω, hΩ, hiso⟩ := exists_isRegFam_E_of_typeB h hB
  have hInd : Ind (thetaOf θ E) = Ω :=
    IsDirectProduct.ind_eq hΩ.isDirectProduct
      (h.sol_thetaOf hB.mem.1 (h.ne_bot_of_mem_E1 hB.mem)) hΩ.ne_bot fun L hL =>
        card_lcal_eq_one_of_mulEquiv (hiso L hL).some (isFStarSimple_D_of_typeB hB)
  rw [hInd]
  exact hΩ

theorem card_ind_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) :
    Nat.card (Ind (thetaOf θ E)) = p ^ 2 := by
  have h1 := (isRegFam_ind_E_of_typeB h hB).card_mul_card
  rw [hB.mem.2, h.card, pow_one] at h1
  exact Nat.eq_of_mul_eq_mul_right h.prime.pos (h1.trans (by ring))

theorem nonempty_mulEquiv_ind_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {L : Subgroup G} (hL : L ∈ Ind (thetaOf θ E)) : Nonempty (↥L ≃* ↥(thetaOf θ A)) := by
  have hΩ := isRegFam_ind_E_of_typeB h hB
  exact h.nonempty_mulEquiv_of_isRegFam hB.mem.1 (h.ne_bot_of_mem_E1 hB.mem) hΩ hL
    (Subgroup.le_centralizer_iff.mp ((hΩ.isDirectProduct.le hL).trans
      (h.isFunctor.thetaOf_le_centralizer hB.mem.1)))

theorem lcal_of_mem_ind_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {L : Subgroup G} (hL : L ∈ Ind (thetaOf θ E)) :
    lcal L = {CFSG.inSubgroup CFSG.generalizedFitting L} :=
  lcal_eq_singleton_of_mulEquiv (nonempty_mulEquiv_ind_E_of_typeB h hB hL).some
    (isFStarSimple_D_of_typeB hB)

theorem lcal_E_eq_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) :
    lcal (thetaOf θ E) =
      {J | ∃ L ∈ Ind (thetaOf θ E), J = CFSG.inSubgroup CFSG.generalizedFitting L} := by
  ext J
  rw [mem_lcal_iff_of_isDirectProduct (isRegFam_ind_E_of_typeB h hB).isDirectProduct]
  constructor
  · rintro ⟨L, hL, hJ⟩
    rw [lcal_of_mem_ind_E_of_typeB h hB hL] at hJ
    exact ⟨L, hL, hJ⟩
  · rintro ⟨L, hL, rfl⟩
    exact ⟨L, hL, by rw [lcal_of_mem_ind_E_of_typeB h hB hL]; rfl⟩

theorem card_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) :
    Nat.card (thetaOf θ E) = Nat.card (thetaOf θ A) ^ (p ^ 2) := by
  rw [(isRegFam_ind_E_of_typeB h hB).card_eq_pow (m := Nat.card (thetaOf θ A)) fun L hL =>
    Nat.card_congr (nonempty_mulEquiv_ind_E_of_typeB h hB hL).some.toEquiv,
    card_ind_E_of_typeB h hB]

theorem isRegFam_smear_ind_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    IsRegFam A (thetaOf θ (E ⊔ F)) {Y | ∃ L ∈ Ind (thetaOf θ E), Y = smear L F} (E ⊔ F) := by
  have hsm := (isRegFam_ind_E_of_typeB h hB).smear_family h.elemAbelian.1 hF.1
    (inf_line_eq_bot_of_typeB h hB hF hFE)
  rwa [h.thetaOf_line_inf_centralizer hB.mem hF.1] at hsm

theorem ind_plane_eq_smear_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Ind (thetaOf θ (E ⊔ F)) = {Y | ∃ L ∈ Ind (thetaOf θ E), Y = smear L F} := by
  have hP := h.sup_mem_E2_of_ne hB.mem hF hFE.symm
  have hsm := isRegFam_smear_ind_E_of_typeB h hB hF hFE
  refine IsDirectProduct.ind_eq hsm.isDirectProduct
    (h.sol_thetaOf hP.1 (h.ne_bot_of_mem_E2 hP)) hsm.ne_bot ?_
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨e₁⟩ := (isRegFam_ind_E_of_typeB h hB).nonempty_mulEquiv_smear hF.1
    (inf_line_eq_bot_of_typeB h hB hF hFE) hL
  obtain ⟨e₂⟩ := nonempty_mulEquiv_ind_E_of_typeB h hB hL
  exact card_lcal_eq_one_of_mulEquiv (e₁.trans e₂) (isFStarSimple_D_of_typeB hB)

theorem isRegFam_ind_plane_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    IsRegFam A (thetaOf θ (E ⊔ F)) (Ind (thetaOf θ (E ⊔ F))) (E ⊔ F) := by
  rw [ind_plane_eq_smear_of_typeB h hB hF hFE]
  exact isRegFam_smear_ind_E_of_typeB h hB hF hFE

theorem card_ind_plane_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Nat.card (Ind (thetaOf θ (E ⊔ F))) = p := by
  have h1 := (isRegFam_ind_plane_of_typeB h hB hF hFE).card_mul_card
  rw [(h.sup_mem_E2_of_ne hB.mem hF hFE.symm).2, h.card] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) (h1.trans (by ring))

theorem ind_plane_eq_inf_centralizer_of_typeB
    (h : Counterexample p A θ)
    (hB : TypeBCore p A θ E K) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : F ≠ E) :
    Ind (thetaOf θ (E ⊔ F)) =
      {C | ∃ R ∈ lcal (thetaOf θ F), C = R ⊓ Subgroup.centralizer (E : Set G)} := by
  have hP := h.sup_mem_E2_of_ne hB.mem hF hFE.symm
  have hF0 := h.ne_bot_of_mem_E1 hF
  have hKS := h.kSetting_thetaOf hF.1 hF0
  have hKA := h.kDown_thetaOf hF.1 hF0
  have hΩ := isRegFam_line_of_typeB h hB hF hFE
  have hsmear : ∀ R ∈ lcal (thetaOf θ F),
      smear R E = R ⊓ Subgroup.centralizer (E : Set G) := fun R hR => by
    have hEN := le_normalizer_of_mem_lcal_line_of_typeB h hB hF hFE hR
    have : orbitClosure R E = R := le_antisymm (orbitClosure_le fun a ha =>
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEN ha)).le) (le_orbitClosure R E)
    rw [smear, this]
  have hne : ∀ R ∈ lcal (thetaOf θ F), R ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
    intro R hR hbot
    have hRA : R ∈ lcalA (thetaOf θ F) E := T515f.mem_lcalA_of_le hKS hB.mem.1
      ((lcalA_eq_lcal_of_kDown_eq_bot hKS hKA).symm ▸ hR)
    exact hRA.2 (by rw [hsmear R hR, hbot]; infer_instance)
  have hfam := hΩ.inf_centralizer_family h.elemAbelian.1 hB.mem.1 le_sup_left hne
  rw [h.thetaOf_line_inf_centralizer hF hB.mem.1, sup_comm F E] at hfam
  refine IsDirectProduct.ind_eq hfam.isDirectProduct
    (h.sol_thetaOf hP.1 (h.ne_bot_of_mem_E2 hP)) hfam.ne_bot ?_
  rintro _ ⟨R, hR, rfl⟩
  rw [← hsmear R hR, T515f.lcal_smear_eq hKS hKA hB.mem.1 hR]
  exact Nat.card_unique

theorem nonempty_mulEquiv_ind_plane_of_typeB
    (h : Counterexample p A θ)
    (hB : TypeBCore p A θ E K) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : F ≠ E) {L : Subgroup G} (hL : L ∈ Ind (thetaOf θ (E ⊔ F))) :
    Nonempty (↥L ≃* ↥(thetaOf θ A)) := by
  rw [ind_plane_eq_smear_of_typeB h hB hF hFE] at hL
  obtain ⟨L', hL', rfl⟩ := hL
  obtain ⟨e₁⟩ := (isRegFam_ind_E_of_typeB h hB).nonempty_mulEquiv_smear hF.1
    (inf_line_eq_bot_of_typeB h hB hF hFE) hL'
  obtain ⟨e₂⟩ := nonempty_mulEquiv_ind_E_of_typeB h hB hL'
  exact ⟨e₁.trans e₂⟩

theorem nonempty_mulEquiv_complement_of_typeB
    (h : Counterexample p A θ)
    (hB : TypeBCore p A θ E K) {B : Subgroup G} (hB2 : B ∈ signalizerFunctorEk p 2 A)
    (hEB : ¬ E ≤ B) : Nonempty (↥(thetaOf θ B) ≃* ↥K) := by
  obtain ⟨F₁, hF₁, hF₁B⟩ := h.exists_line_le_of_mem_E2 hB2
  obtain ⟨F₂, hF₂, -, -, hsup⟩ := h.exists_line_sup_eq_of_mem_E2 hB2 hF₁ hF₁B
  have hF₁E : F₁ ≠ E := fun heq => hEB (heq ▸ hF₁B)
  have hN₁ : E ⊔ F₁ ∈ signalizerFunctorEk p 2 A := h.sup_mem_E2_of_ne hB.mem hF₁ hF₁E.symm
  have hnle : ¬ F₂ ≤ E ⊔ F₁ := by
    intro hle
    have hle' : B ≤ E ⊔ F₁ := hsup ▸ sup_le le_sup_right hle
    exact hEB (Subgroup.eq_of_le_of_card_ge hle' (by rw [hB2.2, hN₁.2]) ▸ le_sup_left)
  have hFN' : (E ⊔ F₁) ⊓ F₂ = ⊥ := inf_eq_bot_of_not_le h.prime (by rw [hF₂.2, pow_one]) hnle
  have hFN : F₂ ⊓ (E ⊔ F₁) = ⊥ := by rw [inf_comm]; exact hFN'
  have hΩ := isRegFam_line_of_typeB h hB hF₁ hF₁E
  have hsm := hΩ.smear_family h.elemAbelian.1 hF₂.1 hFN
  have hcard : Nat.card {Y | ∃ L ∈ lcal (thetaOf θ F₁), Y = smear L F₂} = 1 := by
    have h1 := hsm.card_mul_card
    rw [card_sup_of_le_elemAbelian h.elemAbelian hN₁.1 hF₂.1 hFN', hN₁.2, hF₂.2, h.card] at h1
    refine Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 3) ?_
    calc _ = Nat.card {Y | ∃ L ∈ lcal (thetaOf θ F₁), Y = smear L F₂} * (p ^ 2 * p ^ 1) := by ring
      _ = 1 * p ^ 3 := by rw [h1, one_mul]
  obtain ⟨L, hL⟩ := hΩ.nonempty
  have hLY : smear L F₂ ∈ {Y | ∃ L ∈ lcal (thetaOf θ F₁), Y = smear L F₂} := ⟨L, hL, rfl⟩
  have hsub : ∀ Y ∈ {Y | ∃ L ∈ lcal (thetaOf θ F₁), Y = smear L F₂}, Y = smear L F₂ := fun Y hY =>
    congrArg Subtype.val (((Nat.card_eq_one_iff_unique.mp hcard).1).elim ⟨Y, hY⟩ ⟨_, hLY⟩)
  have hHB : thetaOf θ B = smear L F₂ := by
    have h2 : sSup {Y | ∃ L ∈ lcal (thetaOf θ F₁), Y = smear L F₂} = smear L F₂ :=
      le_antisymm (sSup_le fun Y hY => (hsub Y hY).le) (le_sSup hLY)
    rw [hsm.isDirectProduct.sSup_eq, h.thetaOf_line_inf_centralizer hF₁ hF₂.1, hsup] at h2
    exact h2
  obtain ⟨e₁⟩ := hΩ.nonempty_mulEquiv_smear hF₂.1 hFN hL
  obtain ⟨e₂⟩ := nonempty_mulEquiv_line_of_typeB h hB hF₁ hF₁E hL
  exact ⟨(MulEquiv.subgroupCongr hHB).trans (e₁.trans e₂)⟩

theorem lcal_complement_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {B : Subgroup G} (hB2 : B ∈ signalizerFunctorEk p 2 A) (hEB : ¬ E ≤ B) :
    lcal (thetaOf θ B) = {thetaOf θ B} := by
  obtain ⟨e⟩ := nonempty_mulEquiv_complement_of_typeB h hB hB2 hEB
  exact lcal_eq_singleton_self (e.isSimpleGroup_congr.mpr hB.simple_K.1)
    fun hc => hB.simple_K.2 ((isMulCommutative_congr e).mp hc)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
