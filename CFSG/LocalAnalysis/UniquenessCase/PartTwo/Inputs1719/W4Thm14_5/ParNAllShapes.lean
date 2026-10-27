module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.GroupTheory.ProdFactors
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneABoundShape
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.NaturalClassicalQuasisimple
import all CFSG.Timmesfeld.Orders.Distinct
import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

theorem nParamSingle_of_nParam_of_isQuasisimple {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (hN : NParam L n) (hq : CFSG.Open.IsQuasisimple (Bar2 L)) :
    NParamSingle (Bar2 L) n := by
  rcases hN with h | ⟨L₁, L₂, h₁, h₂, hsup, hne, -⟩
  · exact h
  · exact (not_exists_calC_sup_eq_of_isQuasisimple_bar2 hq ⟨L₁, L₂, h₁, h₂, hsup, hne⟩).elim

theorem isL3_field_unique {X : Type} [Group X] {n m : ℕ} (h₁ : IsL3 X n) (h₂ : IsL3 X m) :
    n = m := by
  have hn : 1 ≤ n := h₁.admissible.2.1
  have hm : 1 ≤ m := h₂.admissible.2.1
  have c₁ : Nat.card X = ordA 2 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h₁.card_eq_lieOrd (by norm_num)
  have c₂ : Nat.card X = ordA 2 (2 ^ m) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h₂.card_eq_lieOrd (by norm_num)
  have hP := CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hn
  rw [← c₁, c₂] at hP
  have := (hP.transfer (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hm)).1
  omega

theorem isSp4_field_unique {X : Type} [Group X] {n m : ℕ} (h₁ : IsSp4 X n) (h₂ : IsSp4 X m) :
    n = m := by
  have hn : 1 ≤ n := h₁.admissible.2.1
  have hm : 1 ≤ m := h₂.admissible.2.1
  have c₁ : Nat.card X = ordBC 2 (2 ^ n) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h₁.card_eq_lieOrd (by norm_num)
  have c₂ : Nat.card X = ordBC 2 (2 ^ m) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h₂.card_eq_lieOrd (by norm_num)
  have hP := CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hn
  rw [← c₁, c₂] at hP
  have := (hP.transfer (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hm)).1
  omega

theorem not_isSL3_of_isSp4 {X : Type} [Group X] {a b : ℕ} (h : IsSp4 X a) : ¬ IsSL3 X b := by
  rintro ⟨hq, hL3⟩
  have : IsSimpleGroup X :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSp) (by decide) h
  have hA : Nat.card X = ordBC 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hB : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ b) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL3.card_eq_lieOrd (by norm_num)
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two (by norm_num) hL3.admissible.2.1
    h.admissible.2.1 (hB.symm.trans ((card_quot_center_of_isSimpleGroup hq).trans hA))

theorem nParamSingle_isSL3_eq {X : Type} [Group X] {n j : ℕ} (h : NParamSingle X n)
    (hX : IsSL3 X j) : n = j := by
  rcases h with hSz | hL2 | hSU3 | hSL3 | hSp4
  · exact (not_isSL3_of_isSz hSz hX).elim
  · exact (not_isSL3_of_isL2 hL2 hX).elim
  · exact (not_isSL3_of_isSU3 hSU3 hX).elim
  · exact isL3_field_unique hSL3.2 hX.2
  · exact (not_isSL3_of_isSp4 hSp4 hX).elim

theorem nParamSingle_isSp4_eq {X : Type} [Group X] {n j : ℕ} (h : NParamSingle X n)
    (hX : IsSp4 X j) : n = j := by
  rcases h with hSz | hL2 | hSU3 | hSL3 | hSp4
  · exact (not_isSz_of_isSp4 hX hSz).elim
  · exact (not_isL2_of_isSp4 hX hL2).elim
  · exact (not_isSp4_of_isSU3 hSU3 hX).elim
  · exact (not_isSL3_of_isSp4 hX hSL3).elim
  · exact isSp4_field_unique hSp4 hX

theorem nParam_eq_of_isSL3 {G : Type} [Group G] [Finite G] {L : Subgroup G} {n j : ℕ}
    (hN : NParam L n) (h : IsSL3 (Bar2 L) j) : n = j :=
  nParamSingle_isSL3_eq (nParamSingle_of_nParam_of_isQuasisimple hN h.1) h

theorem nParam_eq_of_isSp4 {G : Type} [Group G] [Finite G] {L : Subgroup G} {n j : ℕ}
    (hN : NParam L n) (h : IsSp4 (Bar2 L) j) (hj : 2 ≤ j) : n = j :=
  nParamSingle_isSp4_eq (nParamSingle_of_nParam_of_isQuasisimple hN (isQuasisimple_of_isSp4 h hj)) h

theorem isLn_quot_center_of_isSLn {X : Type} [Group X] {d k : ℕ} (h : IsSLn X d k)
    (hd : 3 ≤ d) (hk : 1 ≤ k) : IsLn (X ⧸ Subgroup.center X) d k := by
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  let : Field K := hKf
  let : Finite K := hKfin
  have hZ : (Subgroup.center X).map e.toMonoidHom =
      (StatedScalars (Fin d) K).subgroupOf (StatedSL d K) := by
    have h1 : (Subgroup.center X).map e.toMonoidHom = Subgroup.center ↥(StatedSL d K) :=
      Subgroup.map_center_eq e
    rw [h1, CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq d]
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hk, by omega, by simp; omega, by simp; omega⟩,
    K, hKf, hKfin, hK, ⟨QuotientGroup.congr _ _ e hZ⟩⟩

theorem isSL3_of_isSLn_three {X : Type} [Group X] {j : ℕ} (h : IsSLn X 3 j) (hj : 2 ≤ j) :
    IsSL3 X j :=
  ⟨isQuasisimple_of_isSLn (by norm_num) h hj, isLn_quot_center_of_isSLn h le_rfl (by omega)⟩

theorem not_isQuasisimple_of_mulEquiv_prod {X A B : Type} [Group X] [Group A] [Group B]
    [IsSimpleGroup A] [IsSimpleGroup B] (hAnc : ¬ IsMulCommutative A)
    (hBnc : ¬ IsMulCommutative B) (e : X ≃* A × B) : ¬ CFSG.Open.IsQuasisimple X := by
  have : Nontrivial A := IsSimpleGroup.toNontrivial
  have : Nontrivial B := IsSimpleGroup.toNontrivial
  have hZA : Subgroup.center A = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hAnc
  have hZB : Subgroup.center B = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hBnc
  have hZAB : Subgroup.center (A × B) = ⊥ := by
    rw [Subgroup.center_prod, hZA, hZB, Subgroup.bot_prod_bot]
  intro hq
  have hZmap : (Subgroup.center X).map e.toMonoidHom = Subgroup.center (A × B) :=
    Subgroup.map_center_eq e
  let eQ : (X ⧸ Subgroup.center X) ≃* ((A × B) ⧸ Subgroup.center (A × B)) :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center (A × B)) e hZmap
  let eBot : ((A × B) ⧸ Subgroup.center (A × B)) ≃* A × B :=
    (QuotientGroup.quotientMulEquivOfEq hZAB).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  exact CFSG.LocalAnalysis.EvenBN.U5.not_isSimpleGroup_prod (G₁ := A) (G₂ := B)
    ((eQ.trans eBot).symm.isSimpleGroup)

theorem not_nParamSingle_of_mulEquiv_prod {X A B : Type} [Group X] [Group A] [Group B]
    [IsSimpleGroup A] [IsSimpleGroup B] (hAnc : ¬ IsMulCommutative A)
    (hBnc : ¬ IsMulCommutative B) (e : X ≃* A × B) {n : ℕ} : ¬ NParamSingle X n := by
  have : Nontrivial A := IsSimpleGroup.toNontrivial
  have : Nontrivial B := IsSimpleGroup.toNontrivial
  have hns : ¬ IsSimpleGroup X := fun hX =>
    CFSG.LocalAnalysis.EvenBN.U5.not_isSimpleGroup_prod (G₁ := A) (G₂ := B)
      ((MulEquiv.isSimpleGroup_congr e).mp hX)
  have hnq := not_isQuasisimple_of_mulEquiv_prod hAnc hBnc e
  rintro (hSz | hL2 | hSU3 | hSL3 | hSp4)
  · exact hns (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz)
  · exact hns (LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL2)
  · exact hnq hSU3.1
  · exact hnq hSL3.1
  · exact hns (LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSp) (by decide) hSp4)

theorem barImage_eq_prodFactor_of_mem_calC {G : Type} [Group G] [Finite G] {L L₁ : Subgroup G}
    {A B : Type} [Group A] [Group B] [IsSimpleGroup A] [IsSimpleGroup B]
    (hAnc : ¬ IsMulCommutative A) (hBnc : ¬ IsMulCommutative B) (e : Bar2 L ≃* A × B)
    (h₁ : L₁ ∈ calC L) :
    barImage L L₁ = CFSG.GroupTheory.prodFirstFactor e ∨
      barImage L L₁ = CFSG.GroupTheory.prodSecondFactor e := by
  have : Nontrivial A := IsSimpleGroup.toNontrivial
  let F₁ : Subgroup (Bar2 L) := CFSG.GroupTheory.prodFirstFactor e
  let F₂ : Subgroup (Bar2 L) := CFSG.GroupTheory.prodSecondFactor e
  have hF : F₁ ≠ F₂ := by
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    intro hEq
    have hx₁ : e.symm (a, 1) ∈ F₁ :=
      (CFSG.GroupTheory.mem_prodFirstFactor_iff (e := e)).mpr (by
        simp only [MulEquiv.apply_symm_apply]
        exact ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩)
    have hx₂ : e.symm (a, 1) ∈ F₂ := hEq ▸ hx₁
    have hmem := (CFSG.GroupTheory.mem_prodSecondFactor_iff (e := e)).mp hx₂
    simp only [MulEquiv.apply_symm_apply, Subgroup.mem_prod] at hmem
    exact ha (Subgroup.mem_bot.mp hmem.1)
  let 𝒜 : Finset (Subgroup (Bar2 L)) := Finset.cons F₁ {F₂} (by simpa using hF)
  have hAn : ∀ K ∈ 𝒜, K.Normal := by
    intro K hK
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl
    exacts [CFSG.GroupTheory.prodFirstFactor_normal e,
      CFSG.GroupTheory.prodSecondFactor_normal e]
  have hAs : ∀ K ∈ 𝒜, IsSimpleGroup ↥K := by
    intro K hK
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl
    exacts [(CFSG.GroupTheory.prodFirstFactorMulEquiv e).isSimpleGroup,
      (CFSG.GroupTheory.prodSecondFactorMulEquiv e).isSimpleGroup]
  have hAnab : ∀ K ∈ 𝒜, ¬ IsMulCommutative ↥K := by
    intro K hK
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl
    exacts [fun hc => hAnc
        ((CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr
          (CFSG.GroupTheory.prodFirstFactorMulEquiv e)).mp hc),
      fun hc => hBnc
        ((CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr
          (CFSG.GroupTheory.prodSecondFactorMulEquiv e)).mp hc)]
  have hcomm : ∀ K ∈ 𝒜, ∀ K' ∈ 𝒜, K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', Commute a b := by
    intro K hK K' hK' hne a ha b hb
    rcases (by simpa [𝒜] using hK : K = F₁ ∨ K = F₂) with rfl | rfl <;>
      rcases (by simpa [𝒜] using hK' : K' = F₁ ∨ K' = F₂) with rfl | rfl
    · exact absurd rfl hne
    · exact CFSG.GroupTheory.commute_prodFirstFactor_prodSecondFactor e ha hb
    · exact (CFSG.GroupTheory.commute_prodFirstFactor_prodSecondFactor e hb ha).symm
    · exact absurd rfl hne
  have hsup : 𝒜.sup id = ⊤ := by
    simpa [𝒜, Finset.sup_cons, Finset.sup_singleton]
      using CFSG.GroupTheory.prodFirstFactor_sup_prodSecondFactor e
  obtain ⟨K, hKmem, hKeq⟩ := CFSG.GroupTheory.eq_of_isComponent_sup_of_direct (𝒜 := 𝒜)
    hAn hAs hAnab hcomm hsup _ (uc22p22l_barImage_isComponent h₁)
  rcases (by simpa [𝒜] using hKmem : K = F₁ ∨ K = F₂) with rfl | rfl
  exacts [Or.inl hKeq, Or.inr hKeq]

theorem not_nParam_of_mulEquiv_prod_isL2 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {A B : Type} [Group A] [Group B] (e : Bar2 L ≃* A × B) {i j n : ℕ} (hA : IsL2 A i)
    (hB : IsL2 B j) (hij : i ≠ j) : ¬ NParam L n := by
  have : IsSimpleGroup A :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hA
  have : IsSimpleGroup B :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hB
  have : Nontrivial A := IsSimpleGroup.toNontrivial
  have : Nontrivial B := IsSimpleGroup.toNontrivial
  have hAnc : ¬ IsMulCommutative A := by
    obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hA
    exact fun hc => hab (hc.is_comm.comm a b)
  have hBnc : ¬ IsMulCommutative B := by
    obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hB
    exact fun hc => hab (hc.is_comm.comm a b)
  rintro (hS | ⟨L₁, L₂, h₁, h₂, hsup, -, hshapes⟩)
  · exact not_nParamSingle_of_mulEquiv_prod hAnc hBnc e hS
  have hsingle : ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)), NParamSingle (Bar2 L') n := by
    intro L' hL'
    rcases hshapes L' hL' with h | h | ⟨hn3, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst hn3
      exact Or.inr (Or.inr (Or.inl h))
  have hfac : ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)), L' ∈ calC L →
      (barImage L L' = CFSG.GroupTheory.prodFirstFactor e ∧ n = i) ∨
        (barImage L L' = CFSG.GroupTheory.prodSecondFactor e ∧ n = j) := by
    intro L' hL' hc
    obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hc
    rcases barImage_eq_prodFactor_of_mem_calC hAnc hBnc e hc with hEq | hEq
    · refine Or.inl ⟨hEq, kNshape_holds G L' n i (Or.inl (hsingle L' hL')) (Or.inl ?_)⟩
      have hbar : IsL2 (barImage L L') i := by
        rw [hEq]
        exact LieModel.of_mulEquiv (CFSG.GroupTheory.prodFirstFactorMulEquiv e).symm hA
      exact LieModel.of_mulEquiv e₁.symm hbar
    · refine Or.inr ⟨hEq, kNshape_holds G L' n j (Or.inl (hsingle L' hL')) (Or.inl ?_)⟩
      have hbar : IsL2 (barImage L L') j := by
        rw [hEq]
        exact LieModel.of_mulEquiv (CFSG.GroupTheory.prodSecondFactorMulEquiv e).symm hB
      exact LieModel.of_mulEquiv e₁.symm hbar
  have hsupTop := barImage_sup_eq_top (CFSG.Quasithin.A3.subnormal_le h₁.1)
    (CFSG.Quasithin.A3.subnormal_le h₂.1) hsup
  have hF₁ : CFSG.GroupTheory.prodFirstFactor e ≠ ⊤ := by
    intro htop
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have hmem : e.symm (1, b) ∈ CFSG.GroupTheory.prodFirstFactor e := htop ▸ Subgroup.mem_top _
    rw [CFSG.GroupTheory.mem_prodFirstFactor_iff] at hmem
    simp only [MulEquiv.apply_symm_apply, Subgroup.mem_prod] at hmem
    exact hb (Subgroup.mem_bot.mp hmem.2)
  have hF₂ : CFSG.GroupTheory.prodSecondFactor e ≠ ⊤ := by
    intro htop
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hmem : e.symm (a, 1) ∈ CFSG.GroupTheory.prodSecondFactor e := htop ▸ Subgroup.mem_top _
    rw [CFSG.GroupTheory.mem_prodSecondFactor_iff] at hmem
    simp only [MulEquiv.apply_symm_apply, Subgroup.mem_prod] at hmem
    exact ha (Subgroup.mem_bot.mp hmem.1)
  rcases hfac L₁ (by simp) h₁ with ⟨hE₁, hn₁⟩ | ⟨hE₁, hn₁⟩ <;>
    rcases hfac L₂ (by simp) h₂ with ⟨hE₂, hn₂⟩ | ⟨hE₂, hn₂⟩
  · rw [hE₁, hE₂, sup_idem] at hsupTop
    exact hF₁ hsupTop
  · exact hij (hn₁.symm.trans hn₂)
  · exact hij (hn₂.symm.trans hn₁)
  · rw [hE₁, hE₂, sup_idem] at hsupTop
    exact hF₂ hsupTop

theorem ordA_two_ne_ordA_three {f g : ℕ} (hf : 1 ≤ f) (hg : 2 ≤ g) :
    ordA 2 (2 ^ f) ≠ ordA 3 (2 ^ g) := by
  intro hm
  have h1 := CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hf
  rw [hm] at h1
  obtain ⟨hN, hZ⟩ :=
    h1.transfer (CFSG.Timmesfeld.Orders.profile_ordA (n := 3) (by norm_num) (by omega))
  norm_num at hN
  have hk : CFSG.Timmesfeld.Orders.zA 2 f (f * 3) := ⟨3, by simp, dvd_rfl⟩
  obtain ⟨i, hi, hdvd⟩ := (hZ (f * 3) (by omega) (by omega)).mp hk
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  have hle : f * 3 ≤ g * i := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
  interval_cases i <;> omega

theorem ordA_two_ne_ordBC_three {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA 2 (2 ^ f) ≠ ordBC 3 (2 ^ g) := by
  intro hm
  have h1 := CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hf
  rw [hm] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.Timmesfeld.Orders.profile_ordBC (n := 3) hg)
  norm_num at hN
  have hk : CFSG.Timmesfeld.Orders.zA 2 f (f * 3) := ⟨3, by simp, dvd_rfl⟩
  obtain ⟨i, hi, hdvd⟩ := (hZ (f * 3) (by omega) (by omega)).mp hk
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  have hle : f * 3 ≤ g * (2 * i) := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
  interval_cases i <;> omega

theorem ordA_two_ne_ordTwistedD_four {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA 2 (2 ^ f) ≠ ordTwistedD 4 (2 ^ g) := by
  intro hm
  have h1 := CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) hf
  rw [hm] at h1
  obtain ⟨hN, hZ⟩ :=
    h1.transfer (CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := 4) (by norm_num) hg)
  norm_num at hN
  have hk : CFSG.Timmesfeld.Orders.zA 2 f (f * 3) := ⟨3, by simp, dvd_rfl⟩
  rcases (hZ (f * 3) (by omega) (by omega)).mp hk with ⟨hdvd, -⟩ | ⟨i, hi, hdvd⟩
  · have hle : f * 3 ≤ 2 * (g * 4) := Nat.le_of_dvd (by omega) hdvd
    omega
  · simp only [Finset.mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have hle : f * 3 ≤ g * (2 * i) := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
    interval_cases i <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
