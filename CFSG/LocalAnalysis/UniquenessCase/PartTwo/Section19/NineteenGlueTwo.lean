module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenLpFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwoVZero
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.JMEqualFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape lieModel_eq_of_isChar2LieShape)

variable {G : Type} [Group G] [Finite G]

theorem exists_two_calC_sup_eq_Lp (D : Data G) {p n : ℕ} (h54 : S17.Hyp1754 D p)
    (hH : Hinf D.M = S17.Lp D p) {A B : Type} [Group A] [Group B]
    (e : Bar2 (S17.Lp D p) ≃* A × B) (hA : IsL2 A n) (hB : IsL2 B n ∨ IsU3 B n) :
    ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
      Nonempty (Bar2 K₁ ≃* A) ∧ Nonempty (Bar2 K₂ ≃* B) ∧ K₁ ⊔ K₂ = S17.Lp D p := by
  classical
  let πA : Bar2 (Lp D p) →* A := (MonoidHom.fst A B).comp e.toMonoidHom
  let πB : Bar2 (Lp D p) →* B := (MonoidHom.snd A B).comp e.toMonoidHom
  let CA : Subgroup (Bar2 (Lp D p)) := πB.ker
  let CB : Subgroup (Bar2 (Lp D p)) := πA.ker
  have hCAn : CA.Normal := inferInstance
  have hCBn : CB.Normal := inferInstance
  let fA : CA →* A := πA.comp CA.subtype
  have hfA_inj : Function.Injective fA := by
    intro x y hxy
    have h1 : (e (x : Bar2 (Lp D p))).1 = (e (y : Bar2 (Lp D p))).1 := by
      simpa [fA, πA] using hxy
    have hx : (e (x : Bar2 (Lp D p))).2 = 1 := by
      simpa [πB] using MonoidHom.mem_ker.mp x.2
    have hy : (e (y : Bar2 (Lp D p))).2 = 1 := by
      simpa [πB] using MonoidHom.mem_ker.mp y.2
    apply Subtype.ext
    apply e.injective
    exact Prod.ext h1 (by rw [hx, hy])
  have hfA_surj : Function.Surjective fA := by
    intro a
    refine ⟨⟨e.symm (a, 1), ?_⟩, ?_⟩
    · show πB (e.symm (a, 1)) = 1
      simp [πB]
    · show fA ⟨e.symm (a, 1), _⟩ = a
      simp [fA, πA]
  let eCA : CA ≃* A := MulEquiv.ofBijective fA ⟨hfA_inj, hfA_surj⟩
  let fB : CB →* B := πB.comp CB.subtype
  have hfB_inj : Function.Injective fB := by
    intro x y hxy
    have h1 : (e (x : Bar2 (Lp D p))).2 = (e (y : Bar2 (Lp D p))).2 := by
      simpa [fB, πB] using hxy
    have hx : (e (x : Bar2 (Lp D p))).1 = 1 := by
      simpa [πA] using MonoidHom.mem_ker.mp x.2
    have hy : (e (y : Bar2 (Lp D p))).1 = 1 := by
      simpa [πA] using MonoidHom.mem_ker.mp y.2
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (by rw [hx, hy]) h1
  have hfB_surj : Function.Surjective fB := by
    intro b
    refine ⟨⟨e.symm (1, b), ?_⟩, ?_⟩
    · show πA (e.symm (1, b)) = 1
      simp [πA]
    · show fB ⟨e.symm (1, b), _⟩ = b
      simp [fB, πB]
  let eCB : CB ≃* B := MulEquiv.ofBijective fB ⟨hfB_inj, hfB_surj⟩
  have hAsimp : IsSimpleGroup A :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
  have hAnon : ∃ a b : A, a * b ≠ b * a :=
    CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hA
  have hCAq : CFSG.IsQuasisimple CA :=
    CFSG.IsQuasisimple.of_mulEquiv eCA
      (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup A _ hAsimp hAnon).1
  have hCAcomp : CFSG.IsComponent CA := ⟨hCAq, hCAn.isSubnormal⟩
  have hBq : CFSG.IsQuasisimple B := by
    rcases hB with hB2 | hB3
    · have hBsimp : IsSimpleGroup B :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB2
      exact (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup B _ hBsimp
        (CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hB2)).1
    · have hBsimp : IsSimpleGroup B :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB3
      exact (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup B _ hBsimp
        (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hB3)).1
  have hCBq : CFSG.IsQuasisimple CB := CFSG.IsQuasisimple.of_mulEquiv eCB hBq
  have hCBcomp : CFSG.IsComponent CB := ⟨hCBq, hCBn.isSubnormal⟩
  obtain ⟨K₁, hK₁calLp, hbarK₁⟩ := s13_exists_calC_of_component (Lp D p) hCAcomp
  obtain ⟨K₂, hK₂calLp, hbarK₂⟩ := s13_exists_calC_of_component (Lp D p) hCBcomp
  have hK₁calM : K₁ ∈ calC D.M := calC_of_calC_Lp D hK₁calLp
  have hK₂calM : K₂ ∈ calC D.M := calC_of_calC_Lp D hK₂calLp
  have hK₁leLp : K₁ ≤ Lp D p := hK₁calLp.1.le
  have hK₂leLp : K₂ ≤ Lp D p := hK₂calLp.1.le
  have hK₁normM : (K₁.subgroupOf D.M).Normal := (h54.2 K₁ hK₁calM).1
  have hK₂normM : (K₂.subgroupOf D.M).Normal := (h54.2 K₂ hK₂calM).1
  have hK₁normLp : (K₁.subgroupOf (Lp D p)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁leLp).2
      ((Lp_le_M D p).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁calM.1.le).1 hK₁normM))
  have hK₂normLp : (K₂.subgroupOf (Lp D p)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂leLp).2
      ((Lp_le_M D p).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₂calM.1.le).1 hK₂normM))
  have hCAsup : CA ⊔ CB = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      rw [← map_mul]
      simp
    rw [hx]
    refine Subgroup.mul_mem_sup ?_ ?_
    · show πB (e.symm ((e x).1, 1)) = 1
      simp [πB]
    · show πA (e.symm (1, (e x).2)) = 1
      simp [πA]
  have hCAneCB : CA ≠ CB := by
    intro hEq
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hmemCA : e.symm (a, 1) ∈ CA := by
      show πB (e.symm (a, 1)) = 1
      simp [πB]
    have hmemCB : e.symm (a, 1) ∈ CB := hEq ▸ hmemCA
    have h1 : (e (e.symm (a, 1))).1 = 1 := by
      simpa [πA] using MonoidHom.mem_ker.mp hmemCB
    exact ha (by simpa using h1)
  have hK₁neK₂ : K₁ ≠ K₂ := by
    intro hEq
    apply hCAneCB
    rw [← hbarK₁, ← hbarK₂, hEq]
  let Dsub : Subgroup G := K₁ ⊔ K₂
  have hDle : Dsub ≤ Lp D p := sup_le hK₁leLp hK₂leLp
  have hDsubNorm : (Dsub.subgroupOf (Lp D p)).Normal := by
    rw [show Dsub.subgroupOf (Lp D p) =
      K₁.subgroupOf (Lp D p) ⊔ K₂.subgroupOf (Lp D p) from
      Subgroup.subgroupOf_sup hK₁leLp hK₂leLp]
    exact @Subgroup.sup_normal ↥(Lp D p) _
      (K₁.subgroupOf (Lp D p)) (K₂.subgroupOf (Lp D p)) hK₁normLp hK₂normLp
  have hDnorm : Lp D p ≤ normalizer (Dsub : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDle).1 hDsubNorm
  have hDbar : barImage (Lp D p) Dsub = ⊤ := by
    rw [show Dsub = K₁ ⊔ K₂ from rfl, s13_barImage_sup hK₁leLp hK₂leLp,
      hbarK₁, hbarK₂, hCAsup]
  have hDN : Dsub ⊔ pCoreOf 2 (Lp D p) = Lp D p := by
    have hpre := barPreimage_barImage_eq_sup_pCore (M := Lp D p) (H := Dsub) hDle
    rw [hDbar] at hpre
    have htop : barPreimage (Lp D p) (⊤ : Subgroup (Bar2 (Lp D p))) = Lp D p := by
      refine le_antisymm (uc22p21c_barPreimage_le _ _) fun x hx => ?_
      exact uc22p21c_mem_barPreimage.2 ⟨hx, Subgroup.mem_top _⟩
    rw [htop] at hpre
    simpa [CFSG.Open.pCoreOf] using hpre.symm
  have hdvd : Dsub.relIndex (Lp D p) ∣ Nat.card (pCoreOf 2 (Lp D p)) := by
    have hrelsup : (Dsub.subgroupOf (Lp D p)) ⊔
        ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hDle
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (Lp D p)), hDN, Subgroup.subgroupOf_self]
    have hrel1 : (Dsub.subgroupOf (Lp D p)).relIndex ⊤ =
        (Dsub.subgroupOf (Lp D p)).relIndex
          ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) := by
      rw [← hrelsup]
      exact @Subgroup.relIndex_sup_left ↥(Lp D p) _
        ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p))
        (Dsub.subgroupOf (Lp D p)) hDsubNorm
    have hrelD : Dsub.relIndex (Lp D p) =
        (Dsub.subgroupOf (Lp D p)).relIndex ⊤ := by
      rw [Subgroup.relIndex_top_right]
      rfl
    have hdvd' : (Dsub.subgroupOf (Lp D p)).relIndex ⊤ ∣
        Nat.card ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) := by
      rw [hrel1]
      have h := Subgroup.relIndex_mul_card (Dsub.subgroupOf (Lp D p))
        ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p))
      rw [← h]
      exact dvd_mul_right _ _
    have hcardN : Nat.card ((pCoreOf 2 (Lp D p)).subgroupOf (Lp D p)) =
        Nat.card (pCoreOf 2 (Lp D p)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (Lp D p))).toEquiv
    rw [hcardN] at hdvd'
    rw [hrelD]
    exact hdvd'
  obtain ⟨k, hk⟩ :=
    IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Lp D p))
  have hdvd' : Dsub.relIndex (Lp D p) ∣ 2 ^ k := by rwa [hk] at hdvd
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have hperf : ⁅Lp D p, Lp D p⁆ = Lp D p := by
    rw [← hH]
    exact uc22p21c_Hinf_perfect D.M
  have hLp_le_D : Lp D p ≤ Dsub :=
    Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow Nat.prime_two
      hDle hDnorm hj' le_rfl hperf
  have hD_eq : Dsub = Lp D p := le_antisymm hDle hLp_le_D
  obtain ⟨e1⟩ := s13_bar_equiv hK₁calLp
  obtain ⟨e2⟩ := s13_bar_equiv hK₂calLp
  exact ⟨K₁, K₂, hK₁calM, hK₂calM, hK₁neK₂,
    ⟨(e1.trans (MulEquiv.subgroupCongr hbarK₁)).trans eCA⟩,
    ⟨(e2.trans (MulEquiv.subgroupCongr hbarK₂)).trans eCB⟩, hD_eq⟩

theorem p17_64_2_of_ctx1768 (D : Data G) {V₀ V : Subgroup G}
    {L L' : Subgroup G}
    (c : S17.Ctx1768 D L L') (hL : L ∈ S17.calLp D 5)
    (hX0 : UC22.conjClosure D.M L ∈ S17.calL0Star D 5) (h68 : S17.R17_68At D V₀ V) :
    S17.P17_64_2 D 5 2 := by
  refine Or.inl ⟨?_, sp_five_ne_bot_of_ctx1768 D c hL hX0 h68⟩
  obtain ⟨e⟩ := c.isA5xA5_bar2
  have hLp : S17.Lp D 5 = UC22.conjClosure D.M L := by
    rw [lp_five_eq_sup_of_ctx1768 D c hL hX0 h68, ← c.hX]
  exact ⟨alternatingGroup (Fin 5), alternatingGroup (Fin 5), inferInstance, inferInstance,
    ⟨(MulEquiv.cast (M := fun x : Subgroup G => Bar2 x) hLp).trans e⟩,
    CFSG.Quasithin.H13.A5.lieModel_of_alternating_five (MulEquiv.refl _),
    CFSG.Quasithin.H13.A5.lieModel_of_alternating_five (MulEquiv.refl _)⟩


theorem r19_glue_2At_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) (h42 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V)
    (h642 : S17.R17_64_2At D V₀ V) (h643 : S17.R17_64_3At D V₀ V)
    (h68 : S17.R17_68At D V₀ V)
    (hshape : IsL2 (Bar2 L) 2 ∨ IsU3 (Bar2 L) 2) : R19_glue_2At D V₀ V p L h hshape := by
  have hLC : L ∈ calC D.M := S17.calLp_subset_calC D p h.hL
  have hLle : Hinf D.M = S17.Lp D p → L ≤ S17.Lp D p := fun hH =>
    hH ▸ uc22p21c_le_Hinf hLC.1.le hLC.2.1
  have hfin : ∀ (hp5 : p = 5) {A B : Type} [Group A] [Group B] (K₁ K₂ : Subgroup G),
      K₁ ∈ calC D.M → K₂ ∈ calC D.M → K₁ ≠ K₂ → Nonempty (Bar2 K₁ ≃* A) →
      Nonempty (Bar2 K₂ ≃* B) → K₁ ⊔ K₂ = S17.Lp D 5 → L ≤ S17.Lp D 5 →
      (L = K₁ → IsL2 B 2) → (L = K₂ → IsL2 A 2) → R19_glue_2At D V₀ V p L h hshape := by
    intro hp5 A B _ _ K₁ K₂ hK₁ hK₂ hne ⟨e₁⟩ ⟨e₂⟩ hsup hle hB hA
    rcases eq_left_or_right_of_mem_calC_le_sup hLC hK₁ hK₂ hne (hsup ▸ hle) with rfl | rfl
    · refine ⟨K₂, ⟨h, hshape, hp5, hK₂, ?_, hsup.symm, hne.symm⟩⟩
      exact S17.isAlt_five_of_isL2_two (CFSG.Blueprint.LieModel.of_mulEquiv e₂.symm (hB rfl))
    · refine ⟨K₁, ⟨h, hshape, hp5, hK₁, ?_, by rw [sup_comm]; exact hsup.symm, hne⟩⟩
      exact S17.isAlt_five_of_isL2_two (CFSG.Blueprint.LieModel.of_mulEquiv e₁.symm (hA rfl))
  by_cases hXL : UC22.conjClosure D.M L = L
  · have hL0 : L ∈ S17.calL0Star D p := hXL ▸ h.hX
    rcases hshape with hL2 | hU3
    ·
      have hAlt : IsAlt (Bar2 L) 5 := S17.isAlt_five_of_isL2_two hL2
      obtain ⟨hp5, hH, hP⟩ := S17.p_eq_five_of_eq_self h42 h641 h642 h643 h.hp h.hL hL0 hAlt
      subst hp5
      have h54 : S17.Hyp1754 D 5 :=
        S17.hyp1754_of_thin_mem_calL0Star D h42 h.hp h.hL hL0 (S17.thin8_of_isAlt_five hAlt)
      have hL5 : L ∈ S17.calL5Star D 5 := ⟨(S17.mem_calLpStar).2 ⟨L, h.hL, hXL.symm⟩, hAlt⟩
      have hEmpty : S17.calL4Star D 5 = ∅ :=
        S17.calL4Star_eq_empty_of_jM_eq_five ⟨L, hL0⟩ (S17.jM_eq_five_of_mem_calL5Star h.hL hL0 hL5)
      rcases hP with ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩ | ⟨hu3, -⟩
      · obtain ⟨K₁, K₂, hK₁, hK₂, hne, e₁, e₂, hsup⟩ :=
          exists_two_calC_sup_eq_Lp D h54 hH e hA (Or.inl hB)
        exact hfin rfl K₁ K₂ hK₁ hK₂ hne e₁ e₂ hsup (hLle hH) (fun _ => hB) (fun _ => hA)
      · exact (S17.false_of_isL2U3Product_two h54 hH hEmpty hu3).elim
    ·
      have hs : IsSimpleGroup (Bar2 L) :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
      have hj : S17.jM D p = 4 :=
        S17.jM_eq_four_of_mem_calL0Star hL0 h.hL hs (S17.not_isAlt_five_of_isU3_two hU3)
          ⟨2, Or.inr hU3⟩
      have h54 : S17.Hyp1754 D p := hyp1754_of_jM_eq_four D h h42 hj
      have hH : Hinf D.M = S17.Lp D p := h641 p h54
      obtain ⟨n, hn⟩ := h642 p h54
      have hn2 : n = 2 := by
        rcases S17.bar2_isL2_or_isU3_of_p1642 hLC (h54.2 L hLC).1 (hLle hH) hn with hL2 | hU3'
        · exact (UC22.not_isL2_of_isU3 hU3 hL2).elim
        · exact (lieModel_eq_of_isChar2LieShape hU3 (by unfold IsChar2LieShape; simp) hU3').2.2
      subst hn2
      have hp5 : p = 5 := S17.eq_five_of_modEq_four (D.sig_prime p h.hp).1 (h643 p h54 2 hn).2
      subst hp5
      rcases hn with ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩ | ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩
      · obtain ⟨K₁, K₂, hK₁, hK₂, hne, ⟨e₁⟩, ⟨e₂⟩, hsup⟩ :=
          exists_two_calC_sup_eq_Lp D h54 hH e hA (Or.inl hB)
        exfalso
        rcases eq_left_or_right_of_mem_calC_le_sup hLC hK₁ hK₂ hne (hsup ▸ hLle hH) with rfl | rfl
        · exact UC22.not_isL2_of_isU3 hU3 (CFSG.Blueprint.LieModel.of_mulEquiv e₁.symm hA)
        · exact UC22.not_isL2_of_isU3 hU3 (CFSG.Blueprint.LieModel.of_mulEquiv e₂.symm hB)
      · obtain ⟨K₁, K₂, hK₁, hK₂, hne, e₁, e₂, hsup⟩ :=
          exists_two_calC_sup_eq_Lp D h54 hH e hA (Or.inr hB)
        refine hfin rfl K₁ K₂ hK₁ hK₂ hne e₁ e₂ hsup (hLle hH) (fun hLK => ?_) (fun _ => hA)
        obtain ⟨e₁'⟩ := e₁
        subst hLK
        exact (UC22.not_isL2_of_isU3 hU3 (CFSG.Blueprint.LieModel.of_mulEquiv e₁'.symm hA)).elim
  · rcases hshape with hL2 | hU3
    ·
      obtain ⟨hp5, L', c⟩ := S17.ctx1768_of_ne h42 h.hp h.hL hXL (S17.isAlt_five_of_isL2_two hL2)
      subst hp5
      exact ⟨L', ⟨h, Or.inl hL2, rfl, c.hL', c.hAlt', lp_five_eq_sup_of_ctx1768 D c h.hL h.hX h68,
        c.hne⟩⟩
    ·
      exfalso
      obtain ⟨m, x, -, -, -, hsh, -⟩ := S17.p42_alt2_of_ne h42 h.hp hLC hXL
      rcases hsh with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · exact UC22.not_isL2_of_isU3 hU3 hL2
      · exact UC22.not_isSz_of_isU3 hU3 hSz

theorem p17_64_2_of_ctx19_1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K)
    (h42 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V)
    (h642 : S17.R17_64_2At D V₀ V) (h643 : S17.R17_64_3At D V₀ V)
    (h68 : S17.R17_68At D V₀ V) :
    S17.P17_64_2 D 5 2 := by
  have hp5 := h.p_eq
  subst hp5
  have hLC : L ∈ calC D.M := S17.calLp_subset_calC D 5 h.hyp.hL
  by_cases hXL : UC22.conjClosure D.M L = L
  · have hL0 : L ∈ S17.calL0Star D 5 := hXL ▸ h.hyp.hX
    rcases h.shape with hL2 | hU3
    · exact (S17.p_eq_five_of_eq_self h42 h641 h642 h643 h.hyp.hp h.hyp.hL hL0
        (S17.isAlt_five_of_isL2_two hL2)).2.2
    · have hs : IsSimpleGroup (Bar2 L) :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
      have hj : S17.jM D 5 = 4 :=
        S17.jM_eq_four_of_mem_calL0Star hL0 h.hyp.hL hs (S17.not_isAlt_five_of_isU3_two hU3)
          ⟨2, Or.inr hU3⟩
      have h54 : S17.Hyp1754 D 5 := hyp1754_of_jM_eq_four D h.hyp h42 hj
      have hH : Hinf D.M = S17.Lp D 5 := h641 5 h54
      obtain ⟨n, hn⟩ := h642 5 h54
      have hLle : L ≤ S17.Lp D 5 := hH ▸ uc22p21c_le_Hinf hLC.1.le hLC.2.1
      have hn2 : n = 2 := by
        rcases S17.bar2_isL2_or_isU3_of_p1642 hLC (h54.2 L hLC).1 hLle hn with hL2 | hU3'
        · exact (UC22.not_isL2_of_isU3 hU3 hL2).elim
        · exact (lieModel_eq_of_isChar2LieShape hU3 (by unfold IsChar2LieShape; simp) hU3').2.2
      subst hn2
      exact hn
  · rcases h.shape with hL2 | hU3
    · obtain ⟨-, L', c⟩ :=
        S17.ctx1768_of_ne h42 h.hyp.hp h.hyp.hL hXL (S17.isAlt_five_of_isL2_two hL2)
      exact p17_64_2_of_ctx1768 D c h.hyp.hL h.hyp.hX h68
    · exfalso
      obtain ⟨m, x, -, -, -, hsh, -⟩ := S17.p42_alt2_of_ne h42 h.hyp.hp hLC hXL
      rcases hsh with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · exact UC22.not_isL2_of_isU3 hU3 hL2
      · exact UC22.not_isSz_of_isU3 hU3 hSz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
