module

public import CFSG.Blueprint.Chevalley
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFusion
public import CFSG.LocalAnalysis.StandardType.GGCompListMarked
public import CFSG.LocalAnalysis.StandardType.GGE7TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFacts

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType


theorem e7Label_adjointQuotient_nonempty :
    Nonempty (CFSG.Blueprint.AdjointQuotient .E7 (ZMod 2) ≃*
      ↥(adjointGroup .E7 (ZMod 2))) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := ZMod 2))).trans
    QuotientGroup.quotientBot⟩

theorem e7Label_hasLabel_adjointGroup_two :
    GGHasLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) ↥(adjointGroup .E7 (ZMod 2)) := by
  obtain ⟨eAQ⟩ := e7Label_adjointQuotient_nonempty
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv (K := ZMod 2) (τ := .E7)
  dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeChevalley]
  exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨eAQ.symm.trans eQ.symm⟩⟩

theorem e7Label_center_eq_bot_and_mulEquiv {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hKq : IsQuasisimple ↥K)
    (hlab : GGHasLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K)) :
    Subgroup.center ↥K = ⊥ ∧ Nonempty (↥K ≃* ↥(adjointGroup .E7 (ZMod 2))) := by
  obtain ⟨eAQ⟩ := e7Label_adjointQuotient_nonempty
  obtain ⟨eRA⟩ := nonempty_mulEquiv_of_ggHasLabel hlab e7Label_hasLabel_adjointGroup_two
  have hZ : Subgroup.center ↥K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hKq
      (n := 1) (by norm_num) (by rw [Nat.card_zmod, pow_one]) (eRA.trans eAQ.symm)
  exact ⟨hZ, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).symm.trans eRA⟩⟩

theorem e7Label_eq_of_labelIso_e7 {lab : LargeEvenLabel}
    (h : GGLabelIso lab (⟨.E7, 0, 1⟩ : LargeEvenLabel)) : lab = ⟨.E7, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp_all [GGLabelIso]

theorem ne_of_rowIII_of_e7Label {X : Type} [Group X] [Finite X] {K J : Subgroup X}
    (hrow : GGSixRCKJRow .III J)
    (hlab : GGHasLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K)) :
    J ≠ K := by
  intro hJK
  have hrowK : GGSixRCKJRow .III K := by rw [← hJK]; exact hrow
  obtain ⟨-, labK, hΛK, hrawK⟩ := hrowK
  obtain ⟨R, _instR, I, F, -, -, θK, hrowIII⟩ := largeEvenRawDatum_exists hrawK
  have hlabelK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) :=
    largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨-, -, θ, -⟩ := h
      exact ⟨θ⟩) hrawK
  have hiso : GGLabelIso labK (⟨.E7, 0, 1⟩ : LargeEvenLabel) :=
    ggLabelRigidInput_holds labK ⟨.E7, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K) hΛK
      (by simp [LargeEvenInLambda2])
      hlabelK hlab
  have hEq : labK = ⟨.E7, 0, 1⟩ := e7Label_eq_of_labelIso_e7 hiso
  subst hEq
  have hII : ggSixRCKLabelRow (⟨.E7, 0, 1⟩ : LargeEvenLabel) = .II := by decide
  rw [hII] at hrowIII
  exact absurd hrowIII (by decide)


theorem e7Label_forall_mem_range_conj_adjointGroup_two
    (β : MulAut ↥(adjointGroup .E7 (ZMod 2))) :
    β ∈ (MulAut.conj : ↥(adjointGroup .E7 (ZMod 2)) →*
      MulAut ↥(adjointGroup .E7 (ZMod 2))).range := by
  let e : ↥(⊤ : Subgroup ↥(adjointGroup .E7 (ZMod 2))) ≃*
      adjointGroup .E7 (ZMod 2) := Subgroup.topEquiv
  have h := CFSG.SeitzReduction.E7Pilot.forall_mem_range_conj_of_mulEquiv_E7_two
    (K := ZMod 2) (by rw [Nat.card_zmod]) e ((MulAut.congr e).symm β)
  obtain ⟨y, hy⟩ := h
  refine ⟨e y, ?_⟩
  calc MulAut.conj (e y) = MulAut.congr e (MulAut.conj y) :=
        (CFSG.mulAut_congr_conj e y).symm
    _ = MulAut.congr e ((MulAut.congr e).symm β) := by rw [hy]
    _ = β := MulEquiv.apply_symm_apply _ _

theorem e7Label_eq_of_labelIso_D6 {lab : LargeEvenLabel}
    (h : GGLabelIso (⟨.D, 6, 1⟩ : LargeEvenLabel) lab) : lab = ⟨.D, 6, 1⟩ := by
  rcases h with h | ⟨h1, -, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h.symm
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h2 (by simp)

theorem e7Label_eq_of_labelIso_twD5 {lab : LargeEvenLabel}
    (h : GGLabelIso (⟨.twD, 5, 1⟩ : LargeEvenLabel) lab) :
    lab = ⟨.twD, 5, 1⟩ := by
  rcases h with h | ⟨h1, -, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h.symm
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h2 (by simp)

theorem e7Label_eq_of_labelIso_twE6 {lab : LargeEvenLabel}
    (h : GGLabelIso (⟨.twE6, 0, 1⟩ : LargeEvenLabel) lab) :
    lab = ⟨.twE6, 0, 1⟩ := by
  rcases h with h | ⟨h1, -, -, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h.symm
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact absurd h2 (by simp)

theorem e7Label_exists_conj {X : Type} [Group X] [Finite X] {K J : Subgroup X} {d : X}
    (hKq : IsQuasisimple ↥K) (e : ↥K ≃* ↥(adjointGroup .E7 (ZMod 2)))
    (hdK : d ∈ Subgroup.normalizer (K : Set X)) (hd3 : d ^ 3 = 1)
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) (hJK : J ≤ K) (hJne : J ≠ K) :
    ∃ s : ↥(adjointGroup .E7 (ZMod 2)), s ^ 3 = 1 ∧ s ≠ 1 ∧
      (∀ x : ↥K, ∀ hx : d * (x : X) * d⁻¹ ∈ K,
        e ⟨d * (x : X) * d⁻¹, hx⟩ = s * e x * s⁻¹) ∧
      IsComponentOf ((J.subgroupOf K).map e.toMonoidHom) (Subgroup.centralizer {s}) := by
  let α : MulAut ↥K := K.normalizerMonoidHom ⟨d, hdK⟩
  have hα3 : α ^ 3 = 1 := by
    have hd3' : (⟨d, hdK⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 := Subtype.ext hd3
    change (K.normalizerMonoidHom ⟨d, hdK⟩) ^ 3 = 1
    rw [← map_pow, hd3', map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hcent : d ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun β : MulAut ↥K => ((β ⟨x, hx⟩ : ↥K) : X)) h1
      change d * x * d⁻¹ = x at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have hinf : K ⊓ Subgroup.centralizer ({d} : Set X) = K := by
      refine le_antisymm inf_le_left ?_
      intro x hx
      refine ⟨hx, ?_⟩
      change x ∈ Subgroup.centralizer ({d} : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hcent x hx).symm
    have hJcompK : IsComponentOf J K := by
      rw [← hinf]
      exact hJcomp
    have hKqA : Assembly.IsQuasisimple ↥K :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mpr hKq
    have hJeqK : J = K :=
      CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJcompK
        ⟨le_rfl, IsSubnormal.refl K, hKqA⟩ hJcompK.1
    exact hJne hJeqK
  let β : MulAut ↥(adjointGroup .E7 (ZMod 2)) := MulAut.congr e α
  obtain ⟨s, hs⟩ := e7Label_forall_mem_range_conj_adjointGroup_two β
  have hβ3 : β ^ 3 = 1 := by
    change (MulAut.congr e α) ^ 3 = 1
    rw [← map_pow, hα3, map_one]
  have hact : ∀ x : ↥K, ∀ hx : d * (x : X) * d⁻¹ ∈ K,
      e ⟨d * (x : X) * d⁻¹, hx⟩ = s * e x * s⁻¹ := by
    intro x hx
    have hαx : α x = ⟨d * (x : X) * d⁻¹, hx⟩ := by
      apply Subtype.ext
      simpa [α] using Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨d, hdK⟩ x
    rw [← hαx]
    calc e (α x) = MulAut.congr e α (e x) := by
          simp [MulAut.congr_apply]
      _ = MulAut.conj s (e x) := by rw [show MulAut.congr e α = MulAut.conj s from hs.symm]
      _ = s * e x * s⁻¹ := by rw [MulAut.conj_apply]
  have hfix : ggFixSub α =
      (K ⊓ Subgroup.centralizer ({d} : Set X)).subgroupOf K := by
    ext x
    simp only [mem_ggFixSub, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      intro y hy
      subst hy
      have h := congrArg (fun y : ↥K => (y : X)) hx
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact mul_inv_eq_iff_eq_mul.mpr (hx d rfl)
  have hcompFix : IsComponentOf (J.subgroupOf K) (ggFixSub α) := by
    rw [hfix]
    exact ⟨Subgroup.subgroupOf_mono K hJcomp.1, hJcomp.2.1.comap K.subtype,
      Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJcomp.2.2⟩
  have hfixMap : (ggFixSub α).map e.toMonoidHom =
      Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmem : d * ((x : ↥K) : X) * d⁻¹ ∈ K := by
        have := (α x).2
        simpa [α, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
      have ha := hact x hmem
      have hαx : α x = ⟨d * ((x : ↥K) : X) * d⁻¹, hmem⟩ := Subtype.ext rfl
      have h1 : e x = s * e x * s⁻¹ := by rw [← ha, ← hαx, hx]
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact mul_inv_eq_iff_eq_mul.mp h1.symm
    · intro hy
      rw [Subgroup.mem_centralizer_iff] at hy
      refine ⟨e.symm y, ?_, by simp⟩
      change e.symm y ∈ ggFixSub α
      rw [mem_ggFixSub]
      apply e.injective
      have hmem : d * ((e.symm y : ↥K) : X) * d⁻¹ ∈ K := by
        have := (α (e.symm y)).2
        simpa [α, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
      have ha := hact (e.symm y) hmem
      have hβy : MulAut.congr e α y = s * y * s⁻¹ := by
        rw [show MulAut.congr e α = MulAut.conj s from hs.symm, MulAut.conj_apply]
      have hay : e (α (e.symm y)) = s * y * s⁻¹ := by
        rw [show e (α (e.symm y)) = MulAut.congr e α y from by
          simp [MulAut.congr_apply]]
        exact hβy
      rw [hay, MulEquiv.apply_symm_apply]
      exact mul_inv_eq_iff_eq_mul.mpr (hy s (by simp))
  have hmap := CFSG.isComponentOf_map_mulEquiv e (isComponentOf_iff_open.mp hcompFix)
  rw [hfixMap] at hmap
  refine ⟨s, ?_, ?_, hact, (isComponentOf_iff_open).mpr hmap⟩
  · have hconj3 : MulAut.conj (s ^ 3) = 1 := by
      rw [map_pow, hs, hβ3]
    have hmem : s ^ 3 ∈ Subgroup.center ↥(adjointGroup .E7 (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := DFunLike.congr_fun hconj3 x
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hmem
  · intro hs1
    have hαeq : α = 1 := by
      have h1 : MulAut.congr e α = 1 := by
        rw [show MulAut.congr e α = MulAut.conj s from hs.symm, hs1, map_one]
      exact (MulAut.congr e).injective (by rw [h1, map_one])
    exact hα1 hαeq

theorem e7Label_component_rowIII {X : Type} [Group X] [Finite X] {K J : Subgroup X} {d : X}
    (hKq : IsQuasisimple ↥K)
    (hlab : GGHasLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hdK : d ∈ Subgroup.normalizer (K : Set X)) (hd3 : d ^ 3 = 1)
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) (hJK : J ≤ K)
    (hrow : GGSixRCKJRow .III J) :
    GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) ∨
      GGHasLabel (⟨.twA, 6, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
  have hJne : J ≠ K := ne_of_rowIII_of_e7Label hrow hlab
  obtain ⟨-, ⟨e⟩⟩ := e7Label_center_eq_bot_and_mulEquiv hKq hlab
  obtain ⟨s, hs3, hs1, -, hcomp⟩ :=
    e7Label_exists_conj hKq e hdK hd3 hJcomp hJK hJne
  let A := ↥(adjointGroup .E7 (ZMod 2))
  let α : MulAut A := MulAut.conj s
  have hperfA : commutator A = ⊤ :=
    Group.isPerfect_def.mp
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 (ZMod 2)).1
  have hα3 : α ^ 3 = 1 := by
    change (MulAut.conj s) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hmem : s ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := DFunLike.congr_fun h1 x
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hmem
    exact hs1 hmem
  have hfix : ggFixSub α = Subgroup.centralizer ({s} : Set A) := by
    ext x
    simp only [mem_ggFixSub, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      MulAut.conj_apply]
    constructor
    · intro h y hy
      subst hy
      exact mul_inv_eq_iff_eq_mul.mp h
    · intro h
      exact mul_inv_eq_iff_eq_mul.mpr (h s rfl)
  have hcompA : IsComponentOf ((J.subgroupOf K).map e.toMonoidHom) (ggFixSub α) := by
    rw [hfix]
    exact hcomp
  have hraw : LargeEvenRawDatum (⟨.E7, 0, 1⟩ : LargeEvenLabel)
      (fun R _ I _ => ∃ θ : A ⧸ Subgroup.center A ≃* R,
        ∃ β ∈ I, LargeEvenInduces θ (fun x y => y = α x) β) := by
    obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv (K := ZMod 2) (τ := .E7)
    let θ : A ⧸ Subgroup.center A ≃*
        LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) (ZMod 2) false) :=
      eQ.symm
    refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ?_⟩
    refine ⟨θ, MulAut.conj (θ (QuotientGroup.mk s)), ?_, ?_⟩
    · exact Subgroup.subset_closure (Set.mem_union_left _ ⟨θ (QuotientGroup.mk s), rfl⟩)
    · intro x y hy
      subst hy
      change MulAut.conj (θ (QuotientGroup.mk s)) (θ (QuotientGroup.mk x)) =
        θ (QuotientGroup.mk (MulAut.conj s x))
      rw [MulAut.conj_apply, MulAut.conj_apply]
      simp only [map_mul, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  obtain ⟨labJ, hmem, hlabelJmap⟩ :=
    GGCompList.of_rawMarking E7TwoThree.ggE7TwoThreeComp_holds hperfA hα3 hα1 hraw hcompA
  have hlabelJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_quotCenter_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hJK).symm.trans
        (Subgroup.equivMapOfInjective (J.subgroupOf K) e.toMonoidHom e.injective)).symm
      hlabelJmap
  obtain ⟨-, lab', hΛ', hraw'⟩ := hrow
  obtain ⟨R', _instR', I', F', -, -, θ', hrow'⟩ := largeEvenRawDatum_exists hraw'
  have hlabel' : GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) :=
    largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨-, -, θ, -⟩ := h
      exact ⟨θ⟩) hraw'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hΛJ : LargeEvenInLambda2 labJ := by
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> simp [LargeEvenInLambda2]
  have hiso : GGLabelIso labJ lab' :=
    ggLabelRigidInput_holds labJ lab' (↥J ⧸ Subgroup.center ↥J) hΛJ hΛ' hlabelJ hlabel'
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hEq : lab' = ⟨.D, 6, 1⟩ := e7Label_eq_of_labelIso_D6 hiso
    rw [hEq] at hrow'
    simp [ggSixRCKLabelRow] at hrow'
  · exact Or.inl hlabelJ
  · exact Or.inr hlabelJ
  · exfalso
    have hEq : lab' = ⟨.twD, 5, 1⟩ := e7Label_eq_of_labelIso_twD5 hiso
    rw [hEq] at hrow'
    simp [ggSixRCKLabelRow] at hrow'
  · exfalso
    have hEq : lab' = ⟨.twE6, 0, 1⟩ := e7Label_eq_of_labelIso_twE6 hiso
    rw [hEq] at hrow'
    simp [ggSixRCKLabelRow] at hrow'

end CFSG.StandardType.RCKC1
