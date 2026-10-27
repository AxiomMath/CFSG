module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacTwisted
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4Row
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExcl
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcRee
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn2
public import CFSG.LocalAnalysis.StandardType.KGLangTorAGeneric
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.RankThree.PartOne.TCX.LayerEngineG

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgfniRee_layer_ge5 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {s : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a} (hs : orderOf s = p)
    {J : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s))) :
    CFSG.Open.IsQuasisimple ↥J ∧ Subgroup.center ↥J = ⊥ ∧
      2 ^ (2 * a + 1) - 1 ∣ Nat.card ↥J ∧
      (Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥J) ∨
        Nonempty (CFSG.Blueprint.suzukiGroup a K ≃* ↥J)) := by
  classical
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Subtype.finite
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj] at hJ
  have hnt : Nontrivial ↥J := by
    haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
    exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  have htop : (⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆) = ⊤ := by
    simpa [commutator_def] using hJ.2.2.1
  have hperfJ : ⁅J, J⁆ = J := by
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥J)) (H₂ := (⊤ : Subgroup ↥J))
      (f := J.subtype)
    rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have hp3 : 3 < p := by omega
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116b.largeRee_layer_typed
    ha hK hp hp3 s hs with hsolv | ⟨N, hNC, hCN, hNsimple, hty⟩
  · exfalso
    haveI := hsolv
    have hJsolv : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJ.1)
        (Subgroup.inclusion_injective hJ.1)
    haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
    haveI : Nontrivial ↥J := hnt
    exact Group.IsPerfect.not_isSolvable ↥J hJsolv
  · have hJN : J ≤ N := by
      calc J = ⁅J, J⁆ := hperfJ.symm
        _ ≤ ⁅Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)),
              Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))⁆ :=
            Subgroup.commutator_mono hJ.1 hJ.1
        _ ≤ N := hCN
    have hNnorm : (N.subgroupOf
        (Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)))).Normal :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.l154_normal_subgroupOf_of_commutator_le hNC hCN
    have hsub : CFSG.Open.IsSubnormal J N := by
      have h := CFSG.LocalAnalysis.GLTheoremA.K155X.l154_isSubnormal_inf_normal
        hJ.2.1 hNC hNnorm
      rwa [inf_eq_left.2 hJN] at h
    have hty' : Nonempty (↥N ≃* CFSG.Blueprint.suzukiGroup a K) ∨
        Nonempty (↥N ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
      rcases hty with h | h
      · obtain ⟨e⟩ := h
        exact Or.inr ⟨e.symm⟩
      · obtain ⟨e⟩ := h
        exact Or.inl ⟨e.symm⟩
    obtain ⟨hNq, hNZ, hNdvd⟩ :=
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.layerType_props ha hK hty'
    have hNqOpen : CFSG.Open.IsQuasisimple ↥N :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hNq
    have heq : J = N :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.l154_eq_of_subnormal_quasisimple
        hsub hNqOpen hperfJ ((Subgroup.nontrivial_iff_ne_bot J).mp hnt)
    rw [heq]
    exact ⟨hNqOpen, hNZ, hNdvd, hty⟩

theorem kgfniRee_label_A_one_of_markPSL {a : ℕ} {lab : LargeEvenLabel}
    (ht : markTag lab = .PSL) (hr : markRank lab = 2) (hc : markChar lab = 2)
    (hd : markDeg lab = 2 * a + 1) : lab = ⟨.A, 1, 2 * a + 1⟩ := by
  obtain ⟨t, l, m⟩ := lab
  cases t <;> simp only [markTag, markRank, markChar, markDeg] at ht hr hc hd ⊢
  case A =>
    have hl : l = 1 := by omega
    subst hl
    rw [hd]
  case D =>
    split_ifs at ht hr <;> first | omega | exact absurd ht (by decide)
  case twD =>
    split_ifs at ht hr hd <;> first | omega | exact absurd ht (by decide)
  case B2der => omega
  all_goals exfalso; simpa [markTag] using ht

theorem kgfniRee_label_twB2_of_mark {lab : LargeEvenLabel}
    (h : markTag lab = .twistedB2) : lab.tag = .twB2 := by
  obtain ⟨t, l, m⟩ := lab
  cases t with
  | twB2 => rfl
  | D =>
    simp only [markTag] at h
    split_ifs at h <;> exact absurd h (by decide)
  | twD =>
    simp only [markTag] at h
    split_ifs at h <;> exact absurd h (by decide)
  | _ => simp [markTag] at h

theorem kgfniRee_innerDiagInn_A_one {a : ℕ} :
    GGInnerDiagInnLabel (⟨.A, 1, 2 * a + 1⟩ : LargeEvenLabel) := by
  have hpos : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have heven : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hodd : Odd (2 ^ (2 * a + 1) - 1) := Nat.Even.sub_odd hpos heven odd_one
  have hcop : (2 ^ (2 * a + 1) - 1).Coprime 2 := hodd.coprime_two_right
  simpa [GGInnerDiagInnLabel, GGInndiagInnLabel, GGLinearInnLabel] using hcop

theorem kgfniRee_innerDiagInn_twB2 {lab : LargeEvenLabel}
    (h : lab.tag = .twB2) : GGInnerDiagInnLabel lab := by
  obtain ⟨t, l, m⟩ := lab
  subst h
  simp [GGInnerDiagInnLabel, GGInndiagInnLabel]

theorem kgfniRee_specialMarking_sl2 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {J : Type} [Group J]
    (hperf : commutator J = ⊤)
    (e : Matrix.SpecialLinearGroup (Fin 2) K ≃* J) :
    ∃ P : LargeEvenMarkProp J, LargeEvenMarking J P ∧
      ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
        (θ : J ⧸ Subgroup.center J ≃* R), P lab R I F θ → I ⊆ LargeEvenInnSet R := by
  have hLM := CFSG.LocalAnalysis.GLTheoremA.K155X.l154_lieModel_psl_two ha hK e
  have hmark := largeEvenMarking_of_lieModel_centerQuot hperf hLM
  let S : LargeEvenLabel → Prop := fun lab =>
    markTag lab = .PSL ∧ markRank lab = 2 ∧ markChar lab = 2 ∧ markDeg lab = 2 * a + 1
  have hall : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
    intro lab hlab hS
    obtain ⟨ht, hr, hc, hd⟩ := hS
    have hlabel := kgfniRee_label_A_one_of_markPSL ht hr hc hd
    subst hlabel
    exact largeEvenLabelAll_subset_inn (lab := ⟨.A, 1, 2 * a + 1⟩) hlab
      (kgfniRee_innerDiagInn_A_one (a := a))
  have hmarkS : LargeEvenMarking J (fun lab _ _ _ _ _ => S lab) := by
    simpa only [S] using hmark
  have hboth := largeEvenMarking_and_labelAll_simple hall (fun _ _ _ _ _ _ h => h) hmarkS
  let P : LargeEvenMarkProp J := fun lab R _ I F θ => S lab ∧ I ⊆ LargeEvenInnSet R
  have hP : LargeEvenMarking J P := by
    simpa only [P] using hboth
  refine ⟨P, hP, ?_⟩
  intro lab R _ I F θ h
  exact h.2

theorem kgfniRee_specialMarking_sz {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {J : Type} [Group J]
    (hperf : commutator J = ⊤) (hZ : Subgroup.center J = ⊥)
    (e : CFSG.Blueprint.suzukiGroup a K ≃* J) :
    ∃ P : LargeEvenMarkProp J, LargeEvenMarking J P ∧
      ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
        (θ : J ⧸ Subgroup.center J ≃* R), P lab R I F θ → I ⊆ LargeEvenInnSet R := by
  have hLM := CFSG.LocalAnalysis.GLTheoremA.K155X.l154_lieModel_twistedB2 ha hK hZ e
  have hmark := largeEvenMarking_of_lieModel_centerQuot hperf hLM
  let S : LargeEvenLabel → Prop := fun lab =>
    markTag lab = .twistedB2 ∧ markRank lab = 0 ∧ markChar lab = 2 ∧ markDeg lab = 2 * a + 1
  have hall : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) := by
    intro lab hlab hS
    have hlabel := kgfniRee_label_twB2_of_mark hS.1
    exact largeEvenLabelAll_subset_inn hlab (kgfniRee_innerDiagInn_twB2 hlabel)
  have hmarkS : LargeEvenMarking J (fun lab _ _ _ _ _ => S lab) := by
    simpa only [S] using hmark
  have hboth := largeEvenMarking_and_labelAll_simple hall (fun _ _ _ _ _ _ h => h) hmarkS
  let P : LargeEvenMarkProp J := fun lab R _ I F θ => S lab ∧ I ⊆ LargeEvenInnSet R
  have hP : LargeEvenMarking J P := by
    simpa only [P] using hboth
  refine ⟨P, hP, ?_⟩
  intro lab R _ I F θ h
  exact h.2

theorem kgfniRee_component_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {s : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a} (hs : orderOf s = 3)
    {J : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s))) :
    J = Subgroup.centralizer ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) := by
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Subtype.finite
  have hCq : CFSG.IsQuasisimple ↥(Subgroup.centralizer
      ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) :=
    CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hK s hs
  have hCq' : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer
      ({s} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hCq
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj] at hJ
  have hnt : Nontrivial ↥J := by
    haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
    exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  have hperfJ : ⁅J, J⁆ = J := by
    have htop : (⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆) = ⊤ := by
      simpa [commutator_def] using hJ.2.2.1
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥J)) (H₂ := (⊤ : Subgroup ↥J))
      (f := J.subtype)
    rw [htop, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_eq_of_subnormal_quasisimple
    hJ.2.1 hCq' hperfJ ((Subgroup.nontrivial_iff_ne_bot J).mp hnt)

theorem kgfniRee_kgInducedAut_congr {X Y R : Type*} [Group X] [Group Y] [Group R]
    (e : X ≃* Y) (θ : X ⧸ Subgroup.center X ≃* R) (f : MulAut X) :
    kgInducedAut ((centerQuotCongr e).symm.trans θ) (e.symm.trans (f.trans e)) =
      kgInducedAut θ f := by
  ext x
  obtain ⟨q, rfl⟩ := θ.surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp [kgInducedAut, MulAut.congr_apply, centerQuotAut_mk, centerQuotCongr_mk,
    MulEquiv.trans_apply]
  rw [← centerQuotCongr_mk e (f y)]
  exact MulEquiv.symm_apply_apply (centerQuotCongr e) _

theorem kgfniRee_canonical_of_twA {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    (h : LargeEvenMarking X (fun lab R _ I F θ => P lab R I F θ ∧ lab.tag = .twA)) :
    CFSG.Assembly.LargeEvenMarking X P := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hP, htag⟩ := largeEvenRawDatum_exists hraw
  refine ⟨hX, lab, hlab, ?_⟩
  obtain ⟨t, r, m⟩ := lab
  subst htag
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum]
  simp only [and_true] at hraw
  exact hraw

end CFSG.StandardType
