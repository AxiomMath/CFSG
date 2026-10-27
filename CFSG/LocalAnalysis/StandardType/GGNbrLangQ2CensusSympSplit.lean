module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCenter
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSL StatedSp)
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks

private theorem q2cSpS_two_le_of_isSimpleGroup_centerQuot_statedSL {m : ℕ} {E : Type} [Field E]
    [Finite E]
    (hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E))) : 2 ≤ m := by
  by_contra h
  have hm1 : m ≤ 1 := by omega
  have hsub : Subsingleton (StatedSL m E) :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one hm1
  have hntq : Nontrivial (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) := hsimp.toNontrivial
  have hsubq : Subsingleton (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq]
        have h1 : a⁻¹ * b = 1 := hsub.elim _ _
        rw [h1]
        exact (Subgroup.center (StatedSL m E)).one_mem
  obtain ⟨a, b, hab⟩ := hntq
  exact hab (hsubq.elim a b)

private theorem q2cSpS_two_le_of_card_two_statedSL {f : ℕ} {E : Type} [Field E] [Finite E]
    (hf : 1 ≤ f) (hcard : Nat.card E = 2 ^ f)
    (hperf : commutator (StatedSL 2 E) = ⊤)
    (hsimp : IsSimpleGroup (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E))) : 2 ≤ f := by
  by_contra hf2
  have hf1 : f = 1 := by omega
  have hcard2 : Nat.card E = 2 := by rw [hcard, hf1, pow_one]
  have hcardSL : Nat.card (StatedSL 2 E) = 6 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two, hcard2]
    norm_num
  have hsolv : Group.IsSolvable (StatedSL 2 E) := by
    have hcard6 : @Fintype.card (StatedSL 2 E) (Fintype.ofFinite _) = 2 ^ 1 * 3 ^ 1 := by
      rw [← @Nat.card_eq_fintype_card (StatedSL 2 E) (Fintype.ofFinite _), hcardSL]
      norm_num
    exact @CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (StatedSL 2 E) _ (Fintype.ofFinite _) 2 3 1 1 Nat.prime_two Nat.prime_three
      (by norm_num) hcard6
  have hntq : Nontrivial (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E)) := hsimp.toNontrivial
  have hnt : Nontrivial (StatedSL 2 E) :=
    @Function.Surjective.nontrivial (StatedSL 2 E)
      (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E)) hntq (QuotientGroup.mk)
      (QuotientGroup.mk_surjective (s := Subgroup.center (StatedSL 2 E)))
  have hperf' : Group.IsPerfect (StatedSL 2 E) := Group.isPerfect_def.mpr hperf
  exact @Group.IsPerfect.not_isSolvable (StatedSL 2 E) _ hnt hperf' hsolv

private theorem q2cSpS_largeEvenInLambda2_linearLabel {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f)
    (hmf : m = 2 → 2 ≤ f) : LargeEvenInLambda2 (⟨.A, m - 1, f⟩ : LargeEvenLabel) := by
  refine ⟨hf, by show 1 ≤ m - 1; omega, ?_⟩
  intro h
  have h' : m - 1 = 1 := by simpa using h
  exact hmf (by omega)

private theorem q2cSpS_labelIso_A_A {r n r' n' : ℕ}
    (h : GGLabelIso (⟨.A, r, n⟩ : LargeEvenLabel) ⟨.A, r', n'⟩) : r = r' ∧ n = n' := by
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨congrArg LargeEvenLabel.rank h, congrArg LargeEvenLabel.n h⟩
  · rcases h.2.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.2)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)

private theorem q2cSpS_solvable_projectiveSL_two_small
    (K : Type) [Field K] [Finite K] (hcard : Nat.card K = 2 ∨ Nat.card K = 3) :
    Group.IsSolvable (LinearFlag.projectiveSL 2 K) := by
  haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
  haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  exact Group.isSolvable_of_surjective (LinearFlag.proj_surjective 2 K)

private theorem q2cSpS_not_iso_B_A {r n d k : ℕ} :
    ¬ GGLabelIso (⟨.B, r, n⟩ : LargeEvenLabel) ⟨.A, d, k⟩ := by
  rintro (h | h | h | h | h | h | h | h)
  · exact (by cases h)
  · rcases h.2.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)

private theorem q2cSpS_not_iso_B2der_A {d k : ℕ} :
    ¬ GGLabelIso (⟨.B2der, 0, 1⟩ : LargeEvenLabel) ⟨.A, d, k⟩ := by
  rintro (h | h | h | h | h | h | h | h)
  · exact (by cases h)
  · rcases h.2.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)

theorem q2cSpS_fixed_block {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ n₁ d m : ℕ} [NeZero ℓ]
    {s : ↥(CFSG.Open.StatedSp ℓ F)} (hs1 : s ≠ 1)
    {ε : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F}
    (h1 : ((s : GL (Fin ℓ ⊕ Fin ℓ) F) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) * ε = ε)
    (hn₁ : 2 * n₁ = Module.finrank F (LinearMap.range (Matrix.toLin' ε)))
    {C Blk : Subgroup ↥(CFSG.Open.StatedSp ℓ F)}
    (hCε : CFSG.Open.IsComponentOf C Blk)
    (eS : ↥Blk ≃* ↥(CFSG.Open.StatedSp n₁ F))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (hne : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :
    2 ≤ d ∧ d ≤ ℓ ∧ Nat.card K = Nat.card F := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hC0 : CFSG.Assembly.IsComponentOf C Blk :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr hCε
  obtain ⟨θ⟩ := hne
  haveI hsimpC : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC0.2.2.2
  haveI : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC0.2.2.1
  have eP : ↥C ⧸ Subgroup.center ↥C ≃* LinearFlag.projectiveSL d K :=
    θ.trans (TypeA.recipeEquiv d K)
  haveI hsimpP : IsSimpleGroup (LinearFlag.projectiveSL d K) := eP.isSimpleGroup_congr.mp hsimpC
  haveI hperfP : Group.IsPerfect (LinearFlag.projectiveSL d K) :=
    Group.IsPerfect.ofSurjective (f := eP.toMonoidHom) eP.surjective
  have hd : 2 ≤ d := by
    by_contra h
    have hd1 : d ≤ 1 := by omega
    haveI : Subsingleton (LinearFlag.projectiveSL d K) :=
      CFSG.AGLEmbedding.ToralCensus.subsingleton_projectiveSL hd1 K
    haveI : Subsingleton (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      (TypeA.recipeEquiv d K).toEquiv.subsingleton
    exact not_subsingleton _ θ.toEquiv.subsingleton
  have hm1 : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have hd1 : 1 ≤ d := by omega
  have hmfK : d = 2 → 2 ≤ m := by
    rintro rfl
    by_contra hm2
    have hm1' : m = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hK, hm1', pow_one]
    haveI hsolv : Group.IsSolvable (LinearFlag.projectiveSL 2 K) :=
      q2cSpS_solvable_projectiveSL_two_small K (Or.inl hK2)
    exact (Group.IsPerfect.not_isSolvable (LinearFlag.projectiveSL 2 K)) hsolv
  have hA_lambda : LargeEvenInLambda2 (⟨.A, d - 1, m⟩ : LargeEvenLabel) :=
    q2cSpS_largeEvenInLambda2_linearLabel hd hm1 hmfK
  have hθC : GGHasLabel (⟨.A, d - 1, m⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := by
    unfold GGHasLabel
    rw [show LargeEvenRawDatum (⟨.A, d - 1, m⟩ : LargeEvenLabel) _ =
        LargeEvenRecipeLinear ((d - 1) + 1) (2 ^ m) _ from rfl]
    rw [Nat.sub_add_cancel hd1]
    exact ⟨K, inferInstance, inferInstance, hK, ⟨θ⟩⟩
  let Cb : Subgroup ↥Blk := C.subgroupOf Blk
  have hCb : CFSG.Assembly.IsComponentOf Cb (⊤ : Subgroup ↥Blk) := by
    refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Blk.subtype) (Subgroup.subtype_injective _)).mp ?_
    have hmapCb : Subgroup.map Blk.subtype Cb = C := Subgroup.map_subgroupOf_eq_of_le hCε.1
    simpa only [hmapCb, Subgroup.map_top, Subgroup.range_subtype] using hC0
  have hCbmap_component : CFSG.Assembly.IsComponentOf (Cb.map eS.toMonoidHom)
      (⊤ : Subgroup ↥(StatedSp n₁ F)) := by
    have htop : (⊤ : Subgroup ↥Blk).map eS.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]; exact eS.surjective
    rw [← htop]
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := eS.toMonoidHom) eS.injective).2 hCb
  have hcompGL : CFSG.Assembly.IsComponentOf
      ((Cb.map eS.toMonoidHom).map (StatedSp n₁ F).subtype) (StatedSp n₁ F) := by
    have := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := (StatedSp n₁ F).subtype) (Subgroup.subtype_injective _)).2 hCbmap_component
    simpa only [Subgroup.map_top, Subgroup.range_subtype] using this
  by_cases h0 : n₁ = 0
  · exact (not_isComponentOf_statedSp_of_small (K := F) (Or.inl h0) _ hcompGL).elim
  by_cases h1s : n₁ = 1 ∧ Nat.card F = 2
  · exact (not_isComponentOf_statedSp_of_small (K := F) (Or.inr h1s) _ hcompGL).elim
  by_cases h42 : n₁ = 2 ∧ Nat.card F = 2
  ·
    obtain ⟨h42n, h42K⟩ := h42
    subst h42n
    have hspbot : Subgroup.center ↥(StatedSp 2 F) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (F := F) (by norm_num)
    let A6 : Subgroup (GL (Fin 2 ⊕ Fin 2) F) :=
      ⁅(LargeEvenSpGroup F 2 : Subgroup (GL (Fin 2 ⊕ Fin 2) F)),
        (LargeEvenSpGroup F 2 : Subgroup (GL (Fin 2 ⊕ Fin 2) F))⁆
    have hscal : (LargeEvenScalars (Fin 2 ⊕ Fin 2) F).subgroupOf A6 = ⊥ := by
      have hcenter : (LargeEvenScalars (Fin 2 ⊕ Fin 2) F).subgroupOf
          (LargeEvenSpGroup F 2) = Subgroup.center ↥(LargeEvenSpGroup F 2) := by
        rw [largeEvenSpGroup_eq_statedSp]
        rw [show StatedSp 2 F = TauCeti.GLSymplectic (Fin 2) F from
          CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := F)]
        exact (CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq (n := 2) (K := F)).symm
      have hbot : Subgroup.center ↥(LargeEvenSpGroup F 2) = ⊥ := hspbot
      have hA6le : A6 ≤ (LargeEvenSpGroup F 2 : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) := by
        refine Subgroup.commutator_le.mpr (fun g hg h hh => ?_)
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
          (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hmem : (⟨(x : GL (Fin 2 ⊕ Fin 2) F), hA6le x.2⟩ : ↥(LargeEvenSpGroup F 2)) ∈
          (LargeEvenScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (LargeEvenSpGroup F 2) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hcenter, hbot, Subgroup.mem_bot] at hmem
      have h1 : (x : GL (Fin 2 ⊕ Fin 2) F) = 1 :=
        congrArg (Subtype.val : ↥(LargeEvenSpGroup F 2) → GL (Fin 2 ⊕ Fin 2) F) hmem
      exact Subtype.ext h1
    have hH : ↥A6 ≃* alternatingGroup (Fin 6) :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hscal).symm.trans
          (nonempty_b2der_equiv_alternatingGroup (K := F) h42K).some)
    have hcbH : ↥Cb ≃* ↥A6 := by
      have hqA6 : CFSG.Assembly.IsQuasisimple
          ↥⁅(⊤ : Subgroup ↥(StatedSp 2 F)), (⊤ : Subgroup ↥(StatedSp 2 F))⁆ :=
        (isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two h42K
          (T := (⊤ : Subgroup ↥(StatedSp 2 F)))
          (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(StatedSp 2 F)) ≃* ↥(StatedSp 2 F))).1
      have hQperf : ⁅Cb.map eS.toMonoidHom, Cb.map eS.toMonoidHom⁆ = Cb.map eS.toMonoidHom := by
        have h2 := congrArg (Subgroup.map (Cb.map eS.toMonoidHom).subtype)
          hCbmap_component.2.2.1
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          Subgroup.range_subtype] at h2
        exact h2
      have hQle : Cb.map eS.toMonoidHom ≤
          ⁅(⊤ : Subgroup ↥(StatedSp 2 F)), (⊤ : Subgroup ↥(StatedSp 2 F))⁆ :=
        calc Cb.map eS.toMonoidHom = ⁅Cb.map eS.toMonoidHom, Cb.map eS.toMonoidHom⁆ := hQperf.symm
          _ ≤ ⁅(⊤ : Subgroup ↥(StatedSp 2 F)), (⊤ : Subgroup ↥(StatedSp 2 F))⁆ :=
            Subgroup.commutator_mono le_top le_top
      have heq : Cb.map eS.toMonoidHom =
          ⁅(⊤ : Subgroup ↥(StatedSp 2 F)), (⊤ : Subgroup ↥(StatedSp 2 F))⁆ :=
        GGHalf.eq_of_isComponentOf_isQuasisimple hqA6
          (CFSG.Assembly.IsComponentOf.of_le_of_le hCbmap_component hQle le_top)
      have hmap : (Cb.map eS.toMonoidHom).map (StatedSp 2 F).subtype = A6 := by
        rw [heq, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact (Subgroup.equivMapOfInjective Cb eS.toMonoidHom eS.injective).trans
        ((Subgroup.equivMapOfInjective (Cb.map eS.toMonoidHom) (StatedSp 2 F).subtype
          (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hmap))
    have hZ : Subgroup.center ↥A6 = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hz' : hH z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨w', hw'⟩ := hH.surjective w
        rw [← hw', ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w']
      rw [alternatingGroup.center_eq_bot (α := Fin 6) (by simp), Subgroup.mem_bot] at hz'
      exact hH.injective (by rw [hz', map_one])
    have hXiso : ↥C ⧸ Subgroup.center ↥C ≃* alternatingGroup (Fin 6) :=
      ((QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥Cb)
        (Subgroup.subgroupOfEquivOfLe hCε.1).symm
        (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hCε.1).symm)).trans
        (QuotientGroup.congr (Subgroup.center ↥Cb)
          (Subgroup.center ↥A6) hcbH
          (Subgroup.map_center_eq hcbH))).trans
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientBot.trans hH))
    have hB2 : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
        (↥C ⧸ Subgroup.center ↥C) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der hXiso
    have hB2_lambda : LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) :=
      ⟨le_rfl, rfl, rfl⟩
    have hIso := ggLabelRigidInput_holds (⟨.B2der, 0, 1⟩) (⟨.A, d - 1, m⟩)
      (↥C ⧸ Subgroup.center ↥C) hB2_lambda hA_lambda hB2 hθC
    exact (q2cSpS_not_iso_B2der_A hIso).elim
  ·
    have hn1 : 1 ≤ n₁ := by omega
    have hq : CFSG.Assembly.IsQuasisimple ↥(StatedSp n₁ F) :=
      isQuasisimple_statedSp_of_not_small hn1 (by omega) (by omega)
    have hqtop : CFSG.Assembly.IsQuasisimple (↥(⊤ : Subgroup ↥(StatedSp n₁ F))) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq
    have hCbmap : Cb.map eS.toMonoidHom = ⊤ :=
      GGHalf.eq_of_isComponentOf_isQuasisimple hqtop hCbmap_component
    have hCiso : ↥C ≃* ↥(StatedSp n₁ F) :=
      (Subgroup.subgroupOfEquivOfLe hCε.1).symm.trans
        ((Subgroup.equivMapOfInjective Cb eS.toMonoidHom eS.injective).trans
          ((MulEquiv.subgroupCongr hCbmap).trans Subgroup.topEquiv))
    by_cases hn1' : n₁ = 1
    ·
      subst hn1'
      have hFne2 : Nat.card F ≠ 2 := by
        intro h
        exact h1s ⟨rfl, h⟩
      obtain ⟨f, -, hFcard'⟩ := FiniteField.card F 2
      have hFcard : Nat.card F = 2 ^ (f : ℕ) := by
        rw [Nat.card_eq_fintype_card, hFcard']
      have hf1 : 1 ≤ (f : ℕ) := f.pos
      have hf2 : 2 ≤ (f : ℕ) := by
        by_contra hlt
        have hf1' : (f : ℕ) = 1 := by omega
        rw [hf1', pow_one] at hFcard
        exact hFne2 hFcard
      have eC' : ↥C ≃* StatedSL 2 F :=
        (hCiso.trans
          (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F).symm).trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
      let θ1 : ↥C ⧸ Subgroup.center ↥C ≃*
          LargeEvenProj (LargeEvenSLGroup (Fin 2) F) :=
        (centerQuotCongr eC').trans (statedSLQuotEquivLargeEvenProj (m := 2) (E := F))
      have hA1 : GGHasLabel (⟨.A, 1, (f : ℕ)⟩ : LargeEvenLabel)
          (↥C ⧸ Subgroup.center ↥C) := by
        unfold GGHasLabel
        rw [show LargeEvenRawDatum (⟨.A, 1, (f : ℕ)⟩ : LargeEvenLabel) _ =
            LargeEvenRecipeLinear 2 (2 ^ (f : ℕ)) _ from rfl]
        exact ⟨F, inferInstance, inferInstance, hFcard, ⟨θ1⟩⟩
      have hA1_lambda : LargeEvenInLambda2 (⟨.A, 1, (f : ℕ)⟩ : LargeEvenLabel) :=
        ⟨hf1, le_rfl, fun _ => hf2⟩
      have hIso := ggLabelRigidInput_holds (⟨.A, 1, (f : ℕ)⟩) (⟨.A, d - 1, m⟩)
        (↥C ⧸ Subgroup.center ↥C) hA1_lambda hA_lambda hA1 hθC
      obtain ⟨hr, hn⟩ := q2cSpS_labelIso_A_A hIso
      have hε1 : ε ≠ 1 := by
        intro hε
        apply hs1
        apply Subtype.ext
        apply Units.ext
        have hh := h1
        rw [hε, mul_one] at hh
        exact hh
      have hrange_ne : LinearMap.range (Matrix.toLin' ε) ≠ ⊤ := by
        intro htop
        have hsurj : Function.Surjective (Matrix.toLin' ε) := LinearMap.range_eq_top.mp htop
        have hsmat : ((s : GL (Fin ℓ ⊕ Fin ℓ) F) :
            Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) = 1 := by
          apply Matrix.toLin'.injective
          rw [Matrix.toLin'_one]
          apply LinearMap.ext
          intro v
          obtain ⟨w, hw⟩ := hsurj v
          rw [← hw]
          calc Matrix.toLin' ((s : GL (Fin ℓ ⊕ Fin ℓ) F) :
                  Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) (Matrix.toLin' ε w)
              = Matrix.toLin' (((s : GL (Fin ℓ ⊕ Fin ℓ) F) :
                  Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) * ε) w := by
                rw [Matrix.toLin'_mul]; rfl
            _ = Matrix.toLin' ε w := by rw [h1]
        exact hs1 (Subtype.ext (Units.ext hsmat))
      have hfinlt : Module.finrank F (LinearMap.range (Matrix.toLin' ε)) <
          Module.finrank F ((Fin ℓ ⊕ Fin ℓ) → F) := by
        have h := Submodule.finrank_lt_finrank_of_lt
          (s := LinearMap.range (Matrix.toLin' ε)) (t := ⊤)
          (lt_top_iff_ne_top.mpr hrange_ne)
        simpa using h
      have hdim : Module.finrank F ((Fin ℓ ⊕ Fin ℓ) → F) = 2 * ℓ := by
        rw [Module.finrank_fintype_fun_eq_card F, Fintype.card_sum, Fintype.card_fin]
        omega
      have hℓ2 : 2 ≤ ℓ := by
        have h2 : Module.finrank F (LinearMap.range (Matrix.toLin' ε)) = 2 :=
          hn₁.symm.trans (by norm_num)
        rw [h2, hdim] at hfinlt
        omega
      refine ⟨by omega, by omega, ?_⟩
      calc Nat.card K = 2 ^ m := hK
        _ = 2 ^ (f : ℕ) := by rw [← hn]
        _ = Nat.card F := hFcard.symm
    ·
      have hn2 : 2 ≤ n₁ := by omega
      obtain ⟨eX⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
        (s := n₁) hn2 (by
        rintro ⟨h, h2⟩
        exact h42 ⟨h, h2⟩) (inferInstance : CharP F 2) hCiso
      obtain ⟨f, -, hFcard'⟩ := FiniteField.card F 2
      have hFcard : Nat.card F = 2 ^ (f : ℕ) := by
        rw [Nat.card_eq_fintype_card, hFcard']
      have hf1 : 1 ≤ (f : ℕ) := f.pos
      have hnf : n₁ = 2 → 2 ≤ (f : ℕ) := by
        intro hn₂
        by_contra hlt
        have hf1' : (f : ℕ) = 1 := by omega
        rw [hf1', pow_one] at hFcard
        exact h42 ⟨hn₂, hFcard⟩
      have hB : GGHasLabel (⟨.B, n₁, (f : ℕ)⟩ : LargeEvenLabel)
          (↥C ⧸ Subgroup.center ↥C) :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_typeB hFcard eX
      have hB_lambda : LargeEvenInLambda2 (⟨.B, n₁, (f : ℕ)⟩ : LargeEvenLabel) :=
        ⟨hf1, hn2, hnf⟩
      have hIso := ggLabelRigidInput_holds (⟨.B, n₁, (f : ℕ)⟩) (⟨.A, d - 1, m⟩)
        (↥C ⧸ Subgroup.center ↥C) hB_lambda hA_lambda hB hθC
      exact (q2cSpS_not_iso_B_A hIso).elim

theorem q2cSpS_pair_block {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ m₀ d m : ℕ} [NeZero ℓ]
    {E : Type} [Field E] [Finite E]
    (hm₀ℓ : m₀ ≤ ℓ) (hEcardF : Nat.card E = Nat.card F)
    {C Blk : Subgroup ↥(CFSG.Open.StatedSp ℓ F)}
    (hCε : CFSG.Open.IsComponentOf C Blk)
    (eL : ↥Blk ≃* GL (Fin m₀) E)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (hne : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :
    2 ≤ d ∧ d ≤ ℓ ∧ Nat.card K = Nat.card F := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype F := Fintype.ofFinite F
  have hC0 : CFSG.Assembly.IsComponentOf C Blk :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr hCε
  let eC : ↥C ≃* StatedSL m₀ E := componentEquivStatedSLOfMulEquiv eL hC0
  let θC : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin m₀) E) :=
    (centerQuotCongr eC).trans (statedSLQuotEquivLargeEvenProj (m := m₀) (E := E))
  obtain ⟨θ⟩ := hne
  haveI hsimpC : IsSimpleGroup (↥C ⧸ Subgroup.center ↥C) := hC0.2.2.2
  have hsimpSL : IsSimpleGroup (StatedSL m₀ E ⧸ Subgroup.center (StatedSL m₀ E)) :=
    (centerQuotCongr eC).isSimpleGroup_congr.mp hsimpC
  haveI : Group.IsPerfect ↥C := Group.isPerfect_def.mpr hC0.2.2.1
  have hperfSL : commutator (StatedSL m₀ E) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := eC.toMonoidHom) eC.surjective).commutator_eq_top
  have hm₀ : 2 ≤ m₀ := q2cSpS_two_le_of_isSimpleGroup_centerQuot_statedSL hsimpSL
  have eP : ↥C ⧸ Subgroup.center ↥C ≃* LinearFlag.projectiveSL d K :=
    θ.trans (TypeA.recipeEquiv d K)
  haveI hsimpP : IsSimpleGroup (LinearFlag.projectiveSL d K) := eP.isSimpleGroup_congr.mp hsimpC
  haveI hperfP : Group.IsPerfect (LinearFlag.projectiveSL d K) :=
    Group.IsPerfect.ofSurjective (f := eP.toMonoidHom) eP.surjective
  have hd : 2 ≤ d := by
    by_contra h
    have hd1 : d ≤ 1 := by omega
    haveI : Subsingleton (LinearFlag.projectiveSL d K) :=
      CFSG.AGLEmbedding.ToralCensus.subsingleton_projectiveSL hd1 K
    haveI : Subsingleton (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      (TypeA.recipeEquiv d K).toEquiv.subsingleton
    exact not_subsingleton _ θ.toEquiv.subsingleton
  have hm1 : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨f, -, hFcard'⟩ := FiniteField.card F 2
  have hFcard : Nat.card F = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hFcard']
  have hEcard : Nat.card E = 2 ^ (f : ℕ) := hEcardF.trans hFcard
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hm₀f : m₀ = 2 → 2 ≤ (f : ℕ) := by
    rintro rfl
    exact q2cSpS_two_le_of_card_two_statedSL hf1 hEcard hperfSL hsimpSL
  have hΛE : LargeEvenInLambda2 (⟨.A, m₀ - 1, (f : ℕ)⟩ : LargeEvenLabel) :=
    q2cSpS_largeEvenInLambda2_linearLabel hm₀ hf1 hm₀f
  have hm₀1 : 1 ≤ m₀ := by omega
  have hA_E : GGHasLabel (⟨.A, m₀ - 1, (f : ℕ)⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := by
    unfold GGHasLabel
    rw [show LargeEvenRawDatum (⟨.A, m₀ - 1, (f : ℕ)⟩ : LargeEvenLabel) _ =
        LargeEvenRecipeLinear ((m₀ - 1) + 1) (2 ^ (f : ℕ)) _ from rfl]
    rw [Nat.sub_add_cancel hm₀1]
    exact ⟨E, inferInstance, inferInstance, hEcard, ⟨θC⟩⟩
  have hd1 : 1 ≤ d := by omega
  have hA_K : GGHasLabel (⟨.A, d - 1, m⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := by
    unfold GGHasLabel
    rw [show LargeEvenRawDatum (⟨.A, d - 1, m⟩ : LargeEvenLabel) _ =
        LargeEvenRecipeLinear ((d - 1) + 1) (2 ^ m) _ from rfl]
    rw [Nat.sub_add_cancel hd1]
    exact ⟨K, inferInstance, inferInstance, hK, ⟨θ⟩⟩
  have hmfK : d = 2 → 2 ≤ m := by
    rintro rfl
    by_contra hm2
    have hm1' : m = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hK, hm1', pow_one]
    haveI hsolv : Group.IsSolvable (LinearFlag.projectiveSL 2 K) :=
      q2cSpS_solvable_projectiveSL_two_small K (Or.inl hK2)
    exact (Group.IsPerfect.not_isSolvable (LinearFlag.projectiveSL 2 K)) hsolv
  have hΛK : LargeEvenInLambda2 (⟨.A, d - 1, m⟩ : LargeEvenLabel) :=
    q2cSpS_largeEvenInLambda2_linearLabel hd hm1 hmfK
  have hIso : GGLabelIso (⟨.A, d - 1, m⟩ : LargeEvenLabel)
      (⟨.A, m₀ - 1, (f : ℕ)⟩ : LargeEvenLabel) :=
    ggLabelRigidInput_holds (⟨.A, d - 1, m⟩) (⟨.A, m₀ - 1, (f : ℕ)⟩)
      (↥C ⧸ Subgroup.center ↥C) hΛK hΛE hA_K hA_E
  obtain ⟨hdmeq, hmfeq⟩ := q2cSpS_labelIso_A_A hIso
  refine ⟨hd, by omega, ?_⟩
  calc Nat.card K = 2 ^ m := hK
    _ = 2 ^ (f : ℕ) := by rw [hmfeq]
    _ = Nat.card E := hEcard.symm
    _ = Nat.card F := hEcardF

theorem q2cSp_statedSp_split_component_psl {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ p d m : ℕ} [NeZero ℓ] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {s : ↥(CFSG.Open.StatedSp ℓ F)} (hs : s ^ p = 1) (hs1 : s ≠ 1)
    {C : Subgroup ↥(CFSG.Open.StatedSp ℓ F)}
    (hC : CFSG.Open.IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSp ℓ F))))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (hne : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :
    2 ≤ d ∧ d ≤ ℓ ∧ Nat.card K = Nat.card F := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hord : orderOf s = p := by
    have hdvd : orderOf s ∣ p := orderOf_dvd_of_pow_eq_one hs
    rcases hp.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs1
    · exact h
  have hodd : Odd (orderOf (s : GL (Fin ℓ ⊕ Fin ℓ) F)) := by
    rw [Subgroup.orderOf_coe, hord]
    exact hp.odd_of_ne_two hp2
  obtain ⟨P, hPprim, hPorth, hPsum, hPcomm, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Sp (s : GL (Fin ℓ ⊕ Fin ℓ) F) s.2 hodd
  have hcent : Subgroup.centralizer ({s} : Set ↥(CFSG.Open.StatedSp ℓ F)) =
      (Subgroup.centralizer ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} :
        Set (GL (Fin ℓ ⊕ Fin ℓ) F))).comap (CFSG.Open.StatedSp ℓ F).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  have hCa : CFSG.Assembly.IsComponentOf C
      ((Subgroup.centralizer ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} :
        Set (GL (Fin ℓ ⊕ Fin ℓ) F))).comap (CFSG.Open.StatedSp ℓ F).subtype) := by
    rw [← hcent]
    exact (CFSG.Assembly.isComponentOf_iff_open).mpr hC
  rw [← hPsup] at hCa
  obtain ⟨ε, hεP, hCεa⟩ := exists_isComponentOf_block P
    (fun ε => glBlockCentralizer (CFSG.Open.StatedSp ℓ F).subtype
      ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)) ε)
    (fun i hi j hj hij x hx y hy => hPcomm i hi j hj hij x hx y hy) hCa
  have hCε : CFSG.Open.IsComponentOf C
      (glBlockCentralizer (CFSG.Open.StatedSp ℓ F).subtype
        ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)) ε) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hCεa
  have hneg1 : (-1 : Matrix (Fin ℓ) (Fin ℓ) F) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, CharTwo.neg_eq]
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F).det := by
    rw [show Matrix.fromBlocks 0 1 (-1) 0 =
        Matrix.J (Fin ℓ) F by
      rw [Matrix.J, Matrix.fromBlocks_inj]
      exact ⟨rfl, hneg1.symm, hneg1, rfl⟩]
    exact Matrix.isUnit_det_J (Fin ℓ) F
  have hGt : Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.transpose_neg (1 : Matrix (Fin ℓ) (Fin ℓ) F), Matrix.transpose_one,
      Matrix.fromBlocks_inj]
    exact ⟨rfl, hneg1, hneg1.symm, rfl⟩
  have hS : ∀ x ∈ ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)),
      ∀ y ∈ ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)), Commute x y := by
    intro x hx y hy
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  have hSU : ∀ x ∈ ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)),
      Matrix.transpose (x : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) *
        (x : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) =
        Matrix.fromBlocks 0 1 (-1) 0 := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using CFSG.Open.StatedAPI.mem_statedSp_iff.mp s.2
  have hSUmap : ∀ x ∈ ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)),
      Matrix.transpose ((x : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F).map
        (RingHom.id F)) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) *
        (x : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) =
        Matrix.fromBlocks 0 1 (-1) 0 := by
    intro x hx
    simpa using hSU x hx
  obtain ⟨e, he, heε, -⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id F)
    (fun _ => rfl) (G := (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F)) hG (by simpa [Matrix.map_id] using hGt)
    hS hSUmap (hPprim ε hεP)
  have hpF' : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  have hbp : (s : GL (Fin ℓ ⊕ Fin ℓ) F) ^ p = 1 := by
    have := congrArg (fun x : ↥(CFSG.Open.StatedSp ℓ F) =>
      (x : GL (Fin ℓ ⊕ Fin ℓ) F)) hs
    simpa using this
  have hpow : ∀ x ∈ ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)),
      ∃ c : F, (x : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) ^ p =
        Matrix.scalar (Fin ℓ ⊕ Fin ℓ) (c ^ p) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨1, ?_⟩
    simpa using congrArg (fun u : GL (Fin ℓ ⊕ Fin ℓ) F =>
      (u : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F)) hbp
  have hoddS : ∀ x ∈ ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)),
      Odd (orderOf x) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hodd
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU (hPprim ε hεP) he heε with
    heq | ⟨-, e', he', hne', hεe⟩
  ·
    have heprim : IsPrimIdemIn (Algebra.adjoin F
        (Units.val '' ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)))) ε :=
      heq ▸ he
    by_cases h1 : ((s : GL (Fin ℓ ⊕ Fin ℓ) F) :
        Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) * ε = ε
    ·
      obtain ⟨n₁, hn₁, ⟨eS⟩⟩ := blockGroup_iso_Sp_one (s : GL (Fin ℓ ⊕ Fin ℓ) F) s.2 hodd
        (hPprim ε hεP) h1
      exact q2cSpS_fixed_block hs1 h1 hn₁ hCε eS hK hne
    ·
      obtain ⟨d₀, m₀, E, hEfield, hEfin, hd₀1, hEcard, hdim, hblockdeg, ⟨eU⟩⟩ :=
        blockGroup_iso_Sp_unitary (s : GL (Fin ℓ ⊕ Fin ℓ) F) s.2 hodd (hPprim ε hεP) heprim h1
      have hdeg1 : blockDegree (Algebra.adjoin F
          (Units.val '' ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)))) ε = 1 :=
        CFSG.StandardType.TableCRes.blockDegree_eq_one_of_pow_eq_pow hp hpF' hS hoddS hpow
          heprim
      omega
  ·
    obtain ⟨d₀, m₀, E, hEfield, hEfin, hd₀1, hEcard, hdim, hblockdeg, ⟨eL⟩⟩ :=
      blockGroup_iso_Sp_linear (s : GL (Fin ℓ ⊕ Fin ℓ) F) s.2 hodd (hPprim ε hεP) he he' hne'
        hεe
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    have hdeg1 : blockDegree (Algebra.adjoin F
        (Units.val '' ({(s : GL (Fin ℓ ⊕ Fin ℓ) F)} : Set (GL (Fin ℓ ⊕ Fin ℓ) F)))) e = 1 :=
      CFSG.StandardType.TableCRes.blockDegree_eq_one_of_pow_eq_pow hp hpF' hS hoddS hpow he
    have hd₀_eq : d₀ = 1 := by rw [← hblockdeg, hdeg1]
    have hEcardF : Nat.card E = Nat.card F := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hEcard, hd₀_eq, pow_one]
    have hfin_le : Module.finrank F (LinearMap.range (Matrix.toLin' ε)) ≤ 2 * ℓ := by
      have h1 := LinearMap.finrank_range_le (Matrix.toLin' ε)
      rw [Module.finrank_fintype_fun_eq_card F] at h1
      simp only [Fintype.card_sum, Fintype.card_fin] at h1
      omega
    have hm₀ℓ : m₀ ≤ ℓ := by
      have h2 : 2 * m₀ = Module.finrank F (LinearMap.range (Matrix.toLin' ε)) := by
        rw [← hdim, hd₀_eq, mul_one]
      omega
    exact q2cSpS_pair_block hm₀ℓ hEcardF hCε eL hK hne

end CFSG.StandardType
