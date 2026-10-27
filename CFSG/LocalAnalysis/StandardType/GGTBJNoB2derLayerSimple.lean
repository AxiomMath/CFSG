module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSpIso
import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpLie
import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestr
import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestrStd
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpOne
import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Symplectic.SmallF2Module
import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def l48gS_eiso {K : Type} [Field K] [Finite K] [CharP K 2] :
    LargeEvenProj (LargeEvenSpGroup K 4) ≃*
      ↥(TauCeti.BilinForm.isometryGroup (SmallRule.spBilin K 4)) :=
  ggB2der_spIso.trans (ggB2der_bridge (SmallRule.spBilin K 4))

private lemma l48gS_eiso_coe {K : Type} [Field K] [Finite K] [CharP K 2]
    (r : LargeEvenProj (LargeEvenSpGroup K 4)) :
    ((l48gS_eiso r : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
      Module.End K (Fin 4 ⊕ Fin 4 → K)) =
      (SmallRule.spRep r : Module.End K (Fin 4 ⊕ Fin 4 → K)) := by
  change ((ggB2der_bridge (SmallRule.spBilin K 4) (ggB2der_spIso r) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
      Module.End K (Fin 4 ⊕ Fin 4 → K)) = _
  rw [ggB2der_bridge_coe]
  exact ggB2der_spIso_coe r

private lemma l48gS_mem_iff {K : Type} [Field K] [Finite K] [CharP K 2]
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (s : LargeEvenProj (LargeEvenSpGroup K 4)) :
    s ∈ ggSpFixPerp W ↔
      (l48gS_eiso s : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
        A6Red.ggA6SpFixer (SmallRule.spBilin K 4)
          ((SmallRule.spBilin K 4).orthogonal W) := by
  constructor
  · intro hs
    refine ⟨(l48gS_eiso s).2, ?_⟩
    intro u hu
    exact (congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) => f u)
      (l48gS_eiso_coe s)).trans (hs u hu)
  · intro hs
    intro u hu
    exact (congrArg (fun f : Module.End K (Fin 4 ⊕ Fin 4 → K) => f u)
      (l48gS_eiso_coe s)).symm.trans (hs.2 u hu)

theorem ggB2der_spFixPerp_simple {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {W : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hW : Module.finrank K W = 6)
    (hcompl : IsCompl W ((SmallRule.spBilin K 4).orthogonal W)) :
    IsSimpleGroup ↥(ggSpFixPerp W) ∧ ⁅ggSpFixPerp W, ggSpFixPerp W⁆ = ggSpFixPerp W ∧
      7 ∣ Nat.card ↥(ggSpFixPerp W) := by
  have hB_alt : (SmallRule.spBilin K 4).IsAlt :=
    CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := 4) (K := K)
  have hB_nd : (SmallRule.spBilin K 4).Nondegenerate := SmallRule.spBilin_nondegenerate
  set P : Submodule K (Fin 4 ⊕ Fin 4 → K) :=
    (SmallRule.spBilin K 4).orthogonal W with hPdef
  set SW : Subgroup (LargeEvenProj (LargeEvenSpGroup K 4)) := ggSpFixPerp W with hSWdef
  have hWnd : ((SmallRule.spBilin K 4).restrict W).Nondegenerate :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := SmallRule.spBilin K 4) hB_alt.isRefl).mpr hcompl
  have hcard1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hdimW : Module.finrank K W = 2 * 3 := by rw [hW]
  have hTsimple : IsSimpleGroup ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) :=
    (A6Red.ggA6_spLie (SmallRule.spBilin K 4) hB_alt hB_nd W hWnd 3 1 hcard1 hdimW
      (by norm_num)).1
  have hmem : ∀ s : LargeEvenProj (LargeEvenSpGroup K 4),
      s ∈ SW ↔ (l48gS_eiso s : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
        A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P := by
    intro s
    rw [hSWdef, hPdef]
    exact l48gS_mem_iff W s
  let res : ↥SW →* ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) :=
    { toFun := fun s =>
        ⟨(l48gS_eiso s.1 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
          (hmem s.1).mp s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hbij : Function.Bijective res := by
    constructor
    · intro a b h
      apply Subtype.ext
      have h1 : (res a).1 = (res b).1 :=
        congrArg (fun x : ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) => x.1) h
      exact l48gS_eiso.injective (Subtype.ext h1)
    · intro g
      let r : LargeEvenProj (LargeEvenSpGroup K 4) := l48gS_eiso.symm ⟨g.1, g.2.1⟩
      have hr : l48gS_eiso r = ⟨g.1, g.2.1⟩ := l48gS_eiso.apply_symm_apply _
      have hrg : (l48gS_eiso r : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = g.1 :=
        congrArg (fun x : ↥(TauCeti.BilinForm.isometryGroup (SmallRule.spBilin K 4)) =>
          (x.1 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) hr
      refine ⟨⟨r, ?_⟩, ?_⟩
      · rw [hmem r, hrg]
        exact g.2
      · apply Subtype.ext
        exact hrg
  let eSW : ↥SW ≃* ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) :=
    MulEquiv.ofBijective res hbij
  have hSW_simple : IsSimpleGroup ↥SW := by
    haveI : IsSimpleGroup ↥(A6Red.ggA6SpFixer (SmallRule.spBilin K 4) P) := hTsimple
    exact eSW.isSimpleGroup
  obtain ⟨e1, -⟩ := A6Red.ggA6_sp_restr_equiv (SmallRule.spBilin K 4) hB_alt hB_nd W hWnd
  obtain ⟨e2⟩ := A6Red.ggA6_sp_std_equiv (V := Fin 4 ⊕ Fin 4 → K)
    ((SmallRule.spBilin K 4).restrict W) (fun x => hB_alt x) hWnd 3 hdimW
  have h63st : 63 ∣ Nat.card (CFSG.Open.StatedSp 3 K) := by
    have hd := CFSG.ClassicalGroups.Symplectic.card_pow_two_mul_sub_one_dvd_card_statedSp
      (K := K) (m := 3) (by norm_num)
    rw [hK] at hd
    norm_num at hd
    exact hd
  have hcard_eq : Nat.card ↥SW = Nat.card (CFSG.Open.StatedSp 3 K) := by
    rw [Nat.card_congr eSW.toEquiv, Nat.card_congr (e1.trans e2).toEquiv]
  have h63SW : 63 ∣ Nat.card ↥SW := by
    rw [hcard_eq]
    exact h63st
  have h7SW : 7 ∣ Nat.card ↥SW := dvd_trans (by norm_num : 7 ∣ 63) h63SW
  have hSWnotcomm : ¬ IsMulCommutative ↥SW := by
    intro hcomm
    haveI : IsMulCommutative ↥SW := hcomm
    have hp : Nat.Prime (Nat.card ↥SW) :=
      (Group.is_simple_iff_prime_card (α := ↥SW)).mp hSW_simple
    rcases hp.eq_one_or_self_of_dvd 63 h63SW with h | h
    · norm_num at h
    · rw [← h] at hp
      norm_num at hp
  have hSWperf : Group.IsPerfect ↥SW := by
    haveI : IsSimpleGroup ↥SW := hSW_simple
    exact TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hSWnotcomm
  have hSWcomm : ⁅SW, SW⁆ = SW := by
    haveI : Group.IsPerfect ↥SW := hSWperf
    exact Subgroup.commutator_eq_self
  exact ⟨hSW_simple, hSWcomm, h7SW⟩

end CFSG.StandardType

end
