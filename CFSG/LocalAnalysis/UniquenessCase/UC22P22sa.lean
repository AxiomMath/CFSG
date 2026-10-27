module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22s
public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22x
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

namespace P22s

section Abstract

variable {S H : Type} [Group S] [Group H] [Finite H] {ι : S →* H}

theorem inClassG_comp (h : InClassG S H ι) (c : S ≃* S) : InClassG S H (ι.comp c.toMonoidHom) := by
  have hrange : (ι.comp c.toMonoidHom).range = ι.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 c.surjective, ← MonoidHom.range_eq_map]
  exact ⟨h.injective.comp c.injective, hrange ▸ h.sylow, h.fitting_eq, h.quotient⟩

theorem pCore_le_range (hG : InClassG S H ι) : CFSG.pCore 2 H ≤ ι.range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ι.range := hG.sylow.2.1
  have hidx : ¬ 2 ∣ ι.range.index := by
    have := hG.sylow.2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact (CFSG.pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (hp.toSylow hidx)

theorem tripleE_le_pCore : tripleE H ≤ CFSG.pCore 2 H :=
  Subgroup.map_subtype_le _

theorem tripleE_le_range (hG : InClassG S H ι) : tripleE H ≤ ι.range :=
  tripleE_le_pCore.trans (pCore_le_range hG)

theorem tripleE_normal : (tripleE H).Normal :=
  CFSG.QuasithinUnique.Setup.Campbell.elemCenterIn_normal (G := H) 2 (CFSG.pCore 2 H)

theorem tripleV_le_tripleE : tripleV H ≤ tripleE H := by
  have := tripleE_normal (H := H)
  exact Subgroup.commutator_le_right _ _

theorem tripleV_le_range (hG : InClassG S H ι) : tripleV H ≤ ι.range :=
  tripleV_le_tripleE.trans (tripleE_le_range hG)

end Abstract

theorem map_omegaOne_center_mulEquiv {S : Type} [Group S] (c : S ≃* S) :
    (omegaOne 2 (Subgroup.center S)).map c.toMonoidHom = omegaOne 2 (Subgroup.center S) := by
  have key : ∀ d : S ≃* S, (omegaOne 2 (Subgroup.center S)).map d.toMonoidHom ≤
      omegaOne 2 (Subgroup.center S) := by
    intro d
    unfold omegaOne
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hxc, hx2⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff] at hxc ⊢
      intro y
      have := congrArg d (hxc (d.symm y))
      simpa using this
    · show d x ^ 2 = 1
      rw [← map_pow, hx2, map_one]
  refine le_antisymm (key c) ?_
  intro x hx
  refine ⟨c.symm x, key c.symm ⟨x, hx, rfl⟩, by simp⟩

variable {G : Type} [Group G] [Finite G]

theorem jOf_le_jOf {S T : Subgroup G} (hJS : jOf T ≤ S) (hST : S ≤ T) : jOf T ≤ jOf S := by
  have h1 : ∀ X : Subgroup G, jOf X = CFSG.Quasithin.thompsonJ X := fun X =>
    CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ X
  rw [h1, h1]
  refine iSup₂_le fun A hA => ?_
  have hAJ : A ≤ CFSG.Quasithin.thompsonJ T :=
    le_iSup₂_of_le (f := fun A (_ : CFSG.Quasithin.IsMaxElemAbelian T A) => A) A hA le_rfl
  have hAS : A ≤ S := hAJ.trans (h1 T ▸ hJS)
  have hA' : CFSG.Quasithin.IsMaxElemAbelian S A :=
    ⟨hAS, hA.2.1, fun B hBS hB => hA.2.2 B (hBS.trans hST) hB⟩
  exact le_iSup₂_of_le (f := fun A (_ : CFSG.Quasithin.IsMaxElemAbelian S A) => A) A hA' le_rfl

theorem jOf_le_proofS (D : Data G) : jOf D.T ≤ proofS D := by
  refine le_inf (uc22p22e_jOf_le_self D.T) (fun j hj => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((uc22p22e_mem_omegaZJ'.1 hz).2.1 j hj).symm

theorem centralizer_elemThompsonCenterTorsion_proofS (D : Data G) :
    Subgroup.centralizer (elemThompsonCenterTorsion ↥(proofS D) 2 : Set ↥(proofS D)) = ⊤ := by
  have hST : proofS D ≤ D.T := inf_le_left
  have hJ := jOf_le_jOf (jOf_le_proofS D) hST
  refine eq_top_iff.2 fun s _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzS : (z : G) ∈ omegaZJ22 (proofS D) := ⟨z, hz, rfl⟩
  obtain ⟨hzS', hzc, hz2⟩ := uc22p22e_mem_omegaZJ'.1 hzS
  have hzE : (z : G) ∈ proofE D :=
    uc22p22e_mem_omegaZJ'.2 ⟨hST hzS', fun j hj => hzc j (hJ hj), hz2⟩
  have hs := (Subgroup.mem_centralizer_iff.1 s.2.2) _ hzE
  exact Subtype.ext hs

theorem map_pCore (H : Subgroup G) : (CFSG.pCore 2 ↥H).map H.subtype = CFSG.Open.pCoreOf 2 H := rfl

theorem map_tripleE (H : Subgroup G) : (tripleE ↥H).map H.subtype = omegaZJ22 (CFSG.Open.pCoreOf 2 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold tripleE omegaZJ22 CFSG.inSubgroup
  rw [Subgroup.map_map]
  set P : Subgroup ↥H := CFSG.pCore 2 ↥H
  let e : ↥P ≃* ↥(P.map H.subtype) := P.equivMapOfInjective H.subtype H.subtype_injective
  have hcomp : H.subtype.comp P.subtype = (P.map H.subtype).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map,
    CFSG.QuasithinUnique.Setup.Campbell.elemThompsonCenterTorsion_map_mulEquiv e 2]
  rfl

theorem map_tripleV (H : Subgroup G) :
    (tripleV ↥H).map H.subtype = ⁅H, omegaZJ22 (CFSG.Open.pCoreOf 2 H)⁆ := by
  unfold tripleV
  rw [Subgroup.map_commutator, map_tripleE, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite G] in
theorem map_omegaOne' {G' : Type} [Group G'] (f : G →* G') (hf : Function.Injective f) (X : Subgroup G) :
    (omegaOne 2 X).map f = omegaOne 2 (X.map f) := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxX, hx2⟩, rfl⟩
    exact ⟨⟨x, hxX, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
  · rintro ⟨⟨x, hxX, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxX, hf ?_⟩, rfl⟩
    rw [map_pow, hy2, map_one]

theorem map_omegaOne_center {S H : Subgroup G} (hSH : S ≤ H) :
    ((omegaOne 2 (Subgroup.center ↥S)).map (Subgroup.inclusion hSH)).map H.subtype = omegaOneCenterIn S := by
  rw [Subgroup.map_map]
  have hcomp : H.subtype.comp (Subgroup.inclusion hSH) = S.subtype := by
    ext x
    rfl
  rw [hcomp, map_omegaOne' S.subtype S.subtype_injective]
  rfl

theorem commutator_omegaOne_ne_bot {S H : Subgroup G} (hSH : S ≤ H)
    (h : ¬ H ≤ centralizer (omegaOneCenterIn S : Set G)) :
    ⁅(⊤ : Subgroup ↥H), (omegaOne 2 (Subgroup.center ↥S)).map (Subgroup.inclusion hSH)⁆ ≠ ⊥ := by
  intro hbot
  apply h
  have hmap := congrArg (Subgroup.map H.subtype) hbot
  rw [Subgroup.map_commutator, map_omegaOne_center, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Subgroup.map_bot] at hmap
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hmap

theorem inClassG_inclusion {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.relIndex H)
    (hF : H ⊓ centralizer (CFSG.Open.pCoreOf 2 H : Set G) ≤ CFSG.Open.pCoreOf 2 H)
    {X : Type} [Group X] (φ : ↥H →* X) (hφ : Function.Surjective φ) {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) (hker : φ.ker ≤ CFSG.pCore 2 ↥H) :
    InClassG ↥S ↥H (Subgroup.inclusion hSH) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.inclusion_injective hSH, ?_, ?_, ?_⟩
  · refine ⟨le_top, ?_, ?_⟩
    · rw [Subgroup.inclusion_range]
      exact hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    · rw [Subgroup.inclusion_range, Subgroup.relIndex_top_right]
      exact hidx
  · refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 2).1 ?_
    intro x hx
    have hxG : (x : G) ∈ H ⊓ centralizer (CFSG.Open.pCoreOf 2 H : Set G) := by
      refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hx) y hy)
    obtain ⟨y, hy, hyx⟩ := hF hxG
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · refine ⟨n, hn, φ.ker, inferInstance, ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e⟩, ?_⟩
    intro Y hY hYK hQY
    have hKY : φ.ker ≤ Y := hker.trans hQY
    rw [sup_eq_left.2 hKY] at hYK
    exact hY.ne hYK

end P22s

end CFSG.LocalAnalysis.UniquenessCase.UC22
