module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityLayer
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartOne.S12.Sec1511Model
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType.Triality Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL)

@[expose] def GGD4GraphClassPGLInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    ∀ γ : Om8 K, (MulAut.conj γ * theta) ^ 3 = 1 →
      (∃ g : Om8 K, MulAut.conj γ * theta = MulAut.conj g * theta * (MulAut.conj g)⁻¹) ∨
        Nonempty (↥(ggFix (MulAut.conj γ * theta)) ≃* ProjGenLinGroup (Fin 3) K)

namespace OrdPTriLayer

section Group

variable {S : Type*} [Group S]

theorem center_eq_bot_of_simple_perfect (hs : IsSimpleGroup S) (hp : commutator S = ⊤) :
    Subgroup.center S = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hc : commutator S = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hx : x ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.1 hx y)
    have : Nontrivial S := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : S)
    have hxc : x ∈ commutator S := by rw [hp]; exact Subgroup.mem_top x
    rw [hc, Subgroup.mem_bot] at hxc
    exact hx hxc

theorem isQuasisimple_of_simple_perfect (hs : IsSimpleGroup S) (hp : commutator S = ⊤) :
    CFSG.Assembly.IsQuasisimple S := by
  refine ⟨hp, ?_⟩
  have : IsSimpleGroup S := hs
  exact ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_perfect hs hp)).trans
    QuotientGroup.quotientBot).isSimpleGroup

end Group

theorem lieModel_centerQuot_of_eq {G : Type} [Group G] {X Y : Subgroup G} (hXY : X = Y)
    {t : LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : LieModel (↥Y ⧸ Subgroup.center ↥Y) t n p f) :
    LieModel (↥X ⧸ Subgroup.center ↥X) t n p f := by
  subst hXY
  exact h

theorem commutator_eq_self_of_isQuasisimple {G : Type*} [Group G] {C : Subgroup G}
    (hC : CFSG.Assembly.IsQuasisimple ↥C) : ⁅C, C⁆ = C := by
  have h := congrArg (Subgroup.map C.subtype) hC.1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

section PGL

variable {K : Type} [Field K]

theorem commutator_top_pgl {p f : ℕ} (hK : CFSG.RankThree.PartTwo.Sec4.PiField true p f K)
    (hq2 : 2 < p ^ f) :
    ⁅(⊤ : Subgroup (ProjGenLinGroup (Fin 3) K)), ⊤⁆ = projSL 3 K := by
  have htop : (⊤ : Subgroup (GL (Fin 3) K)).map ProjGenLinGroup.mk = ⊤ :=
    Subgroup.map_top_of_surjective _ ProjGenLinGroup.mk_surjective
  have h := CFSG.RankThree.PartTwo.Sec13.commutator_glPi hK hq2
  have hg : CFSG.RankThree.PartTwo.Sec4.glPi true 3 (p ^ f) K = ⊤ := rfl
  rw [hg] at h
  rw [← htop, ← Subgroup.map_commutator, h, CFSG.RankThree.PartTwo.Sec4.projSL_eq_projImage (p ^ f)]
  rfl

theorem commutator_projSL_three {p f : ℕ} (hK : CFSG.RankThree.PartTwo.Sec4.PiField true p f K)
    (hq2 : 2 < p ^ f) : commutator ↥(projSL 3 K) = ⊤ := by
  have h := CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hK hq2
  rw [← CFSG.RankThree.PartTwo.Sec4.projSL_eq_projImage (p ^ f)] at h
  exact h.commutator_eq_top

variable [Finite K]

theorem lieModel_layer_of_pgl {G : Type} [Group G] {H : Subgroup G} {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : ↥H ≃* ProjGenLinGroup (Fin 3) K) :
    LieModel (↥(LargeEvenLayer H) ⧸ Subgroup.center ↥(LargeEvenLayer H)) .PSL 3 2 f := by
  have hPi : CFSG.RankThree.PartTwo.Sec4.PiField true 2 f K := ⟨Nat.prime_two, by omega, hK⟩
  have hq2 : 2 < 2 ^ f :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hf)
  have hcomm := commutator_top_pgl hPi hq2
  have hs : IsSimpleGroup ↥(projSL 3 K) :=
    CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field K
  have hp := commutator_projSL_three hPi hq2
  have hN : (projSL 3 K).Normal := by
    rw [← hcomm]
    exact Subgroup.commutator_normal ⊤ ⊤
  obtain ⟨T, hT⟩ : ∃ T : Subgroup ↥H, T = (projSL 3 K).comap e.toMonoidHom := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = T.map H.subtype := ⟨_, rfl⟩
  have hTe : T.map e.toMonoidHom = projSL 3 K := by
    rw [hT]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  have eMS : ↥M ≃* ↥(projSL 3 K) :=
    (MulEquiv.subgroupCongr hM).trans
      ((T.equivMapOfInjective H.subtype H.subtype_injective).symm.trans
        ((T.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hTe)))
  have hMq : CFSG.Assembly.IsQuasisimple ↥M := by
    rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native,
      CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eMS,
      ← CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native]
    exact isQuasisimple_of_simple_perfect hs hp
  have hMH : M ≤ H := by
    rw [hM]
    exact Subgroup.map_subtype_le T
  have hMcomp : IsComponentOf M H := by
    refine ⟨hMH, IsSubnormal.step hMH ?_ (IsSubnormal.refl H), hMq⟩
    have hMT : M.subgroupOf H = T := by
      rw [hM]
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective T
    rw [hMT, hT]
    exact hN.comap e.toMonoidHom
  have hle : ∀ C : Subgroup G, IsComponentOf C H → C ≤ M := by
    rintro C ⟨hCH, -, hCq⟩
    have hCC := commutator_eq_self_of_isQuasisimple hCq
    have hC'map : (C.subgroupOf H).map H.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hCH]
    have hC'C' : ⁅C.subgroupOf H, C.subgroupOf H⁆ = C.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, hC'map, hCC]
    have hD : (C.subgroupOf H).map e.toMonoidHom ≤ projSL 3 K := by
      rw [← hC'C', Subgroup.map_commutator, ← hcomm]
      exact Subgroup.commutator_mono le_top le_top
    intro c hc
    rw [hM]
    refine ⟨⟨c, hCH hc⟩, ?_, rfl⟩
    rw [hT]
    exact hD ⟨⟨c, hCH hc⟩, hc, rfl⟩
  have hL : LargeEvenLayer H = M :=
    le_antisymm (sSup_le fun C hC => hle C hC) (le_sSup hMcomp)
  refine lieModel_centerQuot_of_eq hL ?_
  have hZ : Subgroup.center ↥(projSL 3 K) = ⊥ := center_eq_bot_of_simple_perfect hs hp
  have e₂ : ↥(projSL 3 K) ≃* LowTwoRank.StatedProj (LowTwoRank.StatedSL 3 K) :=
    (CFSG.RankThree.PartOne.statedProjEquivRefl
      (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 3 K)).symm
  refine Or.inl ⟨by decide, ?_, ?_⟩
  · exact ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩
  · exact ⟨K, inferInstance, inferInstance, hK, ⟨(L613KG.centerQuotEquiv eMS).trans
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e₂)⟩⟩

end PGL

end OrdPTriLayer

open OrdPTriLayer

theorem ggD4GraphClassInput_of_pgl (h : GGD4GraphClassPGLInput) : GGD4GraphClassInput := by
  intro K _ _ _ f hK h3 γ hβ
  rcases h K (by rw [hK]; exact h3) γ hβ with hc | he
  · exact Or.inl hc
  · obtain ⟨e⟩ := he
    refine Or.inr (lieModel_layer_of_pgl hK ?_ e)
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    rcases Nat.lt_or_ge f 2 with hf | hf
    · interval_cases f
      · norm_num at h1
      · norm_num at h3
    · exact hf

theorem ggD4GraphLayerInput_of_pgl (hC : GGD4GraphClassPGLInput)
    (hQ : GGD4GraphFixQuasisimpleInput) : GGD4GraphLayerInput :=
  ggD4GraphLayerInput_of_class (ggD4GraphClassInput_of_pgl hC) hQ

end CFSG.StandardType
