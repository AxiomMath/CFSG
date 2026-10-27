module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.RankThree.PartTwo.Sec18.Item187NSuz
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSzGen
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofNonsolv
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofComp
import CFSG.RankThree.PartTwo.Sec18.Item187NAut
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Kf1
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartTwo (fixedSubgroupOf mem_fixedSubgroupOf)
open CFSG.RankThree.PartTwo.Sec18.Item187Proof
  (restrictAut coe_restrictAut restrictAut_pow_three)

section Core

variable {Y : Type} [Group Y] [Finite Y]

theorem le_of_isComponent_of_fixedSubgroupOf_le (σ : MulAut Y)
    (hσ : σ ^ 3 = 1) {W T J : Subgroup Y} (hfix : fixedSubgroupOf σ ≤ W)
    (hT : IsSylowOf 2 T ⊤) (hTW : T ≤ W) (hJ : CFSG.IsComponent J) (hZ : center J = ⊥)
    {n : ℕ} (hSz : CFSG.Blueprint.SuzukiModel J 2 n) : J ≤ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_isSubnormal_top hT hJ.2
  have hQT : ∀ a ∈ (Q : Subgroup J), (a : Y) ∈ T ⊓ J := fun a ha => hQ ▸ mem_map_of_mem _ ha
  by_cases hJσ : J.map σ.toMonoidHom = J
  · have hgen := CFSG.RankThree.PartTwo.Sec16.kSzGen166 J n hSz (restrictAut σ J hJσ)
      (restrictAut_pow_three σ J hJσ hσ) Q
    have hle : fixedSubgroupOf (restrictAut σ J hJσ) ⊔ (Q : Subgroup J) ≤ W.subgroupOf J := by
      refine sup_le (fun y hy => ?_) (fun y hy => mem_subgroupOf.2 (hTW (hQT y hy).1))
      rw [mem_subgroupOf]
      apply hfix
      rw [mem_fixedSubgroupOf] at hy ⊢
      have h := congrArg Subtype.val hy
      rwa [coe_restrictAut] at h
    intro x hx
    exact mem_subgroupOf.1 (hle (by rw [hgen]; exact mem_top (⟨x, hx⟩ : J)))
  have h3 : ∀ y : Y, σ (σ (σ y)) = y := fun y => by
    have h := congrArg (fun τ : MulAut Y => τ y) hσ
    simpa [pow_succ, MulAut.mul_apply] using h
  have hc1 := CFSG.LocalCores.isComponent_map_mulEquiv σ hJ
  have hc2 := CFSG.LocalCores.isComponent_map_mulEquiv σ hc1
  have hne1 : J ≠ J.map σ.toMonoidHom := fun h => hJσ h.symm
  have hne2 : J ≠ (J.map σ.toMonoidHom).map σ.toMonoidHom := by
    intro h
    apply hne1
    calc J = ((J.map σ.toMonoidHom).map σ.toMonoidHom).map σ.toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map]
          convert (Subgroup.map_id J).symm
          ext y
          exact h3 y
      _ = J.map σ.toMonoidHom := by rw [← h]
  have hcomm : ∀ {K : Subgroup Y}, CFSG.IsComponent K → J ≠ K → ∀ a ∈ J, ∀ b ∈ K,
      Commute a b := fun hK hne a ha b hb =>
    CFSG.RankThree.PartTwo.Sec16.Comp167.commute_of_isComponent hJ hK hne ha hb
  have hcx : ∀ z ∈ J, ∀ x ∈ J, Commute z (σ x * σ (σ x)) := fun z hz x hx =>
    (hcomm hc1 hne1 z hz (σ x) (mem_map_of_mem _ hx)).mul_right
      (hcomm hc2 hne2 z hz (σ (σ x)) (mem_map_of_mem _ (mem_map_of_mem _ hx)))
  have hδ : ∀ x ∈ J, x * (σ x * σ (σ x)) ∈ W := by
    intro x hx
    apply hfix
    rw [mem_fixedSubgroupOf, _root_.map_mul, _root_.map_mul, h3]
    calc σ x * (σ (σ x) * x) = (σ x * σ (σ x)) * x := (mul_assoc _ _ _).symm
      _ = x * (σ x * σ (σ x)) := (hcx x hx x hx).eq.symm
  have hconj : ∀ x ∈ J, ∀ y ∈ T ⊓ J, x⁻¹ * y * x ∈ W := by
    intro x hx y hy
    have hz : x⁻¹ * y * x ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hx) hy.2) hx
    have c := hcx _ hz x hx
    have e : (x * (σ x * σ (σ x)))⁻¹ * y * (x * (σ x * σ (σ x))) = x⁻¹ * y * x := by
      calc (x * (σ x * σ (σ x)))⁻¹ * y * (x * (σ x * σ (σ x)))
          = (σ x * σ (σ x))⁻¹ * ((x⁻¹ * y * x) * (σ x * σ (σ x))) := by group
        _ = (σ x * σ (σ x))⁻¹ * ((σ x * σ (σ x)) * (x⁻¹ * y * x)) := by rw [c.eq]
        _ = x⁻¹ * y * x := by group
    rw [← e]
    exact W.mul_mem (W.mul_mem (W.inv_mem (hδ x hx)) (hTW hy.1)) (hδ x hx)
  have hNW : Subgroup.normalClosure ((Q : Subgroup J) : Set J) ≤ W.subgroupOf J := by
    show Subgroup.closure (Group.conjugatesOfSet _) ≤ _
    rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    rw [SetLike.mem_coe, mem_subgroupOf]
    have h := hconj ((c⁻¹ : J) : Y) (c⁻¹ : J).2 (a : Y) (hQT a ha)
    simpa [mul_assoc] using h
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ.1
      (Subgroup.normalClosure_normal (s := ((Q : Subgroup J) : Set J))) with hN1 | hN1
  · intro x hx
    exact mem_subgroupOf.1 (hNW (by rw [hN1]; exact mem_top (⟨x, hx⟩ : J)))
  · rw [hZ, le_bot_iff] at hN1
    have hQb : (Q : Subgroup J) = ⊥ := eq_bot_iff.2 fun x hx => by
      have h := Subgroup.subset_normalClosure (s := ((Q : Subgroup J) : Set J)) hx
      rwa [hN1] at h
    exact (Sylow.ne_bot_of_dvd_card Q
      (CFSG.RankThree.PartTwo.KFacts.two_dvd_card_of_suzukiModel hSz) hQb).elim

end Core

variable {G : Type} [Group G] [Finite G]

theorem pCore_I9_eq_bot (p : ℕ) {H : Subgroup G} (hO : pCoreOf p H = ⊥) :
    CFSG.pCore p (I9 H) = ⊥ := by
  have h := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer p (map_subtype_le _ :
    I9 H ≤ H) (le_normalizer_I9 H)
  rw [hO, le_bot_iff] at h
  exact (map_eq_bot_iff_of_injective _ (I9 H).subtype_injective).1 h

theorem rankThreeLayer_I9_le
    (hK : CFSG.Open.IsKProper G) {M H R D₃ : Subgroup G} (hH : H ≠ ⊤) (hO2 : pCoreOf 2 H = ⊥)
    (hRI : IsSylowOf 2 (R ⊓ I9 H) (I9 H)) (hRM : R ≤ M) (hD₃H : D₃ ≤ H)
    (hD₃ : Nat.card D₃ = 3) (hCD : centralizer (D₃ : Set G) ≤ M) :
    rankThreeLayer (I9 H) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hIH : I9 H ≤ H := map_subtype_le _
  haveI : IsCyclic D₃ := isCyclic_of_prime_card hD₃
  obtain ⟨d, hd⟩ := IsCyclic.exists_generator (α := ↥D₃)
  have hd3 : (d : G) ^ 3 = 1 := by
    have h : d ^ Nat.card D₃ = 1 := pow_card_eq_one'
    rw [hD₃] at h
    exact_mod_cast congrArg Subtype.val h
  have hCd : ∀ g : G, (d : G) * g * (d : G)⁻¹ = g → g ∈ M := by
    intro g hg
    apply hCD
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hd ⟨e, he⟩)
    have hk' : (d : G) ^ k = e := by simpa using congrArg Subtype.val hk
    have hc : Commute (d : G) g :=
      calc (d : G) * g = (d * g * (d : G)⁻¹) * d := by group
        _ = g * d := by rw [hg]
    rw [← hk']
    exact (hc.zpow_left k).eq
  have hIσ : (I9 H).map (MulAut.conj (d : G)).toMonoidHom = I9 H :=
    mem_normalizer_iff_map_conj_eq.1 (le_normalizer_I9 H (hD₃H d.2))
  have hσ3 : restrictAut (MulAut.conj (d : G)) (I9 H) hIσ ^ 3 = 1 :=
    restrictAut_pow_three _ _ hIσ (by rw [← _root_.map_pow, hd3, _root_.map_one])
  have hfix : fixedSubgroupOf (restrictAut (MulAut.conj (d : G)) (I9 H) hIσ) ≤
      M.subgroupOf (I9 H) := by
    intro y hy
    rw [mem_fixedSubgroupOf] at hy
    rw [mem_subgroupOf]
    apply hCd
    have h := congrArg Subtype.val hy
    rwa [coe_restrictAut, MulAut.conj_apply] at h
  obtain ⟨Q, hQ⟩ := hRI
  have hT : IsSylowOf 2 (Q : Subgroup (I9 H)) ⊤ := ⟨Q.subtype le_top, by
    rw [Sylow.coe_subtype, subgroupOf_map_subtype, inf_top_eq]⟩
  have hTW : (Q : Subgroup (I9 H)) ≤ M.subgroupOf (I9 H) := by
    intro y hy
    have h1 : (I9 H).subtype y ∈ R ⊓ I9 H := hQ ▸ mem_map_of_mem _ hy
    exact mem_subgroupOf.2 (hRM h1.1)
  have hKI : CFSG.IsKGroup (I9 H) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.isKGroup_of_ne_top_of_isKProper hK
      (ne_top_of_le_ne_top hH hIH)
  have h3 : ¬ 3 ∣ Nat.card (I9 H) := not_dvd_card_I9 H
  have h2 : CFSG.pCore 2 (I9 H) = ⊥ := pCore_I9_eq_bot 2 hO2
  unfold rankThreeLayer
  refine sSup_le fun L hL => ?_
  have hLI : L ≤ I9 H := hL.1
  have hJ : CFSG.IsComponent (L.subgroupOf (I9 H)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLI).1
      (CFSG.Assembly.isComponentOf_iff_open.2 hL)
  obtain ⟨f, hf⟩ :=
    CFSG.RankThree.PartTwo.Sec18.Item187Proof.suzukiModel_of_isComponent hKI h3 h2 hJ
  have hle := le_of_isComponent_of_fixedSubgroupOf_le _ hσ3 hfix hT hTW hJ
    (CFSG.RankThree.PartTwo.Sec16.suzuki_component_facts hKI h3 h2 hJ).1 hf
  intro x hx
  have hx' : (⟨x, hLI hx⟩ : I9 H) ∈ L.subgroupOf (I9 H) := mem_subgroupOf.2 hx
  exact mem_subgroupOf.1 (hle hx')

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
