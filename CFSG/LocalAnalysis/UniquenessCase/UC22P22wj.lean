module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wh
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22w
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22we
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_8Sp4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n → IsSp4 (Bar2 L) n →
    ∃ t ∈ D.T, ActsNontrivOnDiagram L t

theorem uc22p22wj_compShape_sp4 (D : Data G) (Ch : Choice2011 G) (h218 : S21_8Sp4 D Ch) (hH : H1930 D)
    (c : Ctx21 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M) (hcomp : IsComponentOf (mbarImage D.M D.U K) ⊤) {n : ℕ}
    (hodd : Odd n) (hsp : IsSp4 (Bar2 K) n) : CompShape148 (mbarImage D.M D.U K) := by
  obtain ⟨t, htT, ht⟩ := h218 hH c K hK n hodd hsp
  exact uc22p22wc_compShape_of_diag D hK hcomp hsp htT ht

theorem uc22p22wj_compShape (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h119 : R119W D) (h2116 : S21_16 D Ch) (h218 : S21_8Sp4 D Ch) (hH : H1930 D)
    (c : Ctx22c D Ch) {Lb : Subgroup (MBar D.M D.U)} (hLb : IsComponentOf Lb ⊤) : CompShape148 Lb := by
  obtain ⟨K, hK, rfl⟩ := uc22p22wa_lift D hx h61 h119 c.hU hLb
  rcases h2116 hH c.toCtx21 K hK with ⟨n, hodd, hsp⟩ | hrest
  · exact uc22p22wj_compShape_sp4 D Ch h218 hH c.toCtx21 hK hLb hodd hsp
  · exact uc22p22wb_compShape_of_shape D hK hLb hrest

theorem uc22p22wj_nbar_compShape (hK148 : K148)
    (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h31 : S22_3_1 D Ch) (h119 : R119W D)
    (h2116 : S21_16 D Ch) (h218 : S21_8Sp4 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {Umod : Type}
    [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ) :
    ∀ L : Subgroup ↥(mbarImage D.M D.U (proofN D)), IsComponentOf L ⊤ → CompShape148 L := by
  intro L hL
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  haveI hNn : (mbarImage D.M D.U (proofN D)).Normal := uc22p22ya_nbar_normal D
  have hW := uc22p22o_inCalW_U_of_not_isTI D hx h61 c.hU
  have hpc : CFSG.pCore 2 (MBar D.M D.U) = ⊥ := (uc22br4_pCore_bot_iff D.M D.U hMU).2 hW.2.2
  have hNne : mbarImage D.M D.U (proofN D) ≠ ⊥ := (h31 hH c).1
  obtain ⟨m, Hs, hHs, -, hsh⟩ := hK148 (MBar D.M D.U) Umod ρ (uc22br4_isKGroup_mbar_data_catalog D D.U) hpc
    (uc22br4_injective D.M D.U hMU e ρ hρ)
    (fun Lb hLb => uc22p22wj_compShape D Ch hx h61 h119 h2116 h218 hH c hLb) (uc22p22w_hP_ne_bot D e ρ hρ hNne)
  set L₁ : Subgroup (MBar D.M D.U) := L.map (mbarImage D.M D.U (proofN D)).subtype with hL₁
  have eL₁ : ↥L ≃* ↥L₁ := L.equivMapOfInjective _ (mbarImage D.M D.U (proofN D)).subtype_injective
  have hL₁q : CFSG.Open.IsQuasisimple ↥L₁ := CFSG.Open.IsQuasisimple.of_mulEquiv eL₁.symm hL.2.2
  have hL₁sub : CFSG.Open.IsSubnormal L₁ ⊤ := by
    have h1 := CFSG.Open.IsSubnormal.map (mbarImage D.M D.U (proofN D)).subtype hL.2.1
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.trans (CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hNn))
  have hL₁H : L₁ ≤ hP ρ := (Subgroup.map_subtype_le L).trans (uc22p22w_nbar_le_hP D e ρ hρ)
  have hL₁sub' : CFSG.Open.IsSubnormal L₁ (hP ρ) := by
    have h1 := CFSG.Open.IsSubnormal.inf_of_le hL₁sub (le_top : hP ρ ≤ ⊤)
    rwa [inf_eq_left.2 hL₁H] at h1
  obtain ⟨i, hi⟩ := P22w.exists_le_factor hHs hL₁q hL₁sub'
  have hcomp : CFSG.Open.IsComponentOf (L₁.subgroupOf (Hs i)) ⊤ := by
    refine ⟨le_top, ?_, CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hi) hL₁q⟩
    have h1 := CFSG.Open.IsSubnormal.inf_of_le hL₁sub (le_top : Hs i ≤ ⊤)
    rw [inf_eq_left.2 hi] at h1
    exact CFSG.Open.IsSubnormal.of_mathlib ((CFSG.Open.IsSubnormal.iff_subgroupOf hi).1 h1)
  have eL : ↥(L₁.subgroupOf (Hs i)) ≃* ↥L := (Subgroup.subgroupOfEquivOfLe hi).trans eL₁.symm
  rcases uc22p22we_compShape_of_factor (uc22p22we_factorShape_of_shape148 (hsh i)) hcomp with ⟨n, hn⟩ | h7
  · exact Or.inr (Or.inl ⟨n, Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eL hn))⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨7, by norm_num, CFSG.Blueprint.LieModel.of_mulEquiv eL h7⟩))

theorem uc22p22wj_decomp (hK148 : K148) (D : Data G)
    (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h31 : S22_3_1 D Ch) (h119 : R119W D)
    (h2116 : S21_16 D Ch) (h218 : S21_8Sp4 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {Umod : Type}
    [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ) :
    ∃ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)), NbarSplit D Nb ∧
      IsDirectSumMod (modI D ρ) (modCI D ρ) (fun i => commOn ρ (Nb i) (modI D ρ)) ∧
      ∀ i, Shape148 ρ (Nb i) (commOn ρ (Nb i) (modI D ρ)) (modCI D ρ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  have hW := uc22p22o_inCalW_U_of_not_isTI D hx h61 c.hU
  have hpc : CFSG.pCore 2 (MBar D.M D.U) = ⊥ := (uc22br4_pCore_bot_iff D.M D.U hMU).2 hW.2.2
  have hNne : mbarImage D.M D.U (proofN D) ≠ ⊥ := (h31 hH c).1
  haveI hNn : (mbarImage D.M D.U (proofN D)).Normal := uc22p22ya_nbar_normal D
  set N := mbarImage D.M D.U (proofN D) with hN
  set ρ' : Representation (ZMod 2) ↥N Umod := ρ.comp N.subtype with hρ'
  have hρinj : Function.Injective ρ := uc22br4_injective D.M D.U hMU e ρ hρ
  have hpcN : CFSG.pCore 2 ↥N = ⊥ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_bot, eq_bot_iff, ← hpc]
    exact uc22br4_map_pCore_le_pCore_of_isSubnormal 2 (Subgroup.Normal.isSubnormal hNn)
  have hP' : hP ρ' = ⊤ := uc22p22w_hP_restrict D e ρ hρ
  have hPne : hP ρ' ≠ ⊥ := by
    rw [hP']
    haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).2 hNne
    exact top_ne_bot
  obtain ⟨m, Hs, hHs, hdsum, hsh⟩ := hK148 ↥N Umod ρ'
    ((uc22br4_isKGroup_mbar_data_catalog D D.U).subgroup N) hpcN (hρinj.comp N.subtype_injective)
    (uc22p22wj_nbar_compShape hK148 D Ch hx h61 h31 h119 h2116 h218 hH c e ρ hρ) hPne
  rw [hP'] at hHs
  have huP : uP ρ' = modI D ρ := by
    unfold uP modI
    rw [hP', P22w.commOn_restrict, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcUP : cUP ρ' = modCI D ρ := by
    unfold cUP modCI
    rw [huP, hP', uc22p22w_fixSub_restrict, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomm : ∀ i, commOn ρ' (Hs i) (uP ρ') = commOn ρ ((Hs i).map N.subtype) (modI D ρ) := fun i => by
    rw [P22w.commOn_restrict, huP]
  refine ⟨m, fun i => (Hs i).map N.subtype, ⟨P22w.isInternalDirect_map hHs, fun i => ?_⟩, ?_, fun i => ?_⟩
  · exact P22w.factorShape22_of_mulEquiv ((Hs i).equivMapOfInjective N.subtype N.subtype_injective)
      (uc22p22we_factorShape_of_shape148 (hsh i))
  · have h1 := hdsum
    simp only [hcomm] at h1
    rw [huP, hcUP] at h1
    exact h1
  · have h1 := P22w.shape148_map (hsh i)
    rw [hcomm i, hcUP] at h1
    exact h1

theorem uc22p22wj_s22_3_of_sp4 (hK148 : K148)
    (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h31 : S22_3_1 D Ch) (h119 : R119W D)
    (h2116 : S21_16 D Ch) (h218 : S21_8Sp4 D Ch) : S22_3_2 D Ch ∧ S22_3_3 D Ch := by
  refine ⟨fun hH c => ?_, fun hH c m Nb hNb Umod _ _ _ e ρ hρ => ?_⟩
  · have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
    obtain ⟨Umod, i1, i2, i3, e, ρ, hρ⟩ := uc22br4_exists_conjModule D.M D.U hMU (uc22p22c_U_facts D).2
    obtain ⟨m, Nb, hNb, -⟩ := uc22p22wj_decomp hK148 D Ch hx h61 h31 h119 h2116 h218 hH c e ρ hρ
    exact ⟨m, Nb, hNb⟩
  · obtain ⟨m', Nb', hNb', hds, hsh⟩ := uc22p22wj_decomp hK148 D Ch hx h61 h31 h119 h2116 h218 hH c e ρ hρ
    obtain ⟨σ, hσ⟩ := uc22p22wg_nbarSplit_unique D hNb hNb'
    have hfun : (fun i => commOn ρ (Nb i) (modI D ρ)) = fun i => commOn ρ (Nb' (σ i)) (modI D ρ) := by
      funext i
      rw [hσ i]
    refine ⟨?_, fun i => ?_⟩
    · rw [hfun]
      exact uc22p22wh_isDirectSumMod_reindex σ (Ui := fun j => commOn ρ (Nb' j) (modI D ρ)) hds
    · rw [hσ i]
      exact hsh (σ i)

end CFSG.LocalAnalysis.UniquenessCase.UC22
