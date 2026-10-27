module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowOverlapModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowInput
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)

local instance twistedE6PilotQ2SwapRowOverlapNeZero : NeZero TwistTag.E6.foldedTag.rank :=
  ⟨by decide⟩

section Generic

variable {G : Type*} [Group G]

theorem centralizer_map_mulAut_ovl (α : MulAut G) (H : Subgroup G) :
    centralizer ((H.map α.toMonoidHom : Subgroup G) : Set G) =
      (centralizer (H : Set G)).map α.toMonoidHom := by
  ext g
  constructor
  · intro hg
    refine ⟨α.symm g, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    have := mem_centralizer_iff.1 hg (α h) ⟨h, hh, rfl⟩
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  · rintro ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hg h hh]

theorem exists_le_map_eq_of_le_map_ovl (α : MulAut G) {H Y : Subgroup G}
    (hY : Y ≤ H.map α.toMonoidHom) : ∃ Y' : Subgroup G, Y' ≤ H ∧ Y'.map α.toMonoidHom = Y := by
  refine ⟨Y.comap α.toMonoidHom, fun y hy => ?_, map_comap_eq_self_of_surjective α.surjective Y⟩
  obtain ⟨h, hh, hhy⟩ := hY (show α y ∈ Y from hy)
  rwa [← α.injective hhy]

theorem map_conj_eq_self_of_mem_ovl {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end Generic

@[expose] def ovlWord : Fin 3 → List (Fin TwistTag.E6.foldedTag.rank) :=
  ![[3, 2, 1, 0, 2, 1, 3], [3, 2, 0, 1, 2, 3], [3, 1, 2, 0, 1, 2, 3]]

set_option maxRecDepth 100000 in
theorem ovlWord_check : ∀ p : Fin 3,
    twistedE6RelAct (ovlWord p) e6HighestRoot = matRoot (ovlPt p) (Fin.rev (ovlPt p)) ∧
      twistedE6RelAct (ovlWord p) (-e6HighestRoot) = -matRoot (ovlPt p) (Fin.rev (ovlPt p)) := by
  decide +kernel

theorem exists_eq_matRoot_of_mem_perpFixedRoots
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : δ ∈ perpFixedRoots) :
    ∃ p : Fin 3, δ = matRoot (ovlPt p) (Fin.rev (ovlPt p)) := by
  unfold perpFixedRoots at hδ
  rcases List.mem_cons.1 hδ with rfl | hδ
  · exact ⟨0, by funext i; fin_cases i <;> decide⟩
  rcases List.mem_cons.1 hδ with rfl | hδ
  · exact ⟨1, by funext i; fin_cases i <;> decide⟩
  rcases List.mem_cons.1 hδ with rfl | hδ
  · exact ⟨2, by funext i; fin_cases i <;> decide⟩
  simp at hδ

@[expose] noncomputable def ovlGroup {K : Type} [Field K]
    (h2 : (2 : K) = 0) (σ : K →+* K) (p : Fin 3) : Subgroup (ModGL TwistTag.E6.tag K) :=
  (unitarySL σ ⊓ LinearPilot.blockSpecialLinear (ovlSet p)).map (realize h2)

section OverlapBasic

variable {K : Type} [Field K]

theorem ovlGroup_eq_range (h2 : (2 : K) = 0) {σ : K →+* K} (σ' : K ≃+* K)
    (hσ' : ∀ c, σ c = σ' c) (p : Fin 3) :
    ovlGroup h2 σ p = ((realize h2).comp (ovlSU σ' p)).range := by
  rw [MonoidHom.range_comp, range_ovlSU σ' p hσ', ovlGroup]

theorem realize_ovlSU_injective (h2 : (2 : K) = 0) (σ' : K ≃+* K) (p : Fin 3) :
    Function.Injective ((realize h2).comp (ovlSU σ' p)) :=
  (realize_ovlEmbed_injective h2 p).comp (suToSL4_injective σ')

@[expose] noncomputable def ovlGroupEquiv (h2 : (2 : K) = 0) {σ : K →+* K} (σ' : K ≃+* K)
    (hσ' : ∀ c, σ c = σ' c) (p : Fin 3) :
    CFSG.LieType.Universal.Unitary.SU σ' 4 ≃* ovlGroup h2 σ p :=
  (MonoidHom.ofInjective (realize_ovlSU_injective h2 σ' p)).trans
    (MulEquiv.subgroupCongr (ovlGroup_eq_range h2 σ' hσ' p).symm)

theorem sigma_eq_unitaryInvolution_ovl [Finite K] [CharP K 2] {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (c : K) :
    σ c = CFSG.LieType.BorelTits.unitaryInvolution K 2 1 c := by
  rw [hσ, CFSG.LieType.BorelTits.unitaryInvolution_apply]

theorem isSimpleGroup_ovlGroup [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (p : Fin 3) :
    IsSimpleGroup (ovlGroup h2 σ p) := by
  have := isSimpleGroup_SU_four_ovl hK
  exact (ovlGroupEquiv h2 _ (sigma_eq_unitaryInvolution_ovl hσ) p).symm.isSimpleGroup

theorem ovlGroup_perfect [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (p : Fin 3) :
    ⁅ovlGroup h2 σ p, ovlGroup h2 σ p⁆ = ovlGroup h2 σ p := by
  have hP := isPerfect_SU_four_ovl hK
  rw [ovlGroup_eq_range h2 _ (sigma_eq_unitaryInvolution_ovl hσ) p, MonoidHom.range_eq_map,
    ← Subgroup.map_commutator, ← commutator_def, hP.commutator_eq_top]

end OverlapBasic


section Transport

variable {K : Type} [Field K]

theorem rootRankOneGroup_eq_map_ovlWord [CharP K 2] {k : Type} [Field k] (ι : k →+* K)
    (p : Fin 3) :
    TwistedE6Pilot.rootRankOneGroup ι (matRoot (ovlPt p) (Fin.rev (ovlPt p))) =
      (thetaRankOneGroup ι).map (MulAut.conj (twistedE6RelWeyl K (ovlWord p))).toMonoidHom := by
  obtain ⟨h1, h2⟩ := ovlWord_check p
  rw [TwistedE6Pilot.rootRankOneGroup, thetaRankOneGroup, thetaRootGroup, thetaNegRootGroup,
    Subgroup.map_sup, MonoidHom.map_closure, MonoidHom.map_closure, ← Set.range_comp,
    ← Set.range_comp]
  refine congrArg₂ (· ⊔ ·)
    (congrArg Subgroup.closure (congrArg Set.range (funext fun c => ?_)))
    (congrArg Subgroup.closure (congrArg Set.range (funext fun c => ?_)))
  · simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [twistedE6RelWeyl_conj_pinnedX _ isRoot_e6HighestRoot, h1]
  · simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [twistedE6RelWeyl_conj_pinnedX _ (IsRoot.neg isRoot_e6HighestRoot), h2]

end Transport

section Upper

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem le_centralizer_rootRankOneGroup_of_perfect (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (p : Fin 3)
    {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (hYJ : Y ≤ TwistedE6Pilot.rootRankOneGroup (algebraMap k K)
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))))
    (hY : Nat.card Y = 3) {P : Subgroup (ModGL TwistTag.E6.tag K)} (hPD : P ≤ su6Levi σ)
    (hPY : P ≤ centralizer (Y : Set (ModGL TwistTag.E6.tag K))) (hP : ⁅P, P⁆ = P) :
    P ≤ centralizer (TwistedE6Pilot.rootRankOneGroup (algebraMap k K)
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))) : Set (ModGL TwistTag.E6.tag K)) := by
  have : CharP K 2 := charP_two_of_card le_rfl hK
  set α := MulAut.conj (twistedE6RelWeyl K (ovlWord p)) with hα
  have hnC : twistedE6RelWeyl K (ovlWord p) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    twistedE6RelWeyl_mem σ (ovlWord p)
  have hJ := rootRankOneGroup_eq_map_ovlWord (K := K) (algebraMap k K) p
  rw [hJ] at hYJ ⊢
  obtain ⟨Y', hY'J, rfl⟩ := exists_le_map_eq_of_le_map_ovl α hYJ
  have hY'card : Nat.card Y' = 2 ^ 1 + 1 := by
    rw [Subgroup.card_map_of_injective α.injective] at hY
    rw [hY]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY'cyc : IsCyclic Y' := isCyclic_of_prime_card (p := 3) (by rw [hY'card]; rfl)
  obtain ⟨hcent, -, hY'D, -⟩ :=
    centralizer_nonsplit_twistedE6 (f := 1) le_rfl hk hK hσ hY'J hY'card hY'cyc
  have hPC : P ≤ (graphFixedRootGroup TwistTag.E6 K σ).map α.toMonoidHom := by
    rw [hα, map_conj_eq_self_of_mem_ovl hnC]
    exact hPD.trans (su6Levi_le_graphFixedRootGroup σ)
  obtain ⟨P', hP'C, rfl⟩ := exists_le_map_eq_of_le_map_ovl α hPC
  have hP'Y : P' ≤ centralizer (Y' : Set (ModGL TwistTag.E6.tag K)) := by
    rw [centralizer_map_mulAut_ovl] at hPY
    exact (Subgroup.map_le_map_iff_of_injective α.injective).1 hPY
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
    rw [Subgroup.map_commutator, hP]
  have hP'sup : P' ≤ su6Levi σ ⊔ Y' := by
    rw [sup_comm, ← hcent]
    exact le_inf hP'Y hP'C
  have hnorm : ((su6Levi σ).subgroupOf (su6Levi σ ⊔ Y')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer
      (hY'D.trans (centralizer_le_normalizer _)))
  have hsolv : Group.IsSolvable Y' := Group.isSolvable_of_comm fun a b => by
    let := IsCyclic.commGroup (α := Y')
    exact mul_comm a b
  have hP'D : P' ≤ su6Levi σ :=
    (le_perfectCore_of_perfect hP'sup hP'perf).trans
      (CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left hnorm rfl hsolv)
  have hDJ := (su6Levi_facts (f := 1) le_rfl hk hK hσ).1
  rw [centralizer_map_mulAut_ovl]
  exact Subgroup.map_mono (hP'D.trans hDJ)

end Upper

section Overlap

variable {K : Type} [Field K]

theorem ovlGroup_le_su6Levi [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (p : Fin 3) :
    ovlGroup h2 σ p ≤ su6Levi σ := by
  rw [su6Levi, (subsystemGroup_inf_eq_map_realize hK hσ h2).1]
  exact Subgroup.map_mono inf_le_left

theorem ovlGroup_le_centralizer_rootRankOneGroup (h2 : (2 : K) = 0) (σ : K →+* K) (p : Fin 3)
    {k : Type} [Field k] (ι : k →+* K) :
    ovlGroup h2 σ p ≤ centralizer (TwistedE6Pilot.rootRankOneGroup ι
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))) : Set (ModGL TwistTag.E6.tag K)) := by
  rw [Subgroup.le_centralizer_iff]
  obtain ⟨-, -, -, -, -, -, -, hpp⟩ := ovl_check p
  have hdisj : Disjoint (ovlSet p) ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) :=
    disjoint_compl_left
  have key : ∀ {x y : Fin 6} (hxy : x ≠ y), x ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) →
      y ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) → ∀ c : K,
      realize h2 (SpecialLinearGroup.transvection hxy c) ∈
        centralizer (ovlGroup h2 σ p : Set (ModGL TwistTag.E6.tag K)) := by
    intro x y hxy hx hy c
    rw [mem_centralizer_iff]
    rintro _ ⟨M, hM, rfl⟩
    rw [← map_mul, ← map_mul, (LinearPilot.commute_blockSpecialLinear_of_disjoint hdisj hM.2
      (LinearPilot.transvection_mem_blockSpecialLinear hxy hx hy c)).eq]
  refine sup_le ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    dsimp only
    rw [← realize_transvection_ovl h2 hpp]
    exact key hpp (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (ι c)
  · rintro _ ⟨c, rfl⟩
    dsimp only
    rw [← matRoot_swap_ovl, ← realize_transvection_ovl h2 hpp.symm]
    exact key hpp.symm (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (Finset.mem_insert_self _ _) (ι c)


theorem perfect_le_ovlGroup [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (h2 : (2 : K) = 0) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (p : Fin 3) {k : Type}
    [Field k] (ι : k →+* K) {P : Subgroup (ModGL TwistTag.E6.tag K)} (hPD : P ≤ su6Levi σ)
    (hPJ : P ≤ centralizer (TwistedE6Pilot.rootRankOneGroup ι
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))) : Set (ModGL TwistTag.E6.tag K)))
    (hP : ⁅P, P⁆ = P) : P ≤ ovlGroup h2 σ p := by
  obtain ⟨-, -, -, -, -, -, -, hpp⟩ := ovl_check p
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hDm : su6Levi σ = (unitarySL σ).map (realize h2) := by
    rw [su6Levi]
    exact (subsystemGroup_inf_eq_map_realize hK hσ h2).1
  set Q₀ := unitarySL σ ⊓ P.comap (realize h2) with hQ₀
  have hQ₀P : Q₀.map (realize h2) = P := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_right
    · intro x hx
      obtain ⟨B, hB, rfl⟩ := (hDm ▸ hPD) hx
      exact ⟨B, ⟨hB, hx⟩, rfl⟩
  set Q := perfectCore Q₀ with hQ
  have hQperf : ⁅Q, Q⁆ = Q := perfectCore_perfect Q₀
  have hQP : Q.map (realize h2) = P := by
    rw [hQ, CFSG.Quasithin.map_perfectCore, hQ₀P,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hP]
  have hQU : Q ≤ unitarySL σ := (perfectCore_le Q₀).trans inf_le_left
  have hcent := le_centralizer_comap_of_perfect_ovl (realize h2) (ker_realize_le_center_ovl h2)
    hQperf
  rw [hQP] at hcent
  have hJP : TwistedE6Pilot.rootRankOneGroup ι (matRoot (ovlPt p) (Fin.rev (ovlPt p))) ≤
      centralizer (P : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hPJ
  have hT : ∀ {x y : Fin 6} (hxy : x ≠ y),
      x ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) →
      y ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) →
      SpecialLinearGroup.transvection hxy (1 : K) ∈
        (centralizer (P : Set (ModGL TwistTag.E6.tag K))).comap (realize h2) := by
    intro x y hxy hx hy
    rw [mem_comap, realize_transvection_ovl h2 hxy]
    apply hJP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact mem_sup_left (subset_closure ⟨1, by simp only [map_one]⟩)
    · rw [matRoot_swap_ovl (ovlPt p) (Fin.rev (ovlPt p))]
      exact mem_sup_right (subset_closure ⟨1, by simp only [map_one]⟩)
    · exact absurd rfl hxy
  have hcomm : ∀ A ∈ Q, ∀ i ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)),
      ∀ j ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)), ∀ hij : i ≠ j,
        A * SpecialLinearGroup.transvection hij 1 = SpecialLinearGroup.transvection hij 1 * A := by
    intro A hA i hi j hj hij
    exact (mem_centralizer_iff.1 (hcent hA) _ (hT hij hi hj)).symm
  have hQB := LinearPilot.le_blockSpecialLinear_sdiff_of_commute (N := Finset.univ)
    (T := ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6))) (by rw [Finset.card_pair hpp])
    (by rw [LinearPilot.blockSpecialLinear_univ]; exact le_top) hQperf hcomm
  rw [← Finset.compl_eq_univ_sdiff] at hQB
  rw [← hQP]
  exact Subgroup.map_mono (le_inf hQU hQB)

theorem pinnedX_mem_ovlGroup (h2 : (2 : K) = 0) {σ : K →+* K} (p : Fin 3) {a b : Fin 6}
    (hab : a ≠ b) (ha : a ∈ ovlSet p) (hb : b ∈ ovlSet p) (hba : b = Fin.rev a) {s : K}
    (hs : σ s = s) : pinnedX TwistTag.E6.tag K (matRoot a b) s ∈ ovlGroup h2 σ p := by
  rw [← realize_transvection_ovl h2 hab]
  exact ⟨_, ⟨transvection_rev_mem_unitarySL_ovl h2 hab hba hs,
    LinearPilot.transvection_mem_blockSpecialLinear hab ha hb s⟩, rfl⟩

theorem twistedE6PairX_mem_ovlGroup (h2 : (2 : K) = 0) {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    (p : Fin 3) {a b : Fin 6} (hab : a ≠ b) (ha : a ∈ ovlSet p) (hb : b ∈ ovlSet p) (s : K) :
    twistedE6PairX σ (matRoot a b) s ∈ ovlGroup h2 σ p := by
  have hab' : Fin.rev b ≠ Fin.rev a := fun h => hab (Fin.rev_injective h).symm
  have hSrev := (ovl_check p).2.2.2.2.1
  rw [twistedE6PairX, (rho_matRoot_check_ovl a b).1, ← realize_transvection_ovl h2 hab,
    ← realize_transvection_ovl h2 hab', ← map_mul]
  exact ⟨_, ⟨transvection_mul_rev_mem_unitarySL_ovl h2 hσσ hab s,
    mul_mem (LinearPilot.transvection_mem_blockSpecialLinear hab ha hb s)
      (LinearPilot.transvection_mem_blockSpecialLinear hab' (hSrev b hb) (hSrev a ha) (σ s))⟩,
    rfl⟩

end Overlap

section Main

theorem perfectCore_su6Levi_inf_centralizer_eq_ovlGroup {k K : Type} [Field k] [Field K]
    [Algebra k K] (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (p : Fin 3) {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (hYJ : Y ≤ TwistedE6Pilot.rootRankOneGroup (algebraMap k K)
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))))
    (hY : Nat.card Y = 3) :
    perfectCore (su6Levi σ ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K))) =
      ovlGroup (two_eq_zero_of_card_sq le_rfl hK) σ p := by
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  apply le_antisymm
  · have hP := perfectCore_perfect (su6Levi σ ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K)))
    have hPD := (perfectCore_le _).trans
      (inf_le_left (a := su6Levi σ) (b := centralizer (Y : Set (ModGL TwistTag.E6.tag K))))
    have hPY := (perfectCore_le _).trans
      (inf_le_right (a := su6Levi σ) (b := centralizer (Y : Set (ModGL TwistTag.E6.tag K))))
    exact perfect_le_ovlGroup hK _ hσ p (algebraMap k K) hPD
      (le_centralizer_rootRankOneGroup_of_perfect hk hK hσ p hYJ hY hPD hPY hP) hP
  · refine le_perfectCore_of_perfect (le_inf (ovlGroup_le_su6Levi hK _ hσ p) ?_)
      (ovlGroup_perfect hK _ hσ p)
    exact (ovlGroup_le_centralizer_rootRankOneGroup _ σ p (algebraMap k K)).trans
      (centralizer_le hYJ)

theorem twistedE6TwoOverlapFacts_holds : TwistedE6TwoOverlapFacts := by
  intro k K _ _ _ hk hK σ hσ δ hδ Y hYJ hY
  obtain ⟨p, rfl⟩ := exists_eq_matRoot_of_mem_perpFixedRoots hδ
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  rw [perfectCore_su6Levi_inf_centralizer_eq_ovlGroup hk hK hσ p hYJ hY]
  refine ⟨isSimpleGroup_ovlGroup hK _ hσ p, fun β hβ hθβ hδβ => ?_⟩
  obtain ⟨a, b, hab, ha, hb, rfl⟩ := perp_roots_check_ovl p β (mem_rootFinset.2 hβ) hθβ hδβ
  refine ⟨fun hρ s hs => ?_, fun _ s => twistedE6PairX_mem_ovlGroup _ hσσ p hab ha hb s⟩
  have hba : b = Fin.rev a := ((rho_matRoot_check_ovl a b).2 hab).1 (by
    rw [← (rho_matRoot_check_ovl a b).1]
    exact hρ)
  exact pinnedX_mem_ovlGroup _ p hab ha hb hba hs

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
