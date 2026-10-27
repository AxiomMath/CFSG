module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNative
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameRoots
public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral
public import CFSG.LieType.Chevalley.SimpleRootSubgroupStructure
public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSymplectic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TreeGen
public import CFSG.Sporadic.Th.Max3.Core

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts
open CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.LieType.Chevalley.RootSpace CFSG.LieType.Steinberg.Adjoint
open CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Steinberg.Isogeny
open scoped MatrixGroups


theorem j_le_l7 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) : J β ≤ L7 := by
  change rootRankOneGroup .E7 (ZMod 2) β ≤ adjointGroup .E7 (ZMod 2)
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) hβ]
  exact sup_le (rootSubgroup_le_adjointGroup β) (rootSubgroup_le_adjointGroup (-β))

theorem j_le_centralizer_of_orthogonal {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (h0 : iform α β = 0) :
    J α ≤ Subgroup.centralizer (J β : Set (ModGL .E7 (ZMod 2))) := by
  have hroot : ∀ {γ δ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ → IsRoot .E7 δ →
      iform γ δ = 0 → rootSubgroup .E7 (ZMod 2) γ ≤
        Subgroup.centralizer (rootSubgroup .E7 (ZMod 2) δ : Set (ModGL .E7 (ZMod 2))) := by
    intro γ δ hγ hδ horth x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact (CFSG.SeitzReduction.EPilot.commute_of_iform_eq_zero
      (Or.inr (Or.inl rfl)) hγ hδ horth hx hy).eq.symm
  change rootRankOneGroup .E7 (ZMod 2) α ≤
    Subgroup.centralizer (rootRankOneGroup .E7 (ZMod 2) β : Set (ModGL .E7 (ZMod 2)))
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) hα, rootRankOneGroup_eq_sup (K := ZMod 2) hβ,
    Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    refine sup_le (hroot hα hβ h0) (hroot (IsRoot.neg hα) hβ ?_)
    simpa only [iform_neg_left, neg_zero] using congrArg Neg.neg h0
  · rw [Subgroup.le_centralizer_iff]
    refine sup_le (hroot hα (IsRoot.neg hβ) ?_) (hroot (IsRoot.neg hα) (IsRoot.neg hβ) ?_)
    · simpa only [iform_neg_right, neg_zero] using congrArg Neg.neg h0
    · simpa only [iform_neg_left, iform_neg_right, neg_neg] using h0

theorem jn_le_l7 (i : Fin 7) : Jn i ≤ L7 := j_le_l7 (isRoot_single .E7 i)

theorem iSup_jn_eq_l7 : ⨆ i, Jn i = L7 := by
  have hgen := congrArg (fun H : Subgroup L7 => H.map L7.subtype)
    (iSup_simplePosSubgroup_sup_simpleNegSubgroup (τ := .E7) (K := ZMod 2))
  rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype] at hgen
  have hmap : ∀ i : Fin (Tag.rank .E7),
      (simplePosSubgroup .E7 (ZMod 2) i ⊔ simpleNegSubgroup .E7 (ZMod 2) i).map L7.subtype =
        rootRankOneGroup .E7 (ZMod 2) (Pi.single i 1) := by
    intro i
    rw [Subgroup.map_sup, ← subgroupOf_rootSubgroup_single, ← subgroupOf_rootSubgroup_neg_single,
      Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup _),
      Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup _)]
    exact (rootRankOneGroup_eq_sup (K := ZMod 2) (isRoot_single .E7 i)).symm
  change (⨆ i : Fin (Tag.rank .E7), rootRankOneGroup .E7 (ZMod 2) (Pi.single i 1)) = L7
  simpa only [hmap] using hgen

theorem e7NatFrame_holds : E7NatFrame := by
  refine ⟨jn_le_l7, ?_, ?_, ?_⟩
  · intro i j hij h1 h2 a ha c hc
    have horth : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 8 i.castSucc j.castSucc →
        ¬ edgeE 8 j.castSucc i.castSucc → iform (τ := .E7) (Pi.single i 1) (Pi.single j 1) = 0 := by
      decide +kernel
    exact (Subgroup.mem_centralizer_iff.mp
      (j_le_centralizer_of_orthogonal (isRoot_single .E7 i) (isRoot_single .E7 j)
        (horth i j hij h1 h2) ha) c hc).symm
  · intro i j hij
    apply E7FrameRoots.native_linearPair_of_roots (ZMod 2) (isRoot_single .E7 i) (isRoot_single .E7 j)
    right
    have hedge : ∀ i j : Fin 7, edgeE 8 i.castSucc j.castSucc →
        iform (τ := .E7) (Pi.single i 1) (Pi.single j 1) = -1 := by decide +kernel
    exact hedge i j hij
  · intro H hH
    rw [← iSup_jn_eq_l7]
    exact iSup_le hH

theorem mu_eq_neg_sixStarRoot : mu = -E7FrameRoots.sixStarRoot := by decide +kernel

theorem lam_eq_neg_starTwoRoot : lam = -E7FrameRoots.starTwoRoot := by decide +kernel

theorem theta_eq_thetaE7 : theta = thetaE7 := by
  rw [E7Model.thetaE7_eq]
  rfl

theorem isRoot_mu : IsRoot .E7 mu := by
  rw [mu_eq_neg_sixStarRoot]
  exact IsRoot.neg (mem_rootFinset.mp E7FrameRoots.mem_rootFinset_sixStarRoot)

theorem isRoot_lam : IsRoot .E7 lam := by
  rw [lam_eq_neg_starTwoRoot]
  exact IsRoot.neg E7FrameRoots.isRoot_starTwoRoot

theorem isRoot_theta : IsRoot .E7 theta := by
  rw [theta_eq_thetaE7]
  exact isRoot_thetaE7

theorem native_linearPair_mu_theta :
    ∃ W, LinearBlockStandardPair (ZMod 2) W (J mu) (J theta) := by
  apply E7FrameRoots.native_linearPair_of_roots (ZMod 2) isRoot_mu isRoot_theta
  left
  rw [mu_eq_neg_sixStarRoot, theta_eq_thetaE7, E7Model.thetaE7_eq, iform_neg_left]
  change -iform (τ := .E7) E7FrameRoots.sixStarRoot
    (![2, 2, 3, 4, 3, 2, 1] : Fin (Tag.rank .E7) → ℤ) = 1
  rw [E7FrameRoots.corrected_auxiliary_root_pairings.2.2]
  rfl

theorem commute_j_theta_jn (i : Fin 7) (hi : i ≠ 0) :
    ∀ a ∈ J theta, ∀ c ∈ Jn i, a * c = c * a := by
  have H : ∀ i : Fin 7, i ≠ 0 → iform theta (Pi.single i 1) = 0 := by decide +kernel
  have horth := H i hi
  intro a ha c hc
  exact (Subgroup.mem_centralizer_iff.mp
    (j_le_centralizer_of_orthogonal isRoot_theta (isRoot_single .E7 i) horth ha) c hc).symm

theorem j_le_m0 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (h0 : iform β (Pi.single (0 : Fin 7) 1) = 0) : J β ≤ M0 :=
  le_inf (j_le_l7 hβ)
    (j_le_centralizer_of_orthogonal hβ (isRoot_single .E7 0) h0)

theorem jn_le_m0 (i : Fin 7) (hi0 : i ≠ 0) (hi2 : i ≠ 2) : Jn i ≤ M0 := by
  apply j_le_m0 (isRoot_single .E7 i)
  have H : ∀ i : Fin 7, i ≠ 0 → i ≠ 2 →
      iform (τ := .E7) (Pi.single i 1) (Pi.single (0 : Fin 7) 1) = 0 := by decide +kernel
  exact H i hi0 hi2

theorem j_mu_le_m0 : J mu ≤ M0 := j_le_m0 isRoot_mu (by decide +kernel)

theorem j_lam_le_m0 : J lam ≤ M0 := j_le_m0 isRoot_lam (by decide +kernel)

theorem e7NatWeyl_holds : E7NatWeyl := by
  obtain ⟨w0, hw0, h0⟩ := E7Model.exists_conj_rankOne_to_theta (F := ZMod 2)
    (isRoot_single .E7 (⟨0, by decide⟩ : Fin (Tag.rank .E7)))
  rw [← theta_eq_thetaE7] at h0
  change conjSub w0 (Jn 0) = J theta at h0
  constructor
  · refine ⟨w0⁻¹, inv_mem hw0, ?_⟩
    change conjSub w0⁻¹ (J theta) = Jn 0
    rw [← h0, conjSub_inv_conjSub]
  · obtain ⟨w6, hw6, h6⟩ := E7Model.exists_conj_rankOne_to_theta (F := ZMod 2)
      (isRoot_single .E7 (⟨6, by decide⟩ : Fin (Tag.rank .E7)))
    rw [← theta_eq_thetaE7] at h6
    change conjSub w6 (Jn 6) = J theta at h6
    refine ⟨w6⁻¹ * w0, mul_mem (inv_mem hw6) hw0, ?_⟩
    change conjSub (w6⁻¹ * w0) (Jn 0) = Jn 6
    rw [conjSub_mul, h0, ← h6, conjSub_inv_conjSub]

theorem rootSubgroup_le_centralizer_of_map_eq
    {γ : Fin (Tag.rank .E7) → ℤ} {m : ModGL .E7 (ZMod 2)}
    (hmap : (rootSubgroup .E7 (ZMod 2) γ).map (MulAut.conj m).toMonoidHom =
      rootSubgroup .E7 (ZMod 2) γ) :
    rootSubgroup .E7 (ZMod 2) γ ≤ Subgroup.centralizer ({m} : Set (ModGL .E7 (ZMod 2))) := by
  let P := rootSubgroup .E7 (ZMod 2) γ
  have hcard : Nat.card P = 2 := (card_rootSubgroup γ).trans (by simp)
  let : Finite P := Nat.finite_of_card_ne_zero (by omega)
  let : MulDistribMulAction (Subgroup.normalizer (P : Set (ModGL .E7 (ZMod 2)))) P :=
    MulDistribMulAction.compHom P P.normalizerMonoidHom
  have hm : m ∈ Subgroup.normalizer (P : Set (ModGL .E7 (ZMod 2))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  intro x hx
  have hfixed := CFSG.PreuniquenessRankFour.Helpers.prime_card_two_group_action_trivial hcard
    (⟨m, hm⟩ : Subgroup.normalizer (P : Set (ModGL .E7 (ZMod 2)))) (⟨x, hx⟩ : P)
  have heq := congrArg Subtype.val hfixed
  change m * x * m⁻¹ = x at heq
  apply Subgroup.mem_centralizer_iff.mpr
  rintro y (rfl : y = m)
  exact (mul_inv_eq_iff_eq_mul.mp heq)

theorem exists_m0_conj_theta :
    ∃ m ∈ M0, (J theta).map (MulAut.conj m).toMonoidHom =
      J (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E7)) 1 - theta) := by
  let α : Fin (Tag.rank .E7) → ℤ := Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E7)) 1
  let ω : List ℕ := [2, 0, 3, 1, 2, 3, 4, 3, 1, 2, 0, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 2]
  have h0 : E7Model.wordAct ω α = α := by
    apply E7Model.wordAct_eq_of_chainB ω [
    ![1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0]
  ]
    decide +kernel
  have ht : E7Model.wordAct ω theta = α - theta := by
    apply E7Model.wordAct_eq_of_chainB ω [
    ![2, 2, 3, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![1, 2, 3, 4, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 2, 2, 1],
    ![1, 1, 2, 3, 2, 2, 1],
    ![1, 1, 2, 3, 2, 2, 1],
    ![1, 1, 2, 3, 2, 2, 1],
    ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 2, 1, 1],
    ![1, 1, 1, 2, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, -1, -1, 0],
    ![0, 0, 0, -1, -1, -1, 0],
    ![0, -1, 0, -1, -1, -1, 0],
    ![0, -1, -1, -1, -1, -1, 0],
    ![-1, -1, -1, -1, -1, -1, 0],
    ![-1, -1, -1, -2, -1, -1, 0],
    ![-1, -1, -2, -2, -1, -1, 0],
    ![-1, -1, -2, -2, -2, -1, 0],
    ![-1, -1, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -2, -1, -1],
    ![-1, -2, -2, -3, -2, -2, -1],
    ![-1, -2, -2, -3, -3, -2, -1],
    ![-1, -2, -2, -4, -3, -2, -1],
    ![-1, -2, -3, -4, -3, -2, -1]
  ]
    decide +kernel
  obtain ⟨m, hmL, hm⟩ := E7FrameRoots.exists_conj_rootSubgroup_wordAct (ZMod 2) ω
  have hpos := hm α (isRoot_single .E7 (⟨0, by decide⟩ : Fin (Tag.rank .E7)))
  rw [h0] at hpos
  have hneg := hm (-α) (IsRoot.neg (isRoot_single .E7 (⟨0, by decide⟩ : Fin (Tag.rank .E7))))
  rw [E7Model.wordAct_neg, h0] at hneg
  have hcent : Jn 0 ≤ Subgroup.centralizer ({m} : Set (ModGL .E7 (ZMod 2))) := by
    change rootRankOneGroup .E7 (ZMod 2) α ≤ _
    rw [rootRankOneGroup_eq_sup (K := ZMod 2) (isRoot_single .E7 (⟨0, by decide⟩ : Fin (Tag.rank .E7)))]
    exact sup_le (rootSubgroup_le_centralizer_of_map_eq hpos)
      (rootSubgroup_le_centralizer_of_map_eq hneg)
  have hmC : m ∈ Subgroup.centralizer (Jn 0 : Set (ModGL .E7 (ZMod 2))) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hcent hx) m (by simp)).symm
  have hγ : IsRoot .E7 (α - theta) := ht ▸ E7Model.isRoot_wordAct ω isRoot_theta
  refine ⟨m, ⟨hmL, hmC⟩, ?_⟩
  have htpos := hm theta isRoot_theta
  have htneg := hm (-theta) (IsRoot.neg isRoot_theta)
  rw [ht] at htpos
  rw [E7Model.wordAct_neg, ht] at htneg
  change (rootRankOneGroup .E7 (ZMod 2) theta).map (MulAut.conj m).toMonoidHom =
    rootRankOneGroup .E7 (ZMod 2) (α - theta)
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_theta,
    rootRankOneGroup_eq_sup (K := ZMod 2) hγ, Subgroup.map_sup, htpos, htneg]

theorem jn_zero_le_closure_m0_conjugates :
    Jn 0 ≤ Subgroup.closure {y | ∃ m ∈ M0, ∃ x ∈ J theta, y = m * x * m⁻¹} := by
  let W := Subgroup.closure {y | ∃ m ∈ M0, ∃ x ∈ J theta, y = m * x * m⁻¹}
  let α : Fin (Tag.rank .E7) → ℤ := Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E7)) 1
  let γ := α - theta
  have hα : IsRoot .E7 α := isRoot_single .E7 (⟨0, by decide⟩ : Fin (Tag.rank .E7))
  have hγ : IsRoot .E7 γ := mem_rootFinset.mp (by decide +kernel)
  obtain ⟨m, hm, hmap⟩ := exists_m0_conj_theta
  change (J theta).map (MulAut.conj m).toMonoidHom = J γ at hmap
  have hJT : J theta ≤ W := by
    intro x hx
    apply Subgroup.subset_closure
    exact ⟨1, one_mem _, x, hx, by simp⟩
  have hJG : J γ ≤ W := by
    rw [← hmap]
    rintro y ⟨x, hx, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨m, hm, x, hx, by simp [MulAut.conj_apply]⟩
  have hsum : theta + γ = α := by
    change theta + (α - theta) = α
    abel
  have hnegSum : -theta + -γ = -α := by rw [← neg_add, hsum]
  change rootRankOneGroup .E7 (ZMod 2) theta ≤ W at hJT
  change rootRankOneGroup .E7 (ZMod 2) γ ≤ W at hJG
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_theta] at hJT
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) hγ] at hJG
  have hplus := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootSubgroup_add_le
    (Or.inr (Or.inr (Or.inl rfl))) W isRoot_theta hγ (by decide +kernel) (by decide +kernel)
    (by rw [hsum]; exact hα) (le_sup_left.trans hJT) (le_sup_left.trans hJG)
  have hminus := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.rootSubgroup_add_le
    (Or.inr (Or.inr (Or.inl rfl))) W (IsRoot.neg isRoot_theta) (IsRoot.neg hγ)
    (by decide +kernel) (by decide +kernel) (by rw [hnegSum]; exact IsRoot.neg hα)
    (le_sup_right.trans hJT) (le_sup_right.trans hJG)
  rw [hsum] at hplus
  rw [hnegSum] at hminus
  change rootRankOneGroup .E7 (ZMod 2) α ≤ W
  rw [rootRankOneGroup_eq_sup (K := ZMod 2) hα]
  exact sup_le hplus hminus

theorem e7NatHigh_holds : E7NatHigh := by
  refine ⟨commute_j_theta_jn, native_linearPair_mu_theta, ?_,
    j_le_l7 isRoot_theta, jn_le_m0, j_mu_le_m0, j_lam_le_m0⟩
  intro H hH
  apply jn_zero_le_closure_m0_conjugates.trans
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨m, hm, x, hx, rfl⟩
  exact hH m hm x hx

end CFSG.StandardType.FrameRoute.FS81.E7Frame
