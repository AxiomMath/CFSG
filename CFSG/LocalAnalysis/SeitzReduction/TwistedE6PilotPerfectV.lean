module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectVBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

local instance twistedE6PilotPerfectVNeZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩


section Roots

@[expose] def vRootP3 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 0, 1, 1, 0]

@[expose] def vRootP2 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 0, 1, 1, 1]

@[expose] def vRootF1 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 1, 1, 1, 0]

@[expose] def vRootA2 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 0, 0, 0, 0]

@[expose] def vRootA2n : Fin TwistTag.E6.tag.rank → ℤ := ![0, -1, 0, 0, 0, 0]

theorem vCommutator_check1 :
    vRootP3 + permLattice TwistTag.E6.perm vRootD2 = vRootS1 ∧
    vRootP2 + vRootD1 = vRootS2 ∧
    vRootF1 + permLattice TwistTag.E6.perm vRootD1 = perfRoot011221 ∧
    permLattice TwistTag.E6.perm vRootD1 + (vRootF1 + permLattice TwistTag.E6.perm
      (permLattice TwistTag.E6.perm vRootD1)) = e6HighestRoot ∧
    vRootB2 + vRootP3 = twistedE6ClassRootU ∧
    vRootP3 + (vRootB2 + permLattice TwistTag.E6.perm vRootP3) = e6HighestRoot ∧
    Pi.single 1 1 = vRootA2 ∧
    -Pi.single 1 1 = vRootA2n ∧
    vRootA2 ∈ vFixedRoots ∧
    vRootA2n ∈ vFixedRoots ∧
    vRootF1 ∈ vFixedRoots ∧
    vRootB2 ∈ vFixedRoots := by
  decide +kernel

theorem vCommutator_check2 :
    e6HighestRoot ∈ vFixedRoots ∧
    vRootP3 ∈ vPairRoots ∧
    vRootP2 ∈ vPairRoots ∧
    vRootD1 ∈ vPairRoots ∧
    vRootD2 ∈ vPairRoots ∧
    GoodExp (vExp1 e6HighestRoot) ∧
    permLattice TwistTag.E6.perm vRootF1 = vRootF1 ∧
    permLattice TwistTag.E6.perm vRootB2 = vRootB2 ∧
    vRootP3 ≠ permLattice TwistTag.E6.perm vRootD2 ∧
    vRootP2 ≠ vRootD1 ∧
    vRootP3 + permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm vRootD2) ≠ 0 ∧
    vRootP3 ≠ permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm vRootD2) := by
  decide +kernel

theorem vCommutator_check3 :
    vRootP3 + permLattice TwistTag.E6.perm vRootD2 ≠ -vRootP3 ∧
    vRootP3 + permLattice TwistTag.E6.perm vRootD2 ≠ -permLattice TwistTag.E6.perm vRootD2 ∧
    vRootP2 + permLattice TwistTag.E6.perm vRootD1 ≠ 0 ∧
    vRootP2 ≠ permLattice TwistTag.E6.perm vRootD1 ∧
    vRootP2 + vRootD1 ≠ -vRootP2 ∧
    vRootP2 + vRootD1 ≠ -vRootD1 ∧
    vRootF1 ≠ permLattice TwistTag.E6.perm vRootD1 ∧
    vRootF1 ≠ permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm vRootD1) ∧
    permLattice TwistTag.E6.perm vRootD1 ≠
      vRootF1 + permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm vRootD1) ∧
    e6HighestRoot + (vRootF1 + permLattice TwistTag.E6.perm
      (permLattice TwistTag.E6.perm vRootD1)) ≠ 0 ∧
    vRootB2 ≠ vRootP3 ∧
    vRootB2 ≠ permLattice TwistTag.E6.perm vRootP3 := by
  decide +kernel

theorem vCommutator_check4 :
    vRootP3 ≠ vRootB2 + permLattice TwistTag.E6.perm vRootP3 ∧
    e6HighestRoot + (vRootB2 + permLattice TwistTag.E6.perm vRootP3) ≠ 0 ∧
    twistedE6TwoRootB vRootP3 = true ∧
    twistedE6TwoRootB vRootP2 = true ∧
    twistedE6TwoRootB vRootF1 = true ∧
    twistedE6TwoRootB vRootB2 = true ∧
    twistedE6TwoRootB (permLattice TwistTag.E6.perm vRootD2) = true ∧
    twistedE6TwoRootB (permLattice TwistTag.E6.perm vRootD1) = true ∧
    twistedE6TwoRootB vRootD1 = true ∧
    twistedE6TwoRootB vRootS1 = true ∧
    twistedE6TwoRootB vRootS2 = true ∧
    twistedE6TwoRootB perfRoot011221 = true := by
  decide +kernel

theorem vCommutator_check5 :
    twistedE6TwoRootB twistedE6ClassRootU = true ∧
    twistedE6TwoRootB e6HighestRoot = true ∧
    twistedE6TwoRootB (vRootP3 + permLattice TwistTag.E6.perm
      (permLattice TwistTag.E6.perm vRootD2)) = false ∧
    twistedE6TwoRootB (vRootP3 + permLattice TwistTag.E6.perm vRootD2 + vRootP3) = false ∧
    twistedE6TwoRootB (vRootP3 + permLattice TwistTag.E6.perm vRootD2 +
      permLattice TwistTag.E6.perm vRootD2) = false ∧
    twistedE6TwoRootB (vRootP2 + permLattice TwistTag.E6.perm vRootD1) = false ∧
    twistedE6TwoRootB (vRootP2 + vRootD1 + vRootP2) = false ∧
    twistedE6TwoRootB (vRootP2 + vRootD1 + vRootD1) = false ∧
    twistedE6TwoRootB (e6HighestRoot + (vRootF1 + permLattice TwistTag.E6.perm
      (permLattice TwistTag.E6.perm vRootD1))) = false ∧
    twistedE6TwoRootB (e6HighestRoot + (vRootB2 + permLattice TwistTag.E6.perm vRootP3)) = false ∧
    permLattice TwistTag.E6.perm vRootS1 = vRootS1 ∧
    permLattice TwistTag.E6.perm vRootS2 = vRootS2 := by
  decide +kernel


end Roots

section Perfect

variable {K : Type} [Field K]

@[expose] noncomputable def vPerfect (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  closure ({g | ∃ α ∈ vFixedRoots, ∃ c : K, σ c = c ∧ g = pinnedX TwistTag.E6.tag K α c} ∪
    {g | ∃ α ∈ vPairRoots, ∃ s : K, g = twistedE6PairX σ α s})

theorem pinnedX_mem_vPerfect {σ : K →+* K} {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ vFixedRoots) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.E6.tag K α c ∈ vPerfect σ :=
  subset_closure (Or.inl ⟨α, hα, c, hc, rfl⟩)

theorem twistedE6PairX_mem_vPerfect {σ : K →+* K} {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ vPairRoots) (s : K) : twistedE6PairX σ α s ∈ vPerfect σ :=
  subset_closure (Or.inr ⟨α, hα, s, rfl⟩)

theorem twistedE6PairX_permLattice_mem_vPerfect {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ vPairRoots) (s : K) :
    twistedE6PairX σ (permLattice TwistTag.E6.perm α) s ∈ vPerfect σ := by
  have hr : IsRoot TwistTag.E6.tag α := by
    rw [isRoot_iff_twistedE6TwoRootB]; exact (vPairRoots_check α hα).1
  rw [twistedE6PairX_permLattice hσσ hr]
  exact twistedE6PairX_mem_vPerfect hα _

theorem vPerfect_le_C0 [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) :
    vPerfect σ ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  refine (closure_le _).2 ?_
  rintro g (⟨α, hα, c, hc, rfl⟩ | ⟨α, hα, s, rfl⟩)
  · obtain ⟨hr, hρ, -⟩ := vFixedRoots_check α hα
    exact pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_iff_twistedE6TwoRootB.2 hr) hρ hc
  · obtain ⟨hr, -, -, -⟩ := vPairRoots_check α hα
    exact twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_iff_twistedE6TwoRootB.2 hr) s

theorem twistedE6ClassV_eq_list_prod :
    twistedE6ClassV K = (vReprRoots.map fun ε => pinnedX TwistTag.E6.tag K ε 1).prod := by
  simp only [vReprRoots, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    twistedE6ClassV, mul_assoc]

theorem vPerfect_le_centralizer {σ : K →+* K} :
    vPerfect σ ≤ centralizer ({twistedE6ClassV K} : Set (ModGL TwistTag.E6.tag K)) := by
  have hR : ∀ ε ∈ vReprRoots, IsRoot TwistTag.E6.tag ε := by
    intro ε hε
    rw [isRoot_iff_twistedE6TwoRootB]
    revert ε
    decide +kernel
  refine (closure_le _).2 ?_
  rintro g (⟨α, hα, c, hc, rfl⟩ | ⟨α, hα, s, rfl⟩)
  · obtain ⟨hr, -, hcen⟩ := vFixedRoots_check α hα
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, twistedE6ClassV_eq_list_prod]
    exact (commute_pinnedX_list_prod_of_centralB hR (isRoot_iff_twistedE6TwoRootB.2 hr) hcen c).eq
  · obtain ⟨hr, -, hcen, hcen'⟩ := vPairRoots_check α hα
    have hr' : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
      (isRoot_iff_twistedE6TwoRootB.2 hr).permLattice TwistTag.E6.cartan_perm
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, twistedE6ClassV_eq_list_prod]
    unfold twistedE6PairX
    exact ((commute_pinnedX_list_prod_of_centralB hR (isRoot_iff_twistedE6TwoRootB.2 hr) hcen
      s).mul_left (commute_pinnedX_list_prod_of_centralB hR hr' hcen' (σ s))).eq

theorem twistedE6ClassV_mem_vPerfect (σ : K →+* K) : twistedE6ClassV K ∈ vPerfect σ := by
  rw [twistedE6ClassV_eq_twistedE6PairX σ]
  exact mul_mem (twistedE6PairX_mem_vPerfect (by decide) 1)
    (pinnedX_mem_vPerfect (by decide) (map_one σ))

end Perfect

section Core

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem isRoot_of_twistedE6TwoRootB {α : Fin TwistTag.E6.tag.rank → ℤ}
    (h : twistedE6TwoRootB α = true) : IsRoot TwistTag.E6.tag α :=
  isRoot_iff_twistedE6TwoRootB.2 h

theorem vPerfect_le_commutator [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    vPerfect σ ≤ ⁅vPerfect σ, vPerfect σ⁆ := by
  have hf1 : 1 ≤ f := by omega
  have := finite_of_card hK
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hσσ : ∀ x, σ (σ x) = x := apply_apply_eq hK hσ
  have hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range (algebraMap k K) := sigma_eq_self_iff hk hσ
  set P := vPerfect σ with hP
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a, ha⟩ := exists_units_ne_one_of_four_le h4
  set l : Kˣ := Units.map (algebraMap k K).toMonoidHom a with hl
  have hl1 : l ≠ 1 := by
    intro h
    apply ha
    apply Units.ext
    apply (algebraMap k K).injective
    have := congrArg Units.val h
    simpa [hl] using this
  have hlσ0 : σ (l : K) = l := (hfix _).2 ⟨_, rfl⟩
  have hlσ : Units.map σ.toMonoidHom l = l := Units.ext hlσ0
  have hliσ : σ ((l⁻¹ : Kˣ) : K) = ((l⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hlσ0]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := vCommutator_check1
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12⟩ := vCommutator_check2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := vCommutator_check3
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := vCommutator_check4
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := vCommutator_check5
  set b : Fin TwistTag.E6.tag.rank → Kˣ := fun j => l ^ TwistTag.E6.tag.cartan 1 j with hb
  have hX : ∀ c : K, σ c = c → xUnit TwistTag.E6.tag K 1 c ∈ P := fun c hc => by
    rw [← pinnedX_single, c7]
    exact pinnedX_mem_vPerfect c9 hc
  have hY : ∀ c : K, σ c = c → yUnit TwistTag.E6.tag K 1 c ∈ P := fun c hc => by
    rw [← pinnedX_neg_single, c8]
    exact pinnedX_mem_vPerfect c10 hc
  have hdP : rootDiagUnit TwistTag.E6.tag b ∈ P := by
    rw [hb, ← torusElt_eq_rootDiagUnit, torusElt, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul,
      CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    have h1' : σ ((-1 : Kˣ) : K) = ((-1 : Kˣ) : K) := by simp
    have h1'' : σ (-(((-1 : Kˣ)⁻¹ : Kˣ) : K)) = -(((-1 : Kˣ)⁻¹ : Kˣ) : K) := by simp
    have hl' : σ (-((l⁻¹ : Kˣ) : K)) = -((l⁻¹ : Kˣ) : K) := by rw [map_neg, hliσ]
    exact mul_mem (mul_mem (mul_mem (hX _ hlσ0) (hY _ hl')) (hX _ hlσ0))
      (mul_mem (mul_mem (hX _ h1') (hY _ h1'')) (hX _ h1'))
  have hchar : ∀ α, rootChar b α = l ^ vExp1 α := fun α => rootChar_cartanRow 1 l α
  have hcharσ : ∀ α, σ (rootChar b α : K) = rootChar b α := fun α => by
    rw [hchar]
    have := congrArg Units.val (show Units.map σ.toMonoidHom (l ^ vExp1 α) = l ^ vExp1 α by
      rw [map_zpow, hlσ])
    simpa using this
  have hfixed : ∀ α ∈ vFixedRoots, GoodExp (vExp1 α) → ∀ c : K, σ c = c →
      pinnedX TwistTag.E6.tag K α c ∈ ⁅P, P⁆ := by
    intro α hα hg c hc
    have hr := isRoot_of_twistedE6TwoRootB (vFixedRoots_check α hα).1
    have hbα : rootChar b α ≠ 1 := by rw [hchar]; exact zpow_ne_one_of_goodExp hl1 hg
    rw [pinnedX_eq_rootDiagUnit_conj hr hbα c, ← commutatorElement_def]
    refine commutator_mem_commutator hdP (pinnedX_mem_vPerfect hα ?_)
    rw [map_mul, map_inv₀, map_sub, map_one, hcharσ, hc]
  have hpair : ∀ α ∈ vPairRoots, GoodExp (vExp1 α) → ∀ s : K,
      twistedE6PairX σ α s ∈ ⁅P, P⁆ := by
    intro α hα hg s
    have hr := isRoot_of_twistedE6TwoRootB (vPairRoots_check α hα).1
    have hbα : rootChar b α ≠ 1 := by rw [hchar]; exact zpow_ne_one_of_goodExp hl1 hg
    have hbρ : rootChar b (permLattice TwistTag.E6.perm α) =
        Units.map σ.toMonoidHom (rootChar b α) := by
      apply Units.ext
      rw [Units.coe_map]
      change _ = σ (rootChar b α : K)
      rw [hcharσ, hchar, hchar, vExp1, vExp1, coPair_permLattice_twistedE6,
        show TwistTag.E6.perm 1 = 1 by decide]
    rw [twistedE6PairX_eq_rootDiagUnit_conj σ hr hbα hbρ s, ← commutatorElement_def]
    exact commutator_mem_commutator hdP (twistedE6PairX_mem_vPerfect hα _)
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨t₀, ht₀⟩ := exists_twistedE6_add_sigma_eq_one hf1 hK (σ := σE) (fun c => hσ c)
  have htr : ∀ c : K, σE.toRingHom c = c →
      ∃ s : K, s * 1 + σE.toRingHom (s * 1) = c := fun c hc => by
    refine ⟨c * t₀, ?_⟩
    rw [mul_one, map_mul, hc]
    change c * t₀ + c * σE t₀ = c
    rw [← mul_add, ht₀, mul_one]
  have hcomm : ∀ x y : ModGL TwistTag.E6.tag K, x ∈ P → y ∈ P → ⁅x, y⁆ ∈ ⁅P, P⁆ :=
    fun x y hx hy => commutator_mem_commutator hx hy
  have hθ : ∀ s : K, (pinnedX TwistTag.E6.tag K e6HighestRoot (s * σE.toRingHom s))⁻¹ ∈ ⁅P, P⁆ :=
    fun s => inv_mem (hfixed _ d1 d6 _ (by rw [map_mul, hσσ, mul_comm]))
  have R : ∀ {α : Fin TwistTag.E6.tag.rank → ℤ}, twistedE6TwoRootB α = true →
      IsRoot TwistTag.E6.tag α := fun h => isRoot_of_twistedE6TwoRootB h
  have N : ∀ {α : Fin TwistTag.E6.tag.rank → ℤ}, twistedE6TwoRootB α = false →
      ¬IsRoot TwistTag.E6.tag α := fun h => not_isRoot_of_twistedE6TwoRootB h
  refine (closure_le _).2 ?_
  rintro g (⟨α, hα, c, hc, rfl⟩ | ⟨α, hα, s, rfl⟩)
  · rcases vTorusCheck.1 α hα with hg | rfl | rfl | rfl
    · exact hfixed α hα hg c hc
    ·
      obtain ⟨s, hs⟩ := htr c hc
      have e := commutator_twistedE6PairX σE.toRingHom (R g3) (R g7) (by rw [c1]; exact R g10)
        (by rw [c1]; exact h11) d9 (N h3) d11 d12 (N h4) (N h5) e1 e2 s 1
      rw [c1, hs] at e
      rw [← e]
      exact hcomm _ _ (twistedE6PairX_mem_vPerfect d2 s)
        (twistedE6PairX_permLattice_mem_vPerfect hσσ d5 1)
    ·
      obtain ⟨s, hs⟩ := htr c hc
      have e := commutator_twistedE6PairX σE.toRingHom (R g4) (R g9) (by rw [c2]; exact R g11)
        (by rw [c2]; exact h12) d10 (N h6) e3 e4 (N h7) (N h8) e5 e6 s 1
      rw [c2, hs] at e
      rw [← e]
      exact hcomm _ _ (twistedE6PairX_mem_vPerfect d3 s) (twistedE6PairX_mem_vPerfect d4 1)
    ·
      obtain ⟨hsum, hB1, hB2, -, hne, -⟩ := vCommutator_check
      have e := commutator_pinnedX_of_isRoot_add_E6 (K := K)
        (R (vFixedRoots_check _ hB1).1) (R (vFixedRoots_check _ hB2).1) hne
        (by rw [hsum]; exact R (vFixedRoots_check _ (by decide)).1) c 1
      rw [hsum, mul_one] at e
      rw [← e]
      exact hcomm _ _ (pinnedX_mem_vPerfect hB1 hc) (pinnedX_mem_vPerfect hB2 (map_one _))
  · rcases vTorusCheck.2 α hα with hg | rfl | rfl | rfl
    · exact hpair α hα hg s
    ·
      obtain ⟨-, -, -, -, -, hsum, hD1, hD2, hA, hne, k1, k1', k2, k2', k3, k3', -⟩ :=
        vCommutator_check
      have e := commutator_twistedE6PairX_pairSum σE.toRingHom
        (R (vPairRoots_check _ hD1).1) (R (vPairRoots_check _ hD2).1)
        (by rw [hsum]; exact R (vPairRoots_check _ hA).1) hne (N k1) k1' (N k2) k2' (N k3) k3' s 1
      rw [hsum, mul_one] at e
      rw [← e]
      exact hcomm _ _ (twistedE6PairX_mem_vPerfect hD1 s) (twistedE6PairX_mem_vPerfect hD2 1)
    ·
      have e := commutator_pinnedX_twistedE6PairX_of_fixed σE.toRingHom (R g5) d7 (R g8)
        (by rw [c3]; exact R g12) (by rw [c4]; exact R h2) e7 e8 e9 (by rw [c4]; exact N h9)
        (by rw [c4]; exact e10) (map_one _) s
      rw [c3, c4, one_mul, one_mul] at e
      have e' : twistedE6PairX σE.toRingHom perfRoot011221 s =
          ⁅pinnedX TwistTag.E6.tag K vRootF1 1,
            twistedE6PairX σE.toRingHom (permLattice TwistTag.E6.perm vRootD1) s⁆ *
          (pinnedX TwistTag.E6.tag K e6HighestRoot (s * σE.toRingHom s))⁻¹ := by
        rw [e, mul_inv_cancel_right]
      rw [e']
      exact mul_mem (hcomm _ _ (pinnedX_mem_vPerfect c11 (map_one _))
        (twistedE6PairX_permLattice_mem_vPerfect hσσ d4 s)) (hθ s)
    ·
      have e := commutator_pinnedX_twistedE6PairX_of_fixed σE.toRingHom (R g6) d8 (R g3)
        (by rw [c5]; exact R h1) (by rw [c6]; exact R h2) e11 e12 g1 (by rw [c6]; exact N h10)
        (by rw [c6]; exact g2) (map_one _) s
      rw [c5, c6, one_mul, one_mul] at e
      have e' : twistedE6PairX σE.toRingHom twistedE6ClassRootU s =
          ⁅pinnedX TwistTag.E6.tag K vRootB2 1, twistedE6PairX σE.toRingHom vRootP3 s⁆ *
          (pinnedX TwistTag.E6.tag K e6HighestRoot (s * σE.toRingHom s))⁻¹ := by
        rw [e, mul_inv_cancel_right]
      rw [e']
      exact mul_mem (hcomm _ _ (pinnedX_mem_vPerfect c12 (map_one _))
        (twistedE6PairX_mem_vPerfect d2 s)) (hθ s)

theorem commutator_vPerfect [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅vPerfect σ, vPerfect σ⁆ = vPerfect σ := by
  refine le_antisymm ?_ (vPerfect_le_commutator hf hk hK hσ)
  rw [commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem exists_perfect_le_centralizer_classV [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ P : Subgroup (graphFixedRootGroup TwistTag.E6 K σ), ⁅P, P⁆ = P ∧
      (⟨twistedE6ClassV K, twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩ :
        graphFixedRootGroup TwistTag.E6 K σ) ∈ P ∧
      P ≤ centralizer ({⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩} :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have hPC := vPerfect_le_C0 (apply_apply_eq hK hσ)
  refine ⟨(vPerfect σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), ?_,
    mem_subgroupOf.2 (twistedE6ClassV_mem_vPerfect σ), fun x hx => ?_⟩
  · apply map_injective (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hPC,
      commutator_vPerfect hf hk hK hσ]
  · rw [mem_centralizer_subtype_iff]
    exact vPerfect_le_centralizer (mem_subgroupOf.1 hx)

end Core

end CFSG.SeitzReduction.TwistedE6Pilot
