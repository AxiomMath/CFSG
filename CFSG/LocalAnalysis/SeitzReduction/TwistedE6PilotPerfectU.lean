module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerU

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)
open scoped commutatorElement

local instance twistedE6PilotPerfectUNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotPerfectUNeZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Torus

variable {K : Type} [Field K]

theorem commute_xy_two_four (a b : K) :
    Commute (xUnit .E6 K 2 a) (xUnit .E6 K 4 b) ∧ Commute (yUnit .E6 K 2 a) (xUnit .E6 K 4 b) ∧
      Commute (xUnit .E6 K 2 a) (yUnit .E6 K 4 b) ∧
        Commute (yUnit .E6 K 2 a) (yUnit .E6 K 4 b) := by
  have h0 : iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 := by decide
  have r2 : IsRoot .E6 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 2
  have r4 : IsRoot .E6 (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := isRoot_single Tag.E6 4
  refine ⟨(commute_xUnit_two_four a b).1, ?_, ?_, (commute_xUnit_two_four a b).2⟩
  · rw [← pinnedX_neg_single, ← pinnedX_single]
    exact classD4_commute_pinnedX E6Pilot.e6_simplyLaced (IsRoot.neg r2) r4
      (by rw [iform_neg_left, h0]; norm_num) a b
  · rw [← pinnedX_single, ← pinnedX_neg_single]
    exact classD4_commute_pinnedX E6Pilot.e6_simplyLaced r2 (IsRoot.neg r4)
      (by rw [iform_neg_right, h0]; norm_num) a b

theorem commute_weylElt_two_four (s t : Kˣ) : Commute (weylElt .E6 K 2 s) (weylElt .E6 K 4 t) := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  have hx : ∀ a : K, Commute (xUnit .E6 K 2 a)
      (xUnit .E6 K 4 t * yUnit .E6 K 4 (-((t⁻¹ : Kˣ) : K)) * xUnit .E6 K 4 t) := fun a =>
    (((commute_xy_two_four a _).1.mul_right (commute_xy_two_four a _).2.2.1).mul_right
      (commute_xy_two_four a _).1)
  have hy : ∀ a : K, Commute (yUnit .E6 K 2 a)
      (xUnit .E6 K 4 t * yUnit .E6 K 4 (-((t⁻¹ : Kˣ) : K)) * xUnit .E6 K 4 t) := fun a =>
    (((commute_xy_two_four a _).2.1.mul_right (commute_xy_two_four a _).2.2.2).mul_right
      (commute_xy_two_four a _).2.1)
  exact ((hx _).mul_left (hy _)).mul_left (hx _)

theorem weylElt_two_mul_weylElt_four_mem_yLeviF4' (t : Kˣ) :
    weylElt .E6 K 2 t * weylElt .E6 K 4 t ∈ E6Pilot.yLeviF4 K := by
  have cXX : ∀ a b : K, Commute (xUnit .E6 K 2 a) (xUnit .E6 K 4 b) := fun a b =>
    (commute_xy_two_four a b).1
  have cYX : ∀ a b : K, Commute (yUnit .E6 K 2 a) (xUnit .E6 K 4 b) := fun a b =>
    (commute_xy_two_four a b).2.1
  have cXY : ∀ a b : K, Commute (xUnit .E6 K 2 a) (yUnit .E6 K 4 b) := fun a b =>
    (commute_xy_two_four a b).2.2.1
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  set u : K := -((t⁻¹ : Kˣ) : K)
  set c : K := (t : K)
  have e : xUnit .E6 K 2 c * yUnit .E6 K 2 u * xUnit .E6 K 2 c *
      (xUnit .E6 K 4 c * yUnit .E6 K 4 u * xUnit .E6 K 4 c) =
      xUnit .E6 K 2 c * xUnit .E6 K 4 c * (yUnit .E6 K 2 u * yUnit .E6 K 4 u) *
        (xUnit .E6 K 2 c * xUnit .E6 K 4 c) := by
    calc xUnit .E6 K 2 c * yUnit .E6 K 2 u * xUnit .E6 K 2 c *
          (xUnit .E6 K 4 c * yUnit .E6 K 4 u * xUnit .E6 K 4 c)
        = xUnit .E6 K 2 c * yUnit .E6 K 2 u * (xUnit .E6 K 2 c * xUnit .E6 K 4 c) *
          (yUnit .E6 K 4 u * xUnit .E6 K 4 c) := by group
      _ = xUnit .E6 K 2 c * yUnit .E6 K 2 u * (xUnit .E6 K 4 c * xUnit .E6 K 2 c) *
          (yUnit .E6 K 4 u * xUnit .E6 K 4 c) := by rw [(cXX c c).eq]
      _ = xUnit .E6 K 2 c * (yUnit .E6 K 2 u * xUnit .E6 K 4 c) *
          (xUnit .E6 K 2 c * yUnit .E6 K 4 u) * xUnit .E6 K 4 c := by group
      _ = xUnit .E6 K 2 c * (xUnit .E6 K 4 c * yUnit .E6 K 2 u) *
          (yUnit .E6 K 4 u * xUnit .E6 K 2 c) * xUnit .E6 K 4 c := by
          rw [(cYX u c).eq, (cXY c u).eq]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem (E6Pilot.simple_mem_yLeviF4 _).2.2.2.2.1
    (E6Pilot.simple_mem_yLeviF4 _).2.2.2.2.2) (E6Pilot.simple_mem_yLeviF4 _).2.2.2.2.1

theorem weylElt_mem_yLeviF4' {j : Fin Tag.E6.rank} (hj : j = 1 ∨ j = 3) (t : Kˣ) :
    weylElt .E6 K j t ∈ E6Pilot.yLeviF4 K := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  rcases hj with rfl | rfl
  · exact mul_mem (mul_mem (E6Pilot.simple_mem_yLeviF4 _).1 (E6Pilot.simple_mem_yLeviF4 _).2.1)
      (E6Pilot.simple_mem_yLeviF4 _).1
  · exact mul_mem (mul_mem (E6Pilot.simple_mem_yLeviF4 _).2.2.1
      (E6Pilot.simple_mem_yLeviF4 _).2.2.2.1) (E6Pilot.simple_mem_yLeviF4 _).2.2.1

theorem rootDiagUnit_twistedE6TorusTuple_mem_yLeviF4 (σ : K →+* K) {i : Fin TwistTag.E6.tag.rank}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) {u : Kˣ} (hu : Units.map σ.toMonoidHom u = u) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ i u) ∈ E6Pilot.yLeviF4 K := by
  rw [rootDiagUnit_twistedE6TorusTuple, hu]
  have hT : ∀ (j : Fin Tag.E6.rank), (j = 1 ∨ j = 3) → ∀ t : Kˣ,
      torusElt .E6 K j t ∈ E6Pilot.yLeviF4 K := fun j hj t =>
    mul_mem (weylElt_mem_yLeviF4' hj t) (weylElt_mem_yLeviF4' hj (-1))
  rcases hi with rfl | rfl | rfl
  · rw [show TwistTag.E6.perm 1 = 1 by decide]
    exact mul_mem (hT 1 (Or.inl rfl) u) (hT 1 (Or.inl rfl) u)
  · rw [show TwistTag.E6.perm 2 = 4 by decide]
    change weylElt .E6 K 2 u * weylElt .E6 K 2 (-1) * (weylElt .E6 K 4 u * weylElt .E6 K 4 (-1)) ∈
      E6Pilot.yLeviF4 K
    have e : weylElt .E6 K 2 u * weylElt .E6 K 2 (-1) * (weylElt .E6 K 4 u * weylElt .E6 K 4 (-1)) =
        weylElt .E6 K 2 u * weylElt .E6 K 4 u * (weylElt .E6 K 2 (-1) * weylElt .E6 K 4 (-1)) := by
      rw [mul_assoc, ← mul_assoc (weylElt .E6 K 2 (-1)), (commute_weylElt_two_four (-1) u).eq]
      group
    rw [e]
    exact mul_mem (weylElt_two_mul_weylElt_four_mem_yLeviF4' u)
      (weylElt_two_mul_weylElt_four_mem_yLeviF4' (-1))
  · rw [show TwistTag.E6.perm 3 = 3 by decide]
    exact mul_mem (hT 3 (Or.inr rfl) u) (hT 3 (Or.inr rfl) u)

theorem rootDiagUnit_twistedE6TorusTuple_one_mem (σ : K ≃+* K) (hσ : σ ^ TwistTag.E6.order = 1)
    (u : Kˣ) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ.toRingHom 1 u) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => by
    have h := congrArg (fun f : K ≃+* K => f x) hσ
    simpa [TwistTag.order, pow_two] using h
  rw [rootDiagUnit_twistedE6TorusTuple]
  have hmem : (u : K) * σ u ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 by decide, pow_one]
    change σ ((u : K) * σ u) = (u : K) * σ u
    rw [map_mul, hσσ, mul_comm]
  have hu0 : (⟨(u : K) * σ u, hmem⟩ :
      orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩) ≠ 0 := fun h =>
    mul_ne_zero u.ne_zero ((map_ne_zero σ).2 u.ne_zero) (congrArg Subtype.val h)
  have hm := orbitH_mem_graphFixedRootGroup TwistTag.E6 σ.toRingHom ⟨3, by decide⟩
    (Units.mk0 _ hu0)
  rw [coe_orbitH_of_card_one σ.toRingHom ⟨3, by decide⟩ (by decide),
    show TwistTag.E6.orbitMin ⟨3, by decide⟩ = ⟨1, by decide⟩ by decide] at hm
  have e : torusElt TwistTag.E6.tag K 1 u *
      torusElt TwistTag.E6.tag K (TwistTag.E6.perm 1) (Units.map σ.toRingHom.toMonoidHom u) =
      torusElt TwistTag.E6.tag K ⟨1, by decide⟩ (u * Units.map σ.toRingHom.toMonoidHom u) := by
    rw [show TwistTag.E6.perm 1 = 1 by decide, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
      torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    congr 1
    funext j
    rw [Pi.mul_apply, mul_zpow]
    rfl
  rw [e]
  convert hm using 2
  exact Units.ext rfl

theorem rootDiagUnit_twistedE6TorusTuple_mem_C0 (σ : K ≃+* K) (hσ : σ ^ TwistTag.E6.order = 1)
    {i : Fin TwistTag.E6.tag.rank} (hi : i = 1 ∨ i = 2 ∨ i = 3) (u : Kˣ) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ.toRingHom i u) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  rcases hi with rfl | rfl | rfl
  · exact rootDiagUnit_twistedE6TorusTuple_one_mem σ hσ u
  · exact rootDiagUnit_twistedE6TorusTuple_mem σ hσ (Or.inr (Or.inl rfl)) u
  · exact rootDiagUnit_twistedE6TorusTuple_mem σ hσ (Or.inr (Or.inr rfl)) u

theorem rootDiagUnit_twistedE6TorusTuple_mem_uLevi (σ : K ≃+* K) (hσ : σ ^ TwistTag.E6.order = 1)
    {i : Fin TwistTag.E6.tag.rank} (hi : i = 1 ∨ i = 2 ∨ i = 3) {u : Kˣ}
    (hu : Units.map σ.toRingHom.toMonoidHom u = u) :
    rootDiagUnit TwistTag.E6.tag (twistedE6TorusTuple σ.toRingHom i u) ∈ uLevi σ.toRingHom :=
  mem_inf.2 ⟨rootDiagUnit_twistedE6TorusTuple_mem_yLeviF4 σ.toRingHom hi hu,
    rootDiagUnit_twistedE6TorusTuple_mem_C0 σ hσ hi u⟩

theorem rootChar_twistedE6TorusTuple_of_fixed (σ : K →+* K) (i : Fin TwistTag.E6.tag.rank)
    {u : Kˣ} (hu : Units.map σ.toMonoidHom u = u) (β : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (twistedE6TorusTuple σ i u) β =
      u ^ (coPair TwistTag.E6.tag i β + coPair TwistTag.E6.tag (TwistTag.E6.perm i) β) := by
  rw [rootChar_twistedE6TorusTuple, hu, zpow_add]

end Torus

section Roots

@[expose] def perfRootA1 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 0, 0, 0, 0]

@[expose] def perfRoot011221 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 2, 2, 1]

@[expose] def GoodExp (m : ℤ) : Prop := m ≠ 0 ∧ |m| ≤ 4 ∧ |m| ≠ 3

instance : DecidablePred GoodExp := fun m => by unfold GoodExp; infer_instance

@[expose] def twistedTorusExp (i : Fin TwistTag.E6.tag.rank) (β : Fin TwistTag.E6.tag.rank → ℤ) :
    ℤ :=
  coPair TwistTag.E6.tag i β + coPair TwistTag.E6.tag (TwistTag.E6.perm i) β

theorem uTorusCheck : ∀ β ∈ rootFinset TwistTag.E6.tag, 0 < iform β E6Pilot.yLamAS →
    (GoodExp (twistedTorusExp 1 β) ∨ GoodExp (twistedTorusExp 2 β) ∨
      GoodExp (twistedTorusExp 3 β)) ∨
      β = twistedE6ClassRootU ∨ β = twistedE6ClassRootU' := by
  decide +kernel

theorem twistedTorusExp_permLattice {i : Fin TwistTag.E6.tag.rank}
    (hi : i = 1 ∨ i = 2 ∨ i = 3)
    (β : Fin TwistTag.E6.tag.rank → ℤ) :
    twistedTorusExp i (permLattice TwistTag.E6.perm β) = twistedTorusExp i β := by
  have hρρ : TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
    rcases hi with rfl | rfl | rfl <;> decide
  rw [twistedTorusExp, twistedTorusExp, coPair_permLattice_twistedE6,
    coPair_permLattice_twistedE6, hρρ, add_comm]

theorem zpow_ne_one_of_goodExp {K : Type} [Field K] [CharP K 2] {u : Kˣ} (hu : u ≠ 1) {m : ℤ}
    (hm : GoodExp m) : u ^ m ≠ 1 := by
  obtain ⟨hm0, hm4, hm3⟩ := hm
  by_cases h2 : |m| ≤ 2
  · exact zpow_ne_one_of_abs_le_two_of_charTwo hu hm0 h2
  · have h3 : m ≠ 3 := fun h => hm3 (by rw [h]; norm_num)
    have h3' : m ≠ -3 := fun h => hm3 (by rw [h]; norm_num)
    have hm' : m = 4 ∨ m = -4 := by rw [abs_le] at hm4; rw [abs_le] at h2; omega
    have hu2 : u ^ (2 : ℤ) ≠ 1 :=
      zpow_ne_one_of_abs_le_two_of_charTwo hu (by norm_num) (by norm_num)
    have hu4 : u ^ (4 : ℤ) ≠ 1 := by
      have e : u ^ (4 : ℤ) = (u ^ (2 : ℤ)) ^ (2 : ℤ) := by rw [← zpow_mul]; norm_num
      rw [e]
      exact zpow_ne_one_of_abs_le_two_of_charTwo hu2 (by norm_num) (by norm_num)
    rcases hm' with rfl | rfl
    · exact hu4
    · rw [zpow_neg, ne_eq, inv_eq_one]; exact hu4

end Roots

section Core

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem uRadical_eq_rootSpan_inf (σ : K →+* K) :
    uRadical σ = rootSpan TwistTag.E6.tag K (parabolicRadicalRoots .E6 E6Pilot.nodes16) ⊓
      twistedFixedGroup TwistTag.E6 K σ := by
  refine le_antisymm (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _)) fun g hg => ?_
  exact mem_inf.2 ⟨(mem_inf.1 hg).1, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩)⟩

theorem parabolicRadicalRoots_nodes16_closed :
    ∀ α ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16,
      ∀ β ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot .E6 (a • α + b • β) → a • α + b • β ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16 := by
  intro α hα β hβ a b ha hb hr
  rw [E6Pilot.parabolicRadicalRoots_nodes16] at hα hβ ⊢
  refine ⟨hr, ?_⟩
  rw [iform_add_left, ← natCast_zsmul, ← natCast_zsmul, iform_smul_left, iform_smul_left]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hα.2, hβ.2]

theorem commute_of_mem_parabolicRadical_nodes16 [Finite K] [CharP K 2] {v : ModGL TwistTag.E6.tag K}
    (hv : v ∈ parabolicRadical .E6 K E6Pilot.nodes16) :
    v ∈ centralizer ({stdRep K 1} : Set (ModGL TwistTag.E6.tag K)) := by
  have hQA : parabolicRadical .E6 K E6Pilot.nodes16 ≤ adjointGroup .E6 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  have h1 : (⟨v, hQA hv⟩ : adjointGroup .E6 K) ∈
      perfectCore (centralizer ({E6Pilot.e6ASRep K 1} : Set (adjointGroup .E6 K))) := by
    rw [perfectCore_centralizer_e6ASRep_one]
    exact mem_sup_left (mem_subgroupOf.2 hv)
  have h2 := perfectCore_le _ h1
  rw [mem_centralizer_subtype_iff] at h2
  change v ∈ centralizer ({twistedE6ClassU K} : Set (ModGL TwistTag.E6.tag K))
  rw [twistedE6ClassU_eq_e6ASRep]
  exact h2

theorem uRadical_le_perfectCore [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (uRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have hf1 : 1 ≤ f := by omega
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range (algebraMap k K) := sigma_eq_self_iff hk hσ
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  set X := centralizer ({stdRepC (apply_apply_eq hK hσ) 1} : Set C₀) with hX
  set P : Subgroup (ModGL TwistTag.E6.tag K) := (perfectCore X).map C₀.subtype with hP
  have hKu : (uLevi σ).subgroupOf C₀ ≤ perfectCore X := by
    have h := (isCoreLeviDecomp_stdRepC_one (k := k) hf1 hk hK hσ).1
    rw [h]
    exact le_sup_right
  have hQX : ∀ v (hv : v ∈ uRadical σ), (⟨v, (mem_inf.1 hv).2⟩ : C₀) ∈ X := by
    intro v hv
    rw [hX, mem_centralizer_subtype_iff]
    exact commute_of_mem_parabolicRadical_nodes16 (mem_inf.1 hv).1
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
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσE : σE ^ TwistTag.E6.order = 1 := twistedE6_sigma_pow_order hK (fun c => hσ c)
  have hlσ : Units.map σE.toRingHom.toMonoidHom l = l := by
    apply Units.ext
    change σE.toRingHom (algebraMap k K (a : k)) = algebraMap k K (a : k)
    exact (hfix _).2 ⟨_, rfl⟩
  have hσσ : ∀ x, σE.toRingHom (σE.toRingHom x) = x := apply_apply_eq hK hσ
  set S : Set (Fin TwistTag.E6.tag.rank → ℤ) := parabolicRadicalRoots .E6 E6Pilot.nodes16 with hS
  have hSpos : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα => hα.1
  have hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S := fun α hα =>
    permLattice_mem_parabolicRadicalRoots_nodes16 hα
  have horb : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, α ∈ S → α ≠ twistedE6ClassRootU →
      α ≠ twistedE6ClassRootU' →
      rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
        twistedFixedGroup TwistTag.E6 K σE.toRingHom ≤ P := by
    intro α hαS hU hU' x hx
    have hαS' := hαS
    rw [hS, E6Pilot.parabolicRadicalRoots_nodes16] at hαS'
    obtain ⟨i, hi, hgood⟩ : ∃ i : Fin TwistTag.E6.tag.rank, (i = 1 ∨ i = 2 ∨ i = 3) ∧
        GoodExp (twistedTorusExp i α) := by
      rcases uTorusCheck α (mem_rootFinset.2 hαS'.1) hαS'.2 with (h | h | h) | h | h
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨2, Or.inr (Or.inl rfl), h⟩
      · exact ⟨3, Or.inr (Or.inr rfl), h⟩
      · exact absurd h hU
      · exact absurd h hU'
    set b := twistedE6TorusTuple σE.toRingHom i l with hb
    have hbmem := rootDiagUnit_twistedE6TorusTuple_mem_uLevi σE hσE hi hlσ
    have hbC : rootDiagUnit TwistTag.E6.tag b ∈ C₀ := (mem_inf.1 hbmem).2
    have hbchar : ∀ β ∈ TwistTag.E6.diagramOrbit α, rootChar b β ≠ 1 := by
      intro β hβ
      rw [diagramOrbit_eq_pair_twistedE6Classes, Finset.mem_insert, Finset.mem_singleton] at hβ
      rw [hb, rootChar_twistedE6TorusTuple_of_fixed _ i hlσ]
      rcases hβ with rfl | rfl
      · exact zpow_ne_one_of_goodExp hl1 hgood
      · have e := twistedTorusExp_permLattice hi α
        rw [twistedTorusExp] at e
        rw [e]
        exact zpow_ne_one_of_goodExp hl1 hgood
    obtain ⟨v, hv, rfl⟩ := exists_eq_rootDiagUnit_conj_of_mem_orbitGroup σE.toRingHom
      (hSpos α hαS).1 (hSpos α hαS).2 (graphFixedRootGroup_le _ _ _ hbC) hbchar hx
    have hvQ : v ∈ uRadical σE.toRingHom := by
      have h := orbitGroup_le_rootSpan_inf_C0 hSpos hSρ hαS hv
      exact mem_inf.2 ⟨(mem_inf.1 h).1, (mem_inf.1 h).2⟩
    exact mul_conj_inv_mem_map_perfectCore hbC (mem_inf.1 hvQ).2
      (hKu (mem_subgroupOf.2 hbmem)) (hQX v hvQ)
  have hγ : rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit twistedE6ClassRootU : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σE.toRingHom ≤ P := by
    intro x hx
    have hUr := isRoot_twistedE6ClassRoots
    have hUpos : 0 < height twistedE6ClassRootU := by decide
    have hρU : permLattice TwistTag.E6.perm twistedE6ClassRootU ≠ twistedE6ClassRootU := by
      decide
    obtain ⟨s, rfl⟩ := exists_eq_twistedE6PairX_of_mem_orbitGroup hσσ hUr.1 hUpos hρU hx
    have hA1 : IsRoot TwistTag.E6.tag perfRootA1 := by
      rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
    have hE : IsRoot TwistTag.E6.tag perfRoot011221 := by
      rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
    have hsum : perfRootA1 + perfRoot011221 = twistedE6ClassRootU := by decide
    have h1 : ¬IsRoot TwistTag.E6.tag
        (perfRootA1 + permLattice TwistTag.E6.perm perfRoot011221) := by
      rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
    have h2 : ¬IsRoot TwistTag.E6.tag
        (permLattice TwistTag.E6.perm (perfRootA1 + perfRoot011221) + perfRootA1) := by
      rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
    have h3 : ¬IsRoot TwistTag.E6.tag
        (permLattice TwistTag.E6.perm (perfRootA1 + perfRoot011221) + perfRoot011221) := by
      rw [isRoot_iff_twistedE6TwoRootB]; decide +kernel
    have hc := commutator_twistedE6PairX_pairSum σE.toRingHom hA1 hE (hsum ▸ hUr.1)
      (by decide) h1 (by decide) h2 (by decide) h3 (by decide) s 1
    rw [hsum, mul_one] at hc
    rw [← hc]
    have hA1S : perfRootA1 ∈ S := by
      rw [hS, E6Pilot.parabolicRadicalRoots_nodes16]
      exact ⟨hA1, by decide⟩
    have hES : perfRoot011221 ∈ S := by
      rw [hS, E6Pilot.parabolicRadicalRoots_nodes16]
      exact ⟨hE, by decide⟩
    have m1 := horb _ hA1S (by decide) (by decide) (twistedE6PairX_mem_orbitGroup hσσ hA1 s)
    have m2 := horb _ hES (by decide) (by decide) (twistedE6PairX_mem_orbitGroup hσσ hE 1)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem m1 m2) (inv_mem m1)) (inv_mem m2)
  have hall : rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σE.toRingHom ≤ P := by
    refine rootSpan_inf_twistedFixedGroup_le_of_forall σE.surjective hSpos hSρ
      parabolicRadicalRoots_nodes16_closed fun α hα => ?_
    by_cases hU : α = twistedE6ClassRootU
    · rw [hU]
      exact hγ
    by_cases hU' : α = twistedE6ClassRootU'
    · have hmem : twistedE6ClassRootU' ∈ TwistTag.E6.diagramOrbit twistedE6ClassRootU := by
        rw [← permLattice_twistedE6ClassRootU]
        exact TwistTag.E6.permLattice_mem_diagramOrbit (TwistTag.E6.self_mem_diagramOrbit _)
      rw [hU', TwistTag.E6.diagramOrbit_eq_of_mem hmem]
      exact hγ
    exact horb α hα hU hU'
  intro g hg
  have hg' : (g : ModGL TwistTag.E6.tag K) ∈ P := by
    refine hall ?_
    rw [← uRadical_eq_rootSpan_inf]
    exact mem_subgroupOf.1 hg
  obtain ⟨y, hy, hyg⟩ := hg'
  rwa [show g = y from Subtype.ext hyg.symm]

end Core

section F3

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem factF3u_twistedE6_full [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ Qu Ku : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))) = Qu ⊔ Ku ∧
        IsPGroup 2 Qu ∧ Ku ≤ normalizer (Qu : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
        Disjoint Qu Ku ∧ (∀ N : Subgroup Ku, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        LieModel Ku .PSp 3 2 f ∧ Nat.card Qu = (2 ^ f) ^ 24 :=
  factF3u_twistedE6_of_le (by omega) hk hK hσ (uRadical_le_perfectCore hf hk hK hσ)

theorem stdRep_one_mem_uRadical [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    stdRep K 1 ∈ uRadical σ := by
  have hUr := isRoot_twistedE6ClassRoots
  have hm := twistedE6PairX_mem_orbitGroup hσσ hUr.1 1
  rw [← twistedE6ClassU_eq_twistedE6PairX] at hm
  have hUS : twistedE6ClassRootU ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16 := by
    rw [E6Pilot.parabolicRadicalRoots_nodes16]
    exact ⟨hUr.1, by decide⟩
  have h := orbitGroup_le_rootSpan_inf_C0 (fun α hα => hα.1)
    (fun α hα => permLattice_mem_parabolicRadicalRoots_nodes16 hα) hUS hm
  exact mem_inf.2 ⟨(mem_inf.1 h).1, (mem_inf.1 h).2⟩

theorem stdRepC_one_mem_perfectCore [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    stdRepC (apply_apply_eq hK hσ) 1 ∈ perfectCore (centralizer
      ({stdRepC (apply_apply_eq hK hσ) 1} : Set (graphFixedRootGroup TwistTag.E6 K σ))) :=
  uRadical_le_perfectCore hf hk hK hσ
    (mem_subgroupOf.2 (stdRep_one_mem_uRadical (apply_apply_eq hK hσ)))

end F3

end CFSG.SeitzReduction.TwistedE6Pilot
