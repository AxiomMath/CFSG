module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentHeis
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapCent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.EPilot.HeisIrr
open CFSG.SeitzReduction.E7Pilot CFSG.QuasithinUnique
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

section

variable {K : Type} [Field K]

private def e7CentF (k : ℤ) : Subgroup (ModGL .E7 K) where
  carrier := {q | q ∈ Qθ .E7 K ∧
    ∀ μ ∈ Deg1 .E7, iform μ d6HighRoot < k → heisCoord .E7 K q μ = 0}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro μ _ _
    rw [heisCoord_one]
    rfl
  mul_mem' := by
    rintro q q' ⟨hq, hq'⟩ ⟨hr, hr'⟩
    refine ⟨Subgroup.mul_mem _ hq hr, ?_⟩
    intro μ hμ hk
    rw [e7Cent_heisCoord_mul hq hr, Pi.add_apply, hq' μ hμ hk, hr' μ hμ hk, add_zero]
  inv_mem' := by
    rintro q ⟨hq, hq'⟩
    refine ⟨Subgroup.inv_mem _ hq, ?_⟩
    intro μ hμ hk
    rw [heisCoord_inv hq, Pi.neg_apply, hq' μ hμ hk, neg_zero]

private theorem e7Cent_mem_F {k : ℤ} {q : ModGL .E7 K} :
    q ∈ e7CentF (K := K) k ↔ q ∈ Qθ .E7 K ∧
      ∀ μ ∈ Deg1 .E7, iform μ d6HighRoot < k → heisCoord .E7 K q μ = 0 :=
  Iff.rfl

variable [CharP K 2]

private theorem e7Cent_iform_sub_right (μ β : Fin (Tag.rank .E7) → ℤ) :
    iform (μ - β) d6HighRoot = iform μ d6HighRoot - iform β d6HighRoot := by
  rw [sub_eq_add_neg, iform_add_left, iform_neg_left]
  ring

private theorem e7Cent_coord_sub_eq_zero {β μ : Fin (Tag.rank .E7) → ℤ} {k : ℤ}
    {q : ModGL .E7 K} (hq : q ∈ e7CentF (K := K) k)
    (hlt : iform μ d6HighRoot - iform β d6HighRoot < k) :
    heisCoord .E7 K q (μ - β) = 0 := by
  by_cases hc : heisCoord .E7 K q (μ - β) = 0
  · exact hc
  · obtain ⟨hroot, hdeg⟩ := supportedDeg1_heisCoord hq.1 (μ - β) hc
    refine hq.2 (μ - β) ⟨mem_rootFinset.1 hroot, hdeg⟩ ?_
    rw [e7Cent_iform_sub_right]
    exact hlt

private theorem e7Cent_shifts_mem_F {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hβ0 : β 0 = 0) (hh : 0 ≤ iform β d6HighRoot) {k : ℤ} {q : ModGL .E7 K}
    (hq : q ∈ e7CentF (K := K) k) (s : K) :
    pinnedX .E7 K β s * q * (pinnedX .E7 K β s)⁻¹ ∈ e7CentF (K := K) k := by
  have hβ0' : β (iθ .E7) = 0 := by
    rw [show iθ .E7 = 0 from rfl]
    exact hβ0
  have hconj := heisCoord_conj_pinnedX_of_deg_zero (τ := .E7) (K := K)
    (Or.inr (Or.inl rfl)) hβ hβ0' s hq.1
  refine (e7Cent_mem_F (K := K)).2 ⟨hconj.1, ?_⟩
  intro μ hμ hk
  have hμroot : μ ∈ rootFinset .E7 := mem_rootFinset.2 hμ.1
  have hzero : heisCoord .E7 K q (μ - β) = 0 :=
    e7Cent_coord_sub_eq_zero hq (by omega)
  rw [hconj.2 μ, hq.2 μ hμ hk, if_pos hμroot, hzero, mul_zero, add_zero]

private theorem e7Cent_commutator_mem_F {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hβ0 : β 0 = 0) (hh : 0 < iform β d6HighRoot) {k : ℤ} {q : ModGL .E7 K}
    (hq : q ∈ e7CentF (K := K) k) (s : K) :
    ⁅pinnedX .E7 K β s, q⁆ ∈ e7CentF (K := K) (k + 1) := by
  have hβ0' : β (iθ .E7) = 0 := by
    rw [show iθ .E7 = 0 from rfl]
    exact hβ0
  have hconj := heisCoord_conj_pinnedX_of_deg_zero (τ := .E7) (K := K)
    (Or.inr (Or.inl rfl)) hβ hβ0' s hq.1
  have hqinv : q⁻¹ ∈ Qθ .E7 K := Subgroup.inv_mem _ hq.1
  have hcomm : ⁅pinnedX .E7 K β s, q⁆ = pinnedX .E7 K β s * q *
      (pinnedX .E7 K β s)⁻¹ * q⁻¹ := rfl
  have hmem : pinnedX .E7 K β s * q * (pinnedX .E7 K β s)⁻¹ * q⁻¹ ∈ Qθ .E7 K :=
    Subgroup.mul_mem _ hconj.1 hqinv
  have hcoord : ∀ ν, heisCoord .E7 K ⁅pinnedX .E7 K β s, q⁆ ν =
      s * (if ν ∈ rootFinset .E7 then heisCoord .E7 K q (ν - β) else 0) := by
    intro ν
    rw [hcomm, e7Cent_heisCoord_mul hconj.1 hqinv, Pi.add_apply, hconj.2 ν,
      heisCoord_inv hq.1, Pi.neg_apply]
    split_ifs with hν
    · ring
    · ring
  refine (e7Cent_mem_F (K := K)).2 ⟨hmem, ?_⟩
  intro μ hμ hk
  have hμroot : μ ∈ rootFinset .E7 := mem_rootFinset.2 hμ.1
  have hzero : heisCoord .E7 K q (μ - β) = 0 :=
    e7Cent_coord_sub_eq_zero hq (by omega)
  rw [hcoord μ, if_pos hμroot, hzero, mul_zero]

private def e7CentSGen : Set (ModGL .E7 K) :=
  {x | ∃ β ∈ radicalRoots .E7 d6HighRoot ∩ perpRoots .E7, ∃ c : K, pinnedX .E7 K β c = x}

private theorem e7Cent_rootSpan_eq_closure_S :
    rootSpan .E7 K (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) =
      Subgroup.closure (e7CentSGen (K := K)) :=
  rootSpan_eq_closure K _

private theorem e7Cent_gen_normalizes (k : ℤ) {x : ModGL .E7 K}
    (hx : x ∈ e7CentSGen (K := K)) :
    x ∈ Subgroup.normalizer (e7CentF (K := K) k : Set (ModGL .E7 K)) := by
  obtain ⟨β, hβ, c, rfl⟩ := hx
  have hβr : IsRoot .E7 β := hβ.1.1
  have hβ0 : β 0 = 0 := hβ.2.2
  have hh : 0 < iform β d6HighRoot := hβ.1.2
  have hsq : pinnedX .E7 K β c * pinnedX .E7 K β c = 1 := by
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hxinv : (pinnedX .E7 K β c)⁻¹ = pinnedX .E7 K β c := by
    have h := congrArg (fun z => (pinnedX .E7 K β c)⁻¹ * z) hsq
    simpa [mul_assoc] using h.symm
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · exact e7Cent_shifts_mem_F hβr hβ0 (le_of_lt hh) hy c
  · have hy' : pinnedX .E7 K β c * (pinnedX .E7 K β c * y * (pinnedX .E7 K β c)⁻¹) *
        (pinnedX .E7 K β c)⁻¹ ∈ e7CentF (K := K) k :=
      e7Cent_shifts_mem_F hβr hβ0 (le_of_lt hh) hy c
    have hsimp : pinnedX .E7 K β c * (pinnedX .E7 K β c * y * (pinnedX .E7 K β c)⁻¹) *
        (pinnedX .E7 K β c)⁻¹ = y := by
      rw [hxinv]
      calc pinnedX .E7 K β c * (pinnedX .E7 K β c * y * pinnedX .E7 K β c) *
            pinnedX .E7 K β c
          = (pinnedX .E7 K β c * pinnedX .E7 K β c) * y *
              (pinnedX .E7 K β c * pinnedX .E7 K β c) := by group
        _ = y := by rw [hsq]; simp
    rwa [hsimp] at hy'

private theorem e7Cent_rootSpan_normalizes (k : ℤ) :
    rootSpan .E7 K (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) ≤
      Subgroup.normalizer (e7CentF (K := K) k : Set (ModGL .E7 K)) := by
  rw [e7Cent_rootSpan_eq_closure_S]
  exact (Subgroup.closure_le _).2 fun x hx => e7Cent_gen_normalizes k hx

private theorem e7Cent_rootSpan_commutator_le (k : ℤ) :
    ⁅rootSpan .E7 K (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7),
      e7CentF (K := K) k⁆ ≤ e7CentF (K := K) (k + 1) := by
  rw [Subgroup.commutator_le]
  intro s hs
  have hN : ∀ z ∈ rootSpan .E7 K
      (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7),
      z ∈ Subgroup.normalizer (e7CentF (K := K) (k + 1) : Set (ModGL .E7 K)) :=
    fun z hz => e7Cent_rootSpan_normalizes (k + 1) hz
  rw [e7Cent_rootSpan_eq_closure_S] at hs
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨β, hβ, c, rfl⟩ := hx
      intro y hy
      exact e7Cent_commutator_mem_F hβ.1.1 hβ.2.2 hβ.1.2 hy c
  | one =>
      intro y _
      rw [commutatorElement_one_left]
      exact Subgroup.one_mem _
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      intro y hy
      have hx₁r : x₁ ∈ rootSpan .E7 K
          (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) := by
        rwa [e7Cent_rootSpan_eq_closure_S]
      have hcomm : ⁅x₁ * x₂, y⁆ = (x₁ * ⁅x₂, y⁆ * x₁⁻¹) * ⁅x₁, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hcomm]
      refine Subgroup.mul_mem _ ?_ (ih₁ y hy)
      exact (Subgroup.mem_normalizer_iff.1 (hN x₁ hx₁r) _).1 (ih₂ y hy)
  | inv x hx ih =>
      intro y hy
      have hxr : x ∈ rootSpan .E7 K
          (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) := by
        rwa [e7Cent_rootSpan_eq_closure_S]
      have hcomm : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      rw [hcomm]
      exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hN x hxr)) _).1
        (Subgroup.inv_mem _ (ih y hy))

private theorem e7Cent_iform_d6HighRoot_self :
    iform (d6HighRoot : Fin (Tag.rank .E7) → ℤ) d6HighRoot = 2 := by
  decide

private theorem e7Cent_sigma_commutator_mem_F {k : ℤ} {q : ModGL .E7 K}
    (hq : q ∈ e7CentF (K := K) k) :
    ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ e7CentF (K := K) (k + 2) := by
  have hqinv : q⁻¹ ∈ Qθ .E7 K := Subgroup.inv_mem _ hq.1
  have hconj := e7Cent_conj_d6HighRoot (K := K) hqinv
  have hcomm : ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ =
      q * (pinnedX .E7 K d6HighRoot (1 : K) * q⁻¹ *
        (pinnedX .E7 K d6HighRoot (1 : K))⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hmem : ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ Qθ .E7 K := by
    rw [hcomm]
    exact Subgroup.mul_mem _ hq.1 hconj.1
  refine (e7Cent_mem_F (K := K)).2 ⟨hmem, ?_⟩
  intro μ hμ hk
  have hμroot : μ ∈ rootFinset .E7 := mem_rootFinset.2 hμ.1
  have hzero : heisCoord .E7 K q (μ - d6HighRoot) = 0 :=
    e7Cent_coord_sub_eq_zero hq (by
      rw [e7Cent_iform_d6HighRoot_self]
      omega)
  rw [e7Cent_heisCoord_commutator_sigma hq.1]
  simp only [shiftRoot, hμroot, if_pos]
  exact hzero

private theorem e7Cent_shift_sigma_eq_zero_of_F_zero {q : ModGL .E7 K}
    (hq : q ∈ e7CentF (K := K) 0) :
    shiftRoot K d6HighRoot (heisCoord .E7 K q) = 0 := by
  funext μ
  simp only [shiftRoot]
  by_cases hμroot : μ ∈ rootFinset .E7
  · rw [if_pos hμroot]
    by_cases hμD : μ ∈ Deg1 .E7
    · have hlt : iform (μ - d6HighRoot) d6HighRoot < 0 := by
        rw [e7Cent_iform_sub_right, e7Cent_iform_d6HighRoot_self]
        rcases e7Cent_deg1_iform_d6HighRoot hμD with h | h | h <;> omega
      by_cases hsub : μ - d6HighRoot ∈ Deg1 .E7
      · exact hq.2 (μ - d6HighRoot) hsub hlt
      · exact (heisCoord_spec .E7 K).support q hq.1 (μ - d6HighRoot) hsub
    · have hsub : μ - d6HighRoot ∉ Deg1 .E7 := by
        intro h
        have h1 : (μ - d6HighRoot) 0 = 1 := h.2
        have hμ0 : μ 0 = 1 := by
          simpa [Pi.sub_apply, d6HighRoot_apply_zero] using h1
        exact hμD ⟨mem_rootFinset.1 hμroot, hμ0⟩
      exact (heisCoord_spec .E7 K).support q hq.1 (μ - d6HighRoot) hsub
  · simp only [if_neg hμroot, Pi.zero_apply]

private theorem e7Cent_sigma_commutator_mem_U {q : ModGL .E7 K}
    (hq : q ∈ e7CentF (K := K) 0) :
    ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ Uθ .E7 K := by
  have hqinv : q⁻¹ ∈ Qθ .E7 K := Subgroup.inv_mem _ hq.1
  have hconj := e7Cent_conj_d6HighRoot (K := K) hqinv
  have hcomm : ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ =
      q * (pinnedX .E7 K d6HighRoot (1 : K) * q⁻¹ *
        (pinnedX .E7 K d6HighRoot (1 : K))⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hmem : ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ Qθ .E7 K := by
    rw [hcomm]
    exact Subgroup.mul_mem _ hq.1 hconj.1
  refine ((heisCoord_spec .E7 K).eq_zero_iff _ hmem).1 ?_
  rw [e7Cent_heisCoord_commutator_sigma hq.1]
  exact e7Cent_shift_sigma_eq_zero_of_F_zero hq

private theorem e7Cent_F_zero_of_sigma_commutator_mem_U {q : ModGL .E7 K}
    (hq : q ∈ Qθ .E7 K)
    (h : ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ Uθ .E7 K) :
    q ∈ e7CentF (K := K) 0 := by
  have hQ : ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ Qθ .E7 K := Uθ_le_Qθ h
  have hzero : heisCoord .E7 K ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ = 0 :=
    ((heisCoord_spec .E7 K).eq_zero_iff _ hQ).2 h
  have hshift : shiftRoot K d6HighRoot (heisCoord .E7 K q) = 0 := by
    rw [← e7Cent_heisCoord_commutator_sigma hq]
    exact hzero
  refine (e7Cent_mem_F (K := K)).2 ⟨hq, ?_⟩
  intro μ hμ hk
  have hd : iform μ d6HighRoot = -1 := by
    rcases e7Cent_deg1_iform_d6HighRoot hμ with h' | h' | h' <;> omega
  have hne : μ ≠ -d6HighRoot := by
    intro he
    rw [he, iform_neg_left, e7Cent_iform_d6HighRoot_self] at hd
    omega
  have hroot : IsRoot .E7 (μ + d6HighRoot) :=
    isRoot_add_of_iform_neg hμ.1 isRoot_d6HighRoot hne (by omega)
  have hν : μ + d6HighRoot ∈ rootFinset .E7 := mem_rootFinset.2 hroot
  have hval := congrFun hshift (μ + d6HighRoot)
  simp only [shiftRoot, hν, if_pos, Pi.zero_apply] at hval
  have hsub : μ + d6HighRoot - d6HighRoot = μ := by abel
  rwa [hsub] at hval

private theorem e7Cent_zmod2_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  rcases eq_or_ne c 0 with h | h
  · exact Or.inl h
  · exact Or.inr (((Nat.card_eq_two_iff' (0 : ZMod 2)).1 (by simp)).unique h one_ne_zero)

private theorem e7Cent_mem_highRadical_of_mem_Qθ {x : ↥(adjointGroup .E7 (ZMod 2))}
    (hx : (x : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2)) :
    x ∈ highRadical .E7 (ZMod 2) := by
  have hnode : iθ .E7 = highNode .E7 := by decide
  have hset : perpNodes .E7 = Jθ .E7 := by
    ext j
    simp [perpNodes, Jθ, hnode]
  refine Subgroup.mem_subgroupOf.2 ?_
  simpa [Qθ, hset] using hx

private noncomputable abbrev e7CentW : Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  fs81SigmaW (highRadical .E7 (ZMod 2)) e7CentSigma e7HighInv

private noncomputable abbrev e7CentWm : Subgroup (ModGL .E7 (ZMod 2)) :=
  e7CentW.map (adjointGroup .E7 (ZMod 2)).subtype

private theorem e7Cent_highInv_mem_Wm :
    pinnedX .E7 (ZMod 2) (highRoot .E7) 1 ∈ e7CentWm := by
  refine Subgroup.mem_map.2 ⟨e7HighInv,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers e7HighInv), rfl⟩

private theorem e7Cent_commutator_pinnedX_mem_Wm {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : δ ∈ Deg1 .E7) :
    ⁅pinnedX .E7 (ZMod 2) δ 1, pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ ∈ e7CentWm := by
  let q : ↥(adjointGroup .E7 (ZMod 2)) :=
    ⟨pinnedX .E7 (ZMod 2) δ 1, pinnedX_mem_adjointGroup δ 1⟩
  have hqQ : (q : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2) :=
    pinnedX_mem_Qθ_of_mem_Deg1 hδ 1
  have hqHR : q ∈ highRadical .E7 (ZMod 2) := e7Cent_mem_highRadical_of_mem_Qθ hqQ
  have hmem : ⁅q, e7CentSigma⁆ ∈
      fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma := ⟨q, hqHR, rfl⟩
  have hW : (⁅q, e7CentSigma⁆ : ↥(adjointGroup .E7 (ZMod 2))) ∈ e7CentW :=
    Subgroup.mem_sup_left (Subgroup.subset_closure hmem)
  refine Subgroup.mem_map.2 ⟨⁅q, e7CentSigma⁆, hW, ?_⟩
  rfl

private theorem e7Cent_Uθ_le_Wm : Uθ .E7 (ZMod 2) ≤ e7CentWm := by
  intro u hu
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hu
  rcases e7Cent_zmod2_zero_or_one c with rfl | rfl
  · rw [pinnedX_zero]
    exact Subgroup.one_mem _
  · exact e7Cent_highInv_mem_Wm

private def e7CentD1 : Set (Fin (Tag.rank .E7) → ℤ) :=
  {μ | μ ∈ Deg1 .E7 ∧ iform μ d6HighRoot = 1}

private theorem e7Cent_F_one_le_rootSpan :
    e7CentF (K := ZMod 2) 1 ≤
      rootSpan .E7 (ZMod 2) (e7CentD1 ∪ {highRoot .E7}) := by
  intro q hq
  refine e7Cent_mem_rootSpan_of_coord_support (S :=
    e7CentD1 ∪ {highRoot .E7}) ?_ ?_ hq.1 ?_
  · rintro μ (h | h)
    · exact h.1.1
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact isRoot_highRoot .E7
  · exact Set.mem_union_right _ rfl
  · intro μ hne
    obtain ⟨hroot, hdeg⟩ := supportedDeg1_heisCoord hq.1 μ hne
    have hμD : μ ∈ Deg1 .E7 := ⟨mem_rootFinset.1 hroot, hdeg⟩
    have hge : ¬ iform μ d6HighRoot < 1 := fun hlt => hne (hq.2 μ hμD hlt)
    have hd1 : iform μ d6HighRoot = 1 := by
      rcases e7Cent_deg1_iform_d6HighRoot hμD with h | h | h <;> omega
    exact Set.mem_union_left _ ⟨hμD, hd1⟩

private theorem e7Cent_commutator_pinnedX_mem_Qθ {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : δ ∈ Deg1 .E7) :
    ⁅pinnedX .E7 K δ 1, pinnedX .E7 K d6HighRoot (1 : K)⁆ ∈ Qθ .E7 K := by
  have hq : pinnedX .E7 K δ 1 ∈ Qθ .E7 K := pinnedX_mem_Qθ_of_mem_Deg1 hδ 1
  have hqinv : (pinnedX .E7 K δ 1)⁻¹ ∈ Qθ .E7 K := Subgroup.inv_mem _ hq
  have hconj := e7Cent_conj_d6HighRoot (K := K) hqinv
  have hcomm : ⁅pinnedX .E7 K δ 1, pinnedX .E7 K d6HighRoot (1 : K)⁆ =
      pinnedX .E7 K δ 1 * (pinnedX .E7 K d6HighRoot (1 : K) *
        (pinnedX .E7 K δ 1)⁻¹ * (pinnedX .E7 K d6HighRoot (1 : K))⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  exact Subgroup.mul_mem _ hq hconj.1

private theorem e7Cent_pinnedX_D1_mem_Wm {α : Fin (Tag.rank .E7) → ℤ}
    (hαD : α ∈ Deg1 .E7) (hα1 : iform α d6HighRoot = 1) :
    pinnedX .E7 (ZMod 2) α 1 ∈ e7CentWm := by
  have hne : α ≠ d6HighRoot := by
    intro he
    rw [he, e7Cent_iform_d6HighRoot_self] at hα1
    omega
  set δ : Fin (Tag.rank .E7) → ℤ := α - d6HighRoot with hδdef
  have hδroot : IsRoot .E7 δ := by
    rw [hδdef]
    exact isRoot_sub_of_iform_pos hαD.1 isRoot_d6HighRoot hne (by rw [hα1]; omega)
  have hα0 : α 0 = 1 := hαD.2
  have hδ0 : δ 0 = 1 := by
    rw [hδdef, Pi.sub_apply, hα0, d6HighRoot_apply_zero]
    ring
  have hδD : δ ∈ Deg1 .E7 := ⟨hδroot, hδ0⟩
  set q₁ : ModGL .E7 (ZMod 2) :=
    ⁅pinnedX .E7 (ZMod 2) δ 1, pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ with hq₁
  set q₂ : ModGL .E7 (ZMod 2) := pinnedX .E7 (ZMod 2) α 1 with hq₂
  have hqQ : pinnedX .E7 (ZMod 2) δ 1 ∈ Qθ .E7 (ZMod 2) :=
    pinnedX_mem_Qθ_of_mem_Deg1 hδD 1
  have hq₁Q : q₁ ∈ Qθ .E7 (ZMod 2) := by
    rw [hq₁]
    exact e7Cent_commutator_pinnedX_mem_Qθ hδD
  have hq₂Q : q₂ ∈ Qθ .E7 (ZMod 2) := by
    rw [hq₂]
    exact pinnedX_mem_Qθ_of_mem_Deg1 hαD 1
  have hw : q₁ ∈ e7CentWm := by
    rw [hq₁]
    exact e7Cent_commutator_pinnedX_mem_Wm hδD
  have hθeq : δ + d6HighRoot = α := by
    rw [hδdef]
    abel
  have hcoord : heisCoord .E7 (ZMod 2) q₁ = heisCoord .E7 (ZMod 2) q₂ := by
    rw [hq₁, e7Cent_heisCoord_commutator_sigma hqQ,
      (heisCoord_spec .E7 (ZMod 2)).pinnedX_deg1 δ hδD 1,
      shiftRoot_single (γ := d6HighRoot) (μ := δ) (K := ZMod 2)
        (by rw [hθeq]; exact mem_rootFinset.2 hαD.1), hθeq,
      hq₂, (heisCoord_spec .E7 (ZMod 2)).pinnedX_deg1 α hαD 1]
  have hu : q₁ * q₂⁻¹ ∈ Uθ .E7 (ZMod 2) :=
    e7Cent_mem_Uθ_of_heisCoord_eq (K := ZMod 2) (q₁ := q₁) (q₂ := q₂)
      hq₁Q hq₂Q hcoord
  have huW : (q₁ * q₂⁻¹)⁻¹ ∈ e7CentWm :=
    e7Cent_Uθ_le_Wm (Subgroup.inv_mem _ hu)
  have hmul : (q₁ * q₂⁻¹)⁻¹ * q₁ ∈ e7CentWm := Subgroup.mul_mem _ huW hw
  have heq : (q₁ * q₂⁻¹)⁻¹ * q₁ = q₂ := by group
  rwa [heq, hq₂] at hmul

private theorem e7Cent_rootSpan_D1_le_Wm :
    rootSpan .E7 (ZMod 2) (e7CentD1 ∪ {highRoot .E7}) ≤ e7CentWm := by
  rw [rootSpan_eq_closure (ZMod 2) _]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨α, hα, c, rfl⟩
  rcases e7Cent_zmod2_zero_or_one c with rfl | rfl
  · rw [pinnedX_zero]
    exact Subgroup.one_mem _
  · rcases hα with ⟨hαD, hα1⟩ | hαθ
    · exact e7Cent_pinnedX_D1_mem_Wm hαD hα1
    · rw [Set.mem_singleton_iff] at hαθ
      subst hαθ
      exact e7Cent_highInv_mem_Wm

private theorem e7Cent_F_one_le_Wm :
    e7CentF (K := ZMod 2) 1 ≤ e7CentWm :=
  e7Cent_F_one_le_rootSpan.trans e7Cent_rootSpan_D1_le_Wm

private theorem e7Cent_F_one_mem_SigmaW {q : ↥(adjointGroup .E7 (ZMod 2))}
    (hq : (q : ModGL .E7 (ZMod 2)) ∈ e7CentF (K := ZMod 2) 1) :
    q ∈ e7CentW := by
  have h := e7Cent_F_one_le_Wm hq
  obtain ⟨w, hw, hwq⟩ := Subgroup.mem_map.1 h
  have hwq' : w = q := Subtype.ext hwq
  rwa [hwq'] at hw

private theorem e7Cent_deg1_d1_shift_alpha7_check :
    ∀ μ ∈ rootFinset .E7, μ 0 = 1 → iform μ d6HighRoot = 1 →
      (μ + e7Alpha7 ∉ rootFinset .E7 ∧ μ - e7Alpha7 ∉ rootFinset .E7) := by
  decide +kernel

private theorem e7Cent_shift_alpha7_eq_zero {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)))
    {w : ModGL .E7 K} (hw : w ∈ e7CentF (K := K) 1) :
    shiftRoot K γ (heisCoord .E7 K w) = 0 := by
  funext ν
  simp only [Pi.zero_apply]
  rw [shiftRoot]
  by_cases hν : ν ∈ rootFinset .E7
  · rw [if_pos hν]
    rcases hγ with h | h
    · subst h
      by_cases hc : heisCoord .E7 K w (ν - e7Alpha7) = 0
      · exact hc
      · obtain ⟨hroot, hdeg⟩ := supportedDeg1_heisCoord hw.1 (ν - e7Alpha7) hc
        have hμD : ν - e7Alpha7 ∈ Deg1 .E7 := ⟨mem_rootFinset.1 hroot, hdeg⟩
        have hge : ¬ iform (ν - e7Alpha7) d6HighRoot < 1 := fun hlt =>
          hc (hw.2 _ hμD hlt)
        have hd1 : iform (ν - e7Alpha7) d6HighRoot = 1 := by
          rcases e7Cent_deg1_iform_d6HighRoot hμD with h' | h' | h' <;> omega
        have hchk := e7Cent_deg1_d1_shift_alpha7_check (ν - e7Alpha7) hroot hdeg hd1
        have hν' : (ν - e7Alpha7) + e7Alpha7 ∈ rootFinset .E7 := by
          rw [sub_add_cancel]
          exact hν
        exact absurd hν' hchk.1
    · subst h
      by_cases hc : heisCoord .E7 K w (ν - -e7Alpha7) = 0
      · simpa [sub_neg_eq_add] using hc
      · obtain ⟨hroot, hdeg⟩ := supportedDeg1_heisCoord hw.1 (ν - -e7Alpha7) hc
        have hμD : ν - -e7Alpha7 ∈ Deg1 .E7 := ⟨mem_rootFinset.1 hroot, hdeg⟩
        have hge : ¬ iform (ν - -e7Alpha7) d6HighRoot < 1 := fun hlt =>
          hc (hw.2 _ hμD hlt)
        have hd1 : iform (ν - -e7Alpha7) d6HighRoot = 1 := by
          rcases e7Cent_deg1_iform_d6HighRoot hμD with h' | h' | h' <;> omega
        have hchk := e7Cent_deg1_d1_shift_alpha7_check (ν - -e7Alpha7) hroot hdeg hd1
        have hν' : (ν - -e7Alpha7) - e7Alpha7 ∈ rootFinset .E7 := by
          have heq : (ν - -e7Alpha7) - e7Alpha7 = ν := by abel
          rwa [heq]
        exact absurd hν' hchk.2
  · rw [if_neg hν]

private theorem e7Cent_alpha7_gen_commutator_mem_U {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ))) (c : K)
    {w : ModGL .E7 K} (hw : w ∈ e7CentF (K := K) 1) :
    ⁅pinnedX .E7 K γ c, w⁆ ∈ Uθ .E7 K := by
  have hγr : IsRoot .E7 γ := by
    rcases hγ with h | h
    · rw [h]; exact isRoot_single .E7 6
    · rw [h]; exact IsRoot.neg (isRoot_single .E7 6)
  have hγ0 : γ 0 = 0 := by
    rcases hγ with h | h <;> rw [h] <;> simp [e7Alpha7]
  have hconj := heisCoord_conj_pinnedX_of_deg_zero (τ := .E7) (K := K)
    (Or.inr (Or.inl rfl)) hγr hγ0 c hw.1
  have hshift := e7Cent_shift_alpha7_eq_zero hγ hw
  have hwinv : w⁻¹ ∈ Qθ .E7 K := Subgroup.inv_mem _ hw.1
  have hcomm : ⁅pinnedX .E7 K γ c, w⁆ =
      pinnedX .E7 K γ c * w * (pinnedX .E7 K γ c)⁻¹ * w⁻¹ := rfl
  have hmem : ⁅pinnedX .E7 K γ c, w⁆ ∈ Qθ .E7 K := by
    rw [hcomm]
    exact Subgroup.mul_mem _ hconj.1 hwinv
  refine ((heisCoord_spec .E7 K).eq_zero_iff _ hmem).1 ?_
  funext ν
  simp only [Pi.zero_apply]
  rw [hcomm, e7Cent_heisCoord_mul hconj.1 hwinv, Pi.add_apply, hconj.2 ν,
    heisCoord_inv hw.1, Pi.neg_apply]
  by_cases hν : ν ∈ rootFinset .E7
  · rw [if_pos hν]
    have hval : heisCoord .E7 K w (ν - γ) = 0 := by
      have h := congrFun hshift ν
      rw [shiftRoot, if_pos hν] at h
      simpa only [Pi.zero_apply] using h
    rw [hval]
    ring
  · rw [if_neg hν]
    ring

private theorem e7Cent_rootSpan_pair (α : Fin (Tag.rank .E7) → ℤ) :
    rootSpan .E7 K {α, -α} = rootSubgroup .E7 K α ⊔ rootSubgroup .E7 K (-α) := by
  refine le_antisymm ?_ ?_
  · rw [rootSpan_eq_closure K _]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨β, hβ, c, rfl⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨c, rfl⟩)
  · exact sup_le (rootSubgroup_le_rootSpan_of_mem (Set.mem_insert _ _))
      (rootSubgroup_le_rootSpan_of_mem (Set.mem_insert_of_mem _ rfl))

private theorem e7Cent_rootSpan_alpha7_centralizes_Uθ :
    rootSpan .E7 K ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)) ≤
      Subgroup.centralizer (Uθ .E7 K : Set (ModGL .E7 K)) := by
  have h := rootSpan_le_centralizer_rootPair_E7 (K := K) (β := highRoot .E7)
    (S := ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ))) (isRoot_highRoot .E7)
    (by
      rintro α (rfl | hα)
      · exact ⟨isRoot_single .E7 6, by decide⟩
      · rw [Set.mem_singleton_iff] at hα
        subst hα
        exact ⟨IsRoot.neg (isRoot_single .E7 6), by rw [iform_neg_left]; decide⟩)
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
  exact Subgroup.mem_centralizer_iff.1 (h hx) u (Subgroup.mem_sup_left hu)

private theorem e7Cent_conj_mem_Uθ_of_rootSpan_alpha7 {x u : ModGL .E7 K}
    (hx : x ∈ rootSpan .E7 K ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)))
    (hu : u ∈ Uθ .E7 K) : x * u * x⁻¹ = u := by
  have h := Subgroup.mem_centralizer_iff.1 (e7Cent_rootSpan_alpha7_centralizes_Uθ hx) u hu
  calc x * u * x⁻¹ = (x * u) * x⁻¹ := by group
    _ = (u * x) * x⁻¹ := by rw [← h]
    _ = u := by group

private theorem e7Cent_conj_inv_mem_Uθ_of_rootSpan_alpha7 {x u : ModGL .E7 K}
    (hx : x ∈ rootSpan .E7 K ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)))
    (hu : u ∈ Uθ .E7 K) : x⁻¹ * u * x = u := by
  have h := Subgroup.mem_centralizer_iff.1 (e7Cent_rootSpan_alpha7_centralizes_Uθ hx) u hu
  calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
    _ = x⁻¹ * (x * u) := by rw [h]
    _ = u := by group

private theorem e7Cent_rootSpan_alpha7_commutator_mem_U {x : ModGL .E7 K}
    (hx : x ∈ rootSpan .E7 K ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ))) :
    ∀ w ∈ e7CentF (K := K) 1, ⁅x, w⁆ ∈ Uθ .E7 K := by
  rw [rootSpan_eq_closure K _] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨γ, hγ, c, rfl⟩ := hx
      intro w hw
      exact e7Cent_alpha7_gen_commutator_mem_U hγ c hw
  | one =>
      intro w _
      rw [commutatorElement_one_left]
      exact Subgroup.one_mem _
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
      intro w hw
      have hx₁r : x₁ ∈ rootSpan .E7 K
          ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)) := by
        rwa [rootSpan_eq_closure K _]
      have hcomm : ⁅x₁ * x₂, w⁆ = (x₁ * ⁅x₂, w⁆ * x₁⁻¹) * ⁅x₁, w⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hcomm, e7Cent_conj_mem_Uθ_of_rootSpan_alpha7 hx₁r (ih₂ w hw)]
      exact Subgroup.mul_mem _ (ih₂ w hw) (ih₁ w hw)
  | inv x hx ih =>
      intro w hw
      have hxr : x ∈ rootSpan .E7 K
          ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)) := by
        rwa [rootSpan_eq_closure K _]
      have hcomm : ⁅x⁻¹, w⁆ = x⁻¹ * ⁅x, w⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      rw [hcomm, e7Cent_conj_inv_mem_Uθ_of_rootSpan_alpha7 hxr
        (Subgroup.inv_mem _ (ih w hw))]
      exact Subgroup.inv_mem _ (ih w hw)

private theorem e7Cent_F_two_le_Uθ :
    e7CentF (K := K) 2 ≤ Uθ .E7 K := by
  intro q hq
  refine ((heisCoord_spec .E7 K).eq_zero_iff _ hq.1).1 ?_
  funext μ
  by_cases hμD : μ ∈ Deg1 .E7
  · exact hq.2 μ hμD (by
      rcases e7Cent_deg1_iform_d6HighRoot hμD with h | h | h <;> omega)
  · exact (heisCoord_spec .E7 K).support q hq.1 μ hμD

private theorem e7Cent_mem_F_neg_one {q : ModGL .E7 K} (hq : q ∈ Qθ .E7 K) :
    q ∈ e7CentF (K := K) (-1) :=
  (e7Cent_mem_F (K := K)).2 ⟨hq, fun μ hμ hlt => by
    rcases e7Cent_deg1_iform_d6HighRoot hμ with h | h | h <;> omega⟩

private theorem e7Cent_highRoot_mem_radicalRoots :
    highRoot .E7 ∈ radicalRoots .E7 (highRoot .E7) := by
  refine ⟨isRoot_highRoot .E7, ?_⟩
  rw [iform_self_eq_two (Or.inr (Or.inl rfl)) (isRoot_highRoot .E7)]
  norm_num

private theorem e7Cent_mem_zpowers_of_mem_Uθ {x : ↥(adjointGroup .E7 (ZMod 2))}
    (hx : (x : ModGL .E7 (ZMod 2)) ∈ Uθ .E7 (ZMod 2)) :
    x ∈ Subgroup.zpowers e7HighInv := by
  have hnode : iθ .E7 = highNode .E7 := by decide
  have hU : (x : ModGL .E7 (ZMod 2)) ∈
      rootSpan .E7 (ZMod 2) (radicalRoots .E7 (highRoot .E7)) :=
    rootSubgroup_le_rootSpan_of_mem e7Cent_highRoot_mem_radicalRoots hx
  have hpar : (x : ModGL .E7 (ZMod 2)) ∈
      parabolicRadical .E7 (ZMod 2) (perpNodes .E7) := by
    rw [parabolicRadical, ← radicalRoots_highRoot (Or.inr (Or.inl rfl))]
    exact hU
  have hmem : x ∈ highRadical .E7 (ZMod 2) := Subgroup.mem_subgroupOf.2 hpar
  have hQ : (x : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2) :=
    mem_Qθ_of_mem_highRadical hnode hmem
  have hzero : heisCoord .E7 (ZMod 2) (x : ModGL .E7 (ZMod 2)) = 0 :=
    ((heisCoord_spec .E7 (ZMod 2)).eq_zero_iff _ hQ).2 hx
  exact mem_zpowers_of_heisCoord_eq_zero hnode (by simp) hmem hzero

private theorem e7Cent_mem_Uθ_of_mem_zpowers {x : ↥(adjointGroup .E7 (ZMod 2))}
    (hx : x ∈ Subgroup.zpowers e7HighInv) :
    (x : ModGL .E7 (ZMod 2)) ∈ Uθ .E7 (ZMod 2) := by
  have hgen : e7HighInv ∈
      (Uθ .E7 (ZMod 2)).subgroupOf (adjointGroup .E7 (ZMod 2)) :=
    Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (Set.mem_range_self 1))
  exact Subgroup.zpowers_le.2 hgen hx

private theorem e7Cent_alpha7_mem_perpRoots : e7Alpha7 ∈ perpRoots .E7 := by
  refine ⟨isRoot_single .E7 6, ?_⟩
  decide

private theorem e7Cent_neg_alpha7_mem_perpRoots : -e7Alpha7 ∈ perpRoots .E7 := by
  refine ⟨IsRoot.neg (isRoot_single .E7 6), ?_⟩
  decide

private theorem e7CentS_le_rootRadical :
    e7CentS ≤ rootRadical .E7 (ZMod 2) d6HighRoot := by
  unfold e7CentS rootRadical
  exact Subgroup.subgroupOf_mono _ (rootSpan_mono_of_subset Set.inter_subset_left)

private theorem e7CentS_le_perpLevi : e7CentS ≤ perpLevi .E7 (ZMod 2) := by
  unfold e7CentS perpLevi
  exact Subgroup.subgroupOf_mono _ (rootSpan_mono_of_subset Set.inter_subset_right)

private theorem e7CentA1_le_perpLevi : e7A1 ≤ perpLevi .E7 (ZMod 2) := by
  unfold e7A1 perpLevi
  refine Subgroup.subgroupOf_mono _ (sup_le ?_ ?_)
  · exact rootSubgroup_le_rootSpan_of_mem e7Cent_alpha7_mem_perpRoots
  · exact rootSubgroup_le_rootSpan_of_mem e7Cent_neg_alpha7_mem_perpRoots

private theorem e7Cent_mem_rootSpan_pair_of_mem_A1 {x : ↥(adjointGroup .E7 (ZMod 2))}
    (hx : x ∈ e7A1) :
    (x : ModGL .E7 (ZMod 2)) ∈
      rootSpan .E7 (ZMod 2) ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)) := by
  have h := Subgroup.mem_subgroupOf.1 hx
  rw [e7Cent_rootSpan_pair (K := ZMod 2) e7Alpha7]
  exact h

private theorem e7CentS_centralizes_sigma {s : ↥(adjointGroup .E7 (ZMod 2))}
    (hs : s ∈ e7CentS) : s * e7CentSigma = e7CentSigma * s := by
  have hdec := isTwoRadicalDecomp_root (τ := .E7) (K := ZMod 2)
    (Or.inr (Or.inl rfl)) isRoot_d6HighRoot (one_ne_zero : (1 : ZMod 2) ≠ 0)
  have hcent : rootRadical .E7 (ZMod 2) d6HighRoot ≤
      Subgroup.centralizer ({e7CentSigma} : Set ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hdec.2.1]
    exact le_sup_left
  have h := Subgroup.mem_centralizer_iff.1 (hcent (e7CentS_le_rootRadical hs))
    e7CentSigma (Set.mem_singleton _)
  exact h.symm

private theorem e7CentA1_centralizes_sigma {x : ↥(adjointGroup .E7 (ZMod 2))}
    (hx : x ∈ e7A1) : x * e7CentSigma = e7CentSigma * x := by
  have hxr := e7Cent_mem_rootSpan_pair_of_mem_A1 hx
  have h := rootSpan_le_centralizer_rootPair_E7 (K := ZMod 2) (β := d6HighRoot)
    (S := ({e7Alpha7, -e7Alpha7} : Set (Fin (Tag.rank .E7) → ℤ)))
    isRoot_d6HighRoot (by
      rintro α (rfl | hα)
      · exact ⟨isRoot_single .E7 6, by decide⟩
      · rw [Set.mem_singleton_iff] at hα
        subst hα
        exact ⟨IsRoot.neg (isRoot_single .E7 6), by rw [iform_neg_left]; decide⟩)
  have hσ : pinnedX .E7 (ZMod 2) d6HighRoot 1 ∈
      (rootSubgroup .E7 (ZMod 2) d6HighRoot ⊔
        rootSubgroup .E7 (ZMod 2) (-d6HighRoot) : Subgroup (ModGL .E7 (ZMod 2))) :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, rfl⟩)
  have hcomm := Subgroup.mem_centralizer_iff.1 (h hxr) _ hσ
  exact Subtype.ext hcomm.symm

private theorem e7Cent_coe_commutator {a b : ↥(adjointGroup .E7 (ZMod 2))} :
    ((⁅a, b⁆ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
      ⁅(a : ModGL .E7 (ZMod 2)), (b : ModGL .E7 (ZMod 2))⁆ :=
  map_commutatorElement (Subgroup.subtype _) a b

private theorem e7CentS_commutator_F_one_mem_Uθ {s : ↥(adjointGroup .E7 (ZMod 2))}
    (hs : s ∈ e7CentS) {w : ModGL .E7 (ZMod 2)}
    (hw : w ∈ e7CentF (K := ZMod 2) 1) :
    ⁅(s : ModGL .E7 (ZMod 2)), w⁆ ∈ Uθ .E7 (ZMod 2) := by
  have hs' : (s : ModGL .E7 (ZMod 2)) ∈
      rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) :=
    Subgroup.mem_subgroupOf.1 hs
  exact e7Cent_F_two_le_Uθ ((Subgroup.commutator_le.1
    (e7Cent_rootSpan_commutator_le (K := ZMod 2) 1)) _ hs' w hw)

private theorem e7CentS_commutator_commSet_mem_zpowers
    {s : ↥(adjointGroup .E7 (ZMod 2))} (hs : s ∈ e7CentS)
    {w : ↥(adjointGroup .E7 (ZMod 2))}
    (hw : w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma) :
    ⁅s, w⁆ ∈ Subgroup.zpowers e7HighInv := by
  obtain ⟨q, hq, rfl⟩ := hw
  have hqQ : (q : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2) :=
    mem_Qθ_of_mem_highRadical (by decide) hq
  have hqF : (q : ModGL .E7 (ZMod 2)) ∈ e7CentF (K := ZMod 2) (-1) :=
    e7Cent_mem_F_neg_one hqQ
  have hwF : ⁅(q : ModGL .E7 (ZMod 2)),
      pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ ∈ e7CentF (K := ZMod 2) 1 := by
    have := e7Cent_sigma_commutator_mem_F hqF
    simpa using this
  have hcommF : ⁅(s : ModGL .E7 (ZMod 2)),
      ⁅(q : ModGL .E7 (ZMod 2)), pinnedX .E7 (ZMod 2) d6HighRoot 1⁆⁆ ∈
      Uθ .E7 (ZMod 2) :=
    e7CentS_commutator_F_one_mem_Uθ hs hwF
  have hcoe : ((⁅s, ⁅q, e7CentSigma⁆⁆ : ↥(adjointGroup .E7 (ZMod 2))) :
      ModGL .E7 (ZMod 2)) =
      ⁅(s : ModGL .E7 (ZMod 2)),
        ⁅(q : ModGL .E7 (ZMod 2)), pinnedX .E7 (ZMod 2) d6HighRoot 1⁆⁆ := by
    rw [e7Cent_coe_commutator, e7Cent_coe_commutator]
  exact e7Cent_mem_zpowers_of_mem_Uθ (by rwa [hcoe])

private theorem e7CentA1_commutator_commSet_mem_zpowers
    {x : ↥(adjointGroup .E7 (ZMod 2))} (hx : x ∈ e7A1)
    {w : ↥(adjointGroup .E7 (ZMod 2))}
    (hw : w ∈ fs81CommSet (highRadical .E7 (ZMod 2)) e7CentSigma) :
    ⁅x, w⁆ ∈ Subgroup.zpowers e7HighInv := by
  obtain ⟨q, hq, rfl⟩ := hw
  have hqQ : (q : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2) :=
    mem_Qθ_of_mem_highRadical (by decide) hq
  have hqF : (q : ModGL .E7 (ZMod 2)) ∈ e7CentF (K := ZMod 2) (-1) :=
    e7Cent_mem_F_neg_one hqQ
  have hwF : ⁅(q : ModGL .E7 (ZMod 2)),
      pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ ∈ e7CentF (K := ZMod 2) 1 := by
    have := e7Cent_sigma_commutator_mem_F hqF
    simpa using this
  have hxr := e7Cent_mem_rootSpan_pair_of_mem_A1 hx
  have hcommF : ⁅(x : ModGL .E7 (ZMod 2)),
      ⁅(q : ModGL .E7 (ZMod 2)), pinnedX .E7 (ZMod 2) d6HighRoot 1⁆⁆ ∈
      Uθ .E7 (ZMod 2) :=
    e7Cent_rootSpan_alpha7_commutator_mem_U hxr _ hwF
  have hcoe : ((⁅x, ⁅q, e7CentSigma⁆⁆ : ↥(adjointGroup .E7 (ZMod 2))) :
      ModGL .E7 (ZMod 2)) =
      ⁅(x : ModGL .E7 (ZMod 2)),
        ⁅(q : ModGL .E7 (ZMod 2)), pinnedX .E7 (ZMod 2) d6HighRoot 1⁆⁆ := by
    rw [e7Cent_coe_commutator, e7Cent_coe_commutator]
  exact e7Cent_mem_zpowers_of_mem_Uθ (by rwa [hcoe])

private theorem e7CentS_commutator_sigma_mem_zpowers
    {s : ↥(adjointGroup .E7 (ZMod 2))} (hs : s ∈ e7CentS)
    {q : ↥(adjointGroup .E7 (ZMod 2))} (hq : q ∈ highRadical .E7 (ZMod 2)) :
    ⁅⁅s, q⁆, e7CentSigma⁆ ∈ Subgroup.zpowers e7HighInv := by
  have hs' : (s : ModGL .E7 (ZMod 2)) ∈
      rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) :=
    Subgroup.mem_subgroupOf.1 hs
  have hqQ : (q : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2) :=
    mem_Qθ_of_mem_highRadical (by decide) hq
  have hqF : (q : ModGL .E7 (ZMod 2)) ∈ e7CentF (K := ZMod 2) (-1) :=
    e7Cent_mem_F_neg_one hqQ
  have hcommF : ⁅(s : ModGL .E7 (ZMod 2)), (q : ModGL .E7 (ZMod 2))⁆ ∈
      e7CentF (K := ZMod 2) 0 :=
    (Subgroup.commutator_le.1 (e7Cent_rootSpan_commutator_le (K := ZMod 2) (-1)))
      _ hs' _ hqF
  have hcoe : ((⁅⁅s, q⁆, e7CentSigma⁆ : ↥(adjointGroup .E7 (ZMod 2))) :
      ModGL .E7 (ZMod 2)) =
      ⁅⁅(s : ModGL .E7 (ZMod 2)), (q : ModGL .E7 (ZMod 2))⁆,
        pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ := by
    rw [e7Cent_coe_commutator, e7Cent_coe_commutator]
  refine e7Cent_mem_zpowers_of_mem_Uθ ?_
  rw [hcoe]
  exact e7Cent_sigma_commutator_mem_U hcommF

private theorem e7CentS_commutator_mem_SigmaW
    {s : ↥(adjointGroup .E7 (ZMod 2))} (hs : s ∈ e7CentS)
    {c : ↥(adjointGroup .E7 (ZMod 2))} (hc : c ∈ highRadical .E7 (ZMod 2))
    (hσ : ⁅c, e7CentSigma⁆ ∈ Subgroup.zpowers e7HighInv) :
    ⁅s, c⁆ ∈ e7CentW := by
  have hcU : ((⁅c, e7CentSigma⁆ : ↥(adjointGroup .E7 (ZMod 2))) :
      ModGL .E7 (ZMod 2)) ∈ Uθ .E7 (ZMod 2) := e7Cent_mem_Uθ_of_mem_zpowers hσ
  have hcQ : (c : ModGL .E7 (ZMod 2)) ∈ Qθ .E7 (ZMod 2) :=
    mem_Qθ_of_mem_highRadical (by decide) hc
  have hcU' : ⁅(c : ModGL .E7 (ZMod 2)),
      pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ ∈ Uθ .E7 (ZMod 2) := by
    have hcoe : ((⁅c, e7CentSigma⁆ : ↥(adjointGroup .E7 (ZMod 2))) :
        ModGL .E7 (ZMod 2)) =
        ⁅(c : ModGL .E7 (ZMod 2)), pinnedX .E7 (ZMod 2) d6HighRoot 1⁆ := by
      rw [e7Cent_coe_commutator]
    rwa [hcoe] at hcU
  have hcF : (c : ModGL .E7 (ZMod 2)) ∈ e7CentF (K := ZMod 2) 0 :=
    e7Cent_F_zero_of_sigma_commutator_mem_U hcQ hcU'
  have hs' : (s : ModGL .E7 (ZMod 2)) ∈
      rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) :=
    Subgroup.mem_subgroupOf.1 hs
  have hcommF : ⁅(s : ModGL .E7 (ZMod 2)), (c : ModGL .E7 (ZMod 2))⁆ ∈
      e7CentF (K := ZMod 2) 1 :=
    (Subgroup.commutator_le.1 (e7Cent_rootSpan_commutator_le (K := ZMod 2) 0))
      _ hs' _ hcF
  have hcoe : ((⁅s, c⁆ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
      ⁅(s : ModGL .E7 (ZMod 2)), (c : ModGL .E7 (ZMod 2))⁆ :=
    e7Cent_coe_commutator
  exact e7Cent_F_one_mem_SigmaW (by rwa [hcoe])

private theorem e7CentS_isPGroup : IsPGroup 2 e7CentS := by
  have hP : IsPGroup 2 (rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot)) :=
    isPGroup_rootSpan_radicalRoots 2 (Or.inr (Or.inl rfl)) isRoot_d6HighRoot
  have hle : rootSpan .E7 (ZMod 2) (radicalRoots .E7 d6HighRoot) ≤
      adjointGroup .E7 (ZMod 2) := rootSpan_le_adjointGroup' _
  have hroot : IsPGroup 2 ↥(rootRadical .E7 (ZMod 2) d6HighRoot) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  exact (hroot.to_subgroup
    (e7CentS.subgroupOf (rootRadical .E7 (ZMod 2) d6HighRoot))).of_equiv
    (Subgroup.subgroupOfEquivOfLe e7CentS_le_rootRadical)

end

theorem e7CentModelFlag_holds :
    E7CentModelFlag := by
  refine ⟨e7CentS_le_perpLevi, e7CentA1_le_perpLevi, e7CentS_isPGroup, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro s hs
    exact e7CentS_centralizes_sigma hs
  · intro x hx
    exact e7CentA1_centralizes_sigma hx
  · intro s hs w hw
    exact e7CentS_commutator_commSet_mem_zpowers hs hw
  · intro x hx w hw
    exact e7CentA1_commutator_commSet_mem_zpowers hx hw
  · intro s hs q hq
    exact e7CentS_commutator_sigma_mem_zpowers hs hq
  · intro s hs c hc hσ
    exact e7CentS_commutator_mem_SigmaW hs hc hσ

end CFSG.StandardType.FrameRoute.FS81
