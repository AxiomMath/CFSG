module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenLayer
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative

private theorem ggPhiTwoHyper_rank_one_le {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) : 1 ≤ τ.rank := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide

private noncomputable def ggPhiTwoHyper_linSum (p : ℕ) {r : ℕ} (α : Fin r → ZMod p) :
    (Fin r → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun t := ∑ j, α j * t j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

private theorem ggPhiTwoHyper_card_ker_sum (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 1 ≤ r)
    (α : Fin r → ZMod p) (hα : α ≠ 0) :
    Nat.card {t : Fin r → ZMod p // ∑ j, α j * t j = 0} = p ^ (r - 1) := by
  classical
  set f := ggPhiTwoHyper_linSum p α with hf
  have hmem : ∀ t : Fin r → ZMod p, f t = ∑ j, α j * t j := fun t => rfl
  have hf0 : f ≠ 0 := by
    intro h
    apply hα
    funext j
    have h1 := congrArg (fun g : (Fin r → ZMod p) →ₗ[ZMod p] ZMod p => g (Pi.single j 1)) h
    rw [hmem] at h1
    simp only [LinearMap.zero_apply] at h1
    rwa [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun hc => absurd (Finset.mem_univ j) hc), Pi.single_eq_same, mul_one] at h1
  have hne : ∃ x, f x ≠ 0 := by
    by_contra h
    simp only [not_exists] at h
    exact hf0 (LinearMap.ext fun x => by simpa using h x)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := hne
    exact ⟨(z * (f x)⁻¹) • x, by
      rw [LinearMap.map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]⟩
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective (f := f.toAddMonoidHom) hsurj
  have h1 : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have h2 : Nat.card (Fin r → ZMod p) = p ^ r := by
    rw [Nat.card_fun]
    simp [Nat.card_zmod]
  rw [h1, h2] at hcard
  have h3 : Nat.card {t : Fin r → ZMod p // ∑ j, α j * t j = 0}
      = Nat.card f.toAddMonoidHom.ker := by
    refine Nat.card_congr ?_
    exact Equiv.refl _
  rw [h3]
  have hpow : p ^ r = p ^ (r - 1) * p := by
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    rw [Nat.succ_sub_one, pow_succ]
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hcard

private theorem ggPhiTwoHyper_eq_ker_of_subset_of_ncard {p : ℕ} [Fact p.Prime] {r : ℕ}
    (hr : 1 ≤ r) {V : Set (Fin r → ZMod p)} {α : Fin r → ZMod p} (hα : α ≠ 0)
    (hsub : V ⊆ {t : Fin r → ZMod p | ∑ j, α j * t j = 0})
    (hcard : V.ncard = p ^ (r - 1)) :
    V = {t : Fin r → ZMod p | ∑ j, α j * t j = 0} := by
  have h2 : Nat.card ↥({t : Fin r → ZMod p | ∑ j, α j * t j = 0} : Set _) = p ^ (r - 1) :=
    ggPhiTwoHyper_card_ker_sum p hr α hα
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [hcard, ← Nat.card_coe_set_eq, h2]

private theorem ggPhiTwoHyper_roots_trivial_on_of_ncard
    {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Set (Fin τ.rank → ZMod p)} (hV : V.ncard = p ^ (τ.rank - 1)) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ ∀ β : Fin τ.rank → ℤ, IsRoot τ β →
      (∀ t ∈ V, ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α := by
  have hr : 1 ≤ τ.rank := ggPhiTwoHyper_rank_one_le hτ
  by_cases h : ∃ α : Fin τ.rank → ℤ,
      IsRoot τ α ∧ ∀ t ∈ V, ∑ j, (α j : ZMod p) * t j = 0
  · obtain ⟨α, hαroot, hαvan⟩ := h
    have hne : ¬ ∀ j, (p : ℤ) ∣ α j :=
      CFSG.HardMathSupport.C14G2Three.not_forall_dvd_of_isRoot hαroot (by
        rw [Int.isUnit_iff]
        rintro (h | h)
        · have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).two_le
          omega
        · have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).two_le
          omega)
    obtain ⟨j0, hj0⟩ : ∃ j, ¬ (p : ℤ) ∣ α j := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hne hc
    have hαne : (fun j => (α j : ZMod p)) ≠ 0 := by
      intro hcon
      apply hj0
      have h2 : ((α j0 : ℤ) : ZMod p) = 0 := by
        have := congrFun hcon j0
        simpa using this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
    have hVeq : V = {t : Fin τ.rank → ZMod p | ∑ j, (α j : ZMod p) * t j = 0} :=
      ggPhiTwoHyper_eq_ker_of_subset_of_ncard hr hαne hαvan hV
    refine ⟨α, hαroot, fun β hβroot hβvan => ?_⟩
    exact ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero
      hτ hp2 hαroot hβroot
      (fun t ht => hβvan t (by rw [hVeq]; exact ht))
  · obtain ⟨α, hαroot⟩ : ∃ α : Fin τ.rank → ℤ, IsRoot τ α :=
      ⟨Pi.single ⟨0, hr⟩ 1, isRoot_single τ ⟨0, hr⟩⟩
    exact ⟨α, hαroot, fun β hβroot hβvan => absurd ⟨β, hβroot, hβvan⟩ h⟩

theorem exists_isRoot_perfect_le_phiTwoComp_with_vanishing
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)) {ζ : (AlgebraicClosure K)ˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {V : Set (Fin τ.rank → ZMod p)} (hV : V.ncard = p ^ (τ.rank - 1))
    {P : Subgroup (adjointGroup τ K)} (hperf : ⁅P, P⁆ = P)
    (hP : ∀ x ∈ P, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ P ≤ phiTwoComp g0 α ∧
      (P ≠ ⊥ → ∀ t ∈ V, ∑ j, (α j : ZMod p) * t j = 0) := by
  classical
  obtain ⟨α, hαroot, hαsmall⟩ := ggPhiTwoHyper_roots_trivial_on_of_ncard hτ hp2 hV
  refine ⟨α, hαroot, ?_, ?_⟩
  · intro x hx
    rw [mem_phiTwoComp_iff]
    exact rootSpan_mono (fun γ hγ => by
        have h := hαsmall γ hγ.1 hγ.2
        simpa using h)
      (conj_mem_rootSpan_of_isPerfect hg0C hζo hζ hT hperf hP hx)
  · intro hne
    by_contra hvan
    have hset : {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧
        ∀ t ∈ V, ∑ j, (γ j : ZMod p) * t j = 0} = ∅ := by
      ext γ
      constructor
      · intro hγ
        rcases hαsmall γ hγ.1 hγ.2 with he | he
        · subst γ
          exact hvan hγ.2
        · apply hvan
          intro t ht
          have hh := hγ.2 t ht
          rw [he] at hh
          simpa only [Pi.neg_apply, Int.cast_neg, neg_mul,
            Finset.sum_neg_distrib, neg_eq_zero] using hh
      · intro hγ
        cases hγ
    apply hne
    apply le_antisymm _ bot_le
    intro x hx
    change x = 1
    have hh := conj_mem_rootSpan_of_isPerfect hg0C hζo hζ hT hperf hP hx
    have he : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 = 1 := by
      simpa [hset, rootSpan] using hh
    have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) = 1 := by
      calc
        _ = g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL τ K) * g0) * g0⁻¹ := by group
        _ = g0 * 1 * g0⁻¹ := by rw [he]
        _ = 1 := by group
    apply Subtype.ext
    apply baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K))
    simpa using hbase

theorem exists_isRoot_perfect_le_phiTwoComp
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)) {ζ : (AlgebraicClosure K)ˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {V : Set (Fin τ.rank → ZMod p)} (hV : V.ncard = p ^ (τ.rank - 1))
    {P : Subgroup (adjointGroup τ K)} (hperf : ⁅P, P⁆ = P)
    (hP : ∀ x ∈ P, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x) :
    ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ P ≤ phiTwoComp g0 α := by
  obtain ⟨α, hαroot, hle, -⟩ := exists_isRoot_perfect_le_phiTwoComp_with_vanishing
    hτ hp2 hg0C hζo hζ hT hV hperf hP
  exact ⟨α, hαroot, hle⟩

theorem iSup_le_iSup_phiTwoComp_of_hyperplane_family
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)) {ζ : (AlgebraicClosure K)ˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {ι : Type} (S : ι → Subgroup (adjointGroup τ K)) (hperf : ∀ i, ⁅S i, S i⁆ = S i)
    (hhyp : ∀ i, ∃ V : Set (Fin τ.rank → ZMod p), V.ncard = p ^ (τ.rank - 1) ∧
      ∀ x ∈ S i, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x) :
    (⨆ i, S i) ≤ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1 := by
  refine iSup_le fun i => ?_
  obtain ⟨V, hVcard, hVcent⟩ := hhyp i
  obtain ⟨α, hαroot, hle⟩ :=
    exists_isRoot_perfect_le_phiTwoComp hτ hp2 hg0C hζo hζ hT hVcard (hperf i) hVcent
  exact hle.trans (le_iSup
    (fun γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ} => phiTwoComp g0 γ.1) ⟨α, hαroot⟩)

end CFSG.StandardType.PhiTwoRootGen

end
