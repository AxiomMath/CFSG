module

public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityData
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityRegular

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical CFSG.RankThree.Classical2

theorem rigidity_of_exact_mixing {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {Ã : Subgroup (orthDerived Q)}
    (hD : KernelLineData Q p Ã) (σ : K ≃+* K) (F : V ≃+ V)
    (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : ProjOrthDerived Q ≃* ProjOrthDerived Q)
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
        κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hscal : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v)
    (hmix : (2 : K) ≠ 0 → ∀ M N : Subgroup Ã, Nat.card M = p → Nat.card N = p →
      lineSpace M ≠ ⊥ → lineSpace N ≠ ⊥ → M ≠ N →
        ∃ g : V ≃ₗ[K] V, (∀ v, F (g v) = g (F v)) ∧ ∃ v ∈ lineSpace M, ∃ s ∈ lineSpace M,
          ∃ t ∈ lineSpace N, t ≠ 0 ∧ g v = s + t) :
    σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1 := by
  classical
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁₂, hM₁a, hM₂a⟩ := hD.two_active
  choose! c hc using hscal
  have hcvec : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ∀ v ∈ lineSpace M, F v = ((c M : Kˣ) : K) • v :=
    fun M hM hMa v hv => hc M hM hMa v (Submodule.mem_inf.mp hv).1
  have hσ : σ = RingEquiv.refl K :=
    eq_refl_of_semilinear_scalar hFσ hM₁a (c M₁).ne_zero (hcvec M₁ hM₁ hM₁a)
  have hsq : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ((c M : Kˣ) : K) * ((c M : Kˣ) : K) = μ := by
    intro M hM hMa
    obtain ⟨v, hv, hvQ⟩ := exists_map_ne_zero_of_nondegenerate (hD.regular (some ⟨M, hM⟩)) hMa
    have h1 := hFQ v
    rw [hcvec M hM hMa v hv, QuadraticMap.map_smul, hσ, RingEquiv.refl_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hvQ h1
  have hcc : ∀ M N : Subgroup Ã, Nat.card M = p → Nat.card N = p → lineSpace M ≠ ⊥ →
      lineSpace N ≠ ⊥ → ((c M : Kˣ) : K) = ((c N : Kˣ) : K) := by
    intro M N hM hN hMa hNa
    by_cases h2 : (2 : K) = 0
    · have h1 := hsq M hM hMa
      have h1' := hsq N hN hNa
      have h3 : (((c M : Kˣ) : K) - ((c N : Kˣ) : K)) ^ 2 = 0 := by
        linear_combination h1 - h1' + (((c N : Kˣ) : K) ^ 2 - ((c M : Kˣ) : K) *
          ((c N : Kˣ) : K)) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
    · by_cases hMN : M = N
      · rw [hMN]
      obtain ⟨g, hgc, v, hv, s, hs, t, ht, ht0, hgv⟩ := hmix h2 M N hM hN hMa hNa hMN
      exact eq_of_mixing hgc (hcvec M hM hMa) (hcvec N hN hNa) hv hs ht ht0 hgv
  have hall : ∀ v, F v = ((c M₁ : Kˣ) : K) • v := by
    refine eq_smul_of_iSup_eq_top_additive (S := innerSummand p Ã)
      hD.internal.submodule_iSup_eq_top ?_
    intro i v hv
    rcases i with _ | ⟨M, hM⟩
    · have hv1 : v ∈ planeFixSpace Ã := hv
      rw [planeFixSpace_eq_fixSub, mem_fixSub] at hv1
      refine hc M₁ hM₁ hM₁a v ?_
      rw [lineFixSpace_eq_fixSub, mem_fixSub]
      exact fun m _ => hv1 m trivial
    · have hv1 : v ∈ lineSpace M := hv
      by_cases hMa : lineSpace M = ⊥
      · have : v = 0 := (Submodule.mem_bot K).mp (hMa ▸ hv1)
        rw [this, map_zero, smul_zero]
      · rw [hcvec M hM hMa v hv1, hcc M M₁ hM hM₁ hMa hM₁a]
  refine ⟨hσ, ⟨c M₁, hall⟩, ?_⟩
  refine MulEquiv.ext fun t => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  refine (hκF g g fun v => ?_).trans (MulAut.one_apply _ _).symm
  rw [hall, ← map_smul, ← hall, AddEquiv.apply_symm_apply]

end CFSG.RankThree.PartOne.KCOrthogonal
