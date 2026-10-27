module

public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityAssembly
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityCore
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityDual
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityFactor

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module QuadraticMap CFSG.Assembly CFSG.RankThree.Classical
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

theorem orthogonal_primary_special_groups_kernel_sector_scalar_rigidity_of_orbit_representatives
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (Ã : Subgroup (orthDerived Q))
    (hÃ : Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      ∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype = Ã)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (_hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (κ : ProjOrthDerived Q ≃* ProjOrthDerived Q)
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
        κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hscal : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v)
    (hcent : ∀ x : orthDerived Q, x ∈ Ã → x ≠ 1 → ∃ Rep : Finset K[X],
      IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep ∧ ∀ h ∈ Rep, h ≠ X - 1 →
        2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
          ∀ j ∈ componentImage Q (x : V ≃ₗ[K] V) h, κ j = j) :
    σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1 := by
  classical
  have hD := kernelLineData Q hQ hp (by omega) hpl A hA hAc Ã hÃ
  refine rigidity_of_exact_mixing hD σ F hFσ μ hFQ κ hκF hscal ?_
  intro h2 M N hM hN hMa hNa hMN
  obtain ⟨a, ha1, hx, r₀, hr₀mem, hr₀1, hr₀r1, hMr, hNr⟩ :=
    exists_sector_factor hQ hp hpl hD.comm hD.card hD.exp hD.lines hM hN hMN hMa hNa
  have ha1' : (a : orthDerived Q) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hSM : ∀ v ∈ lineSpace M, ((a : orthDerived Q) : V ≃ₗ[K] V) v ∈ lineSpace M :=
    fun v hv => stable_lineSpace hD.comm M a hv
  have hSN : ∀ v ∈ lineSpace N, ((a : orthDerived Q) : V ≃ₗ[K] V) v ∈ lineSpace N :=
    fun v hv => stable_lineSpace hD.comm N a hv
  obtain ⟨Rep, hRep, hcentRep⟩ := hcent (a : orthDerived Q) a.2 ha1'
  obtain ⟨r, ⟨hrRep, hrr⟩, -⟩ := hRep.2 r₀ hr₀mem
  have hrmem : r ∈ primaryFactors ((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap := hRep.1 hrRep
  have hkey : r ≠ X - 1 ∧
      lineSpace M ⊓ primaryComponent ((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap r ≠ ⊥ ∧
      lineSpace N ⊓ primaryComponent ((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap r ≠ ⊥ := by
    rcases hrr with h | h
    · rw [← h]
      exact ⟨hr₀1, hMr, hNr⟩
    · have hr : r = reciprocalPolynomial r₀ := by rw [h, hx.reciprocal_reciprocal_eq hrmem]
      rw [hr]
      exact ⟨hr₀r1, inf_primaryComponent_reciprocal_ne_bot hx hr₀mem hSM
        (hD.regular (some ⟨M, hM⟩)) hMr, inf_primaryComponent_reciprocal_ne_bot hx hr₀mem hSN
        (hD.regular (some ⟨N, hN⟩)) hNr⟩
  obtain ⟨hm, g, hg, v, hv, s, hs, t, ht, ht0, hgv⟩ := exists_mixing_of_factor hp hp3 h2
    hD.internal hD.orth hD.regular hM hN hMN hx hSM hSN hrmem hkey.1 hkey.2.1 hkey.2.2
  have hperf : Group.IsPerfect ↥(specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) r) :=
    (hx.quasisimple_specialBlock hp hp3 hrmem hkey.1 hm).1
  have hle : specialBlock Q ((a : orthDerived Q) : V ≃ₗ[K] V) r ≤ orthDerived Q :=
    hx.specialBlock_le_orthDerived hp hp3 hrmem hkey.1 hm
  have hcomm' := commute_of_projective_centralizes_of_perfect F σ hFσ μ hFQ hperf hle
    (fun g₀ g' hg₀ hgg' => by
      have h1 := hκF g₀ g' hgg'
      have h2' := hcentRep r hrRep hkey.1 hm (QuotientGroup.mk g₀)
        ⟨g₀, Subgroup.mem_subgroupOf.mpr hg₀, rfl⟩
      rw [h2'] at h1
      exact h1.symm)
  exact ⟨g, hcomm' g hg, v, hv, s, hs, t, ht, ht0, hgv⟩

end CFSG.RankThree.PartOne
