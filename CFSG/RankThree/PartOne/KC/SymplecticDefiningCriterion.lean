module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningPCore
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCUnitaryDefining (eq_bot_of_pointwise_centralizer_of_pCore)

variable {r : ℕ} {K : Type} [Field K]

theorem conj_injective_statedProj_statedSp [Finite K] (hr : 2 ≤ r) (h4 : 4 ≤ Nat.card K) :
    Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) := by
  have hsimple : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega)
      (Or.inl (Or.inr h4))
  have hs4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  have hperf : Group.IsPerfect (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect r K (Or.inl hs4)
  have hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (StatedProj (StatedSp r K))) with h | h
    · exact h
    · have hcomm : IsMulCommutative (StatedProj (StatedSp r K)) :=
        ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a⟩⟩
      exact absurd hcomm (Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp r K)))
  refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
  have hc : g ∈ Subgroup.center (StatedProj (StatedSp r K)) :=
    Subgroup.mem_center_iff.2 fun t => by
      have ht := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ t) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at ht
      calc t * g = g * t * g⁻¹ * g := by rw [ht]
        _ = g * t := by group
  rwa [hZ, Subgroup.mem_bot] at hc

theorem symplectic_normalPrimeComplementsTrivial_of_radical_data {p f : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hf : 1 ≤ f) (hr : 2 ≤ r) [Finite K] [CharP K p] (hK : Nat.card K = p ^ f)
    (u : StatedSp r K) (hup : u ^ p = 1) (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hN : ∀ g : StatedSp r K, g * u = u * g →
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N =
        N * ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (R : Subgroup (StatedSp r K)) (hRu : ∀ y ∈ R, y * u = u * y) (hRp : ∀ y ∈ R, y ^ p = 1)
    (hRnorm : ∀ g : StatedSp r K,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N =
        N * ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
        ∀ y ∈ R, g * y * g⁻¹ ∈ R)
    (hRpt : ∀ (A : gsp r K) (σ : K ≃+* K), (∀ y ∈ R, conjSp r K A (fieldSp r K σ y) = y) →
      ∃ y' ∈ R, conjAut r K A * fieldAut r K σ = MulAut.conj (proj r K y')) :
    NormalPrimeComplementsTrivial p (MulAut.conj (proj r K u)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (show 4 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
  have hinj := conj_injective_statedProj_statedSp (r := r) (K := K) hr h4
  intro B hB S hSC hSn hSp
  refine eq_bot_of_pointwise_centralizer_of_pCore hinj hp (U := R.map (proj r K)) ?_ ?_ ?_ ?_ B hB
    S hSC hSn hSp
  ·
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hRu y hy]
  ·
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hRp y hy, map_one]
  ·
    intro c hc z hz
    obtain ⟨g, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective c
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : proj r K g * proj r K u = proj r K u * proj r K g :=
      Subgroup.mem_centralizer_singleton_iff.1 hc
    have hconj : g * u * g⁻¹ = u :=
      CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_proj_eq_of_pow_eq_one (by omega)
        p (a := 1) (b := 1)
        (by rw [pow_one, conj_pow, hup, mul_one, mul_inv_cancel]) (by rw [pow_one, hup])
        (by rw [map_mul, map_mul, map_inv, hy', mul_inv_cancel_right])
    have hgu : g * u = u * g := by
      calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [hconj]
    refine ⟨g * y * g⁻¹, hRnorm g (hN g hgu) y hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ·
    intro α hα
    have hodd : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      exact hp2
    obtain ⟨A, σ, hαA⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.automorphism_standard hodd
        hr α
    have hexact : ∀ y ∈ R, conjSp r K A (fieldSp r K σ y) = y := by
      intro y hy
      have hfix := hα _ ⟨y, hy, rfl⟩
      rw [hαA, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at hfix
      exact CFSG.ComponentClassification.CatalogueBSymplecticTwo.eq_of_proj_eq_of_pow_eq_one
        (by omega) p (a := 1) (b := 1)
        (by rw [pow_one, ← map_pow, ← map_pow, hRp y hy, map_one, map_one])
        (by rw [pow_one, hRp y hy]) hfix
    obtain ⟨y', hy', hα'⟩ := hRpt A σ hexact
    exact ⟨_, ⟨y', hy', rfl⟩, by rw [hαA, hα']⟩

end CFSG.RankThree.PartOne.KCSymplectic
