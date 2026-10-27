module

public import CFSG.Quasithin.Background.RonanE42Defs
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_quot_le_fStarMod {K : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card ↥(fStarMod K) = p) (q q' : ↥K ⧸ CFSG.pCore 2 ↥K) :
    ⁅q, q'⁆ ∈ fStarMod K := by
  haveI : IsCyclic ↥(fStarMod K) := isCyclic_of_prime_card hcard
  haveI : (fStarMod K).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥K ⧸ CFSG.pCore 2 ↥K)).2
  have hmulAut : ∀ α β : MulAut ↥(fStarMod K), α * β = β * α := fun α β =>
    (IsCyclic.mulAutMulEquiv ↥(fStarMod K)).injective (by
      rw [map_mul, map_mul]; exact mul_comm _ _)
  have h1 : (MulAut.conjNormal (H := fStarMod K) ⁅q, q'⁆ : MulAut ↥(fStarMod K)) = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hmulAut _ _
  refine CFSG.centralizer_generalizedFitting_le (↥K ⧸ CFSG.pCore 2 ↥K) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h2 := congrArg
    (fun α : MulAut ↥(fStarMod K) => ((α ⟨f, hf⟩ : ↥(fStarMod K)) : ↥K ⧸ CFSG.pCore 2 ↥K)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem spl_of_prime {K T : Subgroup G} (hTK : T ≤ K)
    (hF : ∃ p : ℕ, p.Prime ∧ Nat.card ↥(fStarMod K) = p) :
    K ≤ Subgroup.normalizer ((fStarPre K ⊔ T : Subgroup G) : Set G) := by
  obtain ⟨p, hp, hcard⟩ := hF
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : ∀ g ∈ K, ∀ h ∈ K, ⁅g, h⁆ ∈ fStarPre K := by
    intro g hg h hh
    refine (Subgroup.mem_map).2 ⟨⁅(⟨g, hg⟩ : ↥K), ⟨h, hh⟩⁆, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact commutator_quot_le_fStarMod hcard _ _
  have hAK : fStarPre K ≤ K := Subgroup.map_subtype_le _
  have hAn : ∀ k ∈ K, ∀ a ∈ fStarPre K, k * a * k⁻¹ ∈ fStarPre K := by
    intro k hk a ha
    have hc : ⁅a⁻¹, k⁆ ∈ fStarPre K := hA a⁻¹ (K.inv_mem (hAK ha)) k hk
    have e : k * a * k⁻¹ = a * ⁅a⁻¹, k⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (fStarPre K).mul_mem ha hc
  set H : Subgroup G := fStarPre K ⊔ T with hH
  have hTH : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ H := by
    intro k hk t ht
    have hc : ⁅t⁻¹, k⁆ ∈ fStarPre K := hA t⁻¹ (K.inv_mem (hTK ht)) k hk
    have e : k * t * k⁻¹ = t * ⁅t⁻¹, k⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact H.mul_mem (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hc)
  have hfwd : ∀ k ∈ K, ∀ n ∈ H, k * n * k⁻¹ ∈ H := by
    intro k hk
    have hle : H ≤ H.comap (MulAut.conj k).toMonoidHom := by
      apply sup_le
      · intro a ha
        exact Subgroup.mem_sup_left (hAn k hk a ha)
      · intro t ht
        exact hTH k hk t ht
    intro n hn
    exact hle hn
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hfwd k hk n hn
  · intro hn
    have h := hfwd k⁻¹ (K.inv_mem hk) (k * n * k⁻¹) hn
    have e : k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n := by group
    rw [e] at h
    exact h

end CFSG.Quasithin.RonanE42
