module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

private theorem card_three_cycles :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) => σ ^ 3 = 1 ∧ σ ≠ 1).card = 20 := by
  decide +kernel

private theorem sum_three_cycles : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 →
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 5) => σ ^ 3 = 1 ∧ σ ≠ 1),
      (fun i => y (σ.symm i)) = y := by
  decide +kernel

private theorem mem_alternatingGroup_of_pow_three {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {σ : Equiv.Perm Ω} (hσ : σ ^ 3 = 1) : σ ∈ alternatingGroup Ω := by
  refine Equiv.Perm.mem_alternatingGroup.2 ?_
  have h3 : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact h
  · rw [h] at h3
    exact absurd h3 (by decide)

theorem isCompl_commOn_fixSub_of_secNatS5 {L : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (haL : a ∉ L)
    (hS5 : SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥)
    (hZ : commOn ρ L ⊤ ⊓ fixSub ρ L = ⊥) : IsCompl (commOn ρ L ⊤) (fixSub ρ L) := by
  obtain ⟨-, -, -, φ, ψ, -, hK, hsum, -, hE⟩ := hS5
  have hnorm : ∀ m ∈ L, a * m * a⁻¹ ∈ L := fun m hm => (Subgroup.mem_normalizer_iff.1 haN m).1 hm
  have hmap := map_subgroupOf_eq_alternatingGroup ha2 hnorm haL φ
  obtain ⟨T, hT⟩ : ∃ T : Finset (Equiv.Perm (Fin 5)),
      T = Finset.univ.filter fun σ : Equiv.Perm (Fin 5) => σ ^ 3 = 1 ∧ σ ≠ 1 := ⟨_, rfl⟩
  have hmemT : ∀ σ, σ ∈ T ↔ σ ^ 3 = 1 ∧ σ ≠ 1 := fun σ => by
    rw [hT, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ σ)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Equiv.Perm (Fin 5) → G,
      ∀ σ, ℓ σ = ((φ.symm σ : ↥(L ⊔ Subgroup.zpowers a)) : G) := ⟨_, fun _ => rfl⟩
  have hℓL : ∀ σ ∈ T, ℓ σ ∈ L := fun σ hσ => by
    have h := mem_alternatingGroup_of_pow_three ((hmemT σ).1 hσ).1
    rw [← hmap, Subgroup.mem_map_equiv] at h
    rw [hℓ]
    exact Subgroup.mem_subgroupOf.1 h
  obtain ⟨ε, hε⟩ : ∃ ε : Module.End (ZMod 2) V, ∀ v, ε v = ∑ σ ∈ T, ρ (ℓ σ) v :=
    ⟨∑ σ ∈ T, ρ (ℓ σ), fun v => LinearMap.sum_apply _ _ _⟩
  have hεN : ∀ v, ε v ∈ commOn ρ L ⊤ := fun v => by
    have h1 : ε v = ∑ σ ∈ T, (ρ (ℓ σ) v - v) + T.card • v := by
      rw [hε, Finset.sum_sub_distrib, Finset.sum_const, sub_add_cancel]
    have h20 : T.card • v = 0 := by
      rw [hT, card_three_cycles, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
      have : ((20 : ℕ) : ZMod 2) = 0 := by decide
      rw [this, zero_smul]
    rw [h1, h20, add_zero]
    exact Submodule.sum_mem _ fun σ hσ => sub_mem_commOn (hℓL σ hσ) Submodule.mem_top
  have hεid : ∀ x ∈ commOn ρ L ⊤, ε x = x := fun x hx => by
    have h1 : ψ (ε x) = ψ x := by
      rw [hε, map_sum]
      calc ∑ σ ∈ T, ψ (ρ (ℓ σ) x) = ∑ σ ∈ T, (fun i => ψ x (σ.symm i)) :=
            Finset.sum_congr rfl fun σ _ => by rw [hℓ, hE _ x hx, MulEquiv.apply_symm_apply]
        _ = ψ x := by
            rw [hT]
            exact sum_three_cycles (ψ x) (hsum x hx)
    have h2 : ε x - x ∈ commOn ρ L ⊤ := sub_mem (hεN x) hx
    have h3 : ψ (ε x - x) = 0 := by rw [map_sub, h1, sub_self]
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 (hK _ h2 h3))
  have hcomm : ∀ g ∈ L, ∀ v, ρ g (ε v) = ε (ρ g v) := fun g hg v => by
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = φ ⟨g, Subgroup.mem_sup_left hg⟩ := ⟨_, rfl⟩
    have hconj : ∀ σ, ℓ (τ * σ * τ⁻¹) = g * ℓ σ * g⁻¹ := fun σ => by
      rw [hℓ, hℓ, map_mul, map_mul, map_inv, hτ, MulEquiv.symm_apply_apply]
      rfl
    rw [hε, hε, map_sum]
    refine Finset.sum_equiv (MulAut.conj τ).toEquiv (fun σ => ?_) fun σ _ => ?_
    · simp only [hmemT, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
        conj_pow, ne_eq]
      constructor
      · rintro ⟨h3, h1⟩
        refine ⟨by rw [h3, mul_one, mul_inv_cancel], fun h => h1 ?_⟩
        rwa [mul_inv_eq_one, mul_eq_left] at h
      · rintro ⟨h3, h1⟩
        refine ⟨?_, fun h => h1 (by rw [h, mul_one, mul_inv_cancel])⟩
        rwa [mul_inv_eq_one, mul_eq_left] at h3
    · simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hconj, ← glRep_mul_apply, ← glRep_mul_apply, inv_mul_cancel_right]
  refine ⟨Submodule.disjoint_def.2 fun v h₁ h₂ => ?_, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  · rw [← Submodule.mem_bot (ZMod 2), ← hZ]
    exact Submodule.mem_inf.2 ⟨h₁, h₂⟩
  · intro v _
    refine Submodule.mem_sup.2
      ⟨ε v, hεN v, v - ε v, mem_fixSub.2 fun g hg => ?_, add_sub_cancel _ _⟩
    have hn : ρ g v - v ∈ commOn ρ L ⊤ := sub_mem_commOn hg Submodule.mem_top
    have h1 : ε (ρ g v) = ε v + (ρ g v - v) := by
      rw [← hεid _ hn, ← map_add, add_sub_cancel]
    rw [map_sub, hcomm g hg v, h1]
    abel

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
