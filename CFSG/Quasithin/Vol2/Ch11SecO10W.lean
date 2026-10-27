module

public import CFSG.Quasithin.Vol2.Ch11SecO10V

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.H13.A7
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_aligned_sup [Finite G] {K T V : Subgroup G} (hT : quasithinIsSylowTwo T)
    {ψ : V ≃* Multiplicative (evenWeight 7)} (hKV : K ≤ normalizer (V : Set G))
    (hTV : T ≤ normalizer (V : Set G)) (hTK : T ≤ normalizer (K : Set G))
    (hKact : ∀ k ∈ K, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ k σ)
    (hKonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ k ∈ K, IsCoordAct ψ k σ) :
    ∃ ψ' : V ≃* Multiplicative (evenWeight 7),
      (∀ k ∈ K, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ' k σ) ∧
      (∀ σ ∈ alternatingGroup (Fin 7), ∃ k ∈ K, IsCoordAct ψ' k σ) ∧
      ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ' t σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := K ⊔ T with hNdef
  have hNV : N ≤ normalizer (V : Set G) := sup_le hKV hTV
  have hNK : N ≤ normalizer (K : Set G) := sup_le le_normalizer hTK
  have hNact : ∀ n ∈ N, ∃ σ, IsCoordAct ψ n σ := fun n hn =>
    exists_coordAct hKV hKact hKonto (hNV hn) (hNK hn)
  set ρ := coordRep ψ hNV hNact with hρ
  set B := ρ.range with hBdef
  have hρspec : ∀ n : N, IsCoordAct ψ n (ρ n) := coordRep_spec ψ hNV hNact
  have hρeq : ∀ (n : N) {σ : Perm (Fin 7)}, IsCoordAct ψ n σ → ρ n = σ := fun n σ hσ =>
    IsCoordAct.unique ψ (hNV n.2) (hρspec n) hσ
  have hAB : alternatingGroup (Fin 7) ≤ B := by
    intro σ hσ
    obtain ⟨k, hk, hact⟩ := hKonto σ hσ
    exact ⟨⟨k, Subgroup.mem_sup_left hk⟩, hρeq _ hact⟩
  have hB := eq_alternating_or_eq_top hAB
  set TG : Sylow 2 G := hT.1.toSylow hT.2 with hTG
  have hTGcoe : (TG : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  have hTN : (TG : Subgroup G) ≤ N := hTGcoe ▸ le_sup_right
  set TN : Sylow 2 N := TG.subtype hTN with hTNdef
  set TB : Sylow 2 B := TN.mapSurjective ρ.rangeRestrict_surjective with hTBdef
  obtain ⟨hS2, hSidx⟩ := sevenP_inf_isSylow hB
  set S0 : Sylow 2 B := hS2.toSylow hSidx with hS0def
  have hS0coe : (S0 : Subgroup B) = (sevenP ⊓ B).subgroupOf B := IsPGroup.toSylow_coe hS2 hSidx
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B S0 TB
  have hTBmem : ∀ t ∈ T, ∀ htN : t ∈ N, (ρ.rangeRestrict ⟨t, htN⟩ : B) ∈ (TB : Subgroup B) :=
    fun t ht htN => ⟨⟨t, htN⟩, (show (⟨t, htN⟩ : N) ∈ (TG : Subgroup G).subgroupOf N by
      rw [mem_subgroupOf, hTGcoe]; exact ht), rfl⟩
  have hbmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ b⁻¹ * σ * b ∈ (S0 : Subgroup B) := by
    intro σ
    rw [← hb, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  set τ : Perm (Fin 7) := (b : Perm (Fin 7))⁻¹ with hτ
  refine ⟨ψ.trans (relabelE τ), fun k hk => ?_, fun σ hσ => ?_, fun t ht => ?_⟩
  · obtain ⟨σ, hσ, hact⟩ := hKact k hk
    exact ⟨τ * σ * τ⁻¹, (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ,
      (isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  · have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨k, hk, hact⟩ := hKonto _ hσ'
    exact ⟨k, hk, (isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  · have htN : t ∈ N := Subgroup.mem_sup_right ht
    have h1 := (hbmem _).1 (hTBmem t ht htN)
    rw [hS0coe, mem_subgroupOf] at h1
    have h2 : ((b⁻¹ * ρ.rangeRestrict ⟨t, htN⟩ * b : B) : Perm (Fin 7)) =
        τ * ρ ⟨t, htN⟩ * τ⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτ, inv_inv]
      rfl
    rw [h2] at h1
    exact ⟨_, h1.1, (isCoordAct_trans_relabelE_iff ψ τ).2 (hρspec ⟨t, htN⟩)⟩

end CFSG.Quasithin.Vol2.Ch11.O10
