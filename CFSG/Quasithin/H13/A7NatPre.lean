module

public import CFSG.Quasithin.H13.A7Coordinates

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB
open scoped Pointwise

variable {G : Type*} [Group G]

structure A7NatPre (T L V : Subgroup G) (ψ : V ≃* Multiplicative (evenWeight 7)) : Prop where
  le_T : V ≤ T
  L_le : L ≤ normalizer (V : Set G)
  T_le : T ≤ normalizer (V : Set G)
  Lact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ
  Lonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ
  Nact : ∀ n ∈ normalizer (V : Set G), ∃ σ, IsCoordAct ψ n σ
  NM : normalizer (V : Set G) ≤ normalizer (L : Set G)
  TI : ∀ m ∈ normalizer (L : Set G), CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥

namespace A7NatPre

variable {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem toConfig (h : A7NatPre T L V ψ)
    (wt26 : ∀ v : V, (hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 6) →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G))
    (wt4 : ∀ g : G, CFSG.conjugate V g ≠ V → ∀ v : V, (v : G) ∈ CFSG.conjugate V g → v ≠ 1 →
      hammingNorm (vec ψ v) = 4) :
    A7NatConfig T L V ψ :=
  ⟨h.le_T, h.L_le, h.T_le, h.Lact, h.Lonto, h.Nact, h.NM, h.TI, wt26, wt4⟩

theorem relabel (h : A7NatPre T L V ψ) (τ : Perm (Fin 7)) :
    A7NatPre T L V (ψ.trans (relabelE τ)) where
  le_T := h.le_T
  L_le := h.L_le
  T_le := h.T_le
  Lact l hl := by
    obtain ⟨σ, hσ, hact⟩ := h.Lact l hl
    refine ⟨τ * σ * τ⁻¹, ?_, (isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
    exact (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ
  Lonto σ hσ := by
    have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := h.Lonto _ hσ'
    exact ⟨l, hl, (isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  Nact n hn := by
    obtain ⟨σ, hact⟩ := h.Nact n hn
    exact ⟨τ * σ * τ⁻¹, (isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  NM := h.NM
  TI := h.TI

theorem exists_aligned [Finite G] (hT : quasithinIsSylowTwo T) (h : A7NatPre T L V ψ) :
    ∃ ψ' : V ≃* Multiplicative (evenWeight 7), A7NatPre T L V ψ' ∧
      ∀ σ : Perm (Fin 7), (∃ t ∈ T, IsCoordAct ψ' t σ) ↔
        σ ∈ sevenP ∧ ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ' n σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (V : Set G) with hNdef
  set ρ := coordRep ψ (le_refl N) h.Nact with hρ
  set B := ρ.range with hBdef
  have hρspec : ∀ n : N, IsCoordAct ψ n (ρ n) := coordRep_spec ψ (le_refl N) h.Nact
  have hρeq : ∀ (n : N) {σ : Perm (Fin 7)}, IsCoordAct ψ n σ → ρ n = σ := fun n σ hσ =>
    IsCoordAct.unique ψ n.2 (hρspec n) hσ
  have hAB : alternatingGroup (Fin 7) ≤ B := by
    intro σ hσ
    obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
    exact ⟨⟨l, h.L_le hl⟩, hρeq _ hact⟩
  have hB := eq_alternating_or_eq_top hAB
  set TG : Sylow 2 G := hT.1.toSylow hT.2 with hTG
  have hTGcoe : (TG : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  have hTN : (TG : Subgroup G) ≤ N := hTGcoe ▸ h.T_le
  set TN : Sylow 2 N := TG.subtype hTN with hTNdef
  set TB : Sylow 2 B := TN.mapSurjective ρ.rangeRestrict_surjective with hTBdef
  obtain ⟨hS2, hSidx⟩ := sevenP_inf_isSylow hB
  set S0 : Sylow 2 B := hS2.toSylow hSidx with hS0def
  have hS0coe : (S0 : Subgroup B) = (sevenP ⊓ B).subgroupOf B := IsPGroup.toSylow_coe hS2 hSidx
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B S0 TB
  have hTBmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ ∃ t ∈ T, ∃ ht : t ∈ N, ρ ⟨t, ht⟩ = σ := by
    intro σ
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : ((t : G)) ∈ T := by
        have : t ∈ (TG : Subgroup G).subgroupOf N := ht
        rw [mem_subgroupOf, hTGcoe] at this
        exact this
      exact ⟨t, ht', t.2, rfl⟩
    · rintro ⟨t, ht, htN, hσ⟩
      refine ⟨⟨t, htN⟩, ?_, Subtype.ext hσ⟩
      show (⟨t, htN⟩ : N) ∈ (TG : Subgroup G).subgroupOf N
      rw [mem_subgroupOf, hTGcoe]
      exact ht
  have hbmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ b⁻¹ * σ * b ∈ (S0 : Subgroup B) := by
    intro σ
    rw [← hb, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  set τ : Perm (Fin 7) := (b : Perm (Fin 7))⁻¹ with hτ
  refine ⟨ψ.trans (relabelE τ), h.relabel τ, fun σ => ?_⟩
  have hbB : (b : Perm (Fin 7)) ∈ B := b.2
  constructor
  · rintro ⟨t, ht, hact⟩
    rw [isCoordAct_trans_relabelE_iff'] at hact
    have htN : t ∈ N := h.T_le ht
    set σ₀ := τ⁻¹ * σ * τ with hσ₀
    have hσ₀B : σ₀ ∈ B := ⟨⟨t, htN⟩, hρeq ⟨t, htN⟩ hact⟩
    have h1 : (⟨σ₀, hσ₀B⟩ : B) ∈ (TB : Subgroup B) :=
      (hTBmem _).2 ⟨t, ht, htN, hρeq ⟨t, htN⟩ hact⟩
    rw [hbmem, hS0coe, mem_subgroupOf] at h1
    have h2 : ((b⁻¹ * ⟨σ₀, hσ₀B⟩ * b : B) : Perm (Fin 7)) = σ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show (b : Perm (Fin 7))⁻¹ * σ₀ * b = σ
      rw [hσ₀, hτ, inv_inv]
      group
    rw [h2] at h1
    exact ⟨h1.1, t, htN, (isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  · rintro ⟨hσP, n, hn, hact⟩
    rw [isCoordAct_trans_relabelE_iff'] at hact
    set σ₀ := τ⁻¹ * σ * τ with hσ₀
    have hσ₀B : σ₀ ∈ B := ⟨⟨n, hn⟩, hρeq ⟨n, hn⟩ hact⟩
    have hσB : σ ∈ B := by
      have : σ = (b : Perm (Fin 7))⁻¹ * σ₀ * b := by
        rw [hσ₀, hτ, inv_inv]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hbB) hσ₀B) hbB
    have h1 : (⟨σ₀, hσ₀B⟩ : B) ∈ (TB : Subgroup B) := by
      rw [hbmem, hS0coe, mem_subgroupOf]
      have h2 : ((b⁻¹ * ⟨σ₀, hσ₀B⟩ * b : B) : Perm (Fin 7)) = σ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        show (b : Perm (Fin 7))⁻¹ * σ₀ * b = σ
        rw [hσ₀, hτ, inv_inv]
        group
      rw [h2]
      exact ⟨hσP, hσB⟩
    obtain ⟨t, ht, htN, htσ⟩ := (hTBmem _).1 h1
    refine ⟨t, ht, (isCoordAct_trans_relabelE_iff' ψ τ).2 ?_⟩
    have := hρspec ⟨t, htN⟩
    rw [htσ] at this
    exact this

end A7NatPre

end CFSG.Quasithin.H13.A7
