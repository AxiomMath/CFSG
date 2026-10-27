module

public import CFSG.RankThree.Native.ONSevenCentralizers
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofONTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res148

open CFSG.ONSchreier CFSG.RankThree.Native
open scoped Pointwise


theorem seven_record_zero :
    ∃ (x₀ : Equiv.Perm (Fin N)) (F₀ : Subgroup (Equiv.Perm (Fin N))),
      F₀ ≤ Subgroup.centralizer {x₀} ⊓ Pv ∧ Nat.card F₀ = 343 ∧
      Nat.card (Subgroup.centralizer {x₀} ⊓ Pv : Subgroup (Equiv.Perm (Fin N))) = 1372 ∧
      orderOf x₀ = 7 ∧ x₀ ∈ F₀ ∧
      Subgroup.centralizer (F₀ : Set (Equiv.Perm (Fin N))) ⊓ (Subgroup.centralizer {x₀} ⊓ Pv) =
        Subgroup.zpowers x₀ := by
  obtain ⟨-, -, hC, h4, -, -, -⟩ := R3E_ON_full_seven_centralizer_structures
  obtain ⟨hFC, -, hFcard, hcent, hx⟩ := onSevenF_facts 0
  obtain ⟨hCcard, -⟩ := h4 0
  have hCr := hC (Fin.castLE (by norm_num : 3 ≤ 5) 0)
  refine ⟨_, onSevenF 0, ?_, hFcard, ?_, orderOf_onSevenLine _, hx, ?_⟩
  · rw [← hCr]
    exact hFC
  · rw [← hCr]
    exact hCcard
  · rw [← hCr]
    exact hcent

theorem conj_smul_eq_map {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    MulAut.conj g • H = H.map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map_equiv, MulAut.smul_def]
  rfl

theorem sylow_seven_Pv (S : Sylow 7 Pv) :
    Nat.card S = 343 ∧ ¬ 9 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup Pv) : Set Pv)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₀, F₀, hFC, hFcard, hCcard, hord, hxF, hcent⟩ := seven_record_zero
  have hFP : F₀ ≤ Pv := hFC.trans inf_le_right
  have hxP : x₀ ∈ Pv := hFP hxF
  have hFcard' : Nat.card (F₀.subgroupOf Pv) = 7 ^ (Nat.card Pv).factorization 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv, hFcard,
      factorization_card_Pv_seven]
    norm_num
  set S₀ : Sylow 7 Pv := Sylow.ofCard _ hFcard' with hS₀
  have hS₀coe : (S₀ : Subgroup Pv) = F₀.subgroupOf Pv := rfl
  have hcard : ∀ S : Sylow 7 Pv, Nat.card S = 343 := by
    intro S
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S₀, hS₀coe,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv, hFcard]
  refine ⟨hcard S, ?_⟩
  set x : Pv := ⟨x₀, hxP⟩ with hx
  have hxcent : x₀ ∈ Subgroup.centralizer (F₀ : Set (Equiv.Perm (Fin N))) := by
    have : x₀ ∈ Subgroup.zpowers x₀ := Subgroup.mem_zpowers x₀
    rw [← hcent] at this
    exact this.1
  have hconj : ∀ r ∈ Subgroup.normalizer ((S₀ : Subgroup Pv) : Set Pv),
      r * x * r⁻¹ ∈ Subgroup.zpowers x := by
    intro r hr
    set ρ : Equiv.Perm (Fin N) := (r : Equiv.Perm (Fin N)) with hρ
    have hrF : ∀ f : Equiv.Perm (Fin N), f ∈ F₀ → ρ * f * ρ⁻¹ ∈ F₀ := by
      intro f hf
      have hfP : f ∈ Pv := hFP hf
      have h := (Subgroup.mem_normalizer_iff.mp hr ⟨f, hfP⟩).mp
        (by rw [hS₀coe, Subgroup.mem_subgroupOf]; exact hf)
      rw [hS₀coe, Subgroup.mem_subgroupOf] at h
      simpa [hρ] using h
    have hrF' : ∀ f : Equiv.Perm (Fin N), f ∈ F₀ → ρ⁻¹ * f * ρ ∈ F₀ := by
      intro f hf
      have hfP : f ∈ Pv := hFP hf
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hr) ⟨f, hfP⟩).mp
        (by rw [hS₀coe, Subgroup.mem_subgroupOf]; exact hf)
      rw [hS₀coe, Subgroup.mem_subgroupOf] at h
      simpa [hρ] using h
    have h1 : ρ * x₀ * ρ⁻¹ ∈ F₀ := hrF x₀ hxF
    have h2 : ρ * x₀ * ρ⁻¹ ∈ Subgroup.centralizer (F₀ : Set (Equiv.Perm (Fin N))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hf' := hrF' f hf
      have hc := Subgroup.mem_centralizer_iff.mp hxcent _ hf'
      calc f * (ρ * x₀ * ρ⁻¹) = ρ * ((ρ⁻¹ * f * ρ) * x₀) * ρ⁻¹ := by group
        _ = ρ * (x₀ * (ρ⁻¹ * f * ρ)) * ρ⁻¹ := by rw [hc]
        _ = ρ * x₀ * ρ⁻¹ * f := by group
    have h3 : ρ * x₀ * ρ⁻¹ ∈ Subgroup.zpowers x₀ := by
      rw [← hcent]
      exact ⟨h2, hFC h1⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h3
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hk]
    simp [hρ, hx]
  have hCx : Nat.card (Subgroup.centralizer ({x} : Set Pv)) = 1372 := by
    have heq : (Subgroup.centralizer ({x} : Set Pv)).map Pv.subtype =
        Subgroup.centralizer {x₀} ⊓ Pv := by
      ext g
      constructor
      · intro hg
        obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
        refine Subgroup.mem_inf.mpr ⟨?_, g'.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
        exact congrArg Subtype.val hg'
      · intro hg
        obtain ⟨hg1, hgP⟩ := Subgroup.mem_inf.mp hg
        refine Subgroup.mem_map.mpr ⟨⟨g, hgP⟩, ?_, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hg1 ⊢
        exact Subtype.ext hg1
    rw [← hCcard, ← heq, Subgroup.card_map_of_injective Pv.subtype_injective]
  have hS₀N : ¬ 9 ∣ Nat.card (Subgroup.normalizer ((S₀ : Subgroup Pv) : Set Pv)) := by
    intro h9
    obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) (by norm_num; exact h9)
    set R' : Subgroup Pv := R.map (Subgroup.normalizer ((S₀ : Subgroup Pv) : Set Pv)).subtype
    have hR' : Nat.card R' = 9 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hR]
      norm_num
    have hle := card_le_orderOf_of_conj_mem_zpowers (x := x) (R := R')
      (fun r hr => by
        obtain ⟨r', -, rfl⟩ := hr
        exact hconj _ r'.2)
      (by rw [hR', hCx]; norm_num)
    rw [hR', show orderOf x = orderOf x₀ from Subgroup.orderOf_mk x₀ hxP, hord] at hle
    omega
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Pv S₀ S
  intro h9
  apply hS₀N
  rw [Sylow.coe_subgroup_smul, conj_smul_eq_map, ← Subgroup.map_equiv_normalizer_eq] at h9
  rwa [Subgroup.card_map_of_injective (MulEquiv.injective _)] at h9

theorem sylow_seven_of_mulEquiv_Pv {X : Type*} [Group X] [Finite X] (φ : X ≃* Pv)
    (S : Sylow 7 X) :
    Nat.card S = 343 ∧ ¬ 9 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set S' : Sylow 7 Pv := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective S with hS'
  have hS'coe : (S' : Subgroup Pv) = (S : Subgroup X).map φ.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨h1, h2⟩ := sylow_seven_Pv S'
  refine ⟨?_, ?_⟩
  · rw [← h1, hS'coe, Subgroup.card_map_of_injective φ.injective]
  · rw [hS'coe, ← Subgroup.map_equiv_normalizer_eq,
      Subgroup.card_map_of_injective φ.injective] at h2
    exact h2

end CFSG.RankThree.PartTwo.Sec14.Res148
