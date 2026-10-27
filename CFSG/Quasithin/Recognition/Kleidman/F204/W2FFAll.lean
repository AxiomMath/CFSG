module

public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFCount

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup
open scoped Pointwise

theorem mem_inf_centralizer_iff {G : Type*} [Group G] {V L : Subgroup G} (T : Subgroup L)
    (v : G) :
    v ∈ (V ⊓ Subgroup.centralizer ((T.map L.subtype : Subgroup G) : Set G)) ↔
      v ∈ V ∧ ∀ t ∈ T, v * (t : G) = (t : G) * v := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hv, hc⟩
    exact ⟨hv, fun t ht => (hc _ (Subgroup.mem_map_of_mem L.subtype ht)).symm⟩
  · rintro ⟨hv, hc⟩
    refine ⟨hv, ?_⟩
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    exact (hc t ht).symm

theorem inf_centralizer_eq_of_map_eq {G : Type*} [Group G] {V L : Subgroup G}
    (φ : L →* alternatingGroup (Fin 5))
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {T₁ T₂ : Subgroup L} (h : T₁.map φ = T₂.map φ) :
    (V ⊓ Subgroup.centralizer ((T₁.map L.subtype : Subgroup G) : Set G)) =
      (V ⊓ Subgroup.centralizer ((T₂.map L.subtype : Subgroup G) : Set G)) := by
  have key : ∀ S₁ S₂ : Subgroup L, S₁.map φ = S₂.map φ →
      ∀ v ∈ V, (∀ t ∈ S₁, v * (t : G) = (t : G) * v) →
        ∀ t ∈ S₂, v * (t : G) = (t : G) * v := by
    intro S₁ S₂ hS v hv hS₁ t ht
    have hmem : φ t ∈ S₁.map φ := hS ▸ Subgroup.mem_map_of_mem φ ht
    obtain ⟨t₁, ht₁, hφ⟩ := Subgroup.mem_map.mp hmem
    have hk : φ (t₁⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hφ, inv_mul_cancel]
    have hkV : ((t₁⁻¹ * t : L) : G) ∈ Subgroup.centralizer (V : Set G) := hker _ hk
    have hk' : v * ((t₁⁻¹ * t : L) : G) = ((t₁⁻¹ * t : L) : G) * v :=
      Subgroup.mem_centralizer_iff.mp hkV v hv
    have hv1 : v * (t₁ : G) = (t₁ : G) * v := hS₁ t₁ ht₁
    have ht_eq : (t : G) = (t₁ : G) * ((t₁⁻¹ * t : L) : G) := by simp
    rw [ht_eq, ← mul_assoc, hv1, mul_assoc, hk', ← mul_assoc]
  ext v
  rw [mem_inf_centralizer_iff, mem_inf_centralizer_iff]
  constructor
  · rintro ⟨hv, hc⟩
    exact ⟨hv, key T₁ T₂ h v hv hc⟩
  · rintro ⟨hv, hc⟩
    exact ⟨hv, key T₂ T₁ h.symm v hv hc⟩

theorem exists_conj_map_eq_alt5 (K K' : Subgroup (alternatingGroup (Fin 5)))
    (hK : Nat.card K = 4) (hK' : Nat.card K' = 4) :
    ∃ x : alternatingGroup (Fin 5), K.map (MulAut.conj x).toMonoidHom = K' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : ∀ S : Subgroup (alternatingGroup (Fin 5)), Nat.card S = 4 → IsPGroup 2 S :=
    fun S hS => IsPGroup.of_card (n := 2) (by rw [hS]; norm_num)
  have hidx : ∀ S : Subgroup (alternatingGroup (Fin 5)), Nat.card S = 4 → ¬ 2 ∣ S.index := by
    intro S hS h2
    have h := Subgroup.card_mul_index (H := S)
    rw [hS, natCard_alt5] at h
    omega
  let P : Sylow 2 (alternatingGroup (Fin 5)) := (hp K hK).toSylow (hidx K hK)
  let Q : Sylow 2 (alternatingGroup (Fin 5)) := (hp K' hK').toSylow (hidx K' hK')
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) P Q
  refine ⟨y, ?_⟩
  have hc : ((y • P : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup (alternatingGroup (Fin 5))) =
      (Q : Subgroup (alternatingGroup (Fin 5))) := congrArg _ hy
  rw [Sylow.coe_subgroup_smul] at hc
  have h2 : MulAut.conj y • K = K' := hc
  rw [← h2]
  rfl

theorem card_inf_centralizer_conj_L {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup L} (g : L) :
    Nat.card ((V ⊓ Subgroup.centralizer
        ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G) :
          Subgroup G)) =
      Nat.card ((V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G) :
        Subgroup G)) := by
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := hLV g.2
  rw [map_subtype_conj A g]
  exact (card_inf_centralizer_conj hgN _).symm

theorem fa5_ff_all {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hCL : ∀ v ∈ V, (∀ l : L, v * (l : G) = (l : G) * v) → v = 1)
    {A : Subgroup L} (hA : IsPGroup 2 A)
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    (hidx : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ≤ Nat.card (A.map φ)) :
    Nat.card V = 16 ∧ Nat.card (A.map φ) = 4 ∧
      (∀ T : Subgroup L, Nat.card (T.map φ) = 4 →
        Nat.card ((V ⊓ Subgroup.centralizer ((T.map L.subtype : Subgroup G) : Set G) :
          Subgroup G)) = 4) ∧
      (∀ T₁ T₂ : Subgroup L, Nat.card (T₁.map φ) = 4 → Nat.card (T₂.map φ) = 4 →
        T₁.map φ ≠ T₂.map φ →
        (V ⊓ Subgroup.centralizer ((T₁.map L.subtype : Subgroup G) : Set G)) ⊓
          (V ⊓ Subgroup.centralizer ((T₂.map L.subtype : Subgroup G) : Set G)) = ⊥) := by
  obtain ⟨hV16, hK1, hC4, -⟩ :=
    fa5_ff_card hV2 hLV φ hφ hker hCL hA hAnt hidx
  refine ⟨hV16, hK1, ?_, ?_⟩
  · intro T hT
    obtain ⟨x, hx⟩ := exists_conj_map_eq_alt5 (A.map φ) (T.map φ) hK1 hT
    obtain ⟨g, hg⟩ := hφ x
    have hBφ : (A.map (MulAut.conj g).toMonoidHom).map φ = T.map φ := by
      rw [map_map_conj, hg, hx]
    rw [inf_centralizer_eq_of_map_eq φ hker hBφ.symm,
      card_inf_centralizer_conj_L hLV g, hC4]
  · intro T₁ T₂ h1 h2 hne
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨hvV, hvC1⟩ := Subgroup.mem_inf.mp hv1
    obtain ⟨-, hvC2⟩ := Subgroup.mem_inf.mp hv2
    have k1 : ∀ a ∈ T₁, v * (a : G) = (a : G) * v := fun a ha' =>
      (Subgroup.mem_centralizer_iff.mp hvC1 (a : G)
        (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
    have k2 : ∀ a ∈ T₂, v * (a : G) = (a : G) * v := fun a ha' =>
      (Subgroup.mem_centralizer_iff.mp hvC2 (a : G)
        (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
    exact Subgroup.mem_bot.mpr
      (klein_fixed_inf_eq_bot φ hker hCL h1 h2 hne v hvV k1 k2)
