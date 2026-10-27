module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsTab
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsV1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsV2

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem normal_subgroupOf_of_conj {Y V : Subgroup Γ} {E : List Γ}
    (hY : Y = Subgroup.closure {g | g ∈ E}) (hVY : V ≤ Y)
    (h : ∀ g ∈ E, ∀ v ∈ V, g * v * g⁻¹ ∈ V) : (V.subgroupOf Y).Normal := by
  have hnorm : ∀ g ∈ E, g ∈ Subgroup.normalizer (V : Set Γ) := by
    intro g hg
    have hle : V.map (MulAut.conj g).toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact h g hg v hv
    have heq : V.map (MulAut.conj g).toMonoidHom = V :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hYN : Y ≤ Subgroup.normalizer (V : Set Γ) := by
    rw [hY, Subgroup.closure_le]
    exact fun g hg => hnorm g hg
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVY).mpr hYN

theorem pCore_eq_of_normal_card {Y V : Subgroup Γ} {k : ℕ} (hVY : V ≤ Y)
    (hVn : (V.subgroupOf Y).Normal) (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ k)
    (hV : Nat.card V = 2 ^ k) : CFSG.pCore 2 ↥Y = V.subgroupOf Y := by
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card hV
  have hV2' : IsPGroup 2 ↥(V.subgroupOf Y) := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVY).symm
  have hle : V.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := le_sSup ⟨hVn, hV2'⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv, hV]

theorem pCore_equiv_of_data {Y : Subgroup Γ} {E : List Γ} (hY : Y = Subgroup.closure {g | g ∈ E})
    {mulf : ℕ → ℕ → ℕ} {x : ℕ → Γ} (hxY : ∀ i < 64, x i ∈ Y) (h0 : x 0 = 1)
    (hinj : ∀ i < 64, ∀ k < 64, x i = x k → i = k)
    (hmul : ∀ i < 64, ∀ k < 64, mulf i k < 64 ∧ x i * x k = x (mulf i k))
    (hconj : ∀ g ∈ E, ∀ i < 64, ∃ k < 64, g * x i * g⁻¹ = x k)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ 6) :
    ∃ (V : Subgroup Γ) (idx : Fin 64 ≃ V), Nonempty (↥(CFSG.pCore 2 ↥Y) ≃* ↥V) ∧
      ∀ (i k : Fin 64) (hik : mulf i k < 64), idx ⟨mulf i k, hik⟩ = idx i * idx k := by
  obtain ⟨V, idx, hidx, hidxm⟩ := tab_group (by norm_num : 0 < 64) h0 hinj hmul
  have hVmem : ∀ v ∈ V, ∃ i : Fin 64, x i = v := fun v hv => by
    obtain ⟨i, hi⟩ := idx.surjective ⟨v, hv⟩
    exact ⟨i, by rw [← hidx i, hi]⟩
  have hVY : V ≤ Y := fun v hv => by
    obtain ⟨i, rfl⟩ := hVmem v hv
    exact hxY i i.2
  have hVn : (V.subgroupOf Y).Normal := by
    refine normal_subgroupOf_of_conj hY hVY fun g hg v hv => ?_
    obtain ⟨i, rfl⟩ := hVmem v hv
    obtain ⟨k, hk, hkeq⟩ := hconj g hg i i.2
    rw [hkeq, ← hidx ⟨k, hk⟩]
    exact (idx ⟨k, hk⟩).2
  have hcardV : Nat.card V = 2 ^ 6 := by
    rw [← Nat.card_congr idx, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have heq := pCore_eq_of_normal_card hVY hVn hP hcardV
  exact ⟨V, idx, ⟨(MulEquiv.subgroupCongr heq).trans (Subgroup.subgroupOfEquivOfLe hVY)⟩, hidxm⟩

theorem isZ4StarExtra2_pCore_of_data {Y : Subgroup Γ} {E : List Γ}
    (hY : Y = Subgroup.closure {g | g ∈ E}) {x : ℕ → Γ} (hxY : ∀ i < 64, x i ∈ Y) (h0 : x 0 = 1)
    (hinj : ∀ i < 64, ∀ k < 64, x i = x k → i = k)
    (hmul : ∀ i < 64, ∀ k < 64, hsV1Mul i k < 64 ∧ x i * x k = x (hsV1Mul i k))
    (hconj : ∀ g ∈ E, ∀ i < 64, ∃ k < 64, g * x i * g⁻¹ = x k)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ 6) : IsZ4StarExtra2 ↥(CFSG.pCore 2 ↥Y) := by
  obtain ⟨V, idx, ⟨e⟩, hm⟩ := pCore_equiv_of_data hY hxY h0 hinj hmul hconj hP
  exact IsZ4StarExtra2.of_mulEquiv e.symm (isZ4StarExtra2_of_idx idx hm)

theorem isZ4Cubed_pCore_of_data {Y : Subgroup Γ} {E : List Γ}
    (hY : Y = Subgroup.closure {g | g ∈ E}) {x : ℕ → Γ} (hxY : ∀ i < 64, x i ∈ Y) (h0 : x 0 = 1)
    (hinj : ∀ i < 64, ∀ k < 64, x i = x k → i = k)
    (hmul : ∀ i < 64, ∀ k < 64, hsV2Mul i k < 64 ∧ x i * x k = x (hsV2Mul i k))
    (hconj : ∀ g ∈ E, ∀ i < 64, ∃ k < 64, g * x i * g⁻¹ = x k)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ 6) : IsZ4Cubed ↥(CFSG.pCore 2 ↥Y) := by
  obtain ⟨V, idx, ⟨e⟩, hm⟩ := pCore_equiv_of_data hY hxY h0 hinj hmul hconj hP
  obtain ⟨f⟩ := isZ4Cubed_of_idx idx hm
  exact ⟨e.trans f⟩

end Abstract

end CFSG.Quasithin.A312Hs
