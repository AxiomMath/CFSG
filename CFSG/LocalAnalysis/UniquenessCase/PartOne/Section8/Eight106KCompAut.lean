module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8106K

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

private lemma mulAut_conj_injective (hZ : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro a b hab
  have h1 : MulAut.conj (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : a * b⁻¹ ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h3 : (a * b⁻¹) * x * (a * b⁻¹)⁻¹ = x := by
      have h4 : MulAut.conj (a * b⁻¹) x = x := by rw [h1]; rfl
      rwa [MulAut.conj_apply] at h4
    calc x * (a * b⁻¹) = ((a * b⁻¹) * x * (a * b⁻¹)⁻¹) * (a * b⁻¹) := by rw [h3]
      _ = (a * b⁻¹) * x := by group
  rw [hZ, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.mp h2

private lemma conj_apply_mulAut (α : MulAut Y) (k : Y) :
    MulAut.conj (α k) = α * MulAut.conj k * α⁻¹ := by
  ext x
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, show α (α⁻¹ x) = x from MulEquiv.apply_symm_apply α x]

private lemma le_normalizer_comap {K : Subgroup Y} {W : Subgroup (MulAut Y)}
    (hWN : ∀ y ∈ normalizer (K : Set Y), ∀ α ∈ W,
      MulAut.conj y * α * (MulAut.conj y)⁻¹ ∈ W) :
    K ≤ normalizer ((W.comap (MulAut.conj : Y →* MulAut Y) : Subgroup Y) : Set Y) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk u hu
  have hkK : k ∈ normalizer (K : Set Y) := Subgroup.le_normalizer hk
  have h := hWN k hkK (MulAut.conj u) hu
  simpa [map_mul, map_inv] using h

private lemma apply_eq_self_of_mem {K : Subgroup Y} {W : Subgroup (MulAut Y)}
    (hWN : ∀ y ∈ normalizer (K : Set Y), ∀ α ∈ W,
      MulAut.conj y * α * (MulAut.conj y)⁻¹ ∈ W)
    (hU : W.comap (MulAut.conj : Y →* MulAut Y) = ⊥)
    {α : MulAut Y} (hα : α ∈ W) {k : Y} (hk : k ∈ K) : α k = k := by
  have hkK : k ∈ normalizer (K : Set Y) := Subgroup.le_normalizer hk
  have hW' : MulAut.conj k * α⁻¹ * (MulAut.conj k)⁻¹ ∈ W := hWN k hkK α⁻¹ (W.inv_mem hα)
  have h2 : MulAut.conj (α k * k⁻¹) = α * (MulAut.conj k * α⁻¹ * (MulAut.conj k)⁻¹) := by
    rw [map_mul, map_inv, conj_apply_mulAut]
    group
  have hmem : α k * k⁻¹ ∈ W.comap (MulAut.conj : Y →* MulAut Y) := by
    rw [Subgroup.mem_comap, h2]
    exact W.mul_mem hα hW'
  rw [hU, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

private lemma ne_inv_self {g : Y} {f : ℕ} (hgord : orderOf g = 2 ^ f + 1) (hf : 4 ≤ f) :
    g ≠ g⁻¹ := by
  intro h
  have h2 : g ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h]
    exact inv_mul_cancel g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hgord] at hdvd
  have hle : 2 ^ f + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h16 : 16 ≤ 2 ^ f := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf
  omega

private lemma false_of_mem_ne_one {K : Subgroup Y} {W : Subgroup (MulAut Y)} {g : Y}
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hgN : g ∈ normalizer (K : Set Y))
    (hWN : ∀ y ∈ normalizer (K : Set Y), ∀ α ∈ W,
      MulAut.conj y * α * (MulAut.conj y)⁻¹ ∈ W)
    (hinv : ∀ α ∈ W, α ≠ 1 → α g = g⁻¹) (hgne : g ≠ g⁻¹)
    {α : MulAut Y} (hα : α ∈ W) (hαne : α ≠ 1) : False := by
  have hαinv : α g = g⁻¹ := hinv α hα hαne
  set β : MulAut Y := MulAut.conj g * α * (MulAut.conj g)⁻¹ with hβdef
  have hβW : β ∈ W := hWN g hgN α hα
  have hβne : β ≠ 1 := by
    intro h1
    apply hαne
    calc α = (MulAut.conj g)⁻¹ * β * MulAut.conj g := by rw [hβdef]; group
      _ = 1 := by rw [h1]; group
  have hβinv : β g = g⁻¹ := hinv β hβW hβne
  have hβinvg : β⁻¹ g = g⁻¹ := by
    have h1 : β (β g) = g := by rw [hβinv, MulEquiv.map_inv, hβinv, inv_inv]
    calc β⁻¹ g = β⁻¹ (β (β g)) := by rw [h1]
      _ = β g := MulEquiv.symm_apply_apply β (β g)
      _ = g⁻¹ := hβinv
  have hγ1 : α * β⁻¹ = 1 := by
    by_contra hne
    have hmem : α * β⁻¹ ∈ W := W.mul_mem hα (W.inv_mem hβW)
    have h1 : (α * β⁻¹) g = g⁻¹ := hinv (α * β⁻¹) hmem hne
    have h2 : (α * β⁻¹) g = g := by
      rw [MulAut.mul_apply, hβinvg, MulEquiv.map_inv, hαinv, inv_inv]
    exact hgne (h2.symm.trans h1)
  have hβα : β = α := by
    have h : α = β := by
      calc α = α * β⁻¹ * β := by group
        _ = β := by rw [hγ1]; group
    exact h.symm
  have hconjβ : MulAut.conj g * α * (MulAut.conj g)⁻¹ = α := by
    rw [← hβdef]
    exact hβα
  have hcomm : MulAut.conj g * α = α * MulAut.conj g := by
    calc MulAut.conj g * α = (MulAut.conj g * α * (MulAut.conj g)⁻¹) * MulAut.conj g := by
          group
      _ = α * MulAut.conj g := by rw [hconjβ]
  have hαg : α g = g := hinj (by rw [conj_apply_mulAut, ← hcomm]; group)
  exact hgne (hαg.symm.trans hαinv)

theorem eq_bot_of_isU3 (hF : KU3Facts) {f : ℕ} (hY : IsU3 Y f) (hf : 4 ≤ f) (hfe : Even f)
    (hZ : center Y = ⊥) {K : Subgroup Y} (hK : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) f)
    (W : Subgroup (MulAut Y)) (hW2 : IsPGroup 2 W) (hWN : ∀ y ∈ normalizer (K : Set Y), ∀ α ∈ W,
      MulAut.conj y * α * (MulAut.conj y)⁻¹ ∈ W) : W = ⊥ := by
  obtain ⟨hc1, -, g, hgK, hgord, hc3⟩ := hF Y f hY hf hfe K hK hL2
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := mulAut_conj_injective hZ
  have hU2 : IsPGroup 2 (W.comap (MulAut.conj : Y →* MulAut Y)) :=
    IsPGroup.comap_of_injective hW2 _ hinj
  have hKU := le_normalizer_comap (K := K) (W := W) hWN
  have hU : W.comap (MulAut.conj : Y →* MulAut Y) = ⊥ := hc1 _ hU2 hKU
  have hfix : ∀ α ∈ W, ∀ k ∈ K, α k = k := fun α hα k hk => apply_eq_self_of_mem hWN hU hα hk
  obtain ⟨-, hinv⟩ := hc3 W hW2 hfix
  have hgN : g ∈ normalizer (K : Set Y) := Subgroup.centralizer_le_normalizer (K : Set Y) hgK
  refine (Subgroup.eq_bot_iff_forall W).mpr ?_
  intro α hα
  by_contra hαne
  exact false_of_mem_ne_one hinj hgN hWN hinv (ne_inv_self hgord hf) hα hαne

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8106K
