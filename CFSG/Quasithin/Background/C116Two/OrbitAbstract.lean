module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.C116Two

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_commute {Y K : Subgroup G} (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) :
    Y ≤ Subgroup.normalizer (K : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : y * x = x * y := hYK y hy x hx
    have h2 : y * x * y⁻¹ = x := by rw [h1]; group
    rwa [h2]
  · intro hk
    have h1 := hYK y hy _ hk
    have h2 : y * (y * x * y⁻¹) = y * x := by rw [h1]; group
    have h3 : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = y⁻¹ * (y * (y * x * y⁻¹)) := by group
        _ = y⁻¹ * (y * x) := by rw [h2]
        _ = x := by group
    rwa [h3] at hk

theorem relIndex_sup_eq_of_le_normalizer' {Y K : Subgroup G} (hY : Y ≤ Subgroup.normalizer (K : Set G)) :
    K.relIndex (Y ⊔ K) = K.relIndex Y := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hY
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hY
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient Y K hY).toEquiv.symm

theorem card_sup_mul_card_inf_of_commute {Y K : Subgroup G}
    (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y) :
    Nat.card ↥(Y ⊔ K) * Nat.card ↥(Y ⊓ K) = Nat.card ↥Y * Nat.card ↥K := by
  have h1 := relIndex_sup_eq_of_le_normalizer' (le_normalizer_of_commute hYK)
  have h2 := Subgroup.relIndex_mul_card K (Y ⊔ K)
  have h3 := Subgroup.relIndex_mul_card K Y
  have h4 : K ⊓ (Y ⊔ K) = K := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3]
  ring

theorem card_mul_le_of_le_sup {S Y K : Subgroup G} (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y)
    (hS : S ≤ Y ⊔ K) :
    Nat.card ↥S * Nat.card ↥(Y ⊓ K) ≤ Nat.card ↥(S ⊓ K) * Nat.card ↥Y := by
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_commute hYK
  have hSN : S ≤ Subgroup.normalizer (K : Set G) :=
    hS.trans (sup_le hYN Subgroup.le_normalizer)
  have h1 := relIndex_sup_eq_of_le_normalizer' hSN
  have h2 := relIndex_sup_eq_of_le_normalizer' hYN
  have h3 : K.relIndex (S ⊔ K) ≤ K.relIndex (Y ⊔ K) :=
    Subgroup.relIndex_le_of_le_right (sup_le hS le_sup_right) Subgroup.index_ne_zero_of_finite
  rw [h1, h2] at h3
  have h4 := Subgroup.relIndex_mul_card K S
  have h5 := Subgroup.relIndex_mul_card K Y
  rw [inf_comm] at h4 h5
  rw [← h4, ← h5]
  calc K.relIndex S * Nat.card ↥(S ⊓ K) * Nat.card ↥(Y ⊓ K)
      = K.relIndex S * (Nat.card ↥(S ⊓ K) * Nat.card ↥(Y ⊓ K)) := by ring
    _ ≤ K.relIndex Y * (Nat.card ↥(S ⊓ K) * Nat.card ↥(Y ⊓ K)) := Nat.mul_le_mul_right _ h3
    _ = Nat.card ↥(S ⊓ K) * (K.relIndex Y * Nat.card ↥(Y ⊓ K)) := by ring

theorem iSup_inf_centralizers_le {ι : Type} [DecidableEq ι] (U Z L : ι → Subgroup G)
    (hUab : ∀ i j, ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hLU : ∀ i j, i ≠ j → ∀ l ∈ L i, ∀ u ∈ U j, l * u = u * l)
    (hZ : ∀ i, Z i = U i ⊓ Subgroup.centralizer (L i : Set G)) (s : Finset ι) :
    (⨆ i ∈ s, U i) ⊓ (⨅ i ∈ s, Subgroup.centralizer (L i : Set G)) ≤ ⨆ i ∈ s, Z i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    intro x hx
    obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [Finset.iSup_insert] at hxW
    rw [Finset.iInf_insert] at hxC
    rw [Finset.iSup_insert]
    obtain ⟨hxCj, hxCs⟩ := Subgroup.mem_inf.mp hxC
    set Ws : Subgroup G := ⨆ i ∈ s, U i with hWs
    have hWsC : Ws ≤ Subgroup.centralizer (U j : Set G) := by
      refine iSup₂_le fun i _ x hx => ?_
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => hUab j i y hy x hx
    have hcomm : ∀ y ∈ U j, ∀ k ∈ Ws, y * k = k * y := fun y hy k hk =>
      Subgroup.mem_centralizer_iff.mp (hWsC hk) y hy
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (U j) Ws
      (le_normalizer_of_commute hcomm)
    have hx' : x ∈ ((U j ⊔ Ws : Subgroup G) : Set G) := hxW
    rw [hmul] at hx'
    obtain ⟨u, hu, w, hw, rfl⟩ := hx'
    have hWsCj : Ws ≤ Subgroup.centralizer (L j : Set G) := by
      refine iSup₂_le fun i hi x hx => ?_
      have hij : j ≠ i := fun h => hj (h ▸ hi)
      exact Subgroup.mem_centralizer_iff.mpr fun l hl => hLU j i hij l hl x hx
    have huC : u ∈ Subgroup.centralizer (L j : Set G) := by
      have := (Subgroup.centralizer (L j : Set G)).mul_mem hxCj
        ((Subgroup.centralizer (L j : Set G)).inv_mem (hWsCj hw))
      simpa using this
    have huZ : u ∈ Z j := by
      rw [hZ j]
      exact Subgroup.mem_inf.mpr ⟨hu, huC⟩
    have hwC : w ∈ ⨅ i ∈ s, Subgroup.centralizer (L i : Set G) := by
      rw [Subgroup.mem_iInf]
      intro i
      rw [Subgroup.mem_iInf]
      intro hi
      have hxi : u * w ∈ Subgroup.centralizer (L i : Set G) :=
        (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hxCs) i)) hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      have hui : u ∈ Subgroup.centralizer (L i : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun l hl => hLU i j hij l hl u hu
      have := (Subgroup.centralizer (L i : Set G)).mul_mem
        ((Subgroup.centralizer (L i : Set G)).inv_mem hui) hxi
      simpa using this
    have hwZ := ih (Subgroup.mem_inf.mpr ⟨hw, hwC⟩)
    exact Subgroup.mul_mem_sup huZ hwZ

theorem iSup_inf_iInf_centralizer_le {ι : Type} [Fintype ι] [DecidableEq ι] (U Z L : ι → Subgroup G)
    (hUab : ∀ i j, ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hLU : ∀ i j, i ≠ j → ∀ l ∈ L i, ∀ u ∈ U j, l * u = u * l)
    (hZ : ∀ i, Z i = U i ⊓ Subgroup.centralizer (L i : Set G)) :
    (⨆ i, U i) ⊓ (⨅ i, Subgroup.centralizer (L i : Set G)) ≤ ⨆ i, Z i := by
  have := iSup_inf_centralizers_le U Z L hUab hLU hZ Finset.univ
  simpa using this

theorem card_biSup_mul_prod_eq {ι : Type} [DecidableEq ι] (U Z L : ι → Subgroup G)
    (hZU : ∀ i, Z i ≤ U i) (hUab : ∀ i j, ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hLU : ∀ i j, i ≠ j → ∀ l ∈ L i, ∀ u ∈ U j, l * u = u * l)
    (hZ : ∀ i, Z i = U i ⊓ Subgroup.centralizer (L i : Set G)) (s : Finset ι) :
    Nat.card ↥(⨆ i ∈ s, U i) * ∏ i ∈ s, Nat.card ↥(Z i) =
      Nat.card ↥(⨆ i ∈ s, Z i) * ∏ i ∈ s, Nat.card ↥(U i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.iSup_insert, Finset.iSup_insert, Finset.prod_insert hj, Finset.prod_insert hj]
    set Ws : Subgroup G := ⨆ i ∈ s, U i with hWs
    set Cs : Subgroup G := ⨆ i ∈ s, Z i with hCs
    set PZ : ℕ := ∏ i ∈ s, Nat.card ↥(Z i) with hPZ
    set PU : ℕ := ∏ i ∈ s, Nat.card ↥(U i) with hPU
    have hCsWs : Cs ≤ Ws := iSup₂_mono fun i _ => hZU i
    have hWsC : Ws ≤ Subgroup.centralizer (U j : Set G) := by
      refine iSup₂_le fun i _ x hx => ?_
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => hUab j i y hy x hx
    have hcommU : ∀ y ∈ U j, ∀ k ∈ Ws, y * k = k * y := fun y hy k hk =>
      Subgroup.mem_centralizer_iff.mp (hWsC hk) y hy
    have hcommZ : ∀ y ∈ Z j, ∀ k ∈ Cs, y * k = k * y := fun y hy k hk =>
      hcommU y (hZU j hy) k (hCsWs hk)
    have hWsCj : Ws ≤ Subgroup.centralizer (L j : Set G) := by
      refine iSup₂_le fun i hi x hx => ?_
      have hij : j ≠ i := fun h => hj (h ▸ hi)
      exact Subgroup.mem_centralizer_iff.mpr fun l hl => hLU j i hij l hl x hx
    have e1 := card_sup_mul_card_inf_of_commute hcommU
    have e2 := card_sup_mul_card_inf_of_commute hcommZ
    have e3 : U j ⊓ Ws = Z j ⊓ Cs := by
      refine le_antisymm ?_ (inf_le_inf (hZU j) hCsWs)
      intro x hx
      obtain ⟨hxU, hxW⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hZ j]
        exact Subgroup.mem_inf.mpr ⟨hxU, hWsCj hxW⟩
      · refine (iSup_inf_centralizers_le U Z L hUab hLU hZ s) (Subgroup.mem_inf.mpr ⟨hxW, ?_⟩)
        rw [Subgroup.mem_iInf]
        intro i
        rw [Subgroup.mem_iInf]
        intro hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        exact Subgroup.mem_centralizer_iff.mpr fun l hl => hLU i j hij l hl x hxU
    rw [e3] at e1
    have hm : 0 < Nat.card ↥(Z j ⊓ Cs) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hm ?_
    calc Nat.card ↥(U j ⊔ Ws) * (Nat.card ↥(Z j) * PZ) * Nat.card ↥(Z j ⊓ Cs)
        = (Nat.card ↥(U j ⊔ Ws) * Nat.card ↥(Z j ⊓ Cs)) * Nat.card ↥(Z j) * PZ := by ring
      _ = (Nat.card ↥(U j) * Nat.card ↥Ws) * Nat.card ↥(Z j) * PZ := by rw [e1]
      _ = Nat.card ↥(U j) * Nat.card ↥(Z j) * (Nat.card ↥Ws * PZ) := by ring
      _ = Nat.card ↥(U j) * Nat.card ↥(Z j) * (Nat.card ↥Cs * PU) := by rw [ih]
      _ = (Nat.card ↥(Z j ⊔ Cs) * Nat.card ↥(Z j ⊓ Cs)) * Nat.card ↥(U j) * PU := by
          rw [e2]; ring
      _ = Nat.card ↥(Z j ⊔ Cs) * (Nat.card ↥(U j) * PU) * Nat.card ↥(Z j ⊓ Cs) := by ring

theorem card_iSup_mul_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι] (U Z L : ι → Subgroup G)
    (hZU : ∀ i, Z i ≤ U i) (hUab : ∀ i j, ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hLU : ∀ i j, i ≠ j → ∀ l ∈ L i, ∀ u ∈ U j, l * u = u * l)
    (hZ : ∀ i, Z i = U i ⊓ Subgroup.centralizer (L i : Set G)) :
    Nat.card ↥(⨆ i, U i) * ∏ i, Nat.card ↥(Z i) = Nat.card ↥(⨆ i, Z i) * ∏ i, Nat.card ↥(U i) := by
  have := card_biSup_mul_prod_eq U Z L hZU hUab hLU hZ Finset.univ
  simpa using this

end CFSG.Quasithin.C116Two
