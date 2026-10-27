module

public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.Quasithin.Vol2.Ch11SecDSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_iSup {ι : Sort*} {K : Subgroup G} {f : ι → Subgroup G}
    (h : ∀ i, K ≤ Subgroup.normalizer (f i : Set G)) :
    K ≤ Subgroup.normalizer ((⨆ i, f i : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.mp (h i hk)

theorem normal_of_le {U V₁ X : Subgroup G} (hcomm : ⁅U, U⁆ ≤ V₁) (hV₁X : V₁ ≤ X) (hXU : X ≤ U) :
    U ≤ Subgroup.normalizer (X : Set G) := by
  intro u hu
  refine mem_normalizer_of_conj (fun x hx => ?_) (fun x hx => ?_)
  · have hc : ⁅u, x⁆ ∈ V₁ := hcomm (Subgroup.commutator_mem_commutator hu (hXU hx))
    have : u * x * u⁻¹ = ⁅u, x⁆ * x := by rw [commutatorElement_def]; group
    rw [this]
    exact X.mul_mem (hV₁X hc) hx
  · have hc : ⁅u⁻¹, x⁆ ∈ V₁ :=
      hcomm (Subgroup.commutator_mem_commutator (U.inv_mem hu) (hXU hx))
    have : u⁻¹ * x * u = ⁅u⁻¹, x⁆ * x := by rw [commutatorElement_def]; group
    rw [this]
    exact X.mul_mem (hV₁X hc) hx

theorem inf_sup_eq_of_indep {U V₁ A B C : Subgroup G} (hcomm : ⁅U, U⁆ ≤ V₁) (hV₁B : V₁ ≤ B)
    (hBU : B ≤ U) (hCU : C ≤ U) (hV₁A : V₁ ≤ A) (hAB : A ⊓ B = V₁) (hC : C ⊓ (A ⊔ B) = V₁) :
    A ⊓ (B ⊔ C) = V₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf hV₁A (hV₁B.trans le_sup_left))
  have hCB : C ≤ Subgroup.normalizer (B : Set G) := hCU.trans (normal_of_le hcomm hV₁B hBU)
  have hx2 : x ∈ ((B ⊔ C : Subgroup G) : Set G) := hx.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B C hCB] at hx2
  obtain ⟨b, hb, c, hc, rfl⟩ := hx2
  have hcV : c ∈ V₁ := by
    rw [← hC]
    refine ⟨hc, ?_⟩
    have : c = b⁻¹ * (b * c) := by group
    rw [this]
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_right (B.inv_mem hb)) (Subgroup.mem_sup_left hx.1)
  rw [← hAB]
  exact ⟨hx.1, B.mul_mem hb (hV₁B hcV)⟩

theorem le_normalizer_sup {K A B : Subgroup G} (hA : K ≤ Subgroup.normalizer (A : Set G))
    (hB : K ≤ Subgroup.normalizer (B : Set G)) :
    K ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hk),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hk)]

variable [DecidableEq (Subgroup G)]

abbrev sumF (V₁ : Subgroup G) (𝒮 : Finset (Subgroup G)) : Subgroup G := V₁ ⊔ ⨆ X ∈ 𝒮, X

@[expose] def IndepF (V₁ : Subgroup G) (𝒮 : Finset (Subgroup G)) : Prop :=
  ∀ W ∈ 𝒮, W ⊓ sumF V₁ (𝒮.erase W) = V₁

theorem indepF_insert {U V₁ W' : Subgroup G} {𝒮 : Finset (Subgroup G)} (hcomm : ⁅U, U⁆ ≤ V₁)
    (hV₁U : V₁ ≤ U) (h𝒮 : ∀ X ∈ 𝒮, V₁ ≤ X ∧ X ≤ U) (hW'U : W' ≤ U) (hW' : W' ∉ 𝒮)
    (hind : IndepF V₁ 𝒮) (hmeet : W' ⊓ sumF V₁ 𝒮 = V₁) : IndepF V₁ (insert W' 𝒮) := by
  intro W hW
  rcases Finset.mem_insert.mp hW with rfl | hW𝒮
  · rwa [Finset.erase_insert hW']
  · have hne : W ≠ W' := fun h => hW' (h ▸ hW𝒮)
    rw [Finset.erase_insert_of_ne (Ne.symm hne)]
    have hsum : sumF V₁ (insert W' (𝒮.erase W)) = sumF V₁ (𝒮.erase W) ⊔ W' := by
      rw [sumF, sumF, Finset.iSup_insert, sup_left_comm, sup_comm W']
    rw [hsum]
    have hBU : sumF V₁ (𝒮.erase W) ≤ U :=
      sup_le hV₁U (iSup₂_le fun X hX => (h𝒮 X (Finset.mem_of_mem_erase hX)).2)
    refine inf_sup_eq_of_indep hcomm le_sup_left hBU hW'U (h𝒮 W hW𝒮).1 (hind W hW𝒮) ?_
    have hAB : W ⊔ sumF V₁ (𝒮.erase W) = sumF V₁ 𝒮 := by
      conv_rhs => rw [← Finset.insert_erase hW𝒮]
      rw [sumF, sumF, Finset.iSup_insert, sup_left_comm]
    rw [hAB]
    exact hmeet

variable [Finite G]

theorem exists_independent_finset {U V₁ K : Subgroup G} {𝒲 : Set (Subgroup G)}
    (hcomm : ⁅U, U⁆ ≤ V₁) (hV₁U : V₁ ≤ U) (hKV₁ : K ≤ Subgroup.normalizer (V₁ : Set G))
    (hW : ∀ W ∈ 𝒲, V₁ ≤ W ∧ W ≤ U ∧ K ≤ Subgroup.normalizer (W : Set G))
    (hirr : ∀ W ∈ 𝒲, ∀ X : Subgroup G, V₁ ≤ X → X ≤ W →
      K ≤ Subgroup.normalizer (X : Set G) → X = V₁ ∨ X = W)
    (hspan : U ≤ V₁ ⊔ ⨆ W ∈ 𝒲, W) (m : ℕ) :
    ∀ 𝒮 : Finset (Subgroup G), (∀ X ∈ 𝒮, X ∈ 𝒲) → IndepF V₁ 𝒮 →
      Nat.card U - Nat.card (sumF V₁ 𝒮) = m →
      ∃ 𝒮' : Finset (Subgroup G), (∀ X ∈ 𝒮', X ∈ 𝒲) ∧ IndepF V₁ 𝒮' ∧ sumF V₁ 𝒮' = U := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro 𝒮 h𝒮 hind hm
    have hsumU : sumF V₁ 𝒮 ≤ U := sup_le hV₁U (iSup₂_le fun X hX => (hW X (h𝒮 X hX)).2.1)
    by_cases heq : sumF V₁ 𝒮 = U
    · exact ⟨𝒮, h𝒮, hind, heq⟩
    have hex : ∃ W' ∈ 𝒲, ¬ W' ≤ sumF V₁ 𝒮 := by
      by_contra hcon
      push Not at hcon
      exact heq (le_antisymm hsumU (hspan.trans (sup_le le_sup_left (iSup₂_le hcon))))
    obtain ⟨W', hW'𝒲, hW'⟩ := hex
    have hW'𝒮 : W' ∉ 𝒮 := fun h => hW' (le_sup_of_le_right
      (le_iSup₂ (f := fun (X : Subgroup G) (_ : X ∈ 𝒮) => X) W' h))
    obtain ⟨hV₁W', hW'U, hKW'⟩ := hW W' hW'𝒲
    have hKsum : K ≤ Subgroup.normalizer (sumF V₁ 𝒮 : Set G) :=
      le_normalizer_sup hKV₁ (le_normalizer_iSup fun X => le_normalizer_iSup fun hX =>
        (hW X (h𝒮 X hX)).2.2)
    have hmeet : W' ⊓ sumF V₁ 𝒮 = V₁ := by
      rcases hirr W' hW'𝒲 (W' ⊓ sumF V₁ 𝒮) (le_inf hV₁W' le_sup_left) inf_le_left
          (fun k hk => mem_normalizer_inf (hKW' hk) (hKsum hk)) with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) hW'
    have hind' := indepF_insert hcomm hV₁U
      (fun X hX => ⟨(hW X (h𝒮 X hX)).1, (hW X (h𝒮 X hX)).2.1⟩) hW'U hW'𝒮 hind hmeet
    have hsum' : sumF V₁ (insert W' 𝒮) = sumF V₁ 𝒮 ⊔ W' := by
      rw [sumF, sumF, Finset.iSup_insert, sup_left_comm, sup_comm W']
    have hlt : sumF V₁ 𝒮 < sumF V₁ (insert W' 𝒮) := by
      rw [hsum']
      exact lt_of_le_of_ne le_sup_left fun h => hW' (h ▸ le_sup_right)
    have hcard := Subgroup.card_lt_of_lt hlt
    have hsumU' : sumF V₁ (insert W' 𝒮) ≤ U := by
      rw [hsum']
      exact sup_le hsumU hW'U
    have hcardU := Subgroup.card_le_of_le hsumU'
    refine ih _ (by omega) (insert W' 𝒮) (fun X hX => ?_) hind' rfl
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact hW'𝒲
    · exact h𝒮 X hX

omit [DecidableEq (Subgroup G)] in
theorem exists_independent_decomposition {U V₁ K : Subgroup G} {𝒲 : Set (Subgroup G)}
    (hcomm : ⁅U, U⁆ ≤ V₁) (hV₁U : V₁ ≤ U) (hKV₁ : K ≤ Subgroup.normalizer (V₁ : Set G))
    (hW : ∀ W ∈ 𝒲, V₁ ≤ W ∧ W ≤ U ∧ K ≤ Subgroup.normalizer (W : Set G))
    (hirr : ∀ W ∈ 𝒲, ∀ X : Subgroup G, V₁ ≤ X → X ≤ W →
      K ≤ Subgroup.normalizer (X : Set G) → X = V₁ ∨ X = W)
    (hspan : U ≤ V₁ ⊔ ⨆ W ∈ 𝒲, W) :
    ∃ (s : ℕ) (W : Fin s → Subgroup G), (∀ i, W i ∈ 𝒲) ∧
      (∀ i, W i ⊓ (V₁ ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j) = V₁) ∧ (V₁ ⊔ ⨆ i, W i) = U := by
  classical
  obtain ⟨𝒮, h𝒮, hind, hsum⟩ := exists_independent_finset hcomm hV₁U hKV₁ hW hirr hspan _ ∅
    (by simp) (fun W hW => absurd hW (Finset.notMem_empty W)) rfl
  set e := 𝒮.equivFin
  refine ⟨𝒮.card, fun i => ((e.symm i : 𝒮) : Subgroup G), fun i => h𝒮 _ (e.symm i).2,
    fun i => ?_, ?_⟩
  · have key : (⨆ (j : Fin 𝒮.card) (_ : j ≠ i), ((e.symm j : 𝒮) : Subgroup G)) =
        ⨆ X ∈ 𝒮.erase (e.symm i), X := by
      apply le_antisymm
      · refine iSup₂_le fun j hj => le_iSup₂ (f := fun (X : Subgroup G)
          (_ : X ∈ 𝒮.erase (e.symm i)) => X) _ ?_
        exact Finset.mem_erase.mpr ⟨fun h => hj (e.symm.injective (Subtype.ext h)), (e.symm j).2⟩
      · refine iSup₂_le fun X hX => ?_
        obtain ⟨hXne, hX𝒮⟩ := Finset.mem_erase.mp hX
        have hj : e ⟨X, hX𝒮⟩ ≠ i := fun h => hXne (by rw [← h]; simp)
        exact le_iSup₂_of_le (f := fun (j : Fin 𝒮.card) (_ : j ≠ i) =>
          ((e.symm j : 𝒮) : Subgroup G)) (e ⟨X, hX𝒮⟩) hj (by simp)
    rw [key]
    exact hind _ (e.symm i).2
  · have key : (⨆ i, ((e.symm i : 𝒮) : Subgroup G)) = ⨆ X ∈ 𝒮, X := by
      apply le_antisymm
      · exact iSup_le fun i => le_iSup₂ (f := fun (X : Subgroup G) (_ : X ∈ 𝒮) => X) _
          (e.symm i).2
      · exact iSup₂_le fun X hX => le_iSup_of_le (e ⟨X, hX⟩) (by simp)
    rw [key]
    exact hsum

end CFSG.Quasithin.Vol2.Ch11.SecD
