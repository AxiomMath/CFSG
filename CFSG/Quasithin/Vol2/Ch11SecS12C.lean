module

public import CFSG.Quasithin.Vol2.Ch11SecS12B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.OperatorJH
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {Y : Subgroup G} {F : Type} [Field F]

theorem false_of_labels [DecidableEq F] {Γ L K V₁ U W : Subgroup G} {x : G}
    {α₀ : ↥L →* ↥(StatedSL 2 F)} (hLY : L ≤ Y) (hxY : x ∈ Y) (hYΓ : Y ≤ Γ) (hLK : L ≤ K)
    (hα : Function.Surjective α₀) (hV₁W : V₁ ≤ W) (hWU : W < U)
    (hUab : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁)
    (hΓV₁ : Γ ≤ Subgroup.normalizer (V₁ : Set G)) (hΓU : Γ ≤ Subgroup.normalizer (U : Set G))
    {ω : F} (hω : ω ≠ 1) {l₀ : List (Subgroup G × Option F)}
    (hl₀ : IsLabSeries Y L x α₀ V₁ l₀ U) (h1 : Multiset.count 1 (labMultiset l₀) = 1)
    (hωc : Multiset.count ω (labMultiset l₀) = 1) (htop : IsLabFactor Y L x α₀ W U (some 1))
    (hO : ⁅U, pCoreOf 2 L⁆ ≤ W)
    (hB : ∀ C S : Subgroup G, V₁ ≤ C → S ≤ U → IsYSimple Γ C S →
      (∃ k ∈ K, ∃ s ∈ S, k * s * k⁻¹ * s⁻¹ ∉ C) →
      ∃ (μ : F) (j : ℕ), j < 3 ∧ μ ^ 3 = 1 ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries Y L x α₀ C l S ∧
          labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F)) ∧
        (j = 0 → ∀ J : Subgroup G, ⁅S, pCoreOf 2 L⁆ ⊔ C ≤ J → J ≤ S →
          (∀ v ∈ S, x * v * x⁻¹ * v⁻¹ ∈ J) → J = S)) : False := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hJH := operatorJHNatEig_holds G Y L x 2 F α₀ hLY hxY le_rfl hα
  have hB' : ∀ C S : Subgroup G, V₁ ≤ C → S ≤ U → IsYSimple Γ C S →
      (∃ k ∈ K, ∃ s ∈ S, k * s * k⁻¹ * s⁻¹ ∉ C) →
      ∃ (μ : F) (j : ℕ), j < 3 ∧ μ ^ 3 = 1 ∧
        ∃ l : List (Subgroup G × Option F), IsLabSeries Y L x α₀ C l S ∧
          labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F) := by
    intro C S h1 h2 h3 h4
    obtain ⟨μ, j, hj, hμ3, hl, -⟩ := hB C S h1 h2 h3 h4
    exact ⟨μ, j, hj, hμ3, hl⟩
  have hWUle : W ≤ U := hWU.le
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := hYΓ.trans hΓU
  obtain ⟨C, ⟨hV₁C, hCW, hΓC⟩, hCmax⟩ := Set.exists_max_image
    {C : Subgroup G | V₁ ≤ C ∧ C ≤ W ∧ Γ ≤ Subgroup.normalizer (C : Set G)}
    (fun C => Nat.card ↥C) (Set.toFinite _) ⟨V₁, le_rfl, hV₁W, hΓV₁⟩
  have hCU : C ≤ U := hCW.trans hWUle
  obtain ⟨S, ⟨hCS, hSU, hΓS⟩, hSmin⟩ := Set.exists_min_image
    {S : Subgroup G | C < S ∧ S ≤ U ∧ Γ ≤ Subgroup.normalizer (S : Set G)}
    (fun S => Nat.card ↥S) (Set.toFinite _) ⟨U, lt_of_le_of_lt hCW hWU, le_rfl, hΓU⟩
  have hSW : ¬ S ≤ W := fun h =>
    absurd (hCmax S ⟨hV₁C.trans hCS.le, h, hΓS⟩) (not_le.mpr (Subgroup.card_lt_of_lt hCS))
  have hsimple : IsYSimple Γ C S := by
    refine ⟨hCS, le_normalizer_of_comm hV₁C hCU hSU hUab, hΓC, hΓS,
      fun J hCJ hJS _ hΓJ => ?_⟩
    by_cases hJC : J = C
    · exact Or.inl hJC
    right
    have hCJ' : C < J := lt_of_le_of_ne hCJ (Ne.symm hJC)
    exact Subgroup.eq_of_le_of_card_ge hJS (hSmin J ⟨hCJ', hJS.trans hSU, hΓJ⟩)
  have hYS : Y ≤ Subgroup.normalizer (S : Set G) := hYΓ.trans hΓS
  have hLS : L ≤ Subgroup.normalizer (S : Set G) := hLY.trans hYS
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := hYS hxY
  have hnatSW : IsNatEigSection L x α₀ (S ⊓ W) S 1 := by
    obtain ⟨β, hβs, hβk, hβK, hβx⟩ := htop.2.2.2.2.2
    let β' : ↥S →* Multiplicative (Fin 2 → F) := β.comp (Subgroup.inclusion hSU)
    obtain ⟨s, hsS, hsW⟩ := Set.not_subset.mp hSW
    refine ⟨β', ?_, fun c => ?_, fun k c c' hc' => ?_, fun c c' hc' => ?_⟩
    · let T : AddSubgroup (Fin 2 → F) :=
        { carrier := {v | ∃ c : ↥S, Multiplicative.toAdd (β' c) = v}
          add_mem' := by
            rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
            exact ⟨c * c', by rw [map_mul, toAdd_mul]⟩
          zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
          neg_mem' := by
            rintro _ ⟨c, rfl⟩
            exact ⟨c⁻¹, by rw [map_inv, toAdd_inv]⟩ }
      have hTinv : ∀ g : ↥(StatedSL 2 F), ∀ v ∈ T,
          (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) ∈ T := by
        rintro g v ⟨c, rfl⟩
        obtain ⟨k, rfl⟩ := hα g
        have hkc : (k : G) * c * (k : G)⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hLS k.2) _).mp c.2
        exact ⟨⟨_, hkc⟩, hβK k ⟨c, hSU c.2⟩ ⟨_, hSU hkc⟩ rfl⟩
      have hsT : Multiplicative.toAdd (β' ⟨s, hsS⟩) ∈ T := ⟨⟨s, hsS⟩, rfl⟩
      have hs0 : Multiplicative.toAdd (β' ⟨s, hsS⟩) ≠ 0 := by
        intro h0
        apply hsW
        exact (hβk _).mp (Multiplicative.toAdd.injective (h0.trans toAdd_one.symm))
      have hT := eq_top_of_slMulVec_mem (le_refl 2) hTinv hsT hs0
      intro y
      have hy : Multiplicative.toAdd y ∈ T := by rw [hT]; exact AddSubgroup.mem_top _
      obtain ⟨c, hc⟩ := hy
      exact ⟨c, Multiplicative.toAdd.injective hc⟩
    · show β ⟨c, hSU c.2⟩ = 1 ↔ (c : G) ∈ S ⊓ W
      rw [hβk]
      exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
    · exact hβK k ⟨c, hSU c.2⟩ ⟨c', hSU c'.2⟩ hc'
    · exact hβx ⟨c, hSU c.2⟩ ⟨c', hSU c'.2⟩ hc'
  have hnc : ∃ k ∈ K, ∃ s ∈ S, k * s * k⁻¹ * s⁻¹ ∉ C := by
    by_contra hc
    push Not at hc
    exact IsNatEigSection.not_centralized hnatSW le_rfl hα hLS fun k hk s hs =>
      ⟨hCS.le (hc k (hLK hk) s hs), hCW (hc k (hLK hk) s hs)⟩
  obtain ⟨μ, j, hj, hμ3, ⟨l₁, hl₁, hm₁⟩, hhead⟩ := hB C S hV₁C hSU hsimple hnc
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := hYΓ.trans hΓC
  have hV₁U : V₁ ≤ U := hV₁C.trans hCU
  obtain ⟨la, lb, hla, hlb, hab⟩ := (hJH V₁ U l₀ hl₀).2 C hV₁C hCU
    (le_normalizer_of_comm le_rfl hV₁U hCU hUab) (le_normalizer_of_comm hV₁C hCU le_rfl hUab) hYC
  obtain ⟨lb', lc, hlb', hlc, hbc⟩ := (hJH C U lb hlb).2 S hCS.le hSU
    (le_normalizer_of_comm hV₁C hCU hSU hUab)
    (le_normalizer_of_comm (hV₁C.trans hCS.le) hSU le_rfl hUab) hYS
  have hm' : labMultiset lb' = labMultiset l₁ := (hJH C S l₁ hl₁).1 lb' hlb'
  rw [hm', hm₁] at hbc
  have hsum : labMultiset l₀ = labMultiset la +
      (({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F) + labMultiset lc) := by
    rw [← hab, ← hbc]
  have hc1 := h1
  rw [hsum, Multiset.count_add, Multiset.count_add] at hc1
  have hc1' := one_le_count_tw hμ3 hj
  have ha0 : Multiset.count 1 (labMultiset la) = 0 := by omega
  have hc0 : Multiset.count 1 (labMultiset lc) = 0 := by omega
  obtain ⟨ta, hta⟩ := exists_ySeries (Y := Γ) _ rfl hV₁C
    (le_normalizer_of_comm le_rfl hV₁U hCU hUab) hΓV₁ hΓC
  obtain ⟨tc, htc⟩ := exists_ySeries (Y := Γ) _ rfl hSU
    (le_normalizer_of_comm (hV₁C.trans hCS.le) hSU le_rfl hUab) hΓS hΓU
  have hza := labMultiset_eq_zero_of_count hLY hxY hYΓ hLK hα hUab hB' ta V₁ C le_rfl hCU hta
    la hla ha0
  have hzc := labMultiset_eq_zero_of_count hLY hxY hYΓ hLK hα hUab hB' tc S U
    (hV₁C.trans hCS.le) le_rfl htc lc hlc hc0
  rw [hza, hzc, zero_add, add_zero] at hsum
  rw [hsum] at hωc
  have hj0 := j_eq_zero_of_count hμ3 hj hω hωc
  have hH₀ : ⁅S, pCoreOf 2 L⁆ ⊔ C ≤ S ⊓ W := by
    refine sup_le (le_inf ?_ ((Subgroup.commutator_mono hSU le_rfl).trans hO))
      (le_inf hCS.le hCW)
    exact Subgroup.commutator_le.mpr fun s hs p hp => by
      have hpS := hLS (Subgroup.map_subtype_le _ hp)
      have h1 : p * s⁻¹ * p⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp hpS _).mp (S.inv_mem hs)
      rw [commutatorElement_def]
      have e : s * p * s⁻¹ * p⁻¹ = s * (p * s⁻¹ * p⁻¹) := by group
      rw [e]
      exact S.mul_mem hs h1
  have hxc : ∀ v ∈ S, x * v * x⁻¹ * v⁻¹ ∈ S ⊓ W := by
    intro v hv
    obtain ⟨β, -, hβk, -, hβx⟩ := hnatSW
    have hv' : x * v * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS v).mp hv
    have e1 := hβx ⟨v, hv⟩ ⟨_, hv'⟩ rfl
    rw [one_smul] at e1
    have e2 : β ⟨_, hv'⟩ = β ⟨v, hv⟩ := Multiplicative.toAdd.injective e1
    have hmem : x * v * x⁻¹ * v⁻¹ ∈ S := S.mul_mem hv' (S.inv_mem hv)
    have e3 : β ⟨_, hmem⟩ = 1 := by
      have : (⟨_, hmem⟩ : ↥S) = ⟨_, hv'⟩ * ⟨v, hv⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, e2, mul_inv_cancel]
    exact (hβk _).mp e3
  exact hSW ((hhead hj0 (S ⊓ W) hH₀ inf_le_left hxc).symm ▸ inf_le_right)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
