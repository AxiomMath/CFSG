module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedS
public import CFSG.RankThree.GF2n.Parrott.SpinTFacts
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Sporadic.Schreier (tab tab_eq)
open scoped Matrix

local notation "P45" => Equiv.Perm (Fin 45)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)


@[expose] def rangeRho (s : A45) : Set V :=
  Set.range fun v : V => ((rhoA s : GL8) : Mat8) *ᵥ v + v

theorem rangeRho_conj (g s : A45) :
    rangeRho (g * s * g⁻¹) = (fun u : V => ((rhoA g : GL8) : Mat8) *ᵥ u) '' rangeRho s := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨((rhoA s : GL8) : Mat8) *ᵥ (((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v) +
      ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v, ⟨((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v, rfl⟩, ?_⟩
    show ((rhoA g : GL8) : Mat8) *ᵥ (((rhoA s : GL8) : Mat8) *ᵥ (((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v) +
      ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v) = ((rhoA (g * s * g⁻¹) : GL8) : Mat8) *ᵥ v + v
    rw [Matrix.mulVec_add, ← rhoA_mulVec_mul, ← rhoA_mulVec_mul, rhoA_mulVec_mul_inv]
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨((rhoA g : GL8) : Mat8) *ᵥ v, ?_⟩
    show ((rhoA (g * s * g⁻¹) : GL8) : Mat8) *ᵥ (((rhoA g : GL8) : Mat8) *ᵥ v) +
      ((rhoA g : GL8) : Mat8) *ᵥ v = ((rhoA g : GL8) : Mat8) *ᵥ (((rhoA s : GL8) : Mat8) *ᵥ v + v)
    rw [Matrix.mulVec_add, ← rhoA_mulVec_mul, ← rhoA_mulVec_mul, mul_assoc, inv_mul_cancel,
      mul_one]

theorem ncard_rangeRho_conj (g s : A45) : (rangeRho (g * s * g⁻¹)).ncard = (rangeRho s).ncard := by
  rw [rangeRho_conj]
  refine Set.ncard_image_of_injective _ ?_
  exact Function.LeftInverse.injective (g := fun v : V => ((rhoA g⁻¹ : GL8) : Mat8) *ᵥ v)
    (fun u => rhoA_mulVec_inv g u)


theorem four_le_ncard_rangeRho_tA : 4 ≤ (rangeRho tA).ncard := by
  have h : ((rhoA tA : GL8) : Mat8) = Mx := by
    have : rhoA tA = MxUnit := rhoA_x
    rw [this]
    rfl
  have e1 : Mx *ᵥ (Pi.single 0 1 : V) + Pi.single 0 1 = (Pi.single 2 1 : V) := by decide +kernel
  have e2 : Mx *ᵥ (Pi.single 1 1 : V) + Pi.single 1 1 = (![0, 1, 0, 1, 1, 0, 0, 0] : V) := by
    decide +kernel
  have e3 : Mx *ᵥ ((Pi.single 0 1 + Pi.single 1 1 : V)) + (Pi.single 0 1 + Pi.single 1 1 : V) =
      (Pi.single 2 1 : V) + (![0, 1, 0, 1, 1, 0, 0, 0] : V) := by decide +kernel
  have hcard : (({0, Pi.single 2 1, ![0, 1, 0, 1, 1, 0, 0, 0],
      (Pi.single 2 1 : V) + (![0, 1, 0, 1, 1, 0, 0, 0] : V)} : Finset V)).card = 4 := by decide
  have hsub : (({0, Pi.single 2 1, ![0, 1, 0, 1, 1, 0, 0, 0],
      (Pi.single 2 1 : V) + (![0, 1, 0, 1, 1, 0, 0, 0] : V)} : Finset V) : Set V) ⊆
      rangeRho tA := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨Pi.single 0 1, by simp only [h]; exact e1⟩
    · exact ⟨Pi.single 1 1, by simp only [h]; exact e2⟩
    · exact ⟨Pi.single 0 1 + Pi.single 1 1, by simp only [h]; exact e3⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at this
  exact this

theorem sixteen_le_ncard_rangeRho_utA : 16 ≤ (rangeRho (uA * tA)).ncard := by
  have hsub : (spinFixS : Set V) ⊆ rangeRho (uA * tA) := fun w hw => by
    obtain ⟨x, hx⟩ := exists_range_rhoA_uA_mul_tA w hw
    exact ⟨x, hx⟩
  have h16 : (spinFixS : Set V).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact card_spinFixS
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h16] at this
  exact this


private theorem mem_conjOrbit' {N : List P45} {g x : P45} :
    x ∈ conjOrbit N g ↔ ∃ c ∈ N, c * g * c⁻¹ = x := by
  simp [conjOrbit, tab_eq, List.mem_dedup, List.mem_map]

private theorem sOrbitCheck_length {N : List P45} (h : sOrbitCheck N = true) :
    (conjOrbit N t).length = 5 := by
  simp only [sOrbitCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.mem_filter, tab_eq] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

theorem ncard_normalizer_orbit_tA :
    Set.ncard {x : A45 | ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * tA * g⁻¹ = x} = 5 := by
  have ho1 := sOrbitCheck_length qa45L1Facts.s_orbits
  have hot : ∀ x : A45, (x : P45) ∈ conjOrbit (NSlist ()) t ↔
      ∃ c ∈ Subgroup.normalizer (sQA45 : Set A45), c * tA * c⁻¹ = x := by
    intro x
    rw [mem_conjOrbit']
    constructor
    · rintro ⟨c, hc, hcx⟩
      have hcA : c ∈ QA45.originalSubgroup :=
        (mem_elemsT QA45 QA45_ok c).1 (List.mem_filter.1 hc).1
      refine ⟨⟨c, hcA⟩, (mem_NSlist_iff ⟨c, hcA⟩).1 hc, Subtype.ext ?_⟩
      simpa using hcx
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, (mem_NSlist_iff c).2 hc, by simp⟩
  have hotA : ∀ b ∈ conjOrbit (NSlist ()) t, b ∈ QA45.originalSubgroup := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := mem_conjOrbit'.1 hb
    have hcA : c ∈ QA45.originalSubgroup :=
      (mem_elemsT QA45 QA45_ok c).1 (List.mem_filter.1 hc).1
    exact QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem hcA t_mem_A)
      (QA45.originalSubgroup.inv_mem hcA)
  have hnd : (conjOrbit (NSlist ()) t).Nodup := List.nodup_dedup _
  have hset : {x : A45 | ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * tA * g⁻¹ = x} =
      {x : A45 | (x : P45) ∈ conjOrbit (NSlist ()) t} := by
    ext x
    exact (hot x).symm
  rw [hset, ← Nat.card_coe_set_eq]
  have h := CFSG.Sporadic.Schreier.card_eq_length
    (fun x : A45 => (x : P45) ∈ conjOrbit (NSlist ()) t) (fun x => (x : P45))
    Subtype.val_injective (conjOrbit (NSlist ()) t) hnd (by
      intro b
      constructor
      · intro hb
        exact ⟨⟨b, hotA b hb⟩, hb, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ha)
  exact h.trans ho1


@[expose] def normalizerOrbit (s : A45) : Set A45 :=
  {x | ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), x = g * s * g⁻¹}

theorem twenty_le_ncard_orbit_mul_ncard_rangeRho {s : A45} (hs : s ∈ sQA45) (hs1 : s ≠ 1) :
    20 ≤ (normalizerOrbit s).ncard * (rangeRho s).ncard := by
  obtain ⟨-, -, -, hcl, -⟩ := qa45_normalizer_sQA45
  rcases hcl s hs hs1 with ⟨g₀, hg₀, hs₀⟩ | ⟨g₀, hg₀, hs₀⟩
  · have horb : normalizerOrbit s =
        {x | ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * tA * g⁻¹ = x} := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨g * g₀, mul_mem hg hg₀, ?_⟩
        rw [← hs₀]
        group
      · rintro ⟨g, hg, rfl⟩
        refine ⟨g * g₀⁻¹, mul_mem hg (inv_mem hg₀), ?_⟩
        rw [← hs₀]
        group
    rw [horb, ncard_normalizer_orbit_tA, ← hs₀, ncard_rangeRho_conj]
    have := four_le_ncard_rangeRho_tA
    omega
  · have hrange : 16 ≤ (rangeRho s).ncard := by
      rw [← hs₀, ncard_rangeRho_conj]
      exact sixteen_le_ncard_rangeRho_utA
    set Ot : Set A45 := {x | ∃ g ∈ Subgroup.normalizer (sQA45 : Set A45), g * tA * g⁻¹ = x} with hOt
    have hSS : {x : A45 | x ∈ sQA45 ∧ x ≠ 1} ⊆ Ot ∪ normalizerOrbit s := by
      rintro x ⟨hx, hx1⟩
      rcases hcl x hx hx1 with ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
      · exact Or.inl ⟨g, hg, hgx⟩
      · refine Or.inr ⟨g * g₀⁻¹, mul_mem hg (inv_mem hg₀), ?_⟩
        rw [← hgx, ← hs₀]
        group
    have h15 : ({x : A45 | x ∈ sQA45 ∧ x ≠ 1} : Set A45).ncard = 15 := by
      have h1 : ({x : A45 | x ∈ sQA45 ∧ x ≠ 1} : Set A45) = (sQA45 : Set A45) \ {1} := by
        ext x
        simp
      rw [h1, Set.ncard_diff_singleton_of_mem (one_mem sQA45),
        ← Nat.card_coe_set_eq]
      have := card_sQA45
      have h2 : Nat.card ↥(sQA45 : Set A45) = 16 := by
        rw [show Nat.card ↥(sQA45 : Set A45) = Nat.card ↥sQA45 from rfl, this]
        norm_num
      omega
    have hle := Set.ncard_le_ncard hSS (Set.toFinite _)
    have hun := Set.ncard_union_le Ot (normalizerOrbit s)
    have h5 : Ot.ncard = 5 := ncard_normalizer_orbit_tA
    have hOrb : 2 ≤ (normalizerOrbit s).ncard := by omega
    have := Nat.mul_le_mul hOrb hrange
    omega

end CFSG.RankThree.GF2n.Parrott
