module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenBlocks
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Holt.H78.Sec4AltSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm MulAction Subgroup CFSG.ABGLocalTools

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

private theorem fusion_of_isSylowOf {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (h : IsSylowOf p P K) : CFSG.Open.fusionIsSylowIn p P K :=
  ⟨h.le, h.isPGroup, fun _ hQK hQ hPQ => h.eq_of_le hPQ hQK hQ⟩

private theorem sylow_alt {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) :
    CFSG.Open.fusionIsSylowIn 2 (T ⊓ alternatingGroup Ω) (alternatingGroup Ω) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Γ ≤ normalizer (alternatingGroup Ω : Set (Perm Ω)) := by
    rw [normalizer_eq_top_iff.2 (inferInstance : (alternatingGroup Ω).Normal)]
    exact le_top
  exact fusion_of_isSylowOf (hT.inf_of_le_normalizer hA hN)

private theorem orbit_T {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) (h4 : 4 ≤ Fintype.card Ω) (x : Ω) :
    orbit T x = orbit ↥(T ⊓ alternatingGroup Ω) x :=
  CFSG.Holt.H78.orbit_eq_of_fusionIsSylowIn_alternatingGroup_of_le h4 (sylow_alt hA hT)
    hT.isPGroup inf_le_left x

private theorem digits {n a : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11) (ha : n.testBit a) :
    a = 0 ∨ a = 1 ∨ a = 3 := by
  have hlt : a < 4 := by
    by_contra h
    have h16 : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.ge_two_pow_of_testBit ha
    omega
  interval_cases n <;> interval_cases a <;> revert ha <;> decide

private theorem digit3 {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11) : n.testBit 3 := by
  interval_cases n <;> decide

private theorem digit1 {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11) : n.testBit 1 ↔ 10 ≤ n := by
  interval_cases n <;> decide

private theorem card_orbit_T {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) (h8 : 8 ≤ Fintype.card Ω) (h11 : Fintype.card Ω ≤ 11) (x : Ω) :
    Nat.card (orbit T x) = 1 ∨ Nat.card (orbit T x) = 2 ∨ Nat.card (orbit T x) = 8 := by
  obtain ⟨a, ha, hx⟩ :=
    CFSG.Holt.H78.exists_testBit_card_orbit_of_fusionIsSylowIn_alternatingGroup (by omega)
      (sylow_alt hA hT) x
  rw [orbit_T hA hT (by omega) x, hx]
  rcases digits h8 h11 ha with rfl | rfl | rfl <;> simp

private theorem orbit_T_eq {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) (h4 : 4 ≤ Fintype.card Ω) {x y : Ω}
    (h : Nat.card (orbit T x) = Nat.card (orbit T y)) : orbit T x = orbit T y := by
  rw [orbit_T hA hT h4 x, orbit_T hA hT h4 y] at h ⊢
  exact CFSG.Holt.H78.orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup h4
    (sylow_alt hA hT) h

private theorem exists_orbit_T {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) (h8 : 8 ≤ Fintype.card Ω) (h11 : Fintype.card Ω ≤ 11) :
    (∃ x : Ω, Nat.card (orbit T x) = 8) ∧
      (10 ≤ Fintype.card Ω → ∃ x : Ω, Nat.card (orbit T x) = 2) := by
  have key : ∀ a, (Fintype.card Ω).testBit a → ∃ x : Ω, Nat.card (orbit T x) = 2 ^ a := by
    intro a ha
    obtain ⟨x, hx⟩ :=
      (CFSG.Holt.H78.testBit_card_iff_of_fusionIsSylowIn_alternatingGroup (by omega)
        (sylow_alt hA hT) a).1 ha
    exact ⟨x, by rw [orbit_T hA hT (by omega) x]; exact hx⟩
  exact ⟨key 3 (digit3 h8 h11), fun h10 => key 1 ((digit1 h8 h11).2 h10)⟩

theorem exists_labelling {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) (h8 : 8 ≤ Fintype.card Ω) (h11 : Fintype.card Ω ≤ 11) :
    ∃ f : Ω → Fin 4, T ≤ normalizer (fibreStab f : Set (Perm Ω)) ∧
      Nat.card {x // f x = 0} = 4 ∧ Nat.card {x // f x = 1} = 4 ∧
      Nat.card {x // f x = 2} ≤ 2 ∧ Nat.card {x // f x = 3} ≤ 1 ∧
      (10 ≤ Fintype.card Ω → Nat.card {x // f x = 2} = 2) ∧
      ∃ t ∈ T, ∀ x, (f (t x) = 0 ↔ f x = 1) ∧ (f (t x) = 1 ↔ f x = 0) := by
  classical
  have h4 : 4 ≤ Fintype.card Ω := by omega
  obtain ⟨⟨x₀, hx₀⟩, h2ex⟩ := exists_orbit_T hA hT h8 h11
  obtain ⟨β, hβ1, hβ2, -, hβ4, hβ5⟩ := exists_blocks hT.isPGroup
  have hmem : ∀ x, x ∈ β x := fun x => (hβ1 x x).2 rfl
  have hΔc : (orbit T x₀).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hx₀
  have hB₁ : (β x₀).ncard = 4 := hβ4 x₀ (by rw [hx₀]; norm_num)
  obtain ⟨y₀, hy₀Δ, hy₀⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := β x₀)
    (t := orbit T x₀) (by omega)
  have hyorb : orbit T y₀ = orbit T x₀ := orbit_eq_iff.2 hy₀Δ
  have hB₂ : (β y₀).ncard = 4 := hβ4 y₀ (by rw [hyorb, hx₀]; norm_num)
  have hβy₀ : β y₀ ⊆ orbit T x₀ := hyorb ▸ hβ2 y₀
  have hdisj : ∀ z, z ∈ β x₀ → z ∉ β y₀ := by
    intro z hz1 hz2
    exact hy₀ ((hβ1 x₀ y₀).2 (((hβ1 y₀ z).1 hz2).symm.trans ((hβ1 x₀ z).1 hz1)))
  have hcover : ∀ z ∈ orbit T x₀, z ∈ β x₀ ∨ z ∈ β y₀ := by
    have hsub : β x₀ ∪ β y₀ ⊆ orbit T x₀ := Set.union_subset (hβ2 x₀) hβy₀
    have hcard : (orbit T x₀).ncard ≤ (β x₀ ∪ β y₀).ncard := by
      rw [Set.ncard_union_eq (Set.disjoint_left.2 hdisj), hB₁, hB₂, hΔc]
    intro z hz
    rw [← Set.eq_of_subset_of_ncard_le hsub hcard] at hz
    exact hz
  have hsmul : ∀ q ∈ T, ∀ x, Nat.card (orbit T (q x)) = Nat.card (orbit T x) :=
    fun q hq x => by rw [show q x = (⟨q, hq⟩ : T) • x from rfl, MulAction.orbit_smul]
  have hinΔ : ∀ x, x ∈ orbit T x₀ ↔ Nat.card (orbit T x) = 8 := by
    intro x
    constructor
    · intro hx
      rw [orbit_eq_iff.2 hx]
      exact hx₀
    · intro hx
      rw [← orbit_T_eq hA hT h4 (hx.trans hx₀.symm)]
      exact mem_orbit_self x
  have hsetle : ∀ m : ℕ, {x : Ω | Nat.card (orbit T x) = m}.ncard ≤ m := by
    intro m
    rcases Set.eq_empty_or_nonempty {x : Ω | Nat.card (orbit T x) = m} with h | ⟨x, hx⟩
    · rw [h, Set.ncard_empty]
      exact Nat.zero_le m
    · have hle : {x : Ω | Nat.card (orbit T x) = m} ⊆ orbit T x := by
        intro y hy
        have hxy : Nat.card (orbit T y) = Nat.card (orbit T x) :=
          (show Nat.card (orbit T y) = m from hy).trans (show Nat.card (orbit T x) = m from hx).symm
        rw [← orbit_T_eq hA hT h4 hxy]
        exact mem_orbit_self y
      calc {x : Ω | Nat.card (orbit T x) = m}.ncard ≤ (orbit T x).ncard := Set.ncard_le_ncard hle
        _ = m := by rw [← Nat.card_coe_set_eq]; exact hx
  set f : Ω → Fin 4 := fun x => if x ∈ β x₀ then 0 else if x ∈ β y₀ then 1
    else if Nat.card (orbit T x) = 2 then 2 else 3 with hf
  have hf0 : ∀ x, f x = 0 ↔ x ∈ β x₀ := by
    intro x
    by_cases h0 : x ∈ β x₀
    · simp only [hf, h0, ↓reduceIte, iff_true]
    · by_cases h1 : x ∈ β y₀
      · simp only [hf, h0, h1, ↓reduceIte]
        decide
      · by_cases h2 : Nat.card (orbit T x) = 2 <;> simp only [hf, h0, h1, h2, ↓reduceIte] <;>
          decide
  have hf1 : ∀ x, f x = 1 ↔ x ∈ β y₀ := by
    intro x
    by_cases h0 : x ∈ β x₀
    · simp only [hf, h0, hdisj x h0, ↓reduceIte]
      decide
    · by_cases h1 : x ∈ β y₀
      · simp only [hf, h0, h1, ↓reduceIte, iff_true]
      · by_cases h2 : Nat.card (orbit T x) = 2 <;> simp only [hf, h0, h1, h2, ↓reduceIte] <;>
          decide
  have hf2 : ∀ x, f x = 2 ↔ Nat.card (orbit T x) = 2 := by
    intro x
    by_cases h0 : x ∈ β x₀
    · simp only [hf, h0, (hinΔ x).1 (hβ2 x₀ h0), ↓reduceIte]
      decide
    · by_cases h1 : x ∈ β y₀
      · simp only [hf, h0, h1, (hinΔ x).1 (hβy₀ h1), ↓reduceIte]
        decide
      · by_cases h2 : Nat.card (orbit T x) = 2 <;> simp only [hf, h0, h1, h2, ↓reduceIte] <;>
          decide
  have hf3 : ∀ x, f x = 3 ↔ Nat.card (orbit T x) = 1 := by
    intro x
    by_cases h0 : x ∈ β x₀
    · simp only [hf, h0, (hinΔ x).1 (hβ2 x₀ h0), ↓reduceIte]
      decide
    · by_cases h1 : x ∈ β y₀
      · simp only [hf, h0, h1, (hinΔ x).1 (hβy₀ h1), ↓reduceIte]
        decide
      · have h8x : Nat.card (orbit T x) ≠ 8 := fun h =>
          (hcover x ((hinΔ x).2 h)).elim h0 h1
        rcases card_orbit_T hA hT h8 h11 x with h | h | h
        · simp only [hf, h0, h1, h, ↓reduceIte]
          decide
        · simp only [hf, h0, h1, h, ↓reduceIte]
          decide
        · exact absurd h h8x
  have hcardf : ∀ (i : Fin 4) (s : Set Ω), (∀ x, f x = i ↔ x ∈ s) →
      Nat.card {x // f x = i} = s.ncard := by
    intro i s hs
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight hs)
  have hlabel : ∀ q ∈ T, (∀ x, f (q x) = f x) ∨ (∀ x, f (q x) = swap (0 : Fin 4) 1 (f x)) := by
    intro q hq
    have hq0 : q x₀ ∈ orbit T x₀ := mem_orbit x₀ (⟨q, hq⟩ : T)
    have himg : ∀ (s : Set Ω) (x : Ω), q x ∈ q '' s ↔ x ∈ s := fun s x =>
      q.injective.mem_set_image
    have hout : ∀ x, x ∉ β x₀ → x ∉ β y₀ → q x ∉ β x₀ ∧ q x ∉ β y₀ := by
      intro x h0 h1
      have h8x : Nat.card (orbit T x) ≠ 8 := fun h => (hcover x ((hinΔ x).2 h)).elim h0 h1
      refine ⟨fun h => h8x ?_, fun h => h8x ?_⟩
      · rw [← hsmul q hq x]
        exact (hinΔ (q x)).1 (hβ2 x₀ h)
      · rw [← hsmul q hq x]
        exact (hinΔ (q x)).1 (hβy₀ h)
    have hrest : ∀ x, x ∉ β x₀ → x ∉ β y₀ → f (q x) = f x := by
      intro x h0 h1
      obtain ⟨hq0', hq1'⟩ := hout x h0 h1
      simp only [hf, h0, h1, hq0', hq1', hsmul q hq x, if_false]
    rcases hcover (q x₀) hq0 with h | h
    · left
      have hB : q '' β x₀ = β x₀ := by
        rw [← hβ5 q hq x₀]
        exact (hβ1 x₀ (q x₀)).1 h
      intro x
      by_cases h0 : x ∈ β x₀
      · have : q x ∈ β x₀ := hB ▸ (himg (β x₀) x).2 h0
        rw [(hf0 (q x)).2 this, (hf0 x).2 h0]
      · by_cases h1 : x ∈ β y₀
        · have hqx : q x ∈ orbit T x₀ := (hinΔ (q x)).2 (by
            rw [hsmul q hq x]
            exact (hinΔ x).1 (hβy₀ h1))
          have hn0 : q x ∉ β x₀ := fun hc => h0 ((himg (β x₀) x).1 (hB.symm ▸ hc))
          have : q x ∈ β y₀ := (hcover (q x) hqx).resolve_left hn0
          rw [(hf1 (q x)).2 this, (hf1 x).2 h1]
        · exact hrest x h0 h1
    · right
      have hB : q '' β x₀ = β y₀ := by
        rw [← hβ5 q hq x₀]
        exact (hβ1 y₀ (q x₀)).1 h
      intro x
      by_cases h0 : x ∈ β x₀
      · have : q x ∈ β y₀ := hB ▸ (himg (β x₀) x).2 h0
        rw [(hf1 (q x)).2 this, (hf0 x).2 h0, swap_apply_left]
      · by_cases h1 : x ∈ β y₀
        · have hqx : q x ∈ orbit T x₀ := (hinΔ (q x)).2 (by
            rw [hsmul q hq x]
            exact (hinΔ x).1 (hβy₀ h1))
          have hn1 : q x ∉ β y₀ := fun hc => h0 ((himg (β x₀) x).1 (hB.symm ▸ hc))
          have : q x ∈ β x₀ := (hcover (q x) hqx).resolve_right hn1
          rw [(hf0 (q x)).2 this, (hf1 x).2 h1, swap_apply_right]
        · rw [hrest x h0 h1]
          have hne0 : f x ≠ 0 := fun h => h0 ((hf0 x).1 h)
          have hne1 : f x ≠ 1 := fun h => h1 ((hf1 x).1 h)
          exact (swap_apply_of_ne_of_ne hne0 hne1).symm
  refine ⟨f, le_normalizer_fibreStab fun q hq x y => ?_, ?_, ?_, ?_, ?_, fun h10 => ?_, ?_⟩
  · rcases hlabel q hq with h | h
    · rw [h x, h y]
    · rw [h x, h y]
      exact (swap (0 : Fin 4) 1).injective.eq_iff
  · rw [hcardf 0 (β x₀) hf0, hB₁]
  · rw [hcardf 1 (β y₀) hf1, hB₂]
  · rw [hcardf 2 {x | Nat.card (orbit T x) = 2} hf2]
    exact hsetle 2
  · rw [hcardf 3 {x | Nat.card (orbit T x) = 1} hf3]
    exact hsetle 1
  · obtain ⟨r, hr⟩ := h2ex h10
    have hset : {x : Ω | Nat.card (orbit T x) = 2} = orbit T r := by
      ext x
      constructor
      · intro hx
        rw [← orbit_T_eq hA hT h4 ((show Nat.card (orbit T x) = 2 from hx).trans hr.symm)]
        exact mem_orbit_self x
      · intro hx
        show Nat.card (orbit T x) = 2
        rw [orbit_eq_iff.2 hx]
        exact hr
    rw [hcardf 2 {x | Nat.card (orbit T x) = 2} hf2, hset, ← Nat.card_coe_set_eq]
    exact hr
  · obtain ⟨g, hg⟩ := mem_orbit_iff.1 hy₀Δ
    have hgx₀ : (g : Perm Ω) x₀ = y₀ := hg
    refine ⟨g, g.2, fun x => ?_⟩
    rcases hlabel g g.2 with h | h
    · exfalso
      have h' := h x₀
      rw [hgx₀, (hf1 y₀).2 (hmem y₀), (hf0 x₀).2 (hmem x₀)] at h'
      exact absurd h' (by decide)
    · rw [h x, Equiv.swap_apply_eq_iff, Equiv.swap_apply_eq_iff, swap_apply_left,
        swap_apply_right]
      exact ⟨Iff.rfl, Iff.rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
