module

public import CFSG.Quasithin.Background.C41PfCorr
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf

public section

namespace CFSG.Quasithin.C134Case4Fix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem inf_centralizer_ne_bot [Finite G] {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (hA x) (hB x)

theorem mem_normalizer_centralizer {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
      simpa using this
    have e := hx _ hl'
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [e]
      _ = g * x * g⁻¹ * l := by group
  · intro hx l hl
    have hl' : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
    have e := hx _ hl'
    have e' : g * (l * x) * g⁻¹ = g * (x * l) * g⁻¹ := by
      calc g * (l * x) * g⁻¹ = g * l * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * l * g⁻¹) := e
        _ = g * (x * l) * g⁻¹ := by group
    have := congrArg (fun y => g⁻¹ * y * g) e'
    simpa [mul_assoc] using this

theorem le_normalizer_c134CQ {G₀ R L : Subgroup G} (hRG : R ≤ G₀)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) :
    R ≤ Subgroup.normalizer (c134CQ G₀ L : Set G) := fun _ hr =>
  mem_normalizer_inf
    (SBd5.mem_normalizer_commutator_of
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₀ (hRG hr)) (hRL hr))
    (mem_normalizer_centralizer (hRL hr))

theorem exists_mem [Finite G] {G₀ R L : Subgroup G}
    (h4 : C134CorrLocal.IsC134Case4Corr G₀ R L) (hR : IsPGroup 2 R) (hRG : R ≤ G₀)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hQR : c134Q G₀ L ≤ R) :
    ∃ c ∈ c134CQ G₀ L, c ≠ 1 ∧ c ∈ quasithinOmegaOneCenter R := by
  classical
  obtain ⟨⟨n, F, _, _, -, hFc, -, hE, -⟩, -⟩ := h4
  obtain ⟨e⟩ := hE
  set W := c134CQ G₀ L with hW
  have hsq : ∀ x : ↥W, x * x = 1 := fun x => by
    apply e.injective
    rw [map_mul, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
    generalize Multiplicative.toAdd (e x) i = a
    revert a
    decide
  have hn : n ≠ 0 := by
    rintro rfl
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rw [hFc] at h2
    norm_num at h2
  have hW1 : W ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥W = 2 ^ (2 * n) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp [Fintype.card_pi]
    rw [hbot, Subgroup.card_bot] at hcard
    have : 2 ^ (2 * n) ≠ 1 := by
      apply Nat.one_lt_pow (by omega) (by norm_num) |>.ne'
    exact this hcard.symm
  have hWR : W ≤ R := inf_le_left.trans hQR
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot hR hWR (le_normalizer_c134CQ hRG hRL) hW1)
  refine ⟨(c : G), c.2.1, fun h => hc1 (Subtype.ext h), ?_⟩
  have hcW : (c : G) ∈ W := c.2.1
  have hc2 : (c : G) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (hsq ⟨c, hcW⟩)
  exact Subgroup.subset_closure ⟨⟨hWR hcW, c.2.2⟩, hc2⟩

end CFSG.Quasithin.C134Case4Fix
