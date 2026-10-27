module

public import CFSG.RankThree.PartOne.N1322.CaseBasic
import CFSG.RankThree.PartOne.N1322.CaseInner
public import CFSG.RankThree.PartOne.N1322.CoreHyp
public import CFSG.RankThree.PartOne.N1322.Mono
public import Mathlib.Algebra.Algebra.Subalgebra.Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne

theorem card_eq_two_mul_of_forall_mem_or_mul_mem {K : Type*} [Group K] {S T : Subgroup K}
    (hST : S ≤ T) {n : K} (hnT : n ∈ T) (hnS : n ∉ S) (hT : ∀ g ∈ T, g ∈ S ∨ n * g ∈ S) :
    Nat.card T = 2 * Nat.card S := by
  have hidx : (S.subgroupOf T).index = 2 := by
    rw [Subgroup.index_eq_two_iff']
    refine ⟨⟨n, hnT⟩, fun b => ?_⟩
    by_cases hb : (b : K) ∈ S
    · have hnb : n * (b : K) ∉ S := by
        intro hnb
        refine hnS ?_
        rw [show n = n * (b : K) * (b : K)⁻¹ by group]
        exact S.mul_mem hnb (S.inv_mem hb)
      simp [Subgroup.mem_subgroupOf, hb, hnb]
    · have hnb : n * (b : K) ∈ S := by
        rcases hT (b : K) b.2 with h | h
        · exact absurd h hb
        · exact h
      simp [Subgroup.mem_subgroupOf, hb, hnb]
  have h := Subgroup.card_mul_index (S.subgroupOf T)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv] at h
  omega

variable {p : ℕ} [Fact p.Prime] {G H : Subgroup (GL (Fin 3) (ZMod p))}

private lemma rank_add_one_add_rank_sub_one_le_zr {a : GL (Fin 3) (ZMod p)} (ha : a * a = 1) :
    ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1).rank +
      ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1).rank ≤ 3 := by
  have hA : (a : Matrix (Fin 3) (Fin 3) (ZMod p)) * a = 1 := by
    simpa using congrArg (fun x : GL (Fin 3) (ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) ha
  have hzero : ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1) * (a - 1) = 0 := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hA]
    abel
  simpa using Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero

private lemma eq_zero_of_rank_eq_zero_zr {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (h : M.rank = 0) :
    M = 0 := by
  have hr : M.rank = Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun (ZMod p) (Fin 3))
      (Pi.basisFun (ZMod p) (Fin 3)), Matrix.toLin_eq_toLin']
  have h0 : Matrix.toLin' M = 0 :=
    LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (hr ▸ h))
  exact Matrix.toLin'.injective (h0.trans (map_zero _).symm)

private lemma rank_add_one_eq_one_zr (h2 : (2 : ZMod p) ≠ 0) {a : GL (Fin 3) (ZMod p)}
    (hdet : (a : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) (ha : a * a = 1) (ha1 : a ≠ 1) :
    ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1).rank = 1 := by
  have hneg1 : (-1 : ZMod p) ≠ 1 := by
    refine Ring.neg_one_ne_one_of_char_ne_two ?_
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    exact h2 (ZMod.natCast_self 2)
  have hle := rank_add_one_add_rank_sub_one_le_zr ha
  have hs0 : ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1).rank ≠ 0 := fun h =>
    ha1 (Units.ext (by simpa using sub_eq_zero.mp (eq_zero_of_rank_eq_zero_zr h)))
  have hr0 : ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1).rank ≠ 0 := by
    intro h
    have hnegM : (a : Matrix (Fin 3) (Fin 3) (ZMod p)) = -1 :=
      eq_neg_of_add_eq_zero_left (eq_zero_of_rank_eq_zero_zr h)
    refine hneg1 ?_
    rw [hnegM, Matrix.det_neg, Matrix.det_one, Fintype.card_fin] at hdet
    linear_combination hdet
  have hr2 : ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1).rank ≠ 2 := by
    intro h
    have hs : ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1).rank = 1 := by omega
    refine hneg1 ?_
    rw [← N1322.IsRefl.det_eq (N1322.isRefl_of_rank_one ha hs), hdet]
  omega

theorem isRefl_neg_one_mul (hp : p ≠ 2) {a : GL (Fin 3) (ZMod p)}
    (hdet : (a : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) (ha : a * a = 1) (ha1 : a ≠ 1) :
    N1322.IsRefl ((-1 : GL (Fin 3) (ZMod p)) * a) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine N1322.isRefl_of_rank_one (by rw [neg_one_mul, neg_mul_neg, ha]) ?_
  have hm : (((-1 : GL (Fin 3) (ZMod p)) * a : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) - 1 = -((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1) := by
    simp only [neg_one_mul, Units.val_neg]
    abel
  rw [hm, ← neg_one_smul (ZMod p) ((a : Matrix (Fin 3) (Fin 3) (ZMod p)) + 1),
    Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr one_ne_zero))]
  exact rank_add_one_eq_one_zr h2 hdet ha ha1

theorem neg_one_not_mem (hp : p ≠ 2)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) :
    (-1 : GL (Fin 3) (ZMod p)) ∉ H := by
  intro hmem
  have h1 : ((-1 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 :=
    hdet _ hmem
  rw [Units.val_neg, Units.val_one, Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
    at h1
  have h3 : (-1 : ZMod p) = 1 := by
    ring_nf at h1 ⊢
    exact h1
  rcases (ZMod.neg_one_eq_one_iff (n := p)).mp h3 with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hp h

theorem eq_neg_one_mul_of_inner
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ G, N1322.IsRefl t → ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    {t : GL (Fin 3) (ZMod p)} (ht : t ∈ G) (hrefl : N1322.IsRefl t) :
    ∃ a ∈ H, a * a = 1 ∧ t = (-1 : GL (Fin 3) (ZMod p)) * a := by
  obtain ⟨h₀, hh₀, hin⟩ := hinn t ht hrefl
  have hZ3 : ∀ z ∈ H, (∀ g : GL (Fin 3) (ZMod p), g * z = z * g) → z ^ 3 = 1 := by
    intro z hz hzc
    obtain ⟨c, hc⟩ := hsch (z : Matrix (Fin 3) (Fin 3) (ZMod p)) fun g _ => by
      rw [← Units.val_mul, ← Units.val_mul, hzc g]
    have hc3 : c ^ 3 = 1 := by
      have h := hdet z hz
      rw [hc, Matrix.scalar_apply, Matrix.det_diagonal] at h
      simpa using h
    have hz3 : (z : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ 3 = 1 := by
      rw [hc, ← map_pow, hc3, map_one]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hz3, Units.val_one])
  exact N1322.refl_neg_of_inner hdet hZ3 hsch hrefl hh₀ hin

theorem neg_one_mem_of_inner (hHG : H ≤ G)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ G, N1322.IsRefl t → ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (hex : ∃ t ∈ G, N1322.IsRefl t) : (-1 : GL (Fin 3) (ZMod p)) ∈ G := by
  obtain ⟨t, htG, hrefl⟩ := hex
  obtain ⟨a, haH, -, hta⟩ := eq_neg_one_mul_of_inner hdet hsch hinn htG hrefl
  have hneg : (-1 : GL (Fin 3) (ZMod p)) = t * a⁻¹ := by
    rw [hta, mul_assoc, mul_inv_cancel, mul_one]
  rw [hneg]
  exact G.mul_mem htG (G.inv_mem (hHG haH))

private lemma mul_mem_or_neg_one_mul_mem_zx {x y : GL (Fin 3) (ZMod p)}
    (hx : x ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * x ∈ H)
    (hy : y ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * y ∈ H) :
    x * y ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * (x * y) ∈ H := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (H.mul_mem hx hy)
  · refine Or.inr ?_
    have h : (-1 : GL (Fin 3) (ZMod p)) * (x * y) = x * ((-1) * y) := by
      rw [← mul_assoc, N1322.neg_one_comm x, mul_assoc]
    rw [h]
    exact H.mul_mem hx hy
  · refine Or.inr ?_
    rw [← mul_assoc]
    exact H.mul_mem hx hy
  · refine Or.inl ?_
    have hxy : x * y = ((-1) * x) * ((-1) * y) := by
      rw [neg_one_mul, neg_one_mul, neg_mul_neg]
    rw [hxy]
    exact H.mul_mem hx hy

private lemma inv_mem_or_neg_one_mul_mem_zx {x : GL (Fin 3) (ZMod p)}
    (hx : x ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * x ∈ H) :
    x⁻¹ ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * x⁻¹ ∈ H := by
  rcases hx with hx | hx
  · exact Or.inl (H.inv_mem hx)
  · refine Or.inr ?_
    have h1 := H.inv_mem hx
    rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right N1322.neg_one_mul_neg_one,
      ← N1322.neg_one_comm x⁻¹] at h1

theorem mem_or_neg_one_mul_mem_of_inner (hG : G = closure {t | t ∈ G ∧ N1322.IsRefl t})
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ G, N1322.IsRefl t → ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    {g : GL (Fin 3) (ZMod p)} (hg : g ∈ G) : g ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * g ∈ H := by
  have hgen : ∀ x ∈ ({t | t ∈ G ∧ N1322.IsRefl t} : Set (GL (Fin 3) (ZMod p))),
      x ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * x ∈ H := by
    intro x hx
    obtain ⟨hxG, hxrefl⟩ := hx
    obtain ⟨a, haH, -, hxa⟩ := eq_neg_one_mul_of_inner hdet hsch hinn hxG hxrefl
    refine Or.inr ?_
    rw [hxa, ← mul_assoc, N1322.neg_one_mul_neg_one, one_mul]
    exact haH
  have hmain : ∀ x ∈ closure {t | t ∈ G ∧ N1322.IsRefl t},
      x ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * x ∈ H := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ H ∨ (-1) * x ∈ H) ?_ ?_ ?_ ?_ hx
    · exact hgen
    · exact Or.inl H.one_mem
    · intro y z _ _ hy hz
      exact mul_mem_or_neg_one_mul_mem_zx hy hz
    · intro y _ hy
      exact inv_mem_or_neg_one_mul_mem_zx hy
  exact hmain g (hG ▸ hg)

theorem card_eq_two_mul_of_inner (hp : p ≠ 2) (hG : G = closure {t | t ∈ G ∧ N1322.IsRefl t})
    (hHG : H ≤ G) (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ G, N1322.IsRefl t → ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (hex : ∃ t ∈ G, N1322.IsRefl t) : Nat.card G = 2 * Nat.card H := by
  have hnegG : (-1 : GL (Fin 3) (ZMod p)) ∈ G :=
    neg_one_mem_of_inner hHG hdet hsch hinn hex
  have hnegH : (-1 : GL (Fin 3) (ZMod p)) ∉ H := neg_one_not_mem hp hdet
  exact card_eq_two_mul_of_forall_mem_or_mul_mem hHG hnegG hnegH
    fun g hg => mem_or_neg_one_mul_mem_of_inner hG hdet hsch hinn hg

private lemma central_G_of_central_H_zx
    (hmem : ∀ ⦃g : GL (Fin 3) (ZMod p)⦄, g ∈ G →
      g ∈ H ∨ (-1 : GL (Fin 3) (ZMod p)) * g ∈ H)
    {y : GL (Fin 3) (ZMod p)} (hyc : ∀ x ∈ H, y * x = x * y) :
    ∀ g ∈ G, y * g = g * y := by
  intro g hg
  rcases hmem hg with hgH | hgH
  · exact hyc g hgH
  · have hya : y * ((-1) * g) = ((-1) * g) * y := hyc _ hgH
    rwa [neg_one_mul, mul_neg, neg_mul, neg_inj] at hya

private lemma neg_one_mul_central_zx {y : GL (Fin 3) (ZMod p)}
    (hy : ∀ g ∈ G, y * g = g * y) :
    ∀ g ∈ G, ((-1 : GL (Fin 3) (ZMod p)) * y) * g = g * ((-1) * y) := by
  intro g hg
  calc ((-1 : GL (Fin 3) (ZMod p)) * y) * g = (-1) * (y * g) := by rw [mul_assoc]
    _ = (-1) * (g * y) := by rw [hy g hg]
    _ = ((-1) * g) * y := by rw [mul_assoc]
    _ = (g * (-1)) * y := by rw [N1322.neg_one_comm g]
    _ = g * ((-1) * y) := by rw [mul_assoc]

theorem card_center_eq_two_mul_of_inner (hp : p ≠ 2)
    (hG : G = closure {t | t ∈ G ∧ N1322.IsRefl t}) (hHG : H ≤ G)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    (hinn : ∀ t ∈ G, N1322.IsRefl t → ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (hex : ∃ t ∈ G, N1322.IsRefl t) : Nat.card (center G) = 2 * Nat.card (center H) := by
  have hmem : ∀ ⦃g : GL (Fin 3) (ZMod p)⦄, g ∈ G → g ∈ H ∨ (-1) * g ∈ H :=
    fun g hg => mem_or_neg_one_mul_mem_of_inner hG hdet hsch hinn hg
  have hnegG : (-1 : GL (Fin 3) (ZMod p)) ∈ G :=
    neg_one_mem_of_inner hHG hdet hsch hinn hex
  have hle : (center H).map H.subtype ≤ (center G).map G.subtype := by
    rintro z ⟨y, hy, rfl⟩
    have hyc : ∀ x ∈ H, (y : GL (Fin 3) (ZMod p)) * x = x * y := fun x hx =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨x, hx⟩)).symm
    have hyG := central_G_of_central_H_zx hmem hyc
    have hzy : (⟨(y : GL (Fin 3) (ZMod p)), hHG y.2⟩ : G) ∈ center G :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by
        simpa using (hyG g.1 g.2).symm)
    simpa using Subgroup.mem_map_of_mem G.subtype hzy
  have hnegS : (-1 : GL (Fin 3) (ZMod p)) ∉ (center H).map H.subtype := by
    rintro ⟨y, -, hy⟩
    exact neg_one_not_mem hp hdet (hy ▸ y.2)
  have hnegT : (-1 : GL (Fin 3) (ZMod p)) ∈ (center G).map G.subtype := by
    have hz : (⟨-1, hnegG⟩ : G) ∈ center G :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by simp)
    simpa using Subgroup.mem_map_of_mem G.subtype hz
  have hcov : ∀ g ∈ (center G).map G.subtype,
      g ∈ (center H).map H.subtype ∨ (-1) * g ∈ (center H).map H.subtype := by
    rintro g ⟨y, hy, rfl⟩
    have hyc : ∀ x ∈ H, (y : GL (Fin 3) (ZMod p)) * x = x * y := fun x hx =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨x, hHG hx⟩)).symm
    have hyG := central_G_of_central_H_zx hmem hyc
    rcases hmem y.2 with hyH | hyH
    · have hzy : (⟨(y : GL (Fin 3) (ZMod p)), hyH⟩ : H) ∈ center H :=
        Subgroup.mem_center_iff.mpr fun x => Subtype.ext (by
          simpa using (hyG x.1 (hHG x.2)).symm)
      exact Or.inl (by simpa using Subgroup.mem_map_of_mem H.subtype hzy)
    · have hzy : (⟨(-1) * (y : GL (Fin 3) (ZMod p)), hyH⟩ : H) ∈ center H :=
        Subgroup.mem_center_iff.mpr fun x => Subtype.ext (by
          simpa using (neg_one_mul_central_zx hyG x.1 (hHG x.2)).symm)
      exact Or.inr (by simpa using Subgroup.mem_map_of_mem H.subtype hzy)
  have h := card_eq_two_mul_of_forall_mem_or_mul_mem hle hnegT hnegS hcov
  rwa [Subgroup.card_map_of_injective G.subtype_injective,
    Subgroup.card_map_of_injective H.subtype_injective] at h

end CFSG.StandardType.ZS.DimThree
