module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5Rep
public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsWindow

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

namespace Conf

theorem le_normalizer_win (c : Conf G n) (a b : ℤ) :
    c.H ≤ normalizer (win c.Q₁ c.Q₂ c.x₁ c.x₂ a b : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_win_iff, mem_win_iff]
  refine forall_congr' fun i => ?_
  have hi := Subgroup.mem_normalizer_iff.mp
    (c.track.le_normalizer_qv c.H_le₁ c.H_le₂ c.le_normalizer₁ c.le_normalizer₂ i hh) y
  constructor
  · intro hy h1 h2
    exact hi.mp (hy h1 h2)
  · intro hy h1 h2
    exact hi.mpr (hy h1 h2)

variable [Finite G] (c : Conf G n)

private theorem isPGroup_win_J :
    IsPGroup 2 (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) := by
  refine c.isPGroup₁.to_le ?_
  have h := win_mono (Q₁ := c.Q₁) (Q₂ := c.Q₂) (x₁ := c.x₁) (x₂ := c.x₂)
    (a := 0) (b := c.pattern.J) (a' := 0) (b' := 0) le_rfl (Int.natCast_nonneg _)
  rwa [win_zero_zero] at h

private theorem series_labelled :
    ∀ (l : List (Subgroup G)) (C D : Subgroup G), IsYSeries c.H C l D → IsPGroup 2 D →
      ∃ μ : Multiset (Coord n),
        facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ ∧
        C.relIndex D = 2 ^ (μ.map fun φ => (cls φ).card).sum := by
  intro l
  induction l with
  | nil =>
    intro C D hCD _
    obtain rfl : C = D := hCD
    refine ⟨0, rfl, ?_⟩
    rw [Multiset.map_zero, Multiset.sum_zero, pow_zero, Subgroup.relIndex_eq_one]
  | cons S l ih =>
    intro C D hSD hD
    obtain ⟨hSD, hl⟩ := hSD
    have hS : IsPGroup 2 S := hD.to_le hSD.1.le
    obtain ⟨μ, hfac, hrel⟩ := ih C S hl hS
    have hY : IsYSimple (zpowers c.d₁ ⊔ zpowers c.d₂) S D := by
      rw [← c.H_eq]
      exact hSD
    have hn : n ≠ 0 := by
      have := c.three_le
      omega
    have hd₁ : c.d₁ ^ (2 ^ n - 1) = 1 := by
      rw [← c.orderOf₁]
      exact pow_orderOf_eq_one c.d₁
    have hd₂ : c.d₂ ^ (2 ^ n - 1) = 1 := by
      rw [← c.orderOf₂]
      exact pow_orderOf_eq_one c.d₂
    obtain ⟨φ, β, hβ⟩ :=
      exists_isChiEmb (C := S) (S := D) hY hD c.commute hd₁ hd₂ hn c.orderOf_ζ
    have hS₁ : c.d₁ ∈ normalizer (D : Set G) := hSD.2.2.2.1 c.d₁_mem_H
    have hS₂ : c.d₂ ∈ normalizer (D : Set G) := hSD.2.2.2.1 c.d₂_mem_H
    have hcls : chiLab c.ζ c.d₁ c.d₂ S D = (cls φ : Set (Coord n)) :=
      IsChiEmb.chiLab_eq_cls (C := S) (S := D) hβ hn c.orderOf_ζ hS₁ hS₂
        (not_le_of_gt hSD.1)
    have hrelSD : S.relIndex D = 2 ^ (cls φ).card :=
      IsChiEmb.relIndex_eq (C := S) (S := D) hβ hn c.orderOf_ζ hY
    refine ⟨φ ::ₘ μ, ?_, ?_⟩
    · show chiLab c.ζ c.d₁ c.d₂ S D ::ₘ
          facMultiset (chiLab c.ζ c.d₁ c.d₂) l S = clsSets (φ ::ₘ μ)
      rw [hfac, hcls]
      simp only [clsSets, Multiset.map_cons]
    · rw [← Subgroup.relIndex_mul_relIndex (H := C) (K := S) (L := D) hl.le hSD.1.le,
        hrel, hrelSD,
        Multiset.map_cons, Multiset.sum_cons, pow_add]
      exact Nat.mul_comm _ _

private theorem sigma1_invariant {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H ⊥ l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J))
    (hfac : facMultiset (chiLab c.ζ c.d₁ c.d₂) l
      (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) = clsSets μ) :
    (μ.map (sigma1 c.m₀)).map cls = μ.map cls := by
  obtain ⟨hl', hfac'⟩ := c.series_map_conj_x₁ hl hfac
  have hx₁ : (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J).map
      (MulAut.conj c.x₁).toMonoidHom = win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J := by
    rw [c.track.map_win_x₁ c.le_normalizer₁ c.le_normalizer₂, neg_zero]
    exact c.win_eq_of_le (a := -(c.pattern.J : ℤ)) (b := 0) (by omega)
  simp only [Subgroup.map_bot, hx₁] at hl' hfac'
  have hJH := facMultiset_eq (Y := c.H) (chiLab c.ζ c.d₁ c.d₂)
    (fun S S' D h h' hne => chiLab_eq_inf c.d₁_mem_H c.d₂_mem_H h h' hne)
    (Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J)) ⊥
    (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) rfl l
    (l.map fun T => T.map (MulAut.conj c.x₁).toMonoidHom) hl hl'
  have hcls : clsSets μ = clsSets (μ.map (sigma1 c.m₀)) := by
    rw [← hfac, ← hfac', hJH]
  exact (map_cls_eq_of_clsSets_eq hcls).symm

private theorem sigma2_invariant {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H ⊥ l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J))
    (hfac : facMultiset (chiLab c.ζ c.d₁ c.d₂) l
      (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) = clsSets μ) :
    (μ.map (sigma2 c.k₀)).map cls = μ.map cls := by
  obtain ⟨hl', hfac'⟩ := c.series_map_conj_x₂ hl hfac
  have hx₂ : (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J).map
      (MulAut.conj c.x₂).toMonoidHom = win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J := by
    rw [c.track.map_win_x₂ c.le_normalizer₁ c.le_normalizer₂, sub_zero]
    exact c.win_eq_of_le (a := 2 - (c.pattern.J : ℤ)) (b := 2) (by omega)
  simp only [Subgroup.map_bot, hx₂] at hl' hfac'
  have hJH := facMultiset_eq (Y := c.H) (chiLab c.ζ c.d₁ c.d₂)
    (fun S S' D h h' hne => chiLab_eq_inf c.d₁_mem_H c.d₂_mem_H h h' hne)
    (Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J)) ⊥
    (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) rfl l
    (l.map fun T => T.map (MulAut.conj c.x₂).toMonoidHom) hl hl'
  have hcls : clsSets μ = clsSets (μ.map (sigma2 c.k₀)) := by
    rw [← hfac, ← hfac', hJH]
  exact (map_cls_eq_of_clsSets_eq hcls).symm

theorem exists_muT :
    ∃ μT : Multiset (Coord n),
      (∃ l, IsYSeries c.H ⊥ l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) ∧
        facMultiset (chiLab c.ζ c.d₁ c.d₂) l (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) =
          clsSets μT) ∧
      (μT.map (sigma1 c.m₀)).map cls = μT.map cls ∧
      (μT.map (sigma2 c.k₀)).map cls = μT.map cls ∧
      (μT.map fun φ => (cls φ).card).sum = n * c.pattern.ell := by
  obtain ⟨l, hl⟩ := exists_ySeries (Y := c.H) (C := ⊥)
    (E := win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J) (Nat.card _) rfl bot_le
    (Subgroup.le_normalizer_of_normal (H := ⊥))
    (Subgroup.le_normalizer_of_normal (H := ⊥))
    (c.le_normalizer_win 0 c.pattern.J)
  obtain ⟨μ, hfac, hrel⟩ := c.series_labelled l ⊥ _ hl c.isPGroup_win_J
  refine ⟨μ, ⟨l, hl, hfac⟩, c.sigma1_invariant hl hfac, c.sigma2_invariant hl hfac, ?_⟩
  have h1 : 2 ^ (μ.map fun φ => (cls φ).card).sum = 2 ^ (n * c.pattern.ell) := by
    rw [← hrel, Subgroup.relIndex_bot_left, c.card_win_J]
    exact (pow_mul 2 n c.pattern.ell).symm
  exact Nat.pow_right_injective (a := 2) (by norm_num) h1

end Conf

end CFSG.Quasithin.Stroth.G5

end
