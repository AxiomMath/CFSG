module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ChiConj
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithBasic


public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

theorem qv_zero (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) : qv Q₁ Q₂ x₁ x₂ 0 = Q₁ := by
  ext y
  rw [mem_qv_iff]
  simp [trackElt, trackPar]

theorem win_zero_zero (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) :
    win Q₁ Q₂ x₁ x₂ 0 0 = Q₁ := by
  rw [win_self, qv_zero]

private theorem facMultiset_chiLab_map_conj_aux {ζ : GaloisField 2 n} {d₁ d₂ g : G}
    {Y C D : Subgroup G} {l : List (Subgroup G)} (hl : IsYSeries Y C l D) (hd₁ : d₁ ∈ Y)
    (hd₂ : d₂ ∈ Y) (hn : n ≠ 0) (hζ : orderOf ζ = 2 ^ n - 1) {a b a' b' : ZMod (2 ^ n - 1)}
    (h₁ : g⁻¹ * d₁ * g = d₁ ^ a.val * d₂ ^ b.val)
    (h₂ : g⁻¹ * d₂ * g = d₁ ^ a'.val * d₂ ^ b'.val) {μ : Multiset (Coord n)}
    (hμ : facMultiset (chiLab ζ d₁ d₂) l D = clsSets μ) :
    facMultiset (fun C S => chiLab ζ d₁ d₂ (C.map (MulAut.conj g).toMonoidHom)
        (S.map (MulAut.conj g).toMonoidHom)) l D =
      clsSets (μ.map fun φ => (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2)) := by
  induction l generalizing D μ with
  | nil =>
    have hμ0 : μ = 0 := by
      rw [facMultiset] at hμ
      exact Multiset.map_eq_zero.mp hμ.symm
    rw [facMultiset]
    simp [clsSets, hμ0]
  | cons S l ih =>
    have hmem : chiLab ζ d₁ d₂ S D ∈ clsSets μ := by
      rw [← hμ]
      exact Multiset.mem_cons_self _ _
    obtain ⟨φ, hφμ, hφ⟩ := Multiset.mem_map.mp hmem
    have hφmem : φ ∈ chiLab ζ d₁ d₂ S D := by
      rw [← hφ]
      exact mem_cls_self hn φ
    have hhead : chiLab ζ d₁ d₂ (S.map (MulAut.conj g).toMonoidHom)
        (D.map (MulAut.conj g).toMonoidHom) =
        (cls (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2) : Set (Coord n)) :=
      chiLab_map_conj (C := S) (S := D) hφmem hn hζ
        (hl.1.2.2.2.1 hd₁) (hl.1.2.2.2.1 hd₂) hl.1.1.not_ge h₁ h₂
    have hμ' : clsSets μ = (cls φ : Set (Coord n)) ::ₘ clsSets (μ.erase φ) := by
      conv_lhs => rw [← Multiset.cons_erase hφμ]
      simp [clsSets]
    have hfac_tail : facMultiset (chiLab ζ d₁ d₂) l S = clsSets (μ.erase φ) := by
      rw [facMultiset] at hμ
      rw [hμ', hφ] at hμ
      exact (Multiset.cons_inj_right _).mp hμ
    have hrec := ih hl.2 hfac_tail
    rw [facMultiset, hhead, hrec]
    have hmap : μ.map (fun φ => (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2)) =
        (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2) ::ₘ
          (μ.erase φ).map fun φ => (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2) := by
      conv_lhs => rw [← Multiset.cons_erase hφμ]
      simp
    rw [hmap]
    simp [clsSets]

theorem facMultiset_chiLab_map_conj {ζ : GaloisField 2 n} {d₁ d₂ g : G} {Y C D : Subgroup G}
    {l : List (Subgroup G)} (hl : IsYSeries Y C l D) (hd₁ : d₁ ∈ Y) (hd₂ : d₂ ∈ Y) (hn : n ≠ 0)
    (hζ : orderOf ζ = 2 ^ n - 1) {a b a' b' : ZMod (2 ^ n - 1)}
    (h₁ : g⁻¹ * d₁ * g = d₁ ^ a.val * d₂ ^ b.val)
    (h₂ : g⁻¹ * d₂ * g = d₁ ^ a'.val * d₂ ^ b'.val)
    {μ : Multiset (Coord n)} (hμ : facMultiset (chiLab ζ d₁ d₂) l D = clsSets μ) :
    facMultiset (chiLab ζ d₁ d₂) (l.map fun T => T.map (MulAut.conj g).toMonoidHom)
        (D.map (MulAut.conj g).toMonoidHom) =
      clsSets (μ.map fun φ => (a * φ.1 + b * φ.2, a' * φ.1 + b' * φ.2)) := by
  rw [facMultiset_map_conj (chiLab ζ d₁ d₂) g]
  exact facMultiset_chiLab_map_conj_aux hl hd₁ hd₂ hn hζ h₁ h₂ hμ

theorem pow_val_neg_one {d : G} (hd : orderOf d = 2 ^ n - 1) (hN : 1 < 2 ^ n - 1) :
    d ^ (-1 : ZMod (2 ^ n - 1)).val = d⁻¹ := by
  have hcast : 2 ^ n - 1 = 2 ^ n - 2 + 1 := by omega
  rw [hcast, ZMod.val_neg_one]
  have hpow : d ^ (2 ^ n - 1) = 1 := by
    rw [← hd]
    exact pow_orderOf_eq_one d
  have h1 : d ^ (2 ^ n - 2) * d = 1 := by
    rw [← pow_succ, show 2 ^ n - 2 + 1 = 2 ^ n - 1 by omega, hpow]
  exact eq_inv_of_mul_eq_one_left h1

theorem pow_val_one {d : G} (hN : 1 < 2 ^ n - 1) :
    d ^ (1 : ZMod (2 ^ n - 1)).val = d := by
  rw [ZMod.val_one'' (n := 2 ^ n - 1) (by omega), pow_one]

namespace Conf

variable (c : Conf G n)

theorem d₁_mem_H : c.d₁ ∈ c.H := by
  rw [c.H_eq]
  exact mem_sup_left (mem_zpowers c.d₁)

theorem d₂_mem_H : c.d₂ ∈ c.H := by
  rw [c.H_eq]
  exact mem_sup_right (mem_zpowers c.d₂)

private theorem conj_x₁_d₁ : c.x₁⁻¹ * c.d₁ * c.x₁ = c.d₁⁻¹ := by
  have h1 : c.x₁ * c.d₁⁻¹ * c.x₁⁻¹ = c.d₁ := by
    have := congrArg (fun z : G => z⁻¹) c.conj₁₁
    simpa [mul_assoc] using this
  calc c.x₁⁻¹ * c.d₁ * c.x₁ = c.x₁⁻¹ * (c.x₁ * c.d₁⁻¹ * c.x₁⁻¹) * c.x₁ := by rw [h1]
    _ = c.d₁⁻¹ := by group

private theorem conj_x₁_d₂ :
    c.x₁⁻¹ * c.d₂ * c.x₁ = c.d₁ ^ (-2 * c.m₀).val * c.d₂ := by
  have hd₂ : c.d₂ = c.x₁⁻¹ * (c.d₁ ^ (-2 * c.m₀).val * c.d₂) * c.x₁ := by
    rw [← c.conj₁₂]
    group
  have hpow : c.x₁⁻¹ * c.d₁ ^ (-2 * c.m₀).val * c.x₁ =
      (c.d₁ ^ (-2 * c.m₀).val)⁻¹ := by
    calc c.x₁⁻¹ * c.d₁ ^ (-2 * c.m₀).val * c.x₁ =
        MulAut.conj c.x₁⁻¹ (c.d₁ ^ (-2 * c.m₀).val) := by
          rw [MulAut.conj_apply, inv_inv]
      _ = (MulAut.conj c.x₁⁻¹ c.d₁) ^ (-2 * c.m₀).val := map_pow _ _ _
      _ = (c.d₁⁻¹) ^ (-2 * c.m₀).val := by
          rw [MulAut.conj_apply, inv_inv, conj_x₁_d₁]
      _ = (c.d₁ ^ (-2 * c.m₀).val)⁻¹ := inv_pow _ _
  have hfac : c.x₁⁻¹ * (c.d₁ ^ (-2 * c.m₀).val * c.d₂) * c.x₁ =
      (c.x₁⁻¹ * c.d₁ ^ (-2 * c.m₀).val * c.x₁) * (c.x₁⁻¹ * c.d₂ * c.x₁) := by group
  rw [hfac, hpow] at hd₂
  have := congrArg (fun z => c.d₁ ^ (-2 * c.m₀).val * z) hd₂
  simpa [mul_assoc] using this.symm

private theorem conj_x₂_d₂ : c.x₂⁻¹ * c.d₂ * c.x₂ = c.d₂⁻¹ := by
  have h1 : c.x₂ * c.d₂⁻¹ * c.x₂⁻¹ = c.d₂ := by
    have := congrArg (fun z : G => z⁻¹) c.conj₂₂
    simpa [mul_assoc] using this
  calc c.x₂⁻¹ * c.d₂ * c.x₂ = c.x₂⁻¹ * (c.x₂ * c.d₂⁻¹ * c.x₂⁻¹) * c.x₂ := by rw [h1]
    _ = c.d₂⁻¹ := by group

private theorem conj_x₂_d₁ :
    c.x₂⁻¹ * c.d₁ * c.x₂ = c.d₁ ^ (1 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (-2 * c.k₀).val := by
  have hd₁ : c.d₁ = c.x₂⁻¹ * (c.d₂ ^ (-2 * c.k₀).val * c.d₁) * c.x₂ := by
    rw [← c.conj₂₁]
    group
  have hpow : c.x₂⁻¹ * c.d₂ ^ (-2 * c.k₀).val * c.x₂ =
      (c.d₂ ^ (-2 * c.k₀).val)⁻¹ := by
    calc c.x₂⁻¹ * c.d₂ ^ (-2 * c.k₀).val * c.x₂ =
        MulAut.conj c.x₂⁻¹ (c.d₂ ^ (-2 * c.k₀).val) := by
          rw [MulAut.conj_apply, inv_inv]
      _ = (MulAut.conj c.x₂⁻¹ c.d₂) ^ (-2 * c.k₀).val := map_pow _ _ _
      _ = (c.d₂⁻¹) ^ (-2 * c.k₀).val := by
          rw [MulAut.conj_apply, inv_inv, conj_x₂_d₂]
      _ = (c.d₂ ^ (-2 * c.k₀).val)⁻¹ := inv_pow _ _
  have hfac : c.x₂⁻¹ * (c.d₂ ^ (-2 * c.k₀).val * c.d₁) * c.x₂ =
      (c.x₂⁻¹ * c.d₂ ^ (-2 * c.k₀).val * c.x₂) * (c.x₂⁻¹ * c.d₁ * c.x₂) := by group
  rw [hfac, hpow] at hd₁
  have hT : c.x₂⁻¹ * c.d₁ * c.x₂ = c.d₂ ^ (-2 * c.k₀).val * c.d₁ := by
    have := congrArg (fun z => c.d₂ ^ (-2 * c.k₀).val * z) hd₁
    simpa [mul_assoc] using this.symm
  have hN : 1 < 2 ^ n - 1 := by
    have := seven_le c.three_le
    omega
  rw [hT, ← (c.commute.pow_right (-2 * c.k₀).val).eq, pow_val_one (d := c.d₁) hN]

theorem series_map_conj_x₁ {C D : Subgroup G} {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj c.x₁).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj c.x₁).toMonoidHom)
        (D.map (MulAut.conj c.x₁).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) (l.map fun T => T.map (MulAut.conj c.x₁).toMonoidHom)
          (D.map (MulAut.conj c.x₁).toMonoidHom) = clsSets (μ.map (sigma1 c.m₀)) := by
  have hn : n ≠ 0 := by
    have := c.three_le
    omega
  have hN : 1 < 2 ^ n - 1 := by
    have := seven_le c.three_le
    omega
  have h1 : c.x₁⁻¹ * c.d₁ * c.x₁ =
      c.d₁ ^ (-1 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (0 : ZMod (2 ^ n - 1)).val := by
    rw [conj_x₁_d₁, pow_val_neg_one (d := c.d₁) c.orderOf₁ hN, ZMod.val_zero, pow_zero, mul_one]
  have h2 : c.x₁⁻¹ * c.d₂ * c.x₁ =
      c.d₁ ^ (-2 * c.m₀).val * c.d₂ ^ (1 : ZMod (2 ^ n - 1)).val := by
    rw [conj_x₁_d₂, pow_val_one (d := c.d₂) hN]
  refine ⟨isYSeries_map_conj c.track.x₁_norm hl, ?_⟩
  rw [facMultiset_chiLab_map_conj (a := -1) (b := 0) (a' := -2 * c.m₀) (b' := 1)
    hl c.d₁_mem_H c.d₂_mem_H hn c.orderOf_ζ h1 h2 hμ]
  congr 1
  refine Multiset.map_congr rfl fun φ _ => ?_
  ext <;> simp [sigma1] <;> ring

theorem series_map_conj_x₂ {C D : Subgroup G} {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H C l D) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ) :
    IsYSeries c.H (C.map (MulAut.conj c.x₂).toMonoidHom)
        (l.map fun T => T.map (MulAut.conj c.x₂).toMonoidHom)
        (D.map (MulAut.conj c.x₂).toMonoidHom) ∧
      facMultiset (chiLab c.ζ c.d₁ c.d₂) (l.map fun T => T.map (MulAut.conj c.x₂).toMonoidHom)
          (D.map (MulAut.conj c.x₂).toMonoidHom) = clsSets (μ.map (sigma2 c.k₀)) := by
  have hn : n ≠ 0 := by
    have := c.three_le
    omega
  have hN : 1 < 2 ^ n - 1 := by
    have := seven_le c.three_le
    omega
  have h1 : c.x₂⁻¹ * c.d₁ * c.x₂ =
      c.d₁ ^ (1 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (-2 * c.k₀).val := conj_x₂_d₁ c
  have h2 : c.x₂⁻¹ * c.d₂ * c.x₂ =
      c.d₁ ^ (0 : ZMod (2 ^ n - 1)).val * c.d₂ ^ (-1 : ZMod (2 ^ n - 1)).val := by
    rw [conj_x₂_d₂, ZMod.val_zero, pow_zero, one_mul, pow_val_neg_one (d := c.d₂) c.orderOf₂ hN]
  refine ⟨isYSeries_map_conj c.track.x₂_norm hl, ?_⟩
  rw [facMultiset_chiLab_map_conj (a := 1) (b := -2 * c.k₀) (a' := 0) (b' := -1)
    hl c.d₁_mem_H c.d₂_mem_H hn c.orderOf_ζ h1 h2 hμ]
  congr 1
  refine Multiset.map_congr rfl fun φ _ => ?_
  ext <;> simp [sigma2] <;> ring

end Conf

end CFSG.Quasithin.Stroth.G5

end
