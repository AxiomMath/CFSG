module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBSDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPhanDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoBSAlign
import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private def bsf_chartRanges {G : Type} [Group G] {n : ℕ} (U : Fin n → Subgroup G)
    (W : Fin n → Fin n → Subgroup G) (Θ : Su K 2 1 4 →* G) (i j k : Fin n) : Prop :=
  (blockEmb K 2 1 4 2 0 (by norm_num)).range.map Θ = U i ∧
  (blockEmb K 2 1 4 2 1 (by norm_num)).range.map Θ = U j ∧
  (blockEmb K 2 1 4 2 2 (by norm_num)).range.map Θ = U k ∧
  (blockEmb K 2 1 4 3 0 (by norm_num)).range.map Θ = W i j ∧
  (blockEmb K 2 1 4 3 1 (by norm_num)).range.map Θ = W j k

private theorem bsf_adj_chart {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (hS : QTwoWeakPhanSystem K n H U W) {s : ℕ} (hs : s + 2 < n) :
    ∃ Θ : Su K 2 1 4 →* G, Function.Injective Θ ∧
      bsf_chartRanges U W Θ ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩ := by
  obtain ⟨Θ, hΘ, -, h0, h1, h2, h3, h4⟩ :=
    hS.adj ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩ rfl rfl
  exact ⟨Θ, hΘ, h0, h1, h2, h3, h4⟩

private theorem bsf_map_comp_mulEquiv {G : Type} [Group G]
    {φ : Su K 2 1 4 →* G} {β : Su K 2 1 4 ≃* Su K 2 1 4}
    (hβ : ∀ (k i : ℕ) (h : i + k ≤ 4),
      (blockEmb K 2 1 4 k i h).range.map β.toMonoidHom =
        (blockEmb K 2 1 4 k i h).range)
    (k i : ℕ) (h : i + k ≤ 4) :
    (blockEmb K 2 1 4 k i h).range.map (φ.comp β.toMonoidHom) =
      (blockEmb K 2 1 4 k i h).range.map φ := by
  rw [← Subgroup.map_map, hβ]

private theorem bsf_chartRanges_comp_mulEquiv {G : Type} [Group G] {n : ℕ}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    {φ : Su K 2 1 4 →* G} {β : Su K 2 1 4 ≃* Su K 2 1 4}
    (hβ : ∀ (k i : ℕ) (h : i + k ≤ 4),
      (blockEmb K 2 1 4 k i h).range.map β.toMonoidHom =
        (blockEmb K 2 1 4 k i h).range)
    {i j k : Fin n} (h : bsf_chartRanges U W φ i j k) :
    bsf_chartRanges U W (φ.comp β.toMonoidHom) i j k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [bsf_map_comp_mulEquiv hβ]; exact h1
  · rw [bsf_map_comp_mulEquiv hβ]; exact h2
  · rw [bsf_map_comp_mulEquiv hβ]; exact h3
  · rw [bsf_map_comp_mulEquiv hβ]; exact h4
  · rw [bsf_map_comp_mulEquiv hβ]; exact h5

private def bsf_aligned {G : Type} [Group G] {n : ℕ} (U : Fin n → Subgroup G)
    (W : Fin n → Fin n → Subgroup G) (d : ℕ) (Θ : ℕ → Su K 2 1 4 →* G) : Prop :=
  (∀ s, s ≤ d → Function.Injective (Θ s)) ∧
  (∀ (s : ℕ) (hs : s + 2 < n), s ≤ d →
    bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩) ∧
  (∀ s, s + 1 ≤ d →
    (Θ s).comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      (Θ (s + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)))

private theorem bsf_aligned_zero {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (hS : QTwoWeakPhanSystem K n H U W) :
    ∃ Θ : ℕ → Su K 2 1 4 →* G, bsf_aligned U W 0 Θ := by
  classical
  have h4 : 4 ≤ n := hS.four_le
  obtain ⟨φ, hφ, hRφ⟩ := bsf_adj_chart hS (s := 0) (by omega)
  refine ⟨Function.update (fun _ => 1) 0 φ, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : s = 0 := by omega
    subst hs0
    rw [Function.update_apply, if_pos rfl]
    exact hφ
  · intro s hs hsle
    have hs0 : s = 0 := by omega
    subst hs0
    rw [Function.update_apply, if_pos rfl]
    exact hRφ
  · intro s hs
    omega

private theorem bsf_aligned_succ {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    {Θ : ℕ → Su K 2 1 4 →* G} {d : ℕ}
    (hS : QTwoWeakPhanSystem K n H U W)
    (hInj : ∀ s, s ≤ d → Function.Injective (Θ s))
    (hR : ∀ (s : ℕ) (hs : s + 2 < n), s ≤ d →
      bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩)
    (hAlign : ∀ s, s + 1 ≤ d →
      (Θ s).comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
        (Θ (s + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)))
    (hd : d + 1 ≤ n - 3) :
    ∃ Θ' : ℕ → Su K 2 1 4 →* G, bsf_aligned U W (d + 1) Θ' := by
  classical
  obtain ⟨φ, hφ, hRφ⟩ := bsf_adj_chart hS (s := d + 1) (by omega)
  have hRd := hR d (by omega) (by omega)
  have hInjd : Function.Injective (Θ d) := hInj d (by omega)
  have hφ1 : Function.Injective
      ((Θ d).comp (blockEmb K 2 1 4 3 1 (by norm_num))) :=
    hInjd.comp (blockEmb_injective (by norm_num))
  have hφ2 : Function.Injective
      (φ.comp (blockEmb K 2 1 4 3 0 (by norm_num))) :=
    hφ.comp (blockEmb_injective (by norm_num))
  have h3 : ((Θ d).comp (blockEmb K 2 1 4 3 1 (by norm_num))).range =
      (φ.comp (blockEmb K 2 1 4 3 0 (by norm_num))).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hRd.2.2.2.2, hRφ.2.2.2.1]
  have h21 : ((Θ d).comp (blockEmb K 2 1 4 2 1 (by norm_num))).range =
      (φ.comp (blockEmb K 2 1 4 2 0 (by norm_num))).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hRd.2.1, hRφ.1]
  have h22 : ((Θ d).comp (blockEmb K 2 1 4 2 2 (by norm_num))).range =
      (φ.comp (blockEmb K 2 1 4 2 1 (by norm_num))).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hRd.2.2.1, hRφ.2.1]
  obtain ⟨β, hβ, hβeq⟩ :=
    exists_mulEquiv_comp_blockEmb_eq hS.card_four hφ1 hφ2 h3 h21 h22
  let ψ : Su K 2 1 4 →* G := φ.comp β.toMonoidHom
  refine ⟨Function.update Θ (d + 1) ψ, ?_, ?_, ?_⟩
  · intro s hsle
    rcases Nat.lt_or_eq_of_le hsle with hlt | heq
    · rw [Function.update_of_ne (by omega)]
      exact hInj s (by omega)
    · subst heq
      rw [Function.update_apply, if_pos rfl]
      exact hφ.comp β.injective
  · intro s hs hsle
    rcases Nat.lt_or_eq_of_le hsle with hlt | heq
    · rw [Function.update_of_ne (by omega)]
      exact hR s hs (by omega)
    · subst heq
      rw [Function.update_apply, if_pos rfl]
      exact bsf_chartRanges_comp_mulEquiv hβ hRφ
  · intro s hsle
    rcases Nat.lt_or_ge (s + 1) (d + 1) with hlt | hge
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hAlign s (by omega)
    · have hsd : s = d := by omega
      rw [hsd]
      rw [Function.update_of_ne (by omega : d ≠ d + 1), Function.update_apply, if_pos rfl]
      exact hβeq

private theorem bsf_exists_aligned {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (hS : QTwoWeakPhanSystem K n H U W) :
    ∃ Θ : ℕ → Su K 2 1 4 →* G, bsf_aligned U W (n - 3) Θ := by
  have main : ∀ d, d ≤ n - 3 → ∃ Θ : ℕ → Su K 2 1 4 →* G,
      bsf_aligned U W d Θ := by
    intro d
    induction d with
    | zero => intro _; exact bsf_aligned_zero hS
    | succ d ih =>
      intro hd
      obtain ⟨Θ, hInj, hR, hAlign⟩ := ih (by omega)
      exact bsf_aligned_succ hS hInj hR hAlign (by omega)
  exact main (n - 3) (Nat.le_refl _)


private noncomputable def bsf_theta {G : Type} [Group G] (n : ℕ)
    (Θ : ℕ → Su K 2 1 4 →* G) (i : ℕ) : Su K 2 1 3 →* G :=
  if i + 2 < n then (Θ i).comp (blockEmb K 2 1 4 3 0 (by norm_num))
  else if i + 1 < n then (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num))
  else 1

private noncomputable def bsf_iota {G : Type} [Group G] (n : ℕ)
    (Θ : ℕ → Su K 2 1 4 →* G) (i : ℕ) : Su K 2 1 2 →* G :=
  if i + 1 < n then
    (bsf_theta n Θ i).comp (embSUid (unitaryInvolution K 2 1) 2)
  else (bsf_theta n Θ (n - 2)).comp (embSUid (unitaryInvolution K 2 1) 0)

private theorem bsf_block430_comp_two :
    (blockEmb K 2 1 4 3 0 (by norm_num)).comp
        (embSUid (unitaryInvolution K 2 1) 2) =
      blockEmb K 2 1 4 2 0 (by norm_num) :=
  blockEmb3_comp_embSUid_two (n := 3) (i := 0) (by norm_num)

private theorem bsf_block431_comp_two :
    (blockEmb K 2 1 4 3 1 (by norm_num)).comp
        (embSUid (unitaryInvolution K 2 1) 2) =
      blockEmb K 2 1 4 2 1 (by norm_num) :=
  blockEmb3_comp_embSUid_two (n := 3) (i := 1) (by norm_num)

private theorem bsf_block430_comp_zero :
    (blockEmb K 2 1 4 3 0 (by norm_num)).comp
        (embSUid (unitaryInvolution K 2 1) 0) =
      blockEmb K 2 1 4 2 1 (by norm_num) :=
  blockEmb3_comp_embSUid_zero (n := 3) (i := 0) (by norm_num)

private theorem bsf_block431_comp_zero :
    (blockEmb K 2 1 4 3 1 (by norm_num)).comp
        (embSUid (unitaryInvolution K 2 1) 0) =
      blockEmb K 2 1 4 2 2 (by norm_num) :=
  blockEmb3_comp_embSUid_zero (n := 3) (i := 1) (by norm_num)

private theorem bsf_theta_range {G : Type} [Group G] {n : ℕ} {U : Fin n → Subgroup G}
    {W : Fin n → Fin n → Subgroup G} {Θ : ℕ → Su K 2 1 4 →* G}
    (hR : ∀ (s : ℕ) (hs : s + 2 < n), s ≤ n - 3 →
      bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩)
    (hn : 4 ≤ n) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (bsf_theta n Θ (i : ℕ)).range = W i ⟨(i : ℕ) + 1, hi⟩ := by
  by_cases h2 : (i : ℕ) + 2 < n
  · have hθ : bsf_theta n Θ (i : ℕ) =
        (Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
      unfold bsf_theta
      rw [if_pos h2]
    rw [hθ, MonoidHom.range_comp, (hR (i : ℕ) h2 (by omega)).2.2.2.1]
  · have hlt : (i : ℕ) < n := i.isLt
    have h1' : (⟨n - 3 + 1, by omega⟩ : Fin n) = i := by
      ext
      change n - 3 + 1 = (i : ℕ)
      omega
    have h2' : (⟨n - 3 + 2, by omega⟩ : Fin n) = ⟨(i : ℕ) + 1, hi⟩ := by
      ext
      change n - 3 + 2 = (i : ℕ) + 1
      omega
    have hθ : bsf_theta n Θ (i : ℕ) =
        (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
      unfold bsf_theta
      rw [if_neg h2, if_pos hi]
    rw [hθ, MonoidHom.range_comp, (hR (n - 3) (by omega) (by omega)).2.2.2.2, h1', h2']

private theorem bsf_iota_range {G : Type} [Group G] {n : ℕ} {U : Fin n → Subgroup G}
    {W : Fin n → Fin n → Subgroup G} {Θ : ℕ → Su K 2 1 4 →* G}
    (hR : ∀ (s : ℕ) (hs : s + 2 < n), s ≤ n - 3 →
      bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩)
    (hn : 4 ≤ n) (i : Fin n) :
    (bsf_iota n Θ (i : ℕ)).range = U i := by
  by_cases hi : (i : ℕ) + 1 < n
  · unfold bsf_iota
    rw [if_pos hi]
    by_cases h2 : (i : ℕ) + 2 < n
    · have hθ : bsf_theta n Θ (i : ℕ) =
          (Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
        unfold bsf_theta
        rw [if_pos h2]
      rw [hθ, MonoidHom.comp_assoc, bsf_block430_comp_two, MonoidHom.range_comp,
        (hR (i : ℕ) h2 (by omega)).1]
    · have hin : (i : ℕ) = n - 2 := by omega
      have hθ : bsf_theta n Θ (i : ℕ) =
          (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
        unfold bsf_theta
        rw [if_neg h2, if_pos hi]
      rw [hθ, MonoidHom.comp_assoc, bsf_block431_comp_two, MonoidHom.range_comp,
        (hR (n - 3) (by omega) (by omega)).2.1]
      have hlt : (i : ℕ) < n := i.isLt
      congr 1
      ext
      change n - 3 + 1 = (i : ℕ)
      omega
  · have hin : (i : ℕ) = n - 1 := by omega
    unfold bsf_iota
    rw [if_neg hi]
    have hθ : bsf_theta n Θ (n - 2) =
        (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
      unfold bsf_theta
      rw [if_neg (by omega), if_pos (by omega)]
    rw [hθ, MonoidHom.comp_assoc, bsf_block431_comp_zero, MonoidHom.range_comp,
      (hR (n - 3) (by omega) (by omega)).2.2.1]
    have hlt : (i : ℕ) < n := i.isLt
    congr 1
    ext
    change n - 3 + 2 = (i : ℕ)
    omega


private theorem bsf_right_gen {G : Type} [Group G] {n : ℕ} {Θ : ℕ → Su K 2 1 4 →* G}
    (hAlign : ∀ s, s + 1 ≤ n - 3 →
      (Θ s).comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
        (Θ (s + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)))
    (i : Fin n) (h3 : (i : ℕ) + 3 < n) :
    (bsf_theta n Θ (i : ℕ)).comp (embSUid (unitaryInvolution K 2 1) 0) =
      bsf_iota n Θ ((i : ℕ) + 1) := by
  have h2 : (i : ℕ) + 2 < n := by omega
  have hθ : bsf_theta n Θ (i : ℕ) =
      (Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
    unfold bsf_theta; rw [if_pos h2]
  have hθ' : bsf_theta n Θ ((i : ℕ) + 1) =
      (Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
    unfold bsf_theta; rw [if_pos h3]
  have hι : bsf_iota n Θ ((i : ℕ) + 1) =
      (bsf_theta n Θ ((i : ℕ) + 1)).comp
        (embSUid (unitaryInvolution K 2 1) 2) := by
    unfold bsf_iota; rw [if_pos (by omega)]
  have hal : (Θ (i : ℕ)).comp (blockEmb K 2 1 4 2 1 (by norm_num)) =
      (Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 2 0 (by norm_num)) := by
    calc (Θ (i : ℕ)).comp (blockEmb K 2 1 4 2 1 (by norm_num))
        = (Θ (i : ℕ)).comp ((blockEmb K 2 1 4 3 1 (by norm_num)).comp
            (embSUid (unitaryInvolution K 2 1) 2)) := by rw [bsf_block431_comp_two]
      _ = ((Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 1 (by norm_num))).comp
            (embSUid (unitaryInvolution K 2 1) 2) := by rw [MonoidHom.comp_assoc]
      _ = ((Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num))).comp
            (embSUid (unitaryInvolution K 2 1) 2) := by
          rw [hAlign (i : ℕ) (by omega)]
      _ = (Θ ((i : ℕ) + 1)).comp ((blockEmb K 2 1 4 3 0 (by norm_num)).comp
            (embSUid (unitaryInvolution K 2 1) 2)) := by rw [MonoidHom.comp_assoc]
      _ = (Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 2 0 (by norm_num)) := by
          rw [bsf_block430_comp_two]
  have hL : ((Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num))).comp
        (embSUid (unitaryInvolution K 2 1) 0) =
      (Θ (i : ℕ)).comp (blockEmb K 2 1 4 2 1 (by norm_num)) := by
    rw [MonoidHom.comp_assoc, bsf_block430_comp_zero]
  have hR : ((Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num))).comp
        (embSUid (unitaryInvolution K 2 1) 2) =
      (Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 2 0 (by norm_num)) := by
    rw [MonoidHom.comp_assoc, bsf_block430_comp_two]
  rw [hθ, hι, hθ', hL, hR]
  exact hal

private theorem bsf_right {G : Type} [Group G] {n : ℕ} {Θ : ℕ → Su K 2 1 4 →* G}
    (hn : 4 ≤ n)
    (hAlign : ∀ s, s + 1 ≤ n - 3 →
      (Θ s).comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
        (Θ (s + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)))
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (bsf_theta n Θ (i : ℕ)).comp (embSUid (unitaryInvolution K 2 1) 0) =
      bsf_iota n Θ ((i : ℕ) + 1) := by
  by_cases h3 : (i : ℕ) + 3 < n
  · exact bsf_right_gen hAlign i h3
  · by_cases h2 : (i : ℕ) + 2 < n
    · have hin : (i : ℕ) = n - 3 := by omega
      have hθ : bsf_theta n Θ (i : ℕ) =
          (Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
        unfold bsf_theta; rw [if_pos h2]
      have hθ' : bsf_theta n Θ ((i : ℕ) + 1) =
          (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
        unfold bsf_theta; rw [if_neg (by omega), if_pos (by omega)]
      have hι : bsf_iota n Θ ((i : ℕ) + 1) =
          (bsf_theta n Θ ((i : ℕ) + 1)).comp
            (embSUid (unitaryInvolution K 2 1) 2) := by
        unfold bsf_iota; rw [if_pos (by omega)]
      have hL : ((Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num))).comp
            (embSUid (unitaryInvolution K 2 1) 0) =
          (Θ (i : ℕ)).comp (blockEmb K 2 1 4 2 1 (by norm_num)) := by
        rw [MonoidHom.comp_assoc, bsf_block430_comp_zero]
      have hR : ((Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num))).comp
            (embSUid (unitaryInvolution K 2 1) 2) =
          (Θ (n - 3)).comp (blockEmb K 2 1 4 2 1 (by norm_num)) := by
        rw [MonoidHom.comp_assoc, bsf_block431_comp_two]
      rw [hθ, hι, hθ', hL, hR, ← hin]
    · have hin : (i : ℕ) = n - 2 := by omega
      have hθ : bsf_theta n Θ (i : ℕ) =
          (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
        unfold bsf_theta; rw [if_neg h2, if_pos hi]
      have hθ2 : bsf_theta n Θ (n - 2) =
          (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
        unfold bsf_theta; rw [if_neg (by omega), if_pos (by omega)]
      have hι : bsf_iota n Θ ((i : ℕ) + 1) =
          (bsf_theta n Θ (n - 2)).comp
            (embSUid (unitaryInvolution K 2 1) 0) := by
        unfold bsf_iota; rw [if_neg (by omega)]
      rw [hθ, hι, hθ2]

private theorem bsf_four {G : Type} [Group G] {n : ℕ} {Θ : ℕ → Su K 2 1 4 →* G}
    (hn : 4 ≤ n)
    (hAlign : ∀ s, s + 1 ≤ n - 3 →
      (Θ s).comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
        (Θ (s + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)))
    (i : Fin n) (hi : (i : ℕ) + 2 < n) :
    ∃ Θ' : Su K 2 1 4 →* G,
      Θ'.comp (blockEmb K 2 1 4 3 0 (by norm_num)) = bsf_theta n Θ (i : ℕ) ∧
      Θ'.comp (blockEmb K 2 1 4 3 1 (by norm_num)) = bsf_theta n Θ ((i : ℕ) + 1) := by
  by_cases h3 : (i : ℕ) + 3 < n
  · refine ⟨Θ (i : ℕ), ?_, ?_⟩
    · have hθ : bsf_theta n Θ (i : ℕ) =
          (Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
        unfold bsf_theta; rw [if_pos hi]
      rw [hθ]
    · have hθ : bsf_theta n Θ ((i : ℕ) + 1) =
          (Θ ((i : ℕ) + 1)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
        unfold bsf_theta; rw [if_pos h3]
      rw [hθ]
      exact hAlign (i : ℕ) (by omega)
  · have hin : (i : ℕ) = n - 3 := by omega
    refine ⟨Θ (n - 3), ?_, ?_⟩
    · have hθ : bsf_theta n Θ (i : ℕ) =
          (Θ (i : ℕ)).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
        unfold bsf_theta; rw [if_pos hi]
      rw [hθ, ← hin]
    · have hθ2 : bsf_theta n Θ ((i : ℕ) + 1) =
          (Θ (n - 3)).comp (blockEmb K 2 1 4 3 1 (by norm_num)) := by
        unfold bsf_theta; rw [if_neg (by omega), if_pos (by omega)]
      rw [hθ2]

private theorem bsf_comm {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    {Θ : ℕ → Su K 2 1 4 →* G}
    (hS : QTwoWeakPhanSystem K n H U W) (hn : 4 ≤ n)
    (hR : ∀ (s : ℕ) (hs : s + 2 < n), s ≤ n - 3 →
      bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩)
    (i j : Fin n) (hij : (i : ℕ) + 1 < j) (a b : Su K 2 1 2) :
    bsf_iota n Θ (i : ℕ) a * bsf_iota n Θ (j : ℕ) b =
      bsf_iota n Θ (j : ℕ) b * bsf_iota n Θ (i : ℕ) a := by
  have hi : (bsf_iota n Θ (i : ℕ)).range = U i := bsf_iota_range hR hn i
  have hj : (bsf_iota n Θ (j : ℕ)).range = U j := bsf_iota_range hR hn j
  have ha : bsf_iota n Θ (i : ℕ) a ∈ U i := by rw [← hi]; exact ⟨a, rfl⟩
  have hb : bsf_iota n Θ (j : ℕ) b ∈ U j := by rw [← hj]; exact ⟨b, rfl⟩
  exact hS.comm i j (by omega) hij _ ha _ hb

private theorem bsf_farNodeEdge {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    {Θ : ℕ → Su K 2 1 4 →* G}
    (hS : QTwoWeakPhanSystem K n H U W) (hn : 4 ≤ n)
    (hR : ∀ (s : ℕ) (hs : s + 2 < n), s ≤ n - 3 →
      bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩)
    (i j : Fin n) (hj : (j : ℕ) + 1 < n)
    (hij : (i : ℕ) + 1 < j ∨ (j : ℕ) + 2 < i)
    (a : Su K 2 1 2) (b : Su K 2 1 3) :
    bsf_iota n Θ (i : ℕ) a * bsf_theta n Θ (j : ℕ) b =
      bsf_theta n Θ (j : ℕ) b * bsf_iota n Θ (i : ℕ) a := by
  have hi : (bsf_iota n Θ (i : ℕ)).range = U i := bsf_iota_range hR hn i
  have hθ : (bsf_theta n Θ (j : ℕ)).range = W j ⟨(j : ℕ) + 1, hj⟩ :=
    bsf_theta_range hR hn j hj
  have ha : bsf_iota n Θ (i : ℕ) a ∈ U i := by rw [← hi]; exact ⟨a, rfl⟩
  have hb : bsf_theta n Θ (j : ℕ) b ∈ W j ⟨(j : ℕ) + 1, hj⟩ := by
    rw [← hθ]; exact ⟨b, rfl⟩
  exact hS.farNodeEdge i j ⟨(j : ℕ) + 1, hj⟩ rfl hij _ ha _ hb

private theorem bsf_farEdgeEdge {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    {Θ : ℕ → Su K 2 1 4 →* G}
    (hS : QTwoWeakPhanSystem K n H U W) (hn : 4 ≤ n)
    (hR : ∀ (s : ℕ) (hs : s + 2 < n), s ≤ n - 3 →
      bsf_chartRanges U W (Θ s) ⟨s, by omega⟩ ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩)
    (i j : Fin n) (hj : (j : ℕ) + 1 < n) (hij : (i : ℕ) + 2 < j)
    (a b : Su K 2 1 3) :
    bsf_theta n Θ (i : ℕ) a * bsf_theta n Θ (j : ℕ) b =
      bsf_theta n Θ (j : ℕ) b * bsf_theta n Θ (i : ℕ) a := by
  have hi : (i : ℕ) + 1 < n := by omega
  have hθi : (bsf_theta n Θ (i : ℕ)).range = W i ⟨(i : ℕ) + 1, hi⟩ :=
    bsf_theta_range hR hn i hi
  have hθj : (bsf_theta n Θ (j : ℕ)).range = W j ⟨(j : ℕ) + 1, hj⟩ :=
    bsf_theta_range hR hn j hj
  have ha : bsf_theta n Θ (i : ℕ) a ∈ W i ⟨(i : ℕ) + 1, hi⟩ := by
    rw [← hθi]; exact ⟨a, rfl⟩
  have hb : bsf_theta n Θ (j : ℕ) b ∈ W j ⟨(j : ℕ) + 1, hj⟩ := by
    rw [← hθj]; exact ⟨b, rfl⟩
  exact hS.farEdgeEdge i j ⟨(i : ℕ) + 1, hi⟩ ⟨(j : ℕ) + 1, hj⟩ rfl rfl (Or.inl hij) _ ha _ hb

theorem QTwoWeakPhanSystem.exists_qTwoPhanFamily {G : Type} [Group G] {n : ℕ} {H : Subgroup G}
    {U : Fin n → Subgroup G} {W : Fin n → Fin n → Subgroup G}
    (hS : QTwoWeakPhanSystem K n H U W) :
    ∃ F : QTwoPhanFamily K G n, (∀ i, (F.ι i).range = U i) ∧
      ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), (F.θ i).range = W i ⟨i + 1, h⟩ := by
  classical
  obtain ⟨Θ, hInj, hR, hAlign⟩ := bsf_exists_aligned hS
  have hn : 4 ≤ n := hS.four_le
  let F : QTwoPhanFamily K G n :=
    { ι := fun i => bsf_iota n Θ (i : ℕ)
      θ := fun i => bsf_theta n Θ (i : ℕ)
      left := fun i hi => by
        unfold bsf_iota
        rw [if_pos hi]
      right := fun i hi => bsf_right hn hAlign i hi
      comm := fun i j hij a b => bsf_comm hS hn hR i j hij a b
      four := fun i hi => bsf_four hn hAlign i hi
      farNodeEdge := fun i j hj hij a b => bsf_farNodeEdge hS hn hR i j hj hij a b
      farEdgeEdge := fun i j hj hij a b => bsf_farEdgeEdge hS hn hR i j hj hij a b }
  refine ⟨F, ?_, ?_⟩
  · intro i
    exact bsf_iota_range hR hn i
  · intro i h
    exact bsf_theta_range hR hn i h

end CFSG.StandardType.QTwo

end
