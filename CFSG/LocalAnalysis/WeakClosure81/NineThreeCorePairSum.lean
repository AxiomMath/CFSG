module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairMem
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairSumD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_pair_sum_list_prod_mem {W : Subgroup G} (l : List G) (f : G → G)
    (h : ∀ x ∈ l, f x ∈ W) : (l.map f).prod ∈ W := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.prod_cons]
      exact W.mul_mem (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

private theorem nine3_pair_sum_comm_list {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {i : G} (l : List G)
    (hl : ∀ x ∈ l, x ∈ W) (hlc : ∀ x ∈ l, ⁅i, x⁆ ∈ W) :
    ⁅i, l.prod⁆ = (l.map fun x => ⁅i, x⁆).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hxW : x ∈ W := hl x (by simp)
      have hrestW : (l.map fun x => ⁅i, x⁆).prod ∈ W :=
        nine3_pair_sum_list_prod_mem l (fun x => ⁅i, x⁆) (fun y hy => hlc y (by simp [hy]))
      have hih : ⁅i, l.prod⁆ = (l.map fun x => ⁅i, x⁆).prod :=
        ih (fun y hy => hl y (by simp [hy])) (fun y hy => hlc y (by simp [hy]))
      have hconj : x * (l.map fun x => ⁅i, x⁆).prod * x⁻¹ = (l.map fun x => ⁅i, x⁆).prod := by
        rw [hW x hxW _ hrestW]
        group
      rw [List.prod_cons, commutatorElement_mul_right_eq_mul_conj, hih]
      calc ⁅i, x⁆ * x * (l.map fun x => ⁅i, x⁆).prod * x⁻¹
          = ⁅i, x⁆ * (x * (l.map fun x => ⁅i, x⁆).prod * x⁻¹) := by group
        _ = ⁅i, x⁆ * (l.map fun x => ⁅i, x⁆).prod := by rw [hconj]
        _ = (List.map (fun x => ⁅i, x⁆) (x :: l)).prod := by
              rw [List.map_cons, List.prod_cons]

private theorem nine3_pair_sum_prod_inv {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (l : List ↥W) :
    (l.map fun x => x⁻¹).prod = (l.prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.prod_cons, List.prod_cons, ih, mul_inv_rev]
      exact Subtype.ext (hW x⁻¹ (W.inv_mem x.2) (l.prod)⁻¹ (W.inv_mem (l.prod).2))

private theorem nine3_pair_sum_conj_prod (l : List G) (a : G) :
    (l.map fun z => a⁻¹ * z * a).prod = a⁻¹ * l.prod * a := by
  induction l with
  | nil => simp
  | cons z l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; group

private theorem nine3_pair_sum_finRange_perm {M : Type*} [CommMonoid M] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (f : Fin n → M) :
    ((List.finRange n).map fun i => f (σ i)).prod = ((List.finRange n).map f).prod := by
  have h := Equiv.prod_comp σ f
  rwa [Fin.prod_univ_def, Fin.prod_univ_def] at h

theorem nine3_pair_five_sum (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {B : Fin (4 + 1) → Subgroup G} {σ : Equiv.Perm (Fin (4 + 1))} {bb : Fin (4 + 1) → G}
    (he : Nine3PairEnum V K S A g 4 B σ bb) (hcard : Nat.card ↥(nineDelta V S) = 5) :
    (∀ i ∈ nineI V K, ((List.finRange 5).map fun k => ⁅i, bb k⁆).prod = 1) ∧
      (∀ j ∈ conjSubgroup (nineI V K) g,
        ((List.finRange 5).map fun l => ⁅g⁻¹ * bb (σ.symm l) * g, j⁆).prod = 1) ∧
      ∀ h ∈ nineH V K, ⁅bb 1 * bb 2 * bb 3 * bb 4, h⁆ ∈ nineI V K := by
  classical
  letI : CommMonoid ↥(nineW V S) :=
    { (inferInstance : Monoid ↥(nineW V S)) with
      mul_comm := fun a b => Subtype.ext (hc.core.nineW_mul_comm a.2 b.2) }
  have hbbprod : ((List.finRange 5).map bb).prod = bb 1 * bb 2 * bb 3 * bb 4 := by
    rw [show List.finRange 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [he.bb0]
    group
  have hsum₁ : ∀ i ∈ nineI V K, ((List.finRange 5).map fun k => ⁅i, bb k⁆).prod = 1 := by
    intro i hi
    have hbbW : ∀ x ∈ (List.finRange 5).map bb, x ∈ nineW V S := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      by_cases hk : k = 0
      · rw [hk, he.bb0]
        exact (nineW V S).one_mem
      · exact (le_iSup₂_of_le (B k)
          (hc.core.mem_nineDelta_iff.mpr (Or.inr (he.Ω k hk))) le_rfl : B k ≤ nineW V S)
          (he.bb_mem k hk).1
    have hφW : ∀ x ∈ (List.finRange 5).map bb, ⁅i, x⁆ ∈ nineW V S := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact nine3_pair_P_le_W hc he.mem k (nine3_pair_phi_mem hI he hi k)
    have hcomm := nine3_pair_sum_comm_list (W := nineW V S)
      (fun a ha b hb => hc.core.nineW_mul_comm ha hb) ((List.finRange 5).map bb) hbbW hφW
    have hmap : (List.finRange 5).map (fun k => ⁅i, bb k⁆)
        = ((List.finRange 5).map bb).map (fun x => ⁅i, x⁆) := by
      rw [List.map_map]
      rfl
    rw [hmap, ← hcomm, hbbprod]
    exact nine3_pair_five_delta hc hI he hcard i hi
  refine ⟨hsum₁, ?_, nine3_pair_five_central hc hI he hcard⟩
  intro j hj
  let y : G := g * j * g⁻¹
  have hyI : y ∈ nineI V K := mem_conjSubgroup_iff.mp hj
  let ξ : Fin 5 → G := fun k => ⁅g⁻¹ * bb k * g, j⁆
  let F : Fin 5 → G := fun k => ⁅bb k, y⁆
  let P : Fin 5 → G := fun k => ⁅y, bb k⁆
  have hPmem : ∀ k, P k ∈ nineW V S := fun k =>
    nine3_pair_P_le_W hc he.mem k (nine3_pair_phi_mem hI he hyI k)
  let P' : Fin 5 → ↥(nineW V S) := fun k => ⟨P k, hPmem k⟩
  have hFval : ∀ k, F k = (P k)⁻¹ := fun k =>
    (commutatorElement_inv (g₁ := y) (g₂ := bb k)).symm
  let F' : Fin 5 → ↥(nineW V S) := fun k =>
    ⟨F k, by
      rw [hFval k]
      exact (nineW V S).inv_mem (hPmem k)⟩
  have hF' : ∀ k, F' k = (P' k)⁻¹ := by
    intro k
    apply Subtype.ext
    exact hFval k
  have hP'prod : ((List.finRange 5).map P').prod = 1 := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod]
    have hmap : ((List.finRange 5).map P').map Subtype.val = (List.finRange 5).map P := by
      rw [List.map_map]
      rfl
    rw [hmap, hsum₁ y hyI]
    rfl
  have hF'prod : ((List.finRange 5).map F').prod = 1 := by
    have hmap : ((List.finRange 5).map P').map (fun z => z⁻¹) =
        (List.finRange 5).map F' := by
      rw [List.map_map]
      exact List.map_congr_left (fun k _ => (hF' k).symm)
    rw [← hmap, nine3_pair_sum_prod_inv
      (W := nineW V S) (fun a ha b hb => hc.core.nineW_mul_comm ha hb), hP'prod, inv_one]
  have hF : ((List.finRange 5).map F).prod = 1 := by
    have hco := Subgroup.val_list_prod (H := nineW V S) (l := (List.finRange 5).map F')
    have hmap : ((List.finRange 5).map F').map Subtype.val = (List.finRange 5).map F := by
      rw [List.map_map]
      rfl
    rw [← hmap, ← hco, hF'prod]
    rfl
  have hξF : ∀ k : Fin 5, ξ k = g⁻¹ * F k * g := by
    intro k
    have h := conjugate_commutatorElement (g₁ := bb k) (g₂ := y) (g₃ := g⁻¹)
    rw [inv_inv] at h
    have hy : g⁻¹ * y * g = j := by
      show g⁻¹ * (g * j * g⁻¹) * g = j
      group
    rw [hy] at h
    exact h.symm
  have hξeq : ((List.finRange 5).map ξ).prod = g⁻¹ * ((List.finRange 5).map F).prod * g := by
    have hmap : ((List.finRange 5).map F).map (fun z => g⁻¹ * z * g)
        = (List.finRange 5).map ξ := by
      rw [List.map_map]
      exact List.map_congr_left (fun k _ => (hξF k).symm)
    rw [← hmap, nine3_pair_sum_conj_prod]
  have hξ : ((List.finRange 5).map ξ).prod = 1 := by
    rw [hξeq, hF]
    group
  let Ξ : Fin 5 → ↥(nineW V S) := fun k =>
    ⟨ξ k, by
      have hps := nine3_pair_psi_mem hc hI he hj (σ k)
      rw [Equiv.symm_apply_apply] at hps
      exact nine3_pair_P_le_W hc he.mem (σ k) hps⟩
  let Ψ : Fin 5 → ↥(nineW V S) := fun l => Ξ (σ.symm l)
  have hΞprod : ((List.finRange 5).map Ξ).prod = 1 := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod]
    have hmap : ((List.finRange 5).map Ξ).map Subtype.val = (List.finRange 5).map ξ := by
      rw [List.map_map]
      rfl
    rw [hmap, hξ]
    rfl
  have hΨΞ : ((List.finRange 5).map Ψ).prod = ((List.finRange 5).map Ξ).prod :=
    nine3_pair_sum_finRange_perm (σ := σ.symm) (f := Ξ)
  have hval : ((List.finRange 5).map (fun l => ⁅g⁻¹ * bb (σ.symm l) * g, j⁆)).prod
      = (((List.finRange 5).map Ψ).prod : G) := by
    have hco := Subgroup.val_list_prod (H := nineW V S) (l := (List.finRange 5).map Ψ)
    have hmap : ((List.finRange 5).map Ψ).map Subtype.val
        = (List.finRange 5).map (fun l => ⁅g⁻¹ * bb (σ.symm l) * g, j⁆) := by
      rw [List.map_map]
      rfl
    rw [← hmap, ← hco]
  rw [hval, hΨΞ, hΞprod]
  rfl

end CFSG.LocalAnalysis.WeakClosure81
