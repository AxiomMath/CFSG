module

public import CFSG.LocalAnalysis.StandardType.GGResIINonegDefs
public import CFSG.LocalAnalysis.StandardType.GGResIINegOne
public import CFSG.LocalAnalysis.StandardType.GGForkClassify
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.LocalAnalysis.StandardType.GGResIISmallDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResII_negOne_of_not_noneg {ι : Type} [Fintype ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) {C : Matrix ι ι ℤ} (hC : GGIntCartan M C) (hcard : Fintype.card ι < 9)
    (hn : ¬ GGResIINonegType C) :
    ∃ (n : ℕ) (e : Fin n ≃ ι) (C₀ : Matrix (Fin n) (Fin n) ℤ) (k : ℕ),
      (∀ i j, C (e i) (e j) = C₀ i j) ∧ ggNegOneCheck C₀ k = true ∧
        (C₀.det = 1 ∨ C₀.det = 2 ∨ C₀.det = 4) := by
  have hcardn : ∀ {n : ℕ} (e : Fin n ≃ ι), n < 9 := fun e => by
    rw [← Fintype.card_congr e, Fintype.card_fin] at hcard
    exact hcard
  rcases ggIntCartan_models hM hC with ⟨n, e, hn1, hA | ⟨hn2, hB | hCC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ |
    ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4 | hF4T⟩ | ⟨e, hG2 | hG2T⟩
  · by_cases h1 : n = 1
    · subst h1
      refine ⟨1, e, CartanMatrix.A 1, 1, hA, ggNegOneCheck_A_one, Or.inr (Or.inl ?_)⟩
      rw [CartanMatrix.A_det]; norm_num
    · exact absurd (Or.inl ⟨n, e, by omega, hA⟩) hn
  · refine ⟨n, e, CartanMatrix.B n, n, hB, ggNegOneCheck_B hn2 (by have := hcardn e; omega),
      Or.inr (Or.inl ?_)⟩
    rw [CartanMatrix.B_det (by omega)]
  · refine ⟨n, e, CartanMatrix.C n, n, hCC, ggNegOneCheck_C hn2 (by have := hcardn e; omega),
      Or.inr (Or.inl ?_)⟩
    rw [CartanMatrix.C_det (by omega)]
  · rcases Nat.even_or_odd n with he | ho
    · refine ⟨n, e, CartanMatrix.D n, n - 1, hD,
        ggNegOneCheck_D hn4 (by have := hcardn e; omega) he, Or.inr (Or.inr ?_)⟩
      rw [CartanMatrix.D_det (by omega)]
    · have h5 : 5 ≤ n := by
        rcases ho with ⟨m, rfl⟩
        omega
      exact absurd (Or.inr (Or.inl ⟨n, e, h5, ho, hD⟩)) hn
  · exact absurd (Or.inr (Or.inr ⟨e, hE6⟩)) hn
  · refine ⟨7, e, CartanMatrix.E 7, 9, hE7, ggNegOneCheck_E7, Or.inr (Or.inl ?_)⟩
    rw [CartanMatrix.E_det (by norm_num)]; norm_num
  · exact ⟨8, e, CartanMatrix.E 8, 15, hE8, ggNegOneCheck_E8, Or.inl CartanMatrix.E₈_det⟩
  · exact ⟨4, e, CartanMatrix.F₄, 6, hF4, ggNegOneCheck_F4.1, Or.inl CartanMatrix.F₄_det⟩
  · refine ⟨4, e, CartanMatrix.F₄.transpose, 6, fun i j => hF4T i j, ggNegOneCheck_F4.2,
      Or.inl ?_⟩
    rw [Matrix.det_transpose, CartanMatrix.F₄_det]
  · exact ⟨2, e, CartanMatrix.G₂, 3, hG2, ggNegOneCheck_G2.1, Or.inl CartanMatrix.G₂_det⟩
  · refine ⟨2, e, CartanMatrix.G₂.transpose, 3, fun i j => hG2T i j, ggNegOneCheck_G2.2,
      Or.inl ?_⟩
    rw [Matrix.det_transpose, CartanMatrix.G₂_det]

section Frontier

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem ggResII_prod_fix {ι : Type} (r : ι → (V ≃ₗ[ZMod p] V)) {z : V}
    (hr : ∀ i, r i z = z) (ws : List ι) : (ws.map r).prod z = z := by
  induction ws with
  | nil => rfl
  | cons i ws ih => rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, hr]

private theorem ggResII_prod_mem {ι κ : Type} (g : ι → (V ≃ₗ[ZMod p] V)) (f : κ → ι)
    (ws : List κ) : (ws.map (fun i => g (f i))).prod ∈ Subgroup.closure (Set.range g) := by
  apply Subgroup.list_prod_mem
  intro t ht
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
  exact Subgroup.subset_closure ⟨f i, rfl⟩

private theorem ggResII_neg_of_span {κ : Type} [Fintype κ] (w : V ≃ₗ[ZMod p] V) (v : κ → V)
    (hw : ∀ j, w (v j) = -v j) {u : V} (hu : u ∈ Submodule.span (ZMod p) (Set.range v)) :
    w u = -u := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hu
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hw, smul_neg]

theorem ggResIILin_tv_L (hp2 : p ≠ 2) {Λ : Type} (g : Option Λ → (V ≃ₗ[ZMod p] V))
    (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V) {x : V}
    (hg : ∀ o w, g o w = w - α o w • h o) (hLI : LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hdep : ¬ LinearIndependent (ZMod p) h) (hxfix : ∀ i : Λ, α (some i) x = 0)
    (hxa : α none x ≠ 0) (ha2 : α none (h none) = 2) {n : ℕ} (e : Fin n ≃ Λ)
    {C₀ : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hC : ∀ i j, α (some (e i)) (h (some (e j))) = (C₀ i j : ZMod p))
    (hchk : ggNegOneCheck C₀ k = true) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  let r : Fin n → (V ≃ₗ[ZMod p] V) := fun i => g (some (e i))
  let w := ((ggNegCox n k).map r).prod
  have hw : w ∈ Subgroup.closure (Set.range g) := ggResII_prod_mem g (fun i => some (e i)) _
  have hwj : ∀ j, w (h (some (e j))) = -h (some (e j)) :=
    ggNegOneCheck_sound (fun j => h (some (e j))) (fun i => α (some (e i))) r C₀
      (fun i v => hg (some (e i)) v) hC hchk
  have hmem : h none ∈ Submodule.span (ZMod p) (Set.range fun j : Fin n => h (some (e j))) := by
    have hrange : (Set.range fun j : Fin n => h (some (e j))) = Set.range fun i : Λ => h (some i) :=
      (Set.range_comp (fun i : Λ => h (some i)) e).trans (by rw [e.range_eq_univ, Set.image_univ])
    rw [hrange]
    by_contra hc
    exact hdep ((linearIndependent_option (v := h) (K := ZMod p)).mpr ⟨hLI, hc⟩)
  have hwa : w (h none) = -h none := ggResII_neg_of_span w _ hwj hmem
  have hwx : w x = x := ggResII_prod_fix r (fun i => by
    show g (some (e i)) x = x
    rw [hg, hxfix, zero_smul, sub_zero]) _
  exact ggResII_tv_of_neg hp2 g h α hg ha2 hw hwa hwx hxa

theorem ggResIILin_tv_K [Module.Finite (ZMod p) V] (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {b : Λ}
    (g : Option Λ → (V ≃ₗ[ZMod p] V)) (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod p) V)
    {x y : V} (hg : ∀ o w, g o w = w - α o w • h o)
    (hLI : LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hdep : ¬ LinearIndependent (ZMod p) h) (hb2 : α (some b) (h (some b)) = 2)
    (hspan : ∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x})
    (hyfix : ∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) y = 0)
    (hyx : y ∉ Submodule.span (ZMod p) {x}) {n : ℕ} (eK : Fin n ≃ Option {i : Λ // i ≠ b})
    {C₀ : Matrix (Fin n) (Fin n) ℤ} {k : ℕ}
    (hC : ∀ i j, α ((eK i).map Subtype.val) (h ((eK j).map Subtype.val)) = (C₀ i j : ZMod p))
    (hchk : ggNegOneCheck C₀ k = true) (hdet : C₀.det = 1 ∨ C₀.det = 2 ∨ C₀.det = 4) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  classical
  let hv : Fin n → V := fun j => h ((eK j).map Subtype.val)
  let r : Fin n → (V ≃ₗ[ZMod p] V) := fun i => g ((eK i).map Subtype.val)
  let w := ((ggNegCox n k).map r).prod
  have hw : w ∈ Subgroup.closure (Set.range g) :=
    ggResII_prod_mem g (fun i => (eK i).map Subtype.val) _
  have hwj : ∀ j, w (hv j) = -hv j :=
    ggNegOneCheck_sound hv (fun i => α ((eK i).map Subtype.val)) r C₀
      (fun i v => hg _ v) hC hchk
  have hdet' : (C₀.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
    have hmap := (Int.castRingHom (ZMod p)).map_det C₀
    rw [RingHom.mapMatrix_apply] at hmap
    change (C₀.map (Int.castRingHom (ZMod p))).det ≠ 0
    rw [← hmap]
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
    rcases hdet with h1 | h1 | h1 <;> rw [h1] <;> simp
    · exact h2
    · rw [show (4 : ZMod p) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
  have hind : LinearIndependent (ZMod p) hv := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmv : (C₀.map (Int.cast : ℤ → ZMod p)).mulVec c = 0 := by
      funext i
      have := congrArg (α ((eK i).map Subtype.val)) hc
      rw [map_sum, map_zero] at this
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, Matrix.map_apply, hC, mul_comm]
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet' hmv)
  let U := Submodule.span (ZMod p) (Set.range fun i : Λ => h (some i))
  have hnone : h none ∈ U := by
    by_contra hc
    exact hdep ((linearIndependent_option (v := h) (K := ZMod p)).mpr ⟨hLI, hc⟩)
  have hle : Submodule.span (ZMod p) (Set.range hv) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases hj : eK j with _ | ⟨i, hi⟩
    · simp only [hv, hj, Option.map_none]
      exact hnone
    · simp only [hv, hj, Option.map_some]
      exact Submodule.subset_span ⟨i, rfl⟩
  have hcardK : Fintype.card (Fin n) = Fintype.card Λ := by
    rw [Fintype.card_congr eK, Fintype.card_congr (Equiv.optionSubtypeNe b)]
  have heq : Submodule.span (ZMod p) (Set.range hv) = U := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hind, finrank_span_eq_card hLI, hcardK]
  have hwb : w (h (some b)) = -h (some b) :=
    ggResII_neg_of_span w hv hwj (by rw [heq]; exact Submodule.subset_span ⟨b, rfl⟩)
  have hwy : w y = y := ggResII_prod_fix r (fun i => by
    show g ((eK i).map Subtype.val) y = y
    rw [hg, hyfix, zero_smul, sub_zero]) _
  have hyb : α (some b) y ≠ 0 := by
    intro h0
    refine hyx (hspan y fun i => ?_)
    by_cases hi : i = b
    · rw [hi]; exact h0
    · exact hyfix (some ⟨i, hi⟩)
  exact ggResII_tv_of_neg hp2 g h α hg hb2 hw hwb hwy hyb

end Frontier

theorem ggResIILinInput_of_noneg (hN : GGResIILinNonegInput) : GGResIILinInput := by
  intro p _ Λ _ _ b ML CL MK CK V _ _ _ g h α x y hp2 hcard hWL hCL hWK hCK hdel hg hL hK hLI hdep
    hxfix hspan hxa hyfix hyx
  have ha2 : α none (h none) = 2 := by
    have h1 := hK none none
    rw [hCK.1 none] at h1
    simpa using h1
  have hb2 : α (some b) (h (some b)) = 2 := by
    have h1 := hL b b
    rw [hCL.1 b] at h1
    simpa using h1
  by_cases hnL : GGResIINonegType CL
  · by_cases hnK : GGResIINonegType CK
    · exact hN p Λ b ML CL MK CK V g h α x y hp2 hcard hWL hCL hWK hCK hnL hnK hdel hg hL hK hLI
        hdep hxfix hspan hxa hyfix hyx
    · have hcardK : Fintype.card (Option {i : Λ // i ≠ b}) < 9 := by
        rw [Fintype.card_congr (Equiv.optionSubtypeNe b)]
        exact hcard
      obtain ⟨n, e, C₀, k, hC, hchk, hdet⟩ := ggResII_negOne_of_not_noneg hWK hCK hcardK hnK
      exact Or.inl (ggResIILin_tv_K hp2 g h α hg hLI hdep hb2 hspan hyfix hyx e
        (fun i j => by rw [hK, hC]) hchk hdet)
  · obtain ⟨n, e, C₀, k, hC, hchk, -⟩ := ggResII_negOne_of_not_noneg hWL hCL hcard hnL
    exact Or.inl (ggResIILin_tv_L hp2 g h α hg hLI hdep hxfix hxa ha2 e
      (fun i j => by rw [hL, hC]) hchk)

end CFSG.StandardType
