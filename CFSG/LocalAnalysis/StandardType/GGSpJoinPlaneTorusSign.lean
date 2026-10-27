module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
private theorem conj_spPlaneTorus_single_mulSingle {F : Type} [Field F] {p n : ℕ}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (k i : Fin n) (a : Multiplicative (ZMod p)) :
    lam k sl2W * spPlaneTorus n ζ (Pi.mulSingle i a) *
        (lam k sl2W)⁻¹ =
      spPlaneTorus n ζ
        (Function.update (Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) k
          ((Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) k)⁻¹) := by
  classical
  rw [spPlaneTorus_mulSingle]
  by_cases hik : i = k
  · subst i
    have hU : Function.update (Pi.mulSingle k a : Fin n → Multiplicative (ZMod p)) k
        ((Pi.mulSingle k a : Fin n → Multiplicative (ZMod p)) k)⁻¹ = Pi.mulSingle k a⁻¹ := by
      funext j
      by_cases hj : j = k
      · rw [hj, Function.update_self, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · simp only [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]
    rw [hU, spPlaneTorus_mulSingle, ← hζw a, map_mul, map_mul, map_inv]
  · have hU : Function.update (Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) k
        ((Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) k)⁻¹ = Pi.mulSingle i a := by
      funext j
      by_cases hj : j = k
      · rw [hj, Function.update_self, Pi.mulSingle_eq_of_ne (Ne.symm hik)]
        simp
      · simp only [Function.update_of_ne hj]
    rw [hU, spPlaneTorus_mulSingle]
    have hcomm : Commute (lam i (ζ a)) (lam k sl2W) :=
      commute_lam_lam hik (ζ a) sl2W
    rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
private theorem conj_spPlaneTorus_single {F : Type} [Field F] {p n : ℕ}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (k : Fin n) (t : Fin n → Multiplicative (ZMod p)) :
    lam k sl2W * spPlaneTorus n ζ t * (lam k sl2W)⁻¹ =
      spPlaneTorus n ζ (Function.update t k (t k)⁻¹) := by
  classical
  let U : (Fin n → Multiplicative (ZMod p)) →* (Fin n → Multiplicative (ZMod p)) :=
    { toFun := fun t => Function.update t k (t k)⁻¹
      map_one' := by
        funext j
        by_cases hj : j = k
        · rw [hj, Function.update_self]
          simp
        · rw [Function.update_of_ne hj]
      map_mul' := by
        intro s t
        funext j
        by_cases hj : j = k
        · rw [hj]
          simp only [Pi.mul_apply, Function.update_self, mul_inv_rev]
          exact mul_comm _ _
        · simp only [Pi.mul_apply, Function.update_of_ne hj] }
  have hLR : (MulAut.conj (lam k sl2W)).toMonoidHom.comp
        (spPlaneTorus n ζ) =
      (spPlaneTorus n ζ).comp U := by
    refine MonoidHom.pi_ext fun i a => ?_
    change lam k sl2W * spPlaneTorus n ζ (Pi.mulSingle i a) *
        (lam k sl2W)⁻¹ =
      spPlaneTorus n ζ
        (Function.update (Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) k
          ((Pi.mulSingle i a : Fin n → Multiplicative (ZMod p)) k)⁻¹)
    exact conj_spPlaneTorus_single_mulSingle hζw k i a
  exact DFunLike.congr_fun hLR t

theorem exists_conj_sign_of_update {S : Type*} [Group S] {p n : ℕ}
    {D : (Fin n → Multiplicative (ZMod p)) →* S}
    (hsgn : ∀ k : Fin n, ∃ w : S, ∀ t : Fin n → Multiplicative (ZMod p),
      w * D t * w⁻¹ = D (Function.update t k (t k)⁻¹))
    (ε : Fin n → ZMod p) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    ∃ W : S, ∀ t : Fin n → Multiplicative (ZMod p),
      W⁻¹ * D t * W = D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (t k))) := by
  classical
  have hfin : ∀ s : Finset (Fin n), ∃ V : S, ∀ t : Fin n → Multiplicative (ZMod p),
      V * D t * V⁻¹ =
        D (fun k => if k ∈ s then (t k)⁻¹ else t k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨1, fun t => ?_⟩
        simp
    | insert k s hk ih =>
        obtain ⟨V, hV⟩ := ih
        obtain ⟨w, hw⟩ := hsgn k
        refine ⟨V * w, fun t => ?_⟩
        calc
          (V * w) * D t * (V * w)⁻¹
              = V * (w * D t * w⁻¹) * V⁻¹ := by group
          _ = V * D (Function.update t k (t k)⁻¹) * V⁻¹ := by rw [hw t]
          _ = D (fun j => if j ∈ insert k s then (t j)⁻¹ else t j) := by
                rw [hV (Function.update t k (t k)⁻¹)]
                congr 1
                funext j
                by_cases hjk : j = k
                · subst hjk
                  simp [hk]
                · simp [hjk]
  let s : Finset (Fin n) := Finset.univ.filter (fun k => ε k = -1)
  have hs : ∀ k, k ∈ s ↔ ε k = -1 := by
    intro k
    simp [s]
  obtain ⟨V, hV⟩ := hfin s
  refine ⟨V⁻¹, fun t => ?_⟩
  rw [inv_inv, hV t]
  congr 1
  funext k
  by_cases hk : k ∈ s
  · rw [if_pos hk, (hs k).1 hk, neg_one_mul, ofAdd_neg, ofAdd_toAdd]
  · rw [if_neg hk]
    have hεk : ε k = 1 := by
      rcases hε k with h | h
      · exact h
      · exact absurd ((hs k).2 h) hk
    rw [hεk, one_mul, ofAdd_toAdd]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem spPlaneZetaSplit_conj_sl2W {F : Type} [Field F] {p : ℕ} {ω : Fˣ} (hω : ω ^ p = 1)
    (a : Multiplicative (ZMod p)) :
    sl2W * spPlaneZetaSplit ω hω a * sl2W⁻¹ = spPlaneZetaSplit ω hω a⁻¹ := by
  have hinv : CFSG.StandardType.TableBSymp.zmodPowHom hω a⁻¹ =
      (CFSG.StandardType.TableBSymp.zmodPowHom hω a)⁻¹ := map_inv _ _
  show sl2W * sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω a) * sl2W⁻¹ =
    sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω a⁻¹)
  rw [hinv, mul_inv_eq_iff_eq_mul]
  exact sl2W_mul_sl2Diag _

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem exists_conj_spPlaneTorus_sign {F : Type} [Field F] {p n : ℕ}
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (ε : Fin n → ZMod p) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    ∃ W : StatedSp n F, ∀ t : Fin n → Multiplicative (ZMod p),
      W⁻¹ * spPlaneTorus n ζ t * W =
        spPlaneTorus n ζ
          (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (t k))) := by
  exact exists_conj_sign_of_update (D := spPlaneTorus n ζ)
    (fun k => ⟨lam k sl2W, fun t => conj_spPlaneTorus_single hζw k t⟩) ε hε

end CFSG.StandardType.SpJoin

end
