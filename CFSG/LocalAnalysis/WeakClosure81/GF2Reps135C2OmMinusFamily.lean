module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamGlue
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQNatMinus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamOuter
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQModelMinus
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterInvolution
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfMFam_natural_of_equiv {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 4 ≤ n) (hF : Nat.card F = 2 ^ 1) {b c : F}
    (hquad : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (e : spinGroup (quadMinus n F b c) ≃* ↥L)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadMinus n F b c)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (β : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F))
    (hβ : ∀ (g : spinGroup (quadMinus n F b c)) (v : V),
      β (ρ g v) = Matrix.mulVec (spinMatrix (quadMinus n F b c) g :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
        (β v)) :
    IsOmegaMinus ↥L (2 * n) 1 ∧ NatOmegaMinus L ⊤ ⊥ (2 * n) 1 :=
  w135c2_omMinus_natural_of_equiv hn hF hquad e hθ β hβ

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfMFam_center_eq_bot {F : Type} [Field F] {n : ℕ} {b c : F}
    {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (e : spinGroup (quadMinus n F b c) ≃* ↥L) (hZ : Subgroup.center ↥L = ⊥) :
    Subgroup.center (spinGroup (quadMinus n F b c)) = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (spinGroup (quadMinus n F b c)))
    e.injective).mp (by
    rw [Subgroup.map_center_eq e, hZ])

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis in
private theorem w135c2_omfMFam_inner {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn5 : 5 ≤ n) (hF : Nat.card F = 2 ^ 1) {b c : F}
    (hquad : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (e : spinGroup (quadMinus n F b c) ≃* ↥L)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadMinus n F b c)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (hρ : IsSimpleRep ρ) {t : MulAut W} (htL : t ∈ L) (ht2 : orderOf t = 2) :
    (IsOmegaMinus ↥L (2 * n) 1 ∧ NatOmegaMinus L ⊤ ⊥ (2 * n) 1) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  let y : spinGroup (quadMinus n F b c) := e.symm ⟨t, htL⟩
  have hey : e y = ⟨t, htL⟩ := e.apply_symm_apply ⟨t, htL⟩
  have hge : ((e y : ↥L) : MulAut W) = t := by rw [hey]
  have ht2' : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hy2 : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one, hey]
    exact Subtype.ext ht2'
  have hρy : ρ y ≠ 1 := rho_ne_one_of_conj e hθ hge ht2
  rcases omMinus_two_natural_or_four_le_family (K := F) (b := b) (c := c)
      (hK := by rw [hF]; norm_num) (by omega) hquad hρ hy2 hρy with ⟨β, hβ⟩ | hrank
  · refine Or.inl ?_
    refine w135c2_omfMFam_natural_of_equiv (by omega) hF hquad e hθ β ?_
    intro g v
    rw [hβ g v]
    rfl
  · refine Or.inr (w135c2_four_le_mQuot_of_finrank θ (t := t) (ρ y) ?_ hrank)
    intro w
    rw [← hge]
    exact hθ y w

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfMFam_outer_T {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn5 : 5 ≤ n) {b c : F}
    (hquad : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (e : spinGroup (quadMinus n F b c) ≃* ↥L)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadMinus n F b c)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {t : MulAut W} (ht2' : t * t = 1)
    {α : MulAut (spinGroup (quadMinus n F b c))}
    (hαe : ∀ s : spinGroup (quadMinus n F b c),
      ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {h : spinGroup (quadMinus n F b c)}
    (houter : ∀ g, α g = h * omMinusReflAut n (by omega) hquad g * h⁻¹) :
    ∃ T : V ≃ₗ[ZMod 2] V,
      (∀ w : W, θ (t w) = Multiplicative.ofAdd (T (Multiplicative.toAdd (θ w)))) ∧
      (∀ v : V, T (T v) = v) ∧
      ∀ (g : spinGroup (quadMinus n F b c)) (v : V),
        T (ρ g v) = ρ (h * omMinusReflAut n (by omega) hquad g * h⁻¹) (T v) := by
  obtain ⟨T, hTθ, hTρ⟩ := w135c2_exists_linearEquiv_of_conj e hθ hαe
  have htt : ∀ w : W, t (t w) = w := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) ht2'
    simpa [MulAut.mul_apply] using h
  have hTw : ∀ w : W, T (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ (t w)) := by
    intro w
    simpa using (congrArg Multiplicative.toAdd (hTθ w)).symm
  have hT2 : ∀ v : V, T (T v) = v := by
    intro v
    obtain ⟨w, rfl⟩ : ∃ w : W, v = Multiplicative.toAdd (θ w) :=
      ⟨θ.symm (Multiplicative.ofAdd v), by simp⟩
    rw [hTw w, hTw (t w), htt w]
  have hT : ∀ (g : spinGroup (quadMinus n F b c)) (v : V),
      T (ρ g v) = ρ (h * omMinusReflAut n (by omega) hquad g * h⁻¹) (T v) := by
    intro g v
    rw [hTρ g v, houter g]
  exact ⟨T, hTθ, hT2, hT⟩

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis in
private theorem w135c2_omfMFam_outer {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn5 : 5 ≤ n) (hF : Nat.card F = 2 ^ 1) {b c : F}
    (hquad : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (e : spinGroup (quadMinus n F b c) ≃* ↥L)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadMinus n F b c)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    (hρ : IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1)
    {t : MulAut W} (ht2' : t * t = 1)
    (hZG : Subgroup.center (spinGroup (quadMinus n F b c)) = ⊥)
    {α : MulAut (spinGroup (quadMinus n F b c))} (hα2 : α * α = 1)
    (hαe : ∀ s : spinGroup (quadMinus n F b c),
      ((e (α s) : ↥L) : MulAut W) = t * (e s : MulAut W) * t⁻¹)
    {h : spinGroup (quadMinus n F b c)}
    (houter : ∀ g, α g = h * omMinusReflAut n (by omega) hquad g * h⁻¹) :
    (IsOmegaMinus ↥L (2 * n) 1 ∧ NatOmegaMinus L ⊤ ⊥ (2 * n) 1) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  obtain ⟨T, hTθ, hT2, hT⟩ :=
    w135c2_omfMFam_outer_T hn5 hquad e hθ ht2' hαe houter
  have hh : h * omMinusReflAut n (by omega) hquad h = 1 :=
    w135c2_mul_apply_eq_one_of_mul_self hZG hα2
      (omMinusReflAut_apply_apply (by omega) hquad) houter
  rcases omMinus_two_outer_natural_or_four_le_family (K := F) (b := b) (c := c)
      (hK := by rw [hF]; norm_num) (by omega) hquad hρ hρ1 T hT2 hh hT with
    ⟨β, hβ⟩ | hrank
  · refine Or.inl ?_
    refine w135c2_omfMFam_natural_of_equiv (by omega) hF hquad e hθ β ?_
    intro g v
    rw [hβ g v]
    rfl
  · exact Or.inr (w135c2_four_le_mQuot_of_finrank θ (t := t) T.toLinearMap hTθ hrank)

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfMFam_rho_ne_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} {b c : F} {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) {t : MulAut W} (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (e : spinGroup (quadMinus n F b c) ≃* ↥L)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus n F b c)) V}
    {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : spinGroup (quadMinus n F b c)) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w)))) :
    ∃ g, ρ g ≠ 1 := by
  obtain ⟨y₀, hy₀L, hy₀1, hy₀sq, -⟩ := w135c2_psu_outer_involution hW hctx htY ht2
  have hy₀2 : orderOf y₀ = 2 := orderOf_eq_prime (by rwa [pow_two]) hy₀1
  refine ⟨e.symm ⟨y₀, hy₀L⟩, ?_⟩
  have hge : ((e (e.symm ⟨y₀, hy₀L⟩) : ↥L) : MulAut W) = y₀ := by simp
  exact rho_ne_one_of_conj e hθ hge hy₀2

open CFSG.LieType.Universal.Spin in
private theorem w135c2_omfMFam_two_natural_or_four_le
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2) {n : ℕ} (hn : 5 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 1) :
    (IsOmegaMinus ↥L (2 * n) 1 ∧ NatOmegaMinus L ⊤ ⊥ (2 * n) 1) ∨
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  obtain ⟨F, instF, instFin, instChar, b, c, hF, hquad, hZ, ⟨e⟩⟩ :=
    w135c2_omMinus_model hctx (by omega) hlie
  let instField : Field F := instF
  let instFiniteF : Finite F := instFin
  let instCharP : CharP F 2 := instChar
  obtain ⟨V, _, _, hVfin, ρ, θ, hρ, hθ⟩ := cu_binModel hW (hctx.2.2.2.2.2) e
  let instFiniteV : Finite V := hVfin
  have hZspin : Subgroup.center (spinGroup (quadMinus n F b c)) = ⊥ :=
    w135c2_omfMFam_center_eq_bot e hZ
  have hρ1 : ∃ g, ρ g ≠ 1 := w135c2_omfMFam_rho_ne_one hW hctx htY ht2 e hθ
  have ht2' : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  obtain ⟨α, hαe⟩ := w135c2_exists_mulAut_of_mem hctx htY e
  have hα2 : α * α = 1 := w135c2_mulAut_mul_self_of_conj e ht2' hαe
  have hK : Nat.card F = 2 := by rw [hF]; norm_num
  obtain ⟨h, hinner | houter⟩ :=
    omMinus_two_aut_inner_or_refl (K := F) (b := b) (c := c) hK (by omega) hquad α
  · have htL : t ∈ L := by
      refine w135c2_mem_of_conj_eq_conj hctx htY (e h).2 ?_ hZ
      intro l hl
      let s : spinGroup (quadMinus n F b c) := e.symm ⟨l, hl⟩
      have hes : ((e s : ↥L) : MulAut W) = l := by simp [s]
      have h1 : e (α s) = e h * e s * (e h)⁻¹ := by
        rw [hinner s, map_mul, map_mul, map_inv]
      calc t * l * t⁻¹
          = t * ((e s : ↥L) : MulAut W) * t⁻¹ := by rw [hes]
        _ = ((e (α s) : ↥L) : MulAut W) := (hαe s).symm
        _ = ((e h * e s * (e h)⁻¹ : ↥L) : MulAut W) := by rw [h1]
        _ = ((e h : ↥L) : MulAut W) * l * ((e h : ↥L) : MulAut W)⁻¹ := by simp [hes]
    exact w135c2_omfMFam_inner (by omega) hF hquad e hθ hρ htL ht2
  · exact w135c2_omfMFam_outer (by omega) hF hquad e hθ hρ hρ1 ht2' hZspin hα2 hαe houter

theorem w135c2_omMinus_two_of_five_le
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n : ℕ} (hn : 5 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 1) : W4Lem13_5Concl W Y L t := by
  rcases w135c2_omfMFam_two_natural_or_four_le hW hctx htY ht2 hn hlie with ⟨hIs, hNat⟩ | h4
  · exact w135c2_natural hctx htY ht2 hW
      (Or.inl ⟨2 * n, 1, Or.inr (Or.inr (Or.inr ⟨hIs, hNat⟩))⟩)
  · exact absurd h4 (by omega)

theorem w135c2_omMinus_two
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 1) : W4Lem13_5Concl W Y L t := by
  obtain rfl | hn := (hlie.admissible.2.2 : 4 ≤ n).eq_or_lt
  · exact w135c2_omMinus8_two hW hctx htY ht2 hm hlie
  · exact w135c2_omMinus_two_of_five_le hW hctx htY ht2 hm hn hlie

end CFSG.LocalAnalysis.WeakClosure81
