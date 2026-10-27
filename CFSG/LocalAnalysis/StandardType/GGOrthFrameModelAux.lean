module

public import CFSG.LocalAnalysis.StandardType.GGTBJCoordRefl
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth

theorem ggOFM_permAut_swap_eq_self_of_eq {p r : ℕ} {i j : Fin r}
    {f : Fin r → Multiplicative (ZMod p)} (h : f i = f j) :
    SpCoord.permAut (Equiv.swap i j) f = f := by
  funext x
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases hxi : x = i
  · rw [hxi, Equiv.swap_apply_left]
    exact h.symm
  · by_cases hxj : x = j
    · rw [hxj, Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]

theorem ggOFM_eq_of_permAut_swap_eq_self {p r : ℕ} {i j : Fin r}
    {f : Fin r → Multiplicative (ZMod p)}
    (h : SpCoord.permAut (Equiv.swap i j) f = f) : f i = f j := by
  have h1 := congrFun h i
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h1
  exact h1.symm

theorem ggOFM_mem_reflFixedCoord_iff {p r : ℕ} {i j : Fin r}
    (f : Fin r → Multiplicative (ZMod p)) :
    f ∈ reflFixedCoord p r i j ↔ f i = f j := by
  rw [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply, div_eq_one]

theorem ggOFM_mem_reflFixedCoordPos_iff {p r : ℕ} {i j : Fin r}
    (f : Fin r → Multiplicative (ZMod p)) :
    f ∈ reflFixedCoordPos p r i j ↔ f i * f j = 1 := by
  rw [reflFixedCoordPos, MonoidHom.mem_ker, MonoidHom.mul_apply, Pi.evalMonoidHom_apply,
    Pi.evalMonoidHom_apply]

theorem ggOFM_dinv_permAut_eq_invSwapAut {p r : ℕ} {i j : Fin r}
    (f : Fin r → Multiplicative (ZMod p)) :
    NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f) =
      ggTBJSpC_invSwapAut p r i j f := by
  rw [ggTBJSpC_invSwapAut, MulAut.mul_apply, MulAut.mul_apply]
  rfl

theorem ggOFM_dinv_permAut_eq_self_iff {p r : ℕ} {i j : Fin r} (hij : i ≠ j)
    (f : Fin r → Multiplicative (ZMod p)) :
    NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f) = f ↔ f i * f j = 1 := by
  rw [ggOFM_dinv_permAut_eq_invSwapAut,
    ggTBJSpC_invSwapAut_eq_self_iff hij, eq_inv_iff_mul_eq_one]

theorem ggOFM_dinv_permAut_dinv_permAut {p r : ℕ} {i j : Fin r} (hij : i ≠ j)
    (f : Fin r → Multiplicative (ZMod p)) :
    NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j)
      (NbrOrth.dinv i j (SpCoord.permAut (Equiv.swap i j) f))) = f := by
  rw [ggOFM_dinv_permAut_eq_invSwapAut, ggOFM_dinv_permAut_eq_invSwapAut]
  rw [← MulAut.mul_apply, ← pow_two, ggTBJSpC_invSwapAut_sq hij]
  rfl

theorem ggOFM_surjective_div {p r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    Function.Surjective (Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i /
      Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j) := by
  intro x
  refine ⟨Pi.mulSingle i x, ?_⟩
  rw [MonoidHom.div_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (Ne.symm hij), div_one]

theorem ggOFM_surjective_mul {p r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    Function.Surjective (Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i *
      Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j) := by
  intro x
  refine ⟨Pi.mulSingle i x, ?_⟩
  rw [MonoidHom.mul_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (Ne.symm hij), mul_one]

theorem ggOFM_card_ker_mul_card {p r : ℕ}
    {φ : (Fin r → Multiplicative (ZMod p)) →* Multiplicative (ZMod p)}
    (hφ : Function.Surjective φ) :
    Nat.card ↥(MonoidHom.ker φ) * p = p ^ r := by
  have hcardG : Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := ggTBJSpC_card_coord p r
  have hrange : Nat.card ↥φ.range = p := by
    rw [MonoidHom.range_eq_top.mpr hφ]
    calc
      Nat.card ↥(⊤ : Subgroup (Multiplicative (ZMod p))) =
          Nat.card (Multiplicative (ZMod p)) :=
        Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ZMod p))).toEquiv
      _ = p := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hiso : Nat.card ((Fin r → Multiplicative (ZMod p)) ⧸ MonoidHom.ker φ) =
      Nat.card ↥φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hfirst := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ)
  rw [hiso, hrange, hcardG] at hfirst
  rw [mul_comm p (Nat.card ↥(MonoidHom.ker φ))] at hfirst
  exact hfirst.symm

theorem ggOFM_card_reflFixedCoord {p r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    Nat.card ↥(reflFixedCoord p r i j) * p = p ^ r :=
  ggOFM_card_ker_mul_card (p := p) (r := r)
    (φ := Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i /
      Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j)
    (ggOFM_surjective_div hij)

theorem ggOFM_card_reflFixedCoordPos {p r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    Nat.card ↥(reflFixedCoordPos p r i j) * p = p ^ r :=
  ggOFM_card_ker_mul_card (p := p) (r := r)
    (φ := Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i *
      Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j)
    (ggOFM_surjective_mul hij)

theorem ggOFM_card_reflFixed {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Nat.card ↥(Δ.reflFixed i j) = Nat.card ↥(reflFixedCoord p r i j) := by
  show Nat.card ↥((reflFixedCoord p r i j).map Δ.τ) = Nat.card ↥(reflFixedCoord p r i j)
  exact (Nat.card_congr (Subgroup.equivMapOfInjective (reflFixedCoord p r i j) Δ.τ
    Δ.τ_inj).toEquiv).symm

theorem ggOFM_card_reflFixedPos {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (Δ : TBJOmData Q p A r) (i j : Fin r) :
    Nat.card ↥(Δ.reflFixedPos i j) = Nat.card ↥(reflFixedCoordPos p r i j) := by
  show Nat.card ↥((reflFixedCoordPos p r i j).map Δ.τ) = Nat.card ↥(reflFixedCoordPos p r i j)
  exact (Nat.card_congr (Subgroup.equivMapOfInjective (reflFixedCoordPos p r i j) Δ.τ
    Δ.τ_inj).toEquiv).symm

end OrthTorus

end CFSG.StandardType

end
