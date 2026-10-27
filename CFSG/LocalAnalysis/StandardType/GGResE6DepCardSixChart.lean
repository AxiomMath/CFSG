module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixGroup
public import CFSG.LocalAnalysis.StandardType.GGResE6Coordinates
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private lemma cs6_dot_single (c : CS6E) (j : Fin 6) :
    ggDepAdot c (Pi.single j (1 : ZMod 3)) = c j := by
  rw [ggDepAdot]
  have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun i : Fin 6 => c i * (Pi.single j (1 : ZMod 3) : CS6E) i) j
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)
  simpa [Pi.single_eq_same] using h

private lemma cs6Root_ne_zero (i : Fin 6) : cs6Root i ≠ 0 := by
  fin_cases i <;> decide

private lemma cs6Alpha_castSucc (i : Fin 6) (j : Fin 5) :
    cs6Alpha i j.castSucc = (CartanMatrix.E 6 i j.succ : ZMod 3) := by
  simp only [cs6Alpha, Fin.val_castSucc]
  rw [dif_pos j.isLt]
  exact congrArg (fun k : Fin 6 => (CartanMatrix.E 6 i k : ZMod 3))
    (Fin.ext (by simp [Fin.succ]))

@[expose] noncomputable def cs6Form (θ : V ≃ₗ[ZMod 3] CS6E) (a : Module.Dual (ZMod 3) V) : CS6E :=
  fun j => a (θ.symm (Pi.single j 1))

theorem ggDepAdot_cs6Form (θ : V ≃ₗ[ZMod 3] CS6E) (a : Module.Dual (ZMod 3) V) (w : CS6E) :
    ggDepAdot (cs6Form θ a) w = a (θ.symm w) := by
  have hw : w = ∑ j : Fin 6, w j • Pi.single j (1 : ZMod 3) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h := Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin 6 => w j * (Pi.single j (1 : ZMod 3) : CS6E) i) i
        (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero])
        (fun hi => absurd (Finset.mem_univ i) hi)
    simpa [Pi.single_eq_same] using h.symm
  conv_rhs => rw [hw]
  rw [map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [ggDepAdot]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cs6Form]
  ring

theorem cs6Form_eq (θ : V ≃ₗ[ZMod 3] CS6E) (a : Module.Dual (ZMod 3) V) (c : CS6E)
    (h : ∀ v, ggDepAdot c (θ v) = a v) : cs6Form θ a = c := by
  funext j
  have h1 := h (θ.symm (Pi.single j 1))
  rw [LinearEquiv.apply_symm_apply] at h1
  simp only [cs6Form]
  rw [← h1]
  exact cs6_dot_single c j

theorem cs6Img_reflection {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod 3] CS6E) (φ : MulAut ↥Bs) (hv : V) (a : Module.Dual (ZMod 3) V)
    (hlin : ∀ w, ggLin (p := 3) ι φ w = w - a w • hv) :
    cs6Img ι θ φ = ggDepARefl (θ hv) (cs6Form θ a) := by
  apply LinearMap.ext
  intro w
  have hlin' : ggLin (p := 3) ι φ ((θ.symm : CS6E →ₗ[ZMod 3] V) w) =
      (θ.symm : CS6E →ₗ[ZMod 3] V) w - a ((θ.symm : CS6E →ₗ[ZMod 3] V) w) • hv :=
    hlin _
  change (θ : V →ₗ[ZMod 3] CS6E)
      (ggLin (p := 3) ι φ ((θ.symm : CS6E →ₗ[ZMod 3] V) w)) =
    ggDepARefl (θ hv) (cs6Form θ a) w
  rw [hlin', map_sub, map_smul, l05nPT_refl_apply, ggDepAdot_cs6Form]
  rw [show (θ : V →ₗ[ZMod 3] CS6E) ((θ.symm : CS6E →ₗ[ZMod 3] V) w) = w from
    LinearEquiv.apply_symm_apply θ w]
  rfl

theorem cs6_chart_linear [Finite V] (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x' : V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hdep : ¬ LinearIndependent (ZMod 3) h) (hx : x' ≠ 0) (hxker : ∀ i, α i x' = 0)
    (hcard : Nat.card V = 3 ^ 6) :
    ∃ θ : V ≃ₗ[ZMod 3] CS6E, θ x' = cs6X ∧ (∀ i, θ (h i) = cs6Root i) ∧
      ∀ i v, ggDepAdot (cs6Alpha i) (θ v) = α i v := by
  classical
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hpow.symm.trans hcard)
  have hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x'} := by
    have hker := eq_span_singleton_of_cartan_E6 hdim hpair hx hxker
    intro v
    rw [← hker, LinearMap.mem_ker]
    constructor
    · intro hv; funext i; exact hv i
    · intro hv i; have := congrFun hv i; simpa using this
  obtain ⟨θ, hθx, hθh, hθrefl⟩ :=
    E6QTwo.exists_e6_dependent_six_coordinates h α x' hdep hx hdim hfix hpair
  have hθroot : ∀ i, θ (h i) = cs6Root i := fun i => by simpa [cs6Root] using hθh i
  refine ⟨θ, ?_, hθroot, ?_⟩
  · simpa [cs6X] using hθx
  · intro i v
    have h1 := hθrefl i v
    rw [map_sub, map_smul, hθh i] at h1
    have h2 : α i v • cs6Root i =
        (∑ j : Fin 5, (θ v) j.castSucc * (CartanMatrix.E 6 i j.succ : ZMod 3)) •
          cs6Root i := sub_right_inj.mp h1
    have hEq : (α i v - ∑ j : Fin 5, (θ v) j.castSucc *
        (CartanMatrix.E 6 i j.succ : ZMod 3)) • cs6Root i = 0 := by
      rw [sub_smul, h2, sub_self]
    have hscal : α i v - ∑ j : Fin 5, (θ v) j.castSucc *
        (CartanMatrix.E 6 i j.succ : ZMod 3) = 0 := by
      rcases smul_eq_zero.mp hEq with h | h
      · exact h
      · exact absurd h (cs6Root_ne_zero i)
    have hαv : α i v = ∑ j : Fin 5, (θ v) j.castSucc *
        (CartanMatrix.E 6 i j.succ : ZMod 3) := sub_eq_zero.mp hscal
    rw [hαv]
    calc ggDepAdot (cs6Alpha i) (θ v)
        = ∑ j : Fin 6, cs6Alpha i j * θ v j := rfl
      _ = (∑ j : Fin 5, cs6Alpha i j.castSucc * θ v j.castSucc)
            + cs6Alpha i (Fin.last 5) * θ v (Fin.last 5) := Fin.sum_univ_castSucc _
      _ = ∑ j : Fin 5, (CartanMatrix.E 6 i j.succ : ZMod 3) * θ v j.castSucc := by
            rw [show cs6Alpha i (Fin.last 5) = 0 by simp [cs6Alpha], zero_mul, add_zero]
            exact Finset.sum_congr rfl (fun j _ => by rw [cs6Alpha_castSucc])
      _ = ∑ j : Fin 5, θ v j.castSucc * (CartanMatrix.E 6 i j.succ : ZMod 3) :=
            Finset.sum_congr rfl (fun j _ => by rw [mul_comm])

end

end CFSG.StandardType
