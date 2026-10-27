module

public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private def s16c167_gl23Inv (g : GL (Fin 2) (ZMod 3)) : Prop := g * g = 1 ∧ g ≠ 1

private def s16c167_gl23Cen (g : GL (Fin 2) (ZMod 3)) : Prop :=
  ∀ x : GL (Fin 2) (ZMod 3), x * g = g * x

private instance : DecidablePred s16c167_gl23Inv := fun g => by
  unfold s16c167_gl23Inv; infer_instance

private instance : DecidablePred s16c167_gl23Cen := fun g => by
  unfold s16c167_gl23Cen; infer_instance

private theorem s16c167_gl23_central_eq_neg_one : ∀ g : GL (Fin 2) (ZMod 3),
    s16c167_gl23Inv g → s16c167_gl23Cen g → g = -1 := by
  decide +kernel

private theorem s16c167_gl23_card_centralizer : ∀ g : GL (Fin 2) (ZMod 3),
    s16c167_gl23Inv g → ¬ s16c167_gl23Cen g →
      Fintype.card {x : GL (Fin 2) (ZMod 3) // x * g = g * x} = 4 := by
  decide +kernel

theorem s16c167_card_le_four_of_aut_E9 {E : Type} [Group E] [Finite E]
    (hc : ∀ a b : E, a * b = b * a) (h2 : ∀ a : E, a ^ 2 = 1)
    (φ : E →* MulAut (Multiplicative (Fin 2 → ZMod 3))) (hφ : Function.Injective φ) :
    Nat.card E ≤ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : MulAut (Multiplicative (Fin 2 → ZMod 3)) ≃* GL (Fin 2) (ZMod 3) :=
    CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 3) 2
  let S : Subgroup (GL (Fin 2) (ZMod 3)) := φ.range.map e.toMonoidHom
  have hSexp : ∀ x ∈ S, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, rfl⟩ := hy
    rw [← map_pow, ← map_pow, h2 z, map_one, map_one]
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, rfl⟩ := hx'
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, rfl⟩ := hy'
    simp only [← map_mul]
    rw [hc z w]
  have hcardES : Nat.card E = Nat.card ↥S := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective φ.range e.toMonoidHom e.injective).toEquiv
  rw [hcardES]
  by_cases hcenter : ∀ x ∈ S, ∀ y : GL (Fin 2) (ZMod 3), y * x = x * y
  · have hsub : ∀ x ∈ S, x = 1 ∨ x = -1 := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (s16c167_gl23_central_eq_neg_one x
          ⟨by simpa [pow_two] using hSexp x hx, hx1⟩ fun y => hcenter x hx y)
    have hinj : Function.Injective
        (fun x : ↥S => if (x : GL (Fin 2) (ZMod 3)) = 1 then (0 : Fin 2) else 1) := by
      intro x y hxy
      change (if (x : GL (Fin 2) (ZMod 3)) = 1 then (0 : Fin 2) else 1) =
        (if (y : GL (Fin 2) (ZMod 3)) = 1 then (0 : Fin 2) else 1) at hxy
      by_cases hx1 : (x : GL (Fin 2) (ZMod 3)) = 1
      · rw [if_pos hx1] at hxy
        have hy1 : (y : GL (Fin 2) (ZMod 3)) = 1 := by
          by_contra hy1
          rw [if_neg hy1] at hxy
          exact absurd hxy (by decide)
        exact Subtype.ext (hx1.trans hy1.symm)
      · rw [if_neg hx1] at hxy
        have hy1 : (y : GL (Fin 2) (ZMod 3)) ≠ 1 := by
          intro hy1
          rw [if_pos hy1] at hxy
          exact absurd hxy (by decide)
        exact Subtype.ext (((hsub x x.2).resolve_left hx1).trans
          ((hsub y y.2).resolve_left hy1).symm)
    have hle2 := Nat.card_le_card_of_injective
      (fun x : ↥S => if (x : GL (Fin 2) (ZMod 3)) = 1 then (0 : Fin 2) else 1) hinj
    calc Nat.card ↥S ≤ Nat.card (Fin 2) := hle2
      _ = 2 := by simp
      _ ≤ 4 := by norm_num
  · rw [not_forall] at hcenter
    obtain ⟨x, hx⟩ := hcenter
    rw [not_imp] at hx
    obtain ⟨hxS, hx⟩ := hx
    rw [not_forall] at hx
    obtain ⟨y, hy⟩ := hx
    have hnotcen : ¬ s16c167_gl23Cen x := fun h => hy (h y)
    have hx1 : x ≠ 1 := by
      intro h
      exact hy (by rw [h, mul_one, one_mul])
    have hSle : S ≤ Subgroup.centralizer ({x} : Set (GL (Fin 2) (ZMod 3))) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hScomm z hz x hxS
    have hC4 : Nat.card ↥(Subgroup.centralizer ({x} : Set (GL (Fin 2) (ZMod 3)))) = 4 := by
      rw [Nat.card_congr
        (Equiv.subtypeEquivRight fun z => Subgroup.mem_centralizer_singleton_iff)]
      rw [Nat.card_eq_fintype_card]
      exact s16c167_gl23_card_centralizer x
        ⟨by simpa [pow_two] using hSexp x hxS, hx1⟩ hnotcen
    have hle := Nat.card_le_card_of_injective
      (fun z : ↥S =>
        (⟨z.1, hSle z.2⟩ : ↥(Subgroup.centralizer ({x} : Set (GL (Fin 2) (ZMod 3))))))
      (fun a b hab => Subtype.ext (by
        simpa using congrArg
          (fun w : ↥(Subgroup.centralizer ({x} : Set (GL (Fin 2) (ZMod 3)))) =>
            (w : GL (Fin 2) (ZMod 3))) hab))
    rw [hC4] at hle
    exact hle

theorem s16c167_exists_injective_aut_of_selfCentralizing {H : Type} [Group H] {F X : Subgroup H}
    [F.Normal] (hF : centralizer (F : Set H) ≤ F) (hXF : X ⊓ F = ⊥) :
    ∃ ψ : ↥X →* MulAut ↥F, Function.Injective ψ := by
  refine ⟨MulAut.conjNormal.comp X.subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : (x : H) ∈ centralizer (F : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h2 : (x : H) * f * (x : H)⁻¹ = f := by
      have h := congrArg (fun e : MulAut ↥F => ((e ⟨f, hf⟩ : ↥F) : H)) hx
      simpa only [MonoidHom.comp_apply, MulAut.one_apply, MulAut.conjNormal_apply,
        Subgroup.coe_subtype, Subtype.coe_mk] using h
    calc f * (x : H) = (x : H) * f * (x : H)⁻¹ * (x : H) := by rw [h2]
      _ = (x : H) * f := by group
  have hxF : (x : H) ∈ F := hF hxc
  have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
    have hxinf : (x : H) ∈ X ⊓ F := ⟨x.2, hxF⟩
    rw [hXF] at hxinf
    exact hxinf
  exact Subtype.ext (Subgroup.mem_bot.mp hxbot)

private theorem s16c167_padicValNat_two_le_two {n : ℕ} (hpos : 0 < n) (h4 : n ≤ 4) :
    padicValNat 2 n ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ padicValNat 2 n := not_le.1 h
  have hdvd : 2 ^ 3 ∣ n := (padicValNat_dvd_iff_le (p := 2) hpos.ne').mpr h3
  have h8 : 8 ≤ n := by simpa using Nat.le_of_dvd hpos hdvd
  omega

theorem s16c167_rk_le_two_of_case168_8 (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h8 : Case168_8 D V₀ V hV)
    {X : Subgroup (MulAut (Vtil V₀ V hV))} (hXM : X ≤ Mbar D.M V₀ V hV)
    (hX : IsElemAbelian2 X) : rk ↥X ≤ 2 := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let F₀ : Subgroup ↥Mb := genFittingFStar ↥Mb
  haveI : Finite ↥Mb := Subtype.finite
  haveI : F₀.Normal := CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal
  have hself : centralizer (F₀ : Set ↥Mb) ≤ F₀ :=
    CFSG.Open.Open.generalized_fitting_self_centralizing ↥Mb
  obtain ⟨e'⟩ := h8.1
  let e₀ : ↥F₀ ≃* Multiplicative (Fin 2 → ZMod 3) :=
    (Subgroup.equivMapOfInjective F₀ Mb.subtype Mb.subtype_injective).trans e'
  have h3pow : ∀ v : Multiplicative (Fin 2 → ZMod 3), v ^ 3 = 1 := by
    intro v
    induction v using Multiplicative.rec with
    | ofAdd w =>
      rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3) 3 w, ZMod.natCast_self 3,
        zero_smul, ofAdd_zero]
  have hcube : ∀ f : ↥F₀, f ^ 3 = 1 := by
    intro f
    apply e₀.injective
    rw [map_pow, map_one]
    exact h3pow (e₀ f)
  let X' : Subgroup ↥Mb := X.subgroupOf Mb
  have hXF : X' ⊓ F₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyX', hyF⟩ := hy
    have h2y : y ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hX.2 (y : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp hyX')
    have h3y : y ^ 3 = 1 := by
      have h := hcube ⟨y, hyF⟩
      simpa using h
    have hy1 : y = 1 := by
      calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3y, h2y, inv_one, mul_one]
    rw [Subgroup.mem_bot]
    exact hy1
  obtain ⟨ψ, hψ⟩ := s16c167_exists_injective_aut_of_selfCentralizing (H := ↥Mb)
    (F := F₀) (X := X') hself hXF
  let φ : ↥X' →* MulAut (Multiplicative (Fin 2 → ZMod 3)) :=
    (MulAut.congr e₀).toMonoidHom.comp ψ
  have hφ : Function.Injective φ := by
    intro a b hab
    exact hψ ((MulAut.congr e₀).injective hab)
  have hc' : ∀ a b : ↥X', a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact hX.1 (a : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp a.2)
      (b : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp b.2)
  have h2' : ∀ a : ↥X', a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    exact hX.2 (a : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp a.2)
  have hcard' : Nat.card ↥X' ≤ 4 := s16c167_card_le_four_of_aut_E9 hc' h2' φ hφ
  have hcardX : Nat.card ↥X ≤ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hcard'
    exact hcard'
  rw [rk]
  exact s16c167_padicValNat_two_le_two (Nat.card_pos) hcardX

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
