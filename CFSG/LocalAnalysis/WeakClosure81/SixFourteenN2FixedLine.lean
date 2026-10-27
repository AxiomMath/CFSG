module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem card_fixedPoints_eq_two_or_five {a : Type*} [Fintype a] [DecidableEq a]
    (ha : Fintype.card a = 5) (pi : Equiv.Perm a) (hpi : pi ^ 3 = 1) :
    Fintype.card (Function.fixedPoints pi) = 2 ∨
      Fintype.card (Function.fixedPoints pi) = 5 := by
  let f : Function.End a := ⇑pi
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    have h := congrArg (fun e : Equiv.Perm a => (e : a → a)) hpi
    rw [Equiv.Perm.coe_pow] at h
    change (⇑pi : a → a) ^[3] = id
    exact h
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := f) hf
  have hle : Fintype.card (Function.fixedPoints pi) ≤ 5 := by
    have h := Fintype.card_subtype_le (p := fun x : a => x ∈ Function.fixedPoints pi)
    rw [ha] at h
    exact h
  have hmod' : Fintype.card (Function.fixedPoints pi) ≡ 5 [MOD 3] := by
    rw [ha] at hmod
    exact hmod.symm
  interval_cases h : Fintype.card (Function.fixedPoints pi) <;>
    simp_all [Nat.ModEq]

theorem card_fixed_lineMap_eq_two_or_five {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite V] (hcard : Nat.card (LineOf (K := K) (V := V)) = 5)
    (g : V ≃ₗ[K] V) (hg : g ^ 3 = 1) :
    Nat.card {L : LineOf (K := K) (V := V) // lineMap g L = L} = 2 ∨
      Nat.card {L : LineOf (K := K) (V := V) // lineMap g L = L} = 5 := by
  classical
  haveI : Finite (LineOf (K := K) (V := V)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype (LineOf (K := K) (V := V)) := Fintype.ofFinite _
  have hcard5 : Fintype.card (LineOf (K := K) (V := V)) = 5 := by
    rw [Fintype.card_eq_nat_card, hcard]
  let pi : Equiv.Perm (LineOf (K := K) (V := V)) := MulAction.toPerm g
  have hpi : pi ^ 3 = 1 := by
    have h3 : MulAction.toPermHom (V ≃ₗ[K] V) (LineOf (K := K) (V := V)) (g ^ 3) = 1 := by
      rw [hg, map_one]
    have hp := map_pow (MulAction.toPermHom (V ≃ₗ[K] V) (LineOf (K := K) (V := V))) g 3
    rw [h3] at hp
    simpa [pi] using hp.symm
  have hres := card_fixedPoints_eq_two_or_five hcard5 pi hpi
  have hfixeq : Nat.card {L : LineOf (K := K) (V := V) // lineMap g L = L} =
      Fintype.card (Function.fixedPoints pi) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro L
    change lineMap g L = L ↔ lineMap g L = L
    rfl
  rw [hfixeq]
  exact hres

theorem x_line_fixed_eq_two_or_five {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16) :
    letI := galoisModule hw2 x hx3 hfix
    Nat.card {L : LineOf (K := GaloisField 2 2) (V := Additive W) //
      lineMap (hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)) L = L} = 2 ∨
    Nat.card {L : LineOf (K := GaloisField 2 2) (V := Additive W) //
      lineMap (hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)) L = L} = 5 := by
  letI := galoisModule hw2 x hx3 hfix
  let g := hGaloisLinearEquiv hw2 x hx3 hfix x (by rfl)
  have hc3 : ((x * x) * x) * x = x * ((x * x) * x) := by group
  have hc4 : x ^ 3 * x = x * x ^ 3 := by group
  have hc5 : (1 : MulAut W) * x = x * 1 := by group
  have hGE_congr : ∀ {h1 h2 : MulAut W} (he : h1 = h2)
      (hc1 : h1 * x = x * h1) (hc2 : h2 * x = x * h2),
      hGaloisLinearEquiv hw2 x hx3 hfix h1 hc1 =
        hGaloisLinearEquiv hw2 x hx3 hfix h2 hc2 := by
    intro h1 h2 he hc1 hc2
    subst h2
    exact congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix h1 hc)
      (Subsingleton.elim hc1 hc2)
  have hsq : hGaloisLinearEquiv hw2 x hx3 hfix (x * x) (mul_assoc x x x) = g.trans g := by
    rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix x x rfl rfl (mul_assoc x x x)]
  have hcube : hGaloisLinearEquiv hw2 x hx3 hfix ((x * x) * x) hc3 =
      g.trans (hGaloisLinearEquiv hw2 x hx3 hfix (x * x) (mul_assoc x x x)) := by
    rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix (x * x) x (mul_assoc x x x) rfl hc3]
  have hg : g ^ 3 = 1 := by
    have hpow : g ^ 3 = g.trans (g.trans g) := by
      calc g ^ 3 = g ^ 2 * g := pow_succ g 2
        _ = (g * g) * g := by rw [pow_two]
        _ = g.trans (g * g) := LinearEquiv.mul_eq_trans (g * g) g
        _ = g.trans (g.trans g) := by rw [LinearEquiv.mul_eq_trans g g]
    calc g ^ 3 = g.trans (g.trans g) := hpow
      _ = g.trans (hGaloisLinearEquiv hw2 x hx3 hfix (x * x) (mul_assoc x x x)) := by
            rw [← hsq]
      _ = hGaloisLinearEquiv hw2 x hx3 hfix ((x * x) * x) hc3 := hcube.symm
      _ = hGaloisLinearEquiv hw2 x hx3 hfix (x ^ 3) hc4 :=
            hGE_congr (by rw [pow_succ, pow_two]) hc3 hc4
      _ = hGaloisLinearEquiv hw2 x hx3 hfix 1 hc5 := hGE_congr hx3 hc4 hc5
      _ = 1 := hGaloisLinearEquiv_one hw2 x hx3 hfix hc5
  exact card_fixed_lineMap_eq_two_or_five (card_f4Line hw2 x hx3 hfix hW) g hg

end CFSG.LocalAnalysis.WeakClosure81
