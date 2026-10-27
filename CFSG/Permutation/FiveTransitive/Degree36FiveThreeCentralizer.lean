module

public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer
public import CFSG.Permutation.FiveTransitive.FreeComplementCard
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveThreeCentralizer

open MulAction

private theorem local_fixed_mod_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (fixedPoints Q X) = 6) (z : P) (hz : z ^ 3 = 1)
    (hcomm : ∀ q : Q, z * q.val = q.val * z) :
    Nat.card {x : fixedPoints Q X // z.val x.val = x.val} % 3 = 0 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let F := fixedPoints Q X
  let _ : Fintype F := Fintype.ofFinite F
  have hinv : ∀ x : X, z.val x ∈ F ↔ x ∈ F := by
    intro x
    constructor
    · intro hx q
      apply z.val.injective
      have he := congrArg (fun a : P => a.val x) (hcomm q)
      change z.val (q.val.val x) = q.val.val (z.val x) at he
      exact he.trans (hx q)
    · intro hx q
      have he := congrArg (fun a : P => a.val x) (hcomm q)
      change z.val (q.val.val x) = q.val.val (z.val x) at he
      exact he.symm.trans (congrArg z.val (hx q))
  let f : Equiv.Perm F := z.val.subtypePerm hinv
  have hf3 : f ^ 3 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (z ^ 3).val x.val = x.val
    rw [hz]
    rfl
  let ff : Function.End F := f.toFun
  have hend : ff ^ 3 = 1 := by
    funext x
    change f (f (f x)) = x
    exact congrArg (fun e : Equiv.Perm F => e x) hf3
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := ff) (p := 3) (n := 1)
    (by simpa only [pow_one] using hend)
  let e : Function.fixedPoints f ≃ {x : F // z.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Fintype.card F % 3 = Fintype.card (Function.fixedPoints f) % 3 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,Nat.card_congr e] at hm
  change Nat.card F = 6 at hF
  rw [hF] at hm
  exact hm.symm

private theorem order_three_no_exterior
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hQ : IsPGroup 5 Q) (hQcard : Nat.card Q = 5)
    (hF : Nat.card (fixedPoints Q X) = 6)
    (hthree : ∀ z : P, orderOf z = 3 → 5 ≤ Nat.card (Function.fixedPoints z.val) →
      Nat.card (Function.fixedPoints z.val) = 6)
    (z : P) (hz : orderOf z = 3) (hcomm : ∀ q : Q, z * q.val = q.val * z)
    (x : X) (hx : x ∉ fixedPoints Q X) (hzx : z.val x = x) : False := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fintype (orbit Q x) := Fintype.ofFinite _
  have hm := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer Q X x
  have hd : Nat.card (orbit Q x) ∣ 5 := ⟨Nat.card (stabilizer Q x),by rw [hQcard] at hm; exact hm.symm⟩
  have hO : Nat.card (orbit Q x) = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h | h
    · exact (hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr
        (by rwa [← Nat.card_eq_fintype_card]))).elim
    · exact h
  have hsub : orbit Q x ⊆ Function.fixedPoints z.val := by
    rintro y ⟨q,rfl⟩
    have he := congrArg (fun a : P => a.val x) (hcomm q)
    change z.val (q.val.val x) = q.val.val (z.val x) at he
    exact he.trans (congrArg q.val.val hzx)
  have hlow := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hO] at hlow
  have hglobal := hthree z hz hlow
  let L := {x : fixedPoints Q X // z.val x.val = x.val}
  have hLbound : Nat.card L ≤ 6 := by
    rw [← hF]
    exact Nat.card_le_card_of_injective (fun x : L => x.val) Subtype.val_injective
  have hmod5 := CentralizingFixedPointCongruence.card_modEq P Q hQ z hcomm
  change Nat.card (Function.fixedPoints z.val) % 5 = Nat.card L % 5 at hmod5
  rw [hglobal] at hmod5
  have hmod3 := local_fixed_mod_three P Q hF z
    (by rw [← hz,pow_orderOf_eq_one]) hcomm
  change Nat.card L % 3 = 0 at hmod3
  have hL : Nat.card L = 6 := by omega
  let e : L ≃ ↥(fixedPoints Q X ∩ Function.fixedPoints z.val) :=
    { toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
      invFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hinter : (fixedPoints Q X ∩ Function.fixedPoints z.val).ncard = 6 := by
    rw [← Nat.card_coe_set_eq,← Nat.card_congr e]
    exact hL
  have heq : fixedPoints Q X ∩ Function.fixedPoints z.val = Function.fixedPoints z.val := by
    apply Set.eq_of_subset_of_ncard_le Set.inter_subset_right
    rw [hinter,← Nat.card_coe_set_eq,hglobal]
  have hxinter : x ∈ fixedPoints Q X ∩ Function.fixedPoints z.val := by rwa [heq]
  exact hx hxinter.1

theorem nine_not_dvd_centralizer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hQcard : Nat.card Q = 5)
    (hF : Nat.card (fixedPoints Q X) = 6)
    (hthree : ∀ z : P, orderOf z = 3 → 5 ≤ Nat.card (Function.fixedPoints z.val) →
      Nat.card (Function.fixedPoints z.val) = 6) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P)) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let C := Subgroup.centralizer (Q : Set P)
  let T : Sylow 3 C := Sylow.nonempty.some
  have hcomm (t : T) (q : Q) : t.val.val * q.val = q.val * t.val.val :=
    ((Subgroup.mem_centralizer_iff.mp t.val.property) q.val q.property).symm
  have hstable : ∀ t : T, ∀ x ∈ fixedPoints Q X, t • x ∈ fixedPoints Q X := by
    intro t x hx q
    have he := congrArg (fun a : P => a.val x) (hcomm t q)
    change t.val.val.val (q.val.val x) = q.val.val (t.val.val.val x) at he
    exact he.symm.trans (congrArg t.val.val.val (hx q))
  have hfree : ∀ t : T, ∀ x : X, x ∉ fixedPoints Q X → t • x = x → t = 1 := by
    intro t x hx htx
    by_contra ht
    let R : Subgroup T := stabilizer T x
    have hRne : R ≠ ⊥ := by
      intro he
      have hmem : t ∈ R := htx
      rw [he,Subgroup.mem_bot] at hmem
      exact ht hmem
    obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_subgroup R)
    have hepos : 1 ≤ e := by
      by_contra hn
      have hc : Nat.card R = 1 := by rw [he,show e = 0 by omega,pow_zero]
      exact hRne (Subgroup.card_eq_one.mp hc)
    have hp : 3 ∣ Nat.card R := by rw [he]; exact pow_dvd_pow 3 hepos
    obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 hp
    have huP : orderOf u.val.val.val = 3 := by
      rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,Subgroup.orderOf_coe,hu]
    exact order_three_no_exterior P Q hQ hQcard hF hthree u.val.val.val huP
      (hcomm u.val) x hx u.property
  have hd := FreeComplementCard.card_dvd_complement T X (fixedPoints Q X) hstable hfree
  rw [Nat.card_eq_fintype_card (α := X),hcard,← Nat.card_coe_set_eq,hF] at hd
  intro h9
  have h9T := T.pow_dvd_card_of_pow_dvd_card (n := 2) h9
  have hbad := h9T.trans hd
  norm_num at hbad

end FiveTransitive.Degree36FiveThreeCentralizer

end CFSG
