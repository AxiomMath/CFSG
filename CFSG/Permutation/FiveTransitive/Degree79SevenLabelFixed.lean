module

public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree79SevenLabelFixed
open MulAction FixedNormalizerAction NormalizerOrbitFamily

private theorem seven_mul_fixed_labels_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (g : Normalizer Q) (hg : g ^ 5 = 1) :
    7 * Nat.card (Function.fixedPoints (NormalizerOrbitFamily.toPermHom (X := X) Q 7 g)) ≤
      Nat.card (Function.fixedPoints g.val.val) := by
  classical
  let C := Function.fixedPoints (NormalizerOrbitFamily.toPermHom (X := X) Q 7 g)
  let e (c : C) : Fin 7 ↪ c.val.val.orbit :=
    (Fin.castLEEmb c.val.property.ge).trans (Finite.equivFin c.val.val.orbit).symm.toEmbedding
  have hfixed (c : C) (y : c.val.val.orbit) : g.val • y.val = y.val := by
    have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g c.val.val = c.val.val :=
      congrArg Subtype.val c.property
    have he : (Quotient.mk'' y.val : orbitRel.Quotient Q X) = c.val.val :=
      orbitRel.Quotient.mem_orbit.mp y.property
    have hsize : Nat.card (orbit Q y.val) = 7 := by
      rw [← orbitRel.Quotient.orbit_mk,he]
      exact c.val.property
    have hgy : g.val • y.val ∈ orbit Q y.val := by
      apply Quotient.exact (s := orbitRel Q X)
      change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' y.val) = Quotient.mk'' y.val
      rwa [he]
    exact Degree54SevenOrbitFiveFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val hg) y.val (by rw [hsize]; decide) hgy y.val (mem_orbit_self y.val)
  let f : C × Fin 7 → Function.fixedPoints g.val.val :=
    fun z => ⟨(e z.1 z.2).val,hfixed z.1 (e z.1 z.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : (e a.1 a.2).val = (e b.1 b.2).val := congrArg Subtype.val hab
    have ha : (Quotient.mk'' (e a.1 a.2).val : orbitRel.Quotient Q X) = a.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2).property
    have hb : (Quotient.mk'' (e b.1 b.2).val : orbitRel.Quotient Q X) = b.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).property
    have hc : a.1 = b.1 := Subtype.ext (Subtype.ext (ha.symm.trans ((congrArg Quotient.mk'' hab').trans hb)))
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    dsimp only at hc
    subst b
    have hij : i = j := (e a).injective (Subtype.ext hab')
    subst j
    rfl
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,Nat.card_fin] at hh
  simpa only [Nat.mul_comm] using hh

theorem fixed_card_eq_thirtyNine
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (g : Normalizer Q) (hg : orderOf g = 5)
    (hlabels : Nat.card (Function.fixedPoints (NormalizerOrbitFamily.toPermHom (X := X) Q 7 g)) = 5) :
    Nat.card (Function.fixedPoints g.val.val) = 39 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hge := seven_mul_fixed_labels_le P Q hQ g (hg ▸ pow_orderOf_eq_one g)
  rw [hlabels] at hge
  have hne : g.val.val ≠ 1 := by
    intro he
    have hg1 : g = 1 := Subtype.ext (Subtype.ext he)
    rw [hg1,orderOf_one] at hg
    omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt g.val.property hne
  rw [hcard] at hb
  have hle : Nat.card (Function.fixedPoints g.val.val) ≤ 39 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
    omega
  let a : Function.End X := g.val.val.toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change (g ^ 5).val.val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree79SevenLabelFixed

end CFSG
