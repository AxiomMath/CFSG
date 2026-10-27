module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerImage
public import CFSG.Permutation.FiveTransitive.FixedSetEvenExtension

public section

namespace CFSG

namespace FiveTransitive.FixedNormalizerImageEven

open MulAction FixedNormalizerAction FixedNormalizerImage FixedSetNormalizerPerm

theorem sign_eq_one
    {G X:Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    {p k:ℕ} [Fact p.Prime] (Q:Subgroup G) (B:Subgroup (Normalizer Q))
    (hQA:Q≤Ambient B) (a:Fin k ↪ X) (P:Sylow p (stabilizer G a))
    (hF:fixedPoints (Ambient B) X=
      fixedPoints ((P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype) X)
    (heven:let A := (P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype
      ∀n:G,∀hn:n∈Subgroup.normalizer (A:Set G),
      letI := Fintype.ofFinite (fixedPoints A X)
      letI := Classical.decEq (fixedPoints A X)
      (fixedPerm G X A n hn).sign=1)
    (n:Image (X:=X) Q)
    (hn:n∈Subgroup.normalizer ((Restricted (X:=X) B):Set (Image (X:=X) Q))) :
    letI := Fintype.ofFinite (fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q))
    letI := Classical.decEq (fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q))
    (fixedPerm (Image (X:=X) Q) (Fixed (X:=X) Q) (Restricted (X:=X) B) n hn).sign=1 := by
  classical
  let A := (P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype
  let _ := Fintype.ofFinite (fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q))
  let _ : DecidableEq (fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q)) := Classical.decEq _
  let _ := Fintype.ofFinite (fixedPoints A X)
  let _ : DecidableEq (fixedPoints A X) := Classical.decEq _
  let E : fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q) ≃ fixedPoints A X :=
    (fixedEquiv B hQA).trans (Set.equivOfEq hF)
  let f := fixedPerm (Image (X:=X) Q) (Fixed (X:=X) Q) (Restricted (X:=X) B) n hn
  obtain ⟨g,hg⟩ := (toPermHom (Normalizer Q) (Fixed (X:=X) Q)).rangeRestrict_surjective n
  have hE (x:fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q)) :
      (E x).val=x.val.val := rfl
  have hEinv (y:fixedPoints A X) : (E.symm y).val.val=y.val := by
    have h := hE (E.symm y)
    simpa only [E.apply_symm_apply] using h.symm
  have he : ∀y:fixedPoints A X,((E.permCongr f) y).val=g.val • y.val := by
    intro y
    change (E (f (E.symm y))).val=g.val • y.val
    rw [hE]
    change (n • (E.symm y).val).val=g.val • y.val
    rw [←hg]
    change g.val • (E.symm y).val.val=g.val • y.val
    rw [hEinv]
  have hs := FixedSetEvenExtension.sign_eq_one a P heven g.val (E.permCongr f) he
  simpa only [Equiv.Perm.sign_permCongr] using hs

end FiveTransitive.FixedNormalizerImageEven

end CFSG
