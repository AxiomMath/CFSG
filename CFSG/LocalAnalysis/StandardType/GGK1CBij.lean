module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CCoBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1CCoLabel
public import CFSG.LocalAnalysis.StandardType.GGK1CCoComp
public import CFSG.LocalAnalysis.StandardType.GGK1CCoInj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

private theorem ggK1C_bij_aux {D : GGKacDatum} {R : Type} [Group R] {e : MulAut R} {Q : Type}
    (compSub : Q → Subgroup R)
    (hcomp : ∀ i, CFSG.Assembly.IsComponentOf (compSub i) (ggFixSub e))
    (hinj : Function.Injective compSub)
    (hsurj : ∀ J, CFSG.Assembly.IsComponentOf J (ggFixSub e) → ∃ i, compSub i = J)
    (g : Q ≃ {k : Fin D.orbits.length // D.orbits[k].qs = true}) (blk : Q → GGKacOrbit)
    (hg : ∀ i, D.orbits[(g i).1] = blk i)
    (hlab : ∀ i, GGHasLabel (blk i).lab (↥(compSub i) ⧸ Subgroup.center ↥(compSub i))) :
    GGKacCompBij D R e := by
  let c : Q → {J : Subgroup R // CFSG.Assembly.IsComponentOf J (ggFixSub e)} :=
    fun i => ⟨compSub i, hcomp i⟩
  have hc : Function.Bijective c := by
    refine ⟨fun i j hij => hinj (congrArg Subtype.val hij), ?_⟩
    rintro ⟨J, hJ⟩
    obtain ⟨i, hi⟩ := hsurj J hJ
    exact ⟨i, Subtype.ext hi⟩
  let e' := Equiv.ofBijective c hc
  refine ⟨e'.symm.trans g, fun J => ?_⟩
  have hJ : J.1 = compSub (e'.symm J) := (congrArg Subtype.val (e'.apply_symm_apply J)).symm
  have hpos : D.orbits[((e'.symm.trans g) J).1] = blk (e'.symm J) := hg (e'.symm J)
  have transport : ∀ (lab : LargeEvenLabel) (X Y : Subgroup R), X = Y →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → GGHasLabel lab (↥Y ⧸ Subgroup.center ↥Y) := by
    intro lab X Y h
    subst h
    exact id
  rw [hpos]
  exact transport _ _ _ hJ.symm (hlab (e'.symm J))

theorem ggK1C_core_bij {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hK : Nat.card K = 2 ^ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) :
    GGKacCompBij (ggMultDatumC p nf d m) (StatedProj (StatedSp r K))
      (MulAut.conj (proj r K x)) := by
  have hnf : 1 ≤ nf := by
    rcases Nat.eq_zero_or_pos nf with h0 | hpos
    · subst h0
      rw [pow_zero] at hK
      have h2 := Finite.one_lt_card (α := K)
      omega
    · exact hpos
  obtain ⟨B⟩ := ggK1CCo_blocks_exists hnf hp hp2 hdvd hK hm hx
  obtain ⟨F⟩ := ggK1CCo_family_of_blocks B hK
  obtain ⟨g, hg⟩ := F.hbij
  refine ggK1C_bij_aux (fun i : {i : F.ι // CFSG.IsQuasisimple ↥⁅F.A i, F.A i⁆} =>
      (⁅F.A i.1, F.A i.1⁆).map (proj r K)) (fun i => ggK1CCo_factor_component F i.1 i.2) ?_ ?_
    g (fun i => F.blk i.1) hg (fun i => F.hlab i.1 i.2)
  · intro i j hij
    exact Subtype.ext (ggK1CCo_component_inj hK hnf F i.2 j.2 hij)
  · intro J hJ
    obtain ⟨i, hq, hJeq⟩ := ggK1CCo_component_eq F hJ
    exact ⟨⟨i, hq⟩, hJeq.symm⟩

end CFSG.StandardType

end
