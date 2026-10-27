module

public import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Core
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Hard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggB36JLabel_twA6_false {labX : LargeEvenLabel} {m : ℕ} :
    ¬ GGB36JLabel labX ⟨.twA, 6, m⟩ := by
  intro h
  unfold GGB36JLabel at h
  rcases h with ⟨-, -, h | h | h | h | h⟩ | ⟨-, -, h | h | ⟨-, h⟩⟩ |
    ⟨-, -, h | h⟩ | ⟨-, -, h | h | h | h | h | ⟨-, h⟩⟩
  all_goals
    rw [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr, -⟩ := h
    omega

theorem ggTwA6E6Three_holds
    (hBS : GGK0ExcBS) : GGTwA6E6ThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, -, htagJ, hrankJ, hdvdJ⟩, htagX, -, hpair⟩ := hr
  subst hp3
  obtain ⟨D, hDval, ha, -, hc, he⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  obtain ⟨hlocCore, -, -, -, -, -, honly, -⟩ := hd.1
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := by
    ext x; simp [ggFixSub, ggAutFixedSubgroup]
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [hfix]
    exact hlocCore.2.2.2.1
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabo⟩ := ha J hJfix
  obtain ⟨f, hf⟩ := he
  have hEqJ : ∀ J' (hJ' : IsComponentOf J' (ggFixSub σ)), J' = J :=
    fun J' hJ' => @eq_of_isComponentOf_of_ggTPNOnlyComp 3 ⟨by norm_num⟩ X _ _ σ J J'
      honly (hfix ▸ hJ') (hc J' hJ')
  have hpos : ∀ i j : Fin D.orbits.length, D.orbits[i].qs = true →
      D.orbits[j].qs = true → i = j := by
    intro i j hi hj
    have hsub' : Subsingleton {k : Fin D.orbits.length // D.orbits[k].qs = true} := by
      constructor
      intro a b
      have h1 : f.symm a = f.symm b :=
        Subtype.ext (by rw [hEqJ (f.symm a).1 (f.symm a).2, hEqJ (f.symm b).1 (f.symm b).2])
      have h2 := congrArg f h1
      simpa using h2
    have hthis : (⟨i, hi⟩ : {k : Fin D.orbits.length // D.orbits[k].qs = true}) =
        ⟨j, hj⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hthis
  obtain ⟨Tk, tw, hty, hDmem⟩ := hDval
  have htype := ltqE6c_typeOfLabel_eq hΛX htagX
  rw [htype] at hty
  simp only [Option.some.injEq, Prod.mk.injEq] at hty
  obtain ⟨hT, htwb⟩ := hty
  subst hT
  have htw : ggKacTypeOfLabel labX = some (.E6, tw) := by rw [htype, htwb]
  have hclass : GGB36JLabel labX o.lab ∨ o.lab = labX :=
    ltqE6c_classify hΛX htagX htw hDmem ho hqs hpos hdvd
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  obtain ⟨tJ, rJ, m⟩ := labJ
  have htag : tJ = .twA := htagJ
  have hrank : rJ = 6 := hrankJ
  subst tJ
  subst rJ
  have hmem : o.lab = ⟨.twA, 6, m⟩ := ggLabelIso_twA6_left hiso
  rcases hclass with hGLo | heqo
  · rw [hmem] at hGLo
    exact (ggB36JLabel_twA6_false hGLo).elim
  · exfalso
    rw [hmem] at heqo
    rw [← heqo] at htagX
    simp at htagX

end CFSG.StandardType

end
