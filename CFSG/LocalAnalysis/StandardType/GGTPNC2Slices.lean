module

public import CFSG.LocalAnalysis.StandardType.GGTPNC2Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Core
public import CFSG.LocalAnalysis.StandardType.GGExcCentred
public import CFSG.LocalAnalysis.StandardType.GGTypeAExcOneThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggC2ClRARK_holds :
    GGTablePKnownRK fun p n labJ labX => GGRegimeC2 p n labJ labX ∧ GGKacRA labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨htJ, hrJ, -, -⟩, hRA⟩ := hr
  obtain ⟨⟨hloc, -, -, -, -, -, honly, hm⟩, -⟩ := hd
  rcases labJ with ⟨tJ, rJ, m⟩
  dsimp only at htJ hrJ
  subst htJ
  subst hrJ
  rcases labX with ⟨tX, rX, nX⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked p (fun _ lab => lab = (⟨tX, rX, nX⟩ : LargeEvenLabel)) A :=
    ggTPNMarked_eq_of_ggKacRA hrig hp hm hΛX hRA hhX
  have hcore := split_or_fieldType_of_ggKacRA hp hloc honly hRA hm'
  exfalso
  dsimp only at hcore hRA
  rcases hcore with ⟨a, ds, -, -, -, -, hbr⟩ | ⟨-, -, hbr⟩
  · rcases hbr with ⟨hΛ', hh'⟩ | ⟨-, -, hΛ', hh'⟩
    ·
      rcases ggLabelIso_c2_right (hrig _ _ _ hΛ' hΛJ hh' hhJ) with heq | heq <;>
        simp only [LargeEvenLabel.mk.injEq] at heq <;> obtain ⟨rfl, -, rfl⟩ := heq <;>
        rcases hRA with ⟨h, -⟩ | ⟨h, -, -⟩ <;> cases h
    ·
      rcases ggLabelIso_c2_right (hrig _ _ _ hΛ' hΛJ hh' hhJ) with heq | heq <;> simp at heq
  · rcases hbr with ⟨-, hΛ', hh'⟩ | ⟨-, -, hΛ', hh'⟩
    ·
      rcases ggLabelIso_c2_right (hrig _ _ _ hΛ' hΛJ hh' hhJ) with heq | heq <;> simp at heq
    ·
      rcases ggLabelIso_c2_right (hrig _ _ _ hΛ' hΛJ hh' hhJ) with heq | heq <;> simp at heq

theorem ggC2ExcOneThree_holds
    (hBS : GGK0ExcBS) :
    GGTablePKnownRK fun p n labJ labX =>
      GGRegimeC2 p n labJ labX ∧ GGKacExcPair labX p ∧ GGKacCentred labX p ∧ labX.n = 1 ∧ p = 3 :=
  ggExcOneThreeRK_of_fieldExp hBS fun _ _ labJ _ hreg lab hiso => by
    obtain ⟨ht, hr, hn, -⟩ := hreg
    obtain ⟨tJ, rJ, m⟩ := labJ
    simp only at ht hr hn
    subst ht hr
    rcases ggLabelIso_c2_right hiso with rfl | rfl <;> exact hn

theorem ggC2E6Three_holds
    (hBS : GGK0ExcBS) :
    GGTablePKnownRK fun p n labJ labX =>
      GGRegimeC2 p n labJ labX ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) ∧ p = 3 ∧
        GGKacExcPair labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hJt, hJr, -, -⟩, htagX, hp3, hpair⟩ := hr
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨D, hDval, ha, hb, hc, he⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  obtain ⟨hlocCore, -, -, -, -, -, honly, -⟩ := hd.1
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := by
    ext x; simp [ggFixSub, ggAutFixedSubgroup]
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [hfix]
    exact hlocCore.2.2.2.1
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabo⟩ := ha J hJfix
  obtain ⟨f, hf⟩ := he
  have hEqJ : ∀ J' (hJ' : IsComponentOf J' (ggFixSub σ)), J' = J :=
    fun J' hJ' => eq_of_isComponentOf_of_ggTPNOnlyComp honly (hfix ▸ hJ') (hc J' hJ')
  have : Subsingleton {J' : Subgroup X // IsComponentOf J' (ggFixSub σ)} :=
    ⟨fun a b => Subtype.ext (by rw [hEqJ a.1 a.2, hEqJ b.1 b.2])⟩
  have hpos : ∀ i j : Fin D.orbits.length, D.orbits[i].qs = true →
      D.orbits[j].qs = true → i = j := by
    intro i j hi hj
    have hsub' : Subsingleton {k : Fin D.orbits.length // D.orbits[k].qs = true} := by
      constructor
      intro a b
      have h1 : f.symm a = f.symm b := Subsingleton.elim _ _
      have h2 := congrArg f h1
      simpa using h2
    have hthis : (⟨i, hi⟩ : {k : Fin D.orbits.length // D.orbits[k].qs = true}) =
        ⟨j, hj⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hthis
  obtain ⟨T, tw, hty, hDmem⟩ := hDval
  have htype := ltqE6c_typeOfLabel_eq hΛX htagX
  rw [htype] at hty
  simp only [Option.some.injEq, Prod.mk.injEq] at hty
  obtain ⟨hT, htwb⟩ := hty
  subst hT
  have htw : ggKacTypeOfLabel labX = some (.E6, tw) := by rw [htype, htwb]
  have hclass : GGB36JLabel labX o.lab ∨ o.lab = labX :=
    ltqE6c_classify hΛX htagX htw hDmem ho hqs hpos hdvd
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at hJt hJr
  subst hJt hJr
  have hiso : GGLabelIso o.lab ⟨.C, 2, m⟩ :=
    ggLabelRigidInput_holds o.lab _ (↥J ⧸ Subgroup.center ↥J) hΛo hΛJ hlabo hhJ
  exfalso
  rcases ggLabelIso_c2_right hiso with heq | heq <;> rw [heq] at hclass <;>
    rcases hclass with hG | hG
  · unfold GGB36JLabel at hG
    simp at hG
  · rcases htagX with h | h <;> rw [← hG] at h <;> simp at h
  · unfold GGB36JLabel at hG
    simp at hG
  · rcases htagX with h | h <;> rw [← hG] at h <;> simp at h

theorem ggC2ExcRERK_holds
    (hB3 : GGK0ExcB3) : GGC2ExcRERK := by
  refine GGTablePKnownRK.mono (GGTablePKnownRK.union (ggExcCentredRK_holds hB3 GGRegimeC2)
    (GGTablePKnownRK.union (ggC2ExcOneThree_holds (ggK0ExcBS_of_B3 hB3))
      (ggC2E6Three_holds (ggK0ExcBS_of_B3 hB3)))) ?_
  rintro p n labJ labX ⟨hreg, hRE⟩
  rcases ggKacRE_cases hRE with hq | ho | h3
  · exact Or.inl ⟨hreg, hq⟩
  · exact Or.inr (Or.inl ⟨hreg, ho⟩)
  · exact Or.inr (Or.inr ⟨hreg, h3.1, h3.2, hRE.toExcPair⟩)

end CFSG.StandardType

end
