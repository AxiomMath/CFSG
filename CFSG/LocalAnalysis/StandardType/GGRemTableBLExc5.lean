module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc4
public import CFSG.Yardstones.M3f9567aba59d.TableBL
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLResidualsUni2
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggInnerDiagOnLab_of_sub {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    {S T : ℕ → LargeEvenLabel → Prop}
    (hTS : ∀ lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab → S p lab)
    (h : GGInnerDiagOnLab T p Bs L) : GGInnerDiagOnLab S p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hTS lab hlab hθ.2.1 hθ.1, hθ.2⟩

theorem ggTableBCxInputOn_restrict {S T : ℕ → LargeEvenLabel → Prop}
    (hX : GGTableBCxInputOn S)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab → S p lab) :
    GGTableBCxInputOn T := by
  intro G _ _ p B Bs x L D J hC hL
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_of_sub
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL)

theorem ggTableBModuleInputOn_restrict {S T : ℕ → LargeEvenLabel → Prop}
    (hX : GGTableBModuleInputOn S)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab → S p lab) :
    GGTableBModuleInputOn T := by
  intro G _ _ p B Bs x L D J hC hL
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_of_sub
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL)

theorem ggTableBActionInputOn_restrict {S T : ℕ → LargeEvenLabel → Prop}
    (hX : GGTableBActionInputOn S)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab → S p lab) :
    GGTableBActionInputOn T := by
  intro G _ _ p B Bs x L D J B₂ hC hL hM
  exact hX G p B Bs x L D J B₂ hC (ggInnerDiagOnLab_of_sub
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL) hM

theorem ggLTransvectionCenterInputOn_restrict {S T : ℕ → LargeEvenLabel → Prop}
    (hX : GGLTransvectionCenterInputOn S)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab → S p lab) :
    GGLTransvectionCenterInputOn T := by
  intro G _ _ p B Bs x L D J hC hL
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_of_sub
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL)

theorem ggLNoInvariantLineInputOn_restrict {S T : ℕ → LargeEvenLabel → Prop}
    (hX : GGLNoInvariantLineInputOn S)
    (hTS : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → T p lab → S p lab) :
    GGLNoInvariantLineInputOn T := by
  intro G _ _ p B Bs x L D J hC hL E hEBs hxE hE
  exact hX G p B Bs x L D J hC (ggInnerDiagOnLab_of_sub
    (fun lab h1 h2 h3 => hTS p lab hC.tableB_facts.1 h1 h2 h3) hL) E hEBs hxE hE

@[expose] def GGRemTableBLExc5Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGRemTableBLExc5TvLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3

theorem eq_three_of_dvd_two_pow_add_one {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hd : p ∣ 2 ^ n + 1) (h5 : p < 5) : p = 3 := by
  have h2 := hp.two_le
  interval_cases p
  · have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    exact absurd ((Nat.dvd_add_right h2n).mp hd) (by norm_num)
  · rfl
  · exact absurd hp (by decide)

theorem twE6Three_of_exc4 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ p < 5) :
    GGTableBTwE6ThreeLabel p lab := by
  have h3 := eq_three_of_dvd_two_pow_add_one hp hlab.1 h.2.1 h.2.2
  subst h3
  exact ⟨h.1, rfl, h.2.1⟩

theorem exc5_of_exc4 (p : ℕ) (lab : LargeEvenLabel) (hp : p.Prime) (hlab : LargeEvenInLambda2 lab)
    (h : GGRemTableBLExc4Label p lab ∧ ¬ GGTableBTwE6ThreeLabel p lab) :
    GGRemTableBLExc5Label p lab := by
  obtain ⟨h1 | h1, h2⟩ := h
  · exact (h2 (twE6Three_of_exc4 hp hlab h1)).elim
  · exact h1

theorem exc5Tv_of_exc4Tv (p : ℕ) (lab : LargeEvenLabel) (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab)
    (h : GGRemTableBLExc4TvLabel p lab ∧ ¬ GGTableBTwE6ThreeLabel p lab) :
    GGRemTableBLExc5TvLabel p lab := by
  obtain ⟨h1 | h1, h2⟩ := h
  · exact (h2 (twE6Three_of_exc4 hp hlab h1)).elim
  · exact h1

end CFSG.Yardstones.M3f9567aba59d
