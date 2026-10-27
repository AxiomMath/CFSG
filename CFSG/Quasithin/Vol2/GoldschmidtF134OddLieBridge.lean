module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDescent
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieIso

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem OddConfig.toCfg {A : Type} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {L P T : Subgroup A} (h : OddConfig p L P T) : OddCfg p L P T where
  normal := h.normal
  le := h.le
  exp := h.exp
  card := h.card
  nonab := by
    intro h3
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative P := ⟨⟨fun a b => Subtype.ext (hcon a a.2 b b.2)⟩⟩
    have hel : IsElemAbelian p P := ⟨hcomm, h.exp⟩
    have hrank := (CFSG.SectionRank.isStronglyQuasithin_iff.1 h.hyp.sqt) p hp.out (by omega)
    have := CFSG.SectionRank.le_pRank hp.out.one_lt (le_top : P ≤ ⊤) hel h3
    omega
  sylow := h.sylow
  mul := h.mul
  irred := h.irred

theorem noOddConfigQ_of_noOddCfg {F : ∀ (X : Type) [Group X], Prop} (hF : IsoInvariant F)
    (h : NoOddCfg F) : NoOddConfigQ F := by
  intro A _ _ p _ L P T hp5 hcfg hZ hFq
  obtain ⟨A', _, _, L', P', T', hcfg', ⟨e⟩, -, -⟩ := (hcfg.toCfg hp5).descend hp5 hZ
  exact h A' p L' P' T' hp5 (hF _ _ e.symm hFq) hcfg'

theorem liePsp4Even_of_simple (h : Psp4EvenSimple) : LiePsp4Even := by
  intro n A _ _ p _ L P T hp5 hcfg hZ hmod
  obtain ⟨A', _, _, L', P', T', hcfg', ⟨e⟩, hcard, hcyc⟩ := (hcfg.toCfg hp5).descend hp5 hZ
  obtain ⟨h1, h2, h3, h4⟩ := h n A' p L' P' T' hp5
    (isoInvariant_stated .PSp 2 2 n _ _ e.symm hmod) hcfg'
  exact ⟨hcard ▸ h1, h2, h3, hcyc h4⟩

theorem liePsl3Odd_of_simple (h : Psl3OddSimple) : LiePsl3Odd := by
  intro r A _ _ p _ L P T hr hr2 hp5 hcfg hZ hmod
  obtain ⟨A', _, _, L', P', T', hcfg', ⟨e⟩, hcard, -⟩ := (hcfg.toCfg hp5).descend hp5 hZ
  obtain ⟨h1, h2⟩ := h r A' p L' P' T' hr hr2 hp5
    (isoInvariant_stated .PSL 3 r 1 _ _ e.symm hmod) hcfg'
  exact ⟨h1, hcard ▸ h2⟩

theorem noOddConfigQ_of_noPowerOvergroup {F : ∀ (X : Type) [Group X], Prop}
    (h : NoPowerOvergroup F) : NoOddConfigQ F := by
  intro A _ _ p hp L P T hp5 hcfg hZ hFq
  obtain ⟨a, ha, H, S, hS2, hSi, hSH, hH⟩ := hcfg.exists_model hp5 hZ
  exact h (↥L ⧸ Subgroup.center ↥L) hFq p a hp.out hp5 ha H S hS2 hSi hSH hH

end CFSG.Quasithin.H13.NQCore
