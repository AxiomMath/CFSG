module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAlt6B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAlt6C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_two_alt6_kbar_or_aut {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) ∨ Case168_1 D V₀ V hV L := by
  have hF : s16e_two_Fam D V₀ V L hV (fun H U Z => AlternatingNatural H U Z 6) :=
    s16e_two_fam_alt D hV (by norm_num) hA hsum
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ :=
    s16e_two_cfg2 D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have htrans := s16e_two_trans_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV
    c.setting c.ne c.conc hs hF
  obtain ⟨t, htX, ht2, ht1, htrk⟩ :=
    s16e_two_involution_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.conc
  have hHX := s16e_two_lStar_le D c.setting.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D c.std.h1217 c.setting.hyp151 hV
  have hA' : UC22.IsAlt ↥(lStar D.M V₀ V hV L) 6 := ⟨e.trans hA.some⟩
  have hsig := s168e3_two_alt6_sig c hs hA hsum
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have h9 : 3 ^ 2 ∣ Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
    s168e3_two_pow_dvd_card c h3
  by_cases hψ : ∃ ψ ∈ Subgroup.centralizer
      ((lStar D.M V₀ V hV L) : Set (MulAut (vStar D.M V₀ V hV L))),
      J₀.map ψ.toMonoidHom = J₁
  · exact Or.inl (s168e3_alt6_three_dvd_of_equiv F hHX hA' hE₀ htrans h9
      hψ.choose_spec.1 hψ.choose_spec.2)
  · have hne : ∀ ψ ∈ Subgroup.centralizer
        ((lStar D.M V₀ V hV L) : Set (MulAut (vStar D.M V₀ V hV L))),
        J₀.map ψ.toMonoidHom ≠ J₁ := by
      intro ψ hψmem hψJ
      exact hψ ⟨ψ, hψmem, hψJ⟩
    obtain ⟨eX⟩ := s168e3_alt6_equiv_aut F hHX hA' hJ₀ hJ₁ hE₀ hE₁ htrans
      ⟨t, htX, ht2, ht1, htrk⟩ hne
    obtain ⟨ρ, -, -⟩ := s16e_two_kappa_equiv D c.std.h1217 c.setting.hyp151 hV
    refine Or.inr ⟨⟨ρ.trans (eX.trans (MulAut.congr (e.trans hA.some)))⟩, hA, ?_, hsig⟩
    refine ⟨J₀, J₁, bot_le, bot_le, ?_, ?_, ?_, hJ₀, hJ₁, hne⟩
    · rw [bot_sup_eq, F.inf_eq]
    · rw [bot_sup_eq, inf_comm, F.inf_eq]
    · rw [bot_sup_eq, F.sup_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
