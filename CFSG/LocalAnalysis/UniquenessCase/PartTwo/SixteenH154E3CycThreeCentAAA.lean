module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAF1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAF2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAAF3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycThreeCentAAA_exists_bar_fix_not_mem_v0
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs3 : s15 D.M V₀ V hV L = 3)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6))
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    {E : Subgroup G} (hEM : E ≤ D.M) (hEab : IsElemAbelian 3 E)
    (hEcard : Nat.card ↥E = 3 ^ 3) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, u ∉ V₀ → ∃ φ ∈ barSub V₀ V hV E, φ ≠ 1 ∧
        ∀ (huV : u ∈ V), φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) := by
  intro X hX Y hY _ u huXY _
  have hp3 : p ≠ 3 := by
    rintro rfl
    apply hpσ
    rw [h3]
    exact Set.mem_singleton _
  obtain ⟨hEbab, hEbcard⟩ := s16h_e3_CycThreeCent_barSub_card D hV h hEM hEab hEcard hct
  have hEbM : barSub V₀ V hV E ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hEM
  have hcard : (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 3 :=
    (s16h_e3_cyc_conjSubs_ncard D hV h hc hp hLp).trans hs3
  have hsup : (⨆ Z ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L), Z) = ⊤ := by
    obtain ⟨t, -, -, -, -, hW⟩ := hc
    exact hW.1
  have hperm : ∀ e ∈ barSub V₀ V hV E, ∀ Z ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L),
      Z.map e.toMonoidHom ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) := by
    rintro e he Z ⟨g, hg, rfl⟩
    exact ⟨e * g, (Mbar D.M V₀ V hV).mul_mem (hEbM he) hg, by rw [Subgroup.map_map]; rfl⟩
  have hrank : ∀ Z ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L),
      ∀ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≤ barSub V₀ V hV E → B ≤ stabSub Z →
        Nat.card ↥B ≤ 3 * Nat.card ↥(B ⊓ centSub Z) := by
    rintro Z ⟨g, hg, rfl⟩ B hBE hBZ
    have hBab : IsElemAbelian 3 B := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hEbab.2 x (hBE hx)⟩
      have h1 := congrArg Subtype.val (hEbab.1.is_comm.comm ⟨a, hBE a.2⟩ ⟨b, hBE b.2⟩)
      exact Subtype.ext h1
    exact s16h_e3_cyc_rank_one_conj D hV h hc hp hLp hp3 hn76 hg (hBE.trans hEbM) hBab hBZ
  obtain ⟨φ, hφE, hφ1, hφX, hφY⟩ :=
    s16h_e3_three_summands_fixed_pair hEbab hEbcard hcard hsup hperm hrank
      (s16h_e3_CycThreeCent_imgTil_mem_conjSubs D hV h hX)
      (s16h_e3_CycThreeCent_imgTil_mem_conjSubs D hV h hY)
  exact ⟨φ, hφE, hφ1, fun huV =>
    s16h_e3_CycThreeCent_fix_of_centSub D hV h hX hY hφX hφY huXY huV⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
