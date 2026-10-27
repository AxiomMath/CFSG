module

public import CFSG.LocalAnalysis.StandardType.GGResILinDefs
public import CFSG.LocalAnalysis.StandardType.GGResILineExit
public import CFSG.LocalAnalysis.StandardType.GGResITriple
public import CFSG.LocalAnalysis.StandardType.GGResIStdFork
public import CFSG.LocalAnalysis.StandardType.GGResIO2bExcl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResCaseIQFourInput_of_lin (hFix : GGTBFixInput) (hJr : GGForkJr) (hPump : GGForkPumpOr)
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hReal : GGReflRealizedQFourInputThree)
    (hPL : GGPumpLineThreeInput) (hO2 : GGResCaseIQFourO2Input) (hLin : GGResILinInput) :
    GGResCaseIQFourInput := by
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  obtain ⟨hPD, hq⟩ := hP
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := id hPD
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨-, -, hxBs, hLx, -⟩ := hH.1.tableB_facts
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let g : Option Λ → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  let xv : V := ι (Additive.ofMul ⟨x, hxBs⟩)
  have hind : LinearIndependent (ZMod p) h := hsel
  have hspan := ggResI_span_top hFix hH ι hφ hAL hind
  have hdim := ggResI_finrank hspan hind
  have h3 := ggResI_three_le_card hH ι hdim
  have h8 : Fintype.card Λ < 8 := by
    have hh := htyp
    rw [ggTypRankLt, Nat.card_eq_fintype_card] at hh
    exact hh
  have hα2 : ∀ o : Option Λ, α o (h o) = 2 := by
    intro o
    cases o with
    | none =>
      have h1 := hK none none
      rw [hCK.1 none] at h1
      simpa using h1
    | some i =>
      have h1 := hL i i
      rw [hCL.1 i] at h1
      simpa using h1
  have hxfix : ∀ i : Λ, α (some i) xv = 0 := by
    intro i
    have hmem : φ (some i) ∈ ggAutomizer L Bs := by
      rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩
    exact ggResI_alpha_eq_zero hp2 (hφ (some i)) (hα2 (some i))
      ((ggLin_fix_iff ι (φ (some i)) _).mp (ggResI_automizer_fix hxBs hLx _ hmem))
  have hfixspan := ggResI_fixSpan hFix hH hxBs ι hφ hAL
  have hx0 : xv ≠ 0 := by
    intro h0
    have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
    apply hx1
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective (ι.injective (h0.trans (map_zero ι).symm))
    exact congrArg Subtype.val h1
  have hnf : ¬ GGResIForkShape b CL CK := fun hf =>
    hFork (ggResI_forkDatum hWL hCL hCK hφ hL hK hind hAL hAK hf)
  have hAV : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range g) := ggResI_map_sup ι (ggResI_sup_eq_closure hAL hAK)
  rcases hLin p Λ b ML CL MK CK V g h α xv hp2 h3 h8 hWL hCL hWK hCK hdel hnf hφ hL hK hind hspan
      hxfix hfixspan hx0 with
    ⟨t, ht, htv⟩ | ⟨hu, M₀, hW₀, hC₀⟩ | ⟨hp5, ψ, hψ, j, j', hj, hj', hbad⟩ |
      ⟨hp3, R, hRg, hRc, ψ, hψ, i, hfx, hnot⟩ | ⟨hp3, hcert⟩ | ⟨hcell, hcert⟩ | hcellb | hW
  ·
    exfalso
    rw [← hAV] at ht
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp ht
    exact hH.2.2.2.1 ψ (ggResI_mem_ggInduced_top hψA) (ggRC_isTransvection_of_lin ι ψ htv)
  ·
    exact (hStd (ggResI_stdDatum hφ hL hK hind hAL hAK hu hW₀ hC₀)).elim
  ·
    exact (ggResI_false_of_triBad hJr hPump hLB hSP hp5 hH hφ hα2 hAL hAK hJ hψ hj hj'
      hbad).elim
  ·
    exact (hnot (ggResI_mem_of_q8 hLB hSP hReal hH hp3 hq hWL hCL ι hφ hrefl hL
      (hind.comp some (Option.some_injective _)) hAL hAK hxBs hRg hRc hψ hfx)).elim
  ·
    exact (ggResI_line_exit hLB hSP hReal hPL hH hp3 hq hPD ι hφ hrefl hL hspan hind hAL hAK hJ
      False (fun hf => hf.elim) hcert).elim
  ·
    have hp3 : p = 3 := hcell.1
    rcases ((hH.2.2.1.2 y K hH.2.2.2.2.1).label GGLabQFour p).elim_or with hK4 | hK2
    · exact (ggResI_line_exit hLB hSP hReal hPL hH hp3 hq hPD ι hφ hrefl hL hspan hind hAL hAK
        hJ True (fun _ => hK4) hcert).elim
    · exact hO2 G p B Bs x L D J y K hH hFork hStd hE6
        ⟨⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, hWL, hCL, hWK, hCK, htyp, hφ,
          hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hAL, hAK, hdel, hJ, hcell⟩, hq,
          largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨not_le.mp hP.1, hP.2⟩) hK2⟩
  ·
    exact (ggResI_o2b_excl hFix G p B Bs x L D J y K hH ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
      hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hAL, hAK, hdel,
      hJ, hcellb⟩).elim
  ·
    rw [← hAV] at hW
    exact ggRC_weylReflGroup_of_linWeyl ι _ hW

end CFSG.StandardType
