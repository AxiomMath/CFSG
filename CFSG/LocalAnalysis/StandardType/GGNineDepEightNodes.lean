module

public import CFSG.LocalAnalysis.StandardType.GGTWAlign
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Nodes
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNine_xdatum_of_side {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} (h : GGResTwoNodeSideDatum p Bs X J) : GGResXDatum p Bs X := by
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hW, hC, hWJ, hMJ, hlin, hrefl,
    hpair, hf, hcl, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, hW, hC, hlin, hrefl, hpair, hf, hcl⟩

theorem ggTwoNode_L_weyl {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs K L J : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hXd : GGResXDatumA p Bs K (N - 1)) (hKs : GGResTwoNodeSideDatum p Bs K J)
    (hLs : GGResTwoNodeSideDatum p Bs L J) :
    ∃ M : CoxeterMatrix (Fin (N - 1)), GGIsWeylMatrix M ∧ Nonempty (M.Group ≃* ↥(ggAutomizer L Bs)) := by
  classical
  obtain ⟨Λ₀, i1₀, i2₀, M₀, C₀, V₀, i3₀, i4₀, ι₀, φ₀, h₀, α₀, e₀, hM₀, hW₀, hC₀,
    hlin₀, hrefl₀, hpair₀, hf₀ex, hclos₀⟩ := hXd
  letI := i1₀
  letI := i2₀
  letI := i3₀
  letI := i4₀
  obtain ⟨f₀, hf₀⟩ := hf₀ex
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hWM, hC, hWMJ, hMJ,
    hlin, hrefl, hpair, hfex, hclos, hfJex, hclosJ, hconj⟩ := hKs
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  obtain ⟨f, hf⟩ := hfex
  obtain ⟨fJ, hfJ⟩ := hfJex
  obtain ⟨e, hM⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega) hBs (ggAutomizer K Bs)
      e₀ hM₀ hW₀ f₀ φ₀ hf₀ hrefl₀ hWM f φ hf hrefl
  obtain ⟨eJ, hMJ'⟩ := ggTW_twoNode_J_typeA (N := N) (by omega) e hM hb hWMJ hMJ
  obtain ⟨ΛL, l1, l2, c₁, c₂, ML, CL, MJL, VL, l3, l4, ιL, φL, hL, αL, hc, hWML, hCL, hWMJL,
    hMJL, hlinL, hreflL, hpairL, hfLex, hclosL, hfJLex, hclosJL, hconjL⟩ := hLs
  letI := l1
  letI := l2
  letI := l3
  letI := l4
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨fJL, hfJL⟩ := hfJLex
  obtain ⟨eL, hMJL'⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 3) hp2 (by omega) hBs (ggAutomizer J Bs)
      eJ hMJ' hWMJ fJ (fun j => φ j) hfJ (fun j => hrefl j) hWMJL fJL
      (fun j => φL j) hfJL (fun j => hreflL j)
  have hcardJ : Fintype.card {j : ΛL // j ≠ c₁ ∧ j ≠ c₂} = N - 3 := by
    have h6 := (Fintype.card_congr eL).symm
    simpa using h6
  have hcard : Fintype.card ΛL = N - 1 := by
    have hsub : (Finset.univ.filter fun j : ΛL => j ≠ c₁ ∧ j ≠ c₂) = Finset.univ \ {c₁, c₂} := by
      ext j
      simp [not_or]
    have h1 : Fintype.card {j : ΛL // j ≠ c₁ ∧ j ≠ c₂} =
        (Finset.univ.filter fun j : ΛL => j ≠ c₁ ∧ j ≠ c₂).card := Fintype.card_subtype _
    have h2 : (Finset.univ \ {c₁, c₂}).card = Fintype.card ΛL - ({c₁, c₂} : Finset ΛL).card :=
      Finset.card_univ_sdiff _
    have h3 : ({c₁, c₂} : Finset ΛL).card = 2 := Finset.card_pair hc
    have h4 : ({c₁, c₂} : Finset ΛL).card ≤ Fintype.card ΛL := Finset.card_le_univ _
    rw [hsub, h2, h3] at h1
    omega
  let σ : Fin (N - 1) ≃ ΛL := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨ML.reindex σ.symm, l05nBL_weyl_reindex hWML σ.symm,
    ⟨(ML.reindexGroupEquiv σ.symm).trans fL⟩⟩

end CFSG.StandardType

end
