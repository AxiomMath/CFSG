module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWAlign
public import CFSG.LocalAnalysis.StandardType.GGTWPositions
public import CFSG.LocalAnalysis.StandardType.GGResConjWire

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTW_align_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L J K : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hXL : GGResXDatumA p Bs L (N - 1)) (hLd : GGResTwoNodeSideDatum p Bs L J)
    (hK : GGResSideDatum p Bs K J) : GGTWAligned p N 1 Bs L J K := by
  obtain ⟨Λ, iΛf, iΛd, b₁, b₂, Λa, iΛaf, iΛad, ML, CL, MK, CK, V, iVadd, iVmod, ι, φ, h, α,
    hb, hcard, hWML, hCL, hWMK, hCK, hlin, hrefl, hpairL, hpairK, fLex, fKex,
    hclosL, hclosK, hconn, hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_one ggWeylSimpleSystemsConjInput_holds hp2 hLd hK
  obtain ⟨Λ₁, iΛ₁f, iΛ₁d, M₁, C₁, V₁, iV₁add, iV₁mod, ι₁, φ₁, h₁, α₁, e₁,
    hM₁, hWM₁, hC₁, hlin₁, hrefl₁, hpair₁, f₁ex, hclos₁⟩ := hXL
  obtain ⟨fL, hfL⟩ := fLex
  obtain ⟨f₁, hf₁⟩ := f₁ex
  letI := iΛf; letI := iΛd; letI := iΛaf; letI := iΛad
  letI := iVadd; letI := iVmod
  letI := iΛ₁f; letI := iΛ₁d; letI := iV₁add; letI := iV₁mod
  have hn : 2 ≤ N - 1 := by omega
  let φ₂ : Λ → MulAut ↥Bs := fun i => φ (Sum.inl i)
  have hf₂ : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ₂ i := hfL
  have hrefl₂ : ∀ i, GGIsReflection p (φ₂ i) := fun i => hrefl (Sum.inl i)
  obtain ⟨e₂, hML₂⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 hn hBs (ggAutomizer L Bs) e₁ hM₁ hWM₁
      f₁ φ₁ hf₁ hrefl₁ hWML fL φ₂ hf₂ hrefl₂
  obtain ⟨pos, e', hML₃, hiff⟩ := ggTW_positions hN5 e₂ hML₂ hb hconn
  exact ⟨pos, Λ, iΛf, iΛd, b₁, b₂, Λa, iΛaf, iΛad, ML, CL, MK, CK, V, iVadd, iVmod,
    ι, φ, h, α, e', hb, hcard, hiff, hML₃, hWML, hCL, hWMK, hCK,
    (fun h12 => absurd h12 (by norm_num)), hlin, hrefl, hpairL, hpairK, hclosL, hclosK, hclosJ⟩

end CFSG.StandardType
