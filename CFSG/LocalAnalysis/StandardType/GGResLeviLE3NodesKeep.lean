module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Nodes
public import CFSG.LocalAnalysis.StandardType.GGTWAlign

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLE3_three_nodes_keep {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs X J Y : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hXd : GGResXDatumA p Bs X (N - 1)) (hXs : GGResTwoNodeSideDatum p Bs X J)
    (hY : GGResLeviSideDatumLE3 p Bs Y J) (hY2 : ¬ GGResTwoNodeSideDatum p Bs Y J) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      Fintype.card Λ = N ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
        (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
        (∃ f : M.Group ≃* ↥(ggAutomizer Y Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
        ggAutomizer Y Bs = Subgroup.closure (Set.range φ) := by
  classical
  obtain ⟨Λ₀, i1₀, i2₀, M₀, C₀, V₀, i3₀, i4₀, ι₀, φ₀, h₀, α₀, e₀, hM₀, hW₀, hC₀,
    hlin₀, hrefl₀, hpair₀, hf₀ex, hclos₀⟩ := hXd
  letI := i1₀
  letI := i2₀
  letI := i3₀
  letI := i4₀
  obtain ⟨f₀, hf₀⟩ := hf₀ex
  obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hWM, hC, hWMJ, hMJ,
    hlin, hrefl, hpair, hfex, hclos, hfJex, hclosJ, hconj⟩ := hXs
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  obtain ⟨f, hf⟩ := hfex
  obtain ⟨fJ, hfJ⟩ := hfJex
  obtain ⟨e, hM⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 (by omega) hBs (ggAutomizer X Bs)
      e₀ hM₀ hW₀ f₀ φ₀ hf₀ hrefl₀ hWM f φ hf hrefl
  obtain ⟨eJ, hMJ'⟩ := ggTW_twoNode_J_typeA hN5 e hM hb hWMJ hMJ
  obtain ⟨ΛY, i1Y, i2Y, S, MY, CY, MJY, VY, i3Y, i4Y, ιY, φY, hY, αY, hS1, hS2, hWMY,
    hCY, hWMJY, hMJY, hlinY, hreflY, hpairY, hfYex, hclosY, hfJYex, hclosJY, hconjY⟩ := hY
  letI := i1Y
  letI := i2Y
  letI := i3Y
  letI := i4Y
  obtain ⟨fY, hfY⟩ := hfYex
  obtain ⟨fJY, hfJY⟩ := hfJYex
  have hS3 : S.card = 3 := by
    rcases (by omega : S.card = 2 ∨ S.card = 3) with h2 | h3
    · exact absurd (ggResTwoNodeSideDatum_of_leviLE3_card_two (p := p) h2 ιY φY hY αY hWMY hCY
        hWMJY hMJY hlinY hreflY hpairY ⟨fY, hfY⟩ hclosY ⟨fJY, hfJY⟩ hclosJY hconjY) hY2
    · exact h3
  obtain ⟨eY, hMJY'⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 3) hp2 (by omega) hBs (ggAutomizer J Bs)
      eJ hMJ' hWMJ fJ (fun j => φ j) hfJ (fun j => hrefl j) hWMJY fJY
      (fun j => φY j) hfJY (fun j => hreflY j)
  have hcardJ : Fintype.card {j : ΛY // j ∉ S} = N - 3 := by
    have h := (Fintype.card_congr eY).symm
    simpa using h
  have hcardS : Fintype.card {j : ΛY // j ∈ S} = S.card := by
    simpa using Fintype.card_coe S
  have hcard : Fintype.card ΛY = N := by
    have h := Fintype.card_subtype_compl (fun j : ΛY => j ∈ S)
    rw [hcardJ, hcardS, hS3] at h
    omega
  exact ⟨ΛY, i1Y, i2Y, MY, CY, VY, i3Y, i4Y, ιY, φY, hY, αY, hcard, hWMY, hCY, hlinY, hreflY,
    hpairY, ⟨fY, hfY⟩, hclosY⟩

end CFSG.StandardType

end
