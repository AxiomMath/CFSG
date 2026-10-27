module

public import CFSG.Sporadic.LyI301.RowMax
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyAllInnerThm

public noncomputable section

namespace CFSG.Sporadic.LyI301

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.LyonsSims CFSG.Certificates
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301


theorem ly_cfg {G : Type} [Group G] [Finite G] {t : G}
    {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)} {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
    (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hOut : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) :
    I301ARowCfg .ly (lyR ρ) (lyB1 x₁ x₂ x₃) (x₁ : G) where
  hR := ly_hR D
  hB := ly_hB D S
  hBN := ly_hBN D S
  hd := ly_hd S
  hI := ly_hI D S
  hK := ly_hK D S
  hR0 := ly_hR0 D S
  hR0t := Or.inl (ly_hR0t D S)
  hK6 := Or.inl rfl
  hNL := fun h => absurd h (by decide)
  hMax := ly_hMax D S hOut

theorem i301ARow_ly : I301ARow .ly := by
  intro _ K _ _ hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  obtain rfl : i = .sporadic .Ly := hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  have eK : K ≃* CFSG.Blueprint.NativeSporadic.Ly := e.trans b.symm
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult.oneClassDoubleCover_of_ly ⟨eK⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  exact ⟨_, _, _, ly_cfg D S (CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut.lyAllInner_thm K ⟨eK⟩)⟩

end CFSG.Sporadic.LyI301
