module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdEven
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdOdd
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdL2
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdCent
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdModel
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3IdentBranch
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdTop
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdTheta
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenFinalAll
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.RankThree.SubgroupLists.LinearTwoFamily

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi zPi)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedClassicalModel)
open Matrix (ProjGenLinGroup)

theorem nonempty_alt6_of_psl29 {K : Type} [Group K] (h : StatedClassicalModel K .PSL 2 3 2) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  let _ : Fintype F := Fintype.ofFinite F
  have hF9 : Fintype.card F = 9 := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨e6⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      F hF9
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
    F).symm).trans e6⟩


theorem simpleHeis148_of (hIrr : EvenSL3Irred) (hSub : SubHeis148) : SimpleHeis148 := by
  intro X _ _ P K₀ Q D hH _ hZ _ hPe hP9 hb hQ hh hK hKs hnab
  obtain ⟨π, p, f, F, _, hF, hqF, φ, y₁, y₂, ζ, hy₁, hy₂, hy₁3, hy₂3, hζ1, hζ, hact⟩ := hH
  haveI : Fact p.Prime := ⟨hF.prime⟩
  have hiso : Sec4.IsoLThreePi X p f := isoLThreePi_of_model hF hqF φ
  have hbd := hb p f hF.one_le hiso
  have hinv := Ronan148B.inv_of_hyp hZ hh
  have hfaith : ∀ σ ∈ P, (∀ k ∈ K₀, σ k = k) → σ = 1 := fun σ hσ h =>
    Ronan148B.eq_one_of_trivial hh hσ h
  have hsub := hSub X P K₀ Q D π p f F hF hqF φ y₁ y₂ ζ hy₁ hy₂ hy₁3 hy₂3 hζ1 hζ hact hZ hPe
    hP9 hQ hh hK hKs
  have halt6 : StatedClassicalModel ↥K₀ .PSL 2 3 2 → Ronan148B.L3Ident148 P K₀ := fun h => by
    obtain ⟨φ6⟩ := nonempty_alt6_of_psl29 h
    exact Ronan148B.l3Ident148_of_alt6 hZ hPe hP9 hh φ6
  by_cases hp2 : p = 2
  · subst hp2
    rcases even_ident hIrr hF hqF φ hy₁ hy₂ hy₁3 hy₂3 hζ1 hζ hact hP9 hinv hKs hnab with
        h | ⟨f₁, hf₁, h⟩
    · exact halt6 h
    · exact hsub f₁ hf₁ (Or.inl rfl) h
  · have hf2 : f ≤ 2 := hbd.resolve_left hp2
    rcases odd_ident hp2 hF.one_le hf2 hiso hKs hnab hK with
        ⟨r, k, hr, hr2, hk, hM⟩ | ⟨f₁, hf₁, hf₁2, h⟩ | hφ7
    ·
      have hsolv : ∀ σ ∈ P, σ ≠ 1 → Group.IsSolvable (Sec4.autFix σ) := by
        intro σ hσ hσ1
        obtain ⟨i, j, hij⟩ := hact σ hσ
        have hyZ : y₁ ^ i * y₂ ^ j ∉ zPi π 3 (p ^ f) F := by
          intro hz
          obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hF hqF
          have hs := Sec4.mem_statedScalars_of_mem_zPi hF hqF hτ hτ1 hz
          have h1 := Sec4.mk_eq_one_iff_mem_statedScalars.mpr hs
          apply hσ1
          ext z
          apply φ.injective
          apply Subtype.ext
          rw [hij z, h1, one_mul, inv_one, mul_one]
          rfl
        have hty := type13_of_heisAct hF hqF hy₁ hy₂ hy₁3 hy₂3 hζ1 hζ hyZ
        exact (fix_solvable_of_type13 hF hqF φ hty (hij)).1
      obtain ⟨rfl, rfl⟩ := l2_ident hKs hinv hfaith hP9 (fun σ hσ => hPe.2 σ hσ) hsolv
        (fun E hE => oddThreeRank X p f hF.one_le hiso E hE) hr hr2 hk hM
      exact halt6 hM
    · exact hsub f₁ hf₁ (Or.inr hf₁2) h
    · obtain ⟨φ7⟩ := hφ7
      exact Ronan148B.l3Ident148_of_alt7 hZ hPe hP9 hh φ7

theorem kf148SigGenL3Ident_of_sub (hSub : SubHeis148) : Ronan148B.KF148SigGenL3Ident :=
  kf148SigGenL3Ident_of_heis (l3IdentHeis_of thetaHeis148 (simpleHeis148_of evenSL3Irred hSub))

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
