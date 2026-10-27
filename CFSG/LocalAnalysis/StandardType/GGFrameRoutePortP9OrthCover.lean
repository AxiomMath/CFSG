module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDCoverTwo
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.HardMathSupport.Foote.E27.Q2OrthPlus
import CFSG.HardMathSupport.Foote.E27.Q2OrthMinus
import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
import CFSG.HardMathSupport.Foote.E27.TableMat
import Certificates.Data.E27Q2O

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

theorem false_of_tableB_matConj_of_not_dvd {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Finite F] {H : Subgroup (GL ι F)} {S : Set (GL ι F)}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι F))) (hGL : ¬ 3 ^ 6 ∣ Nat.card (GL ι F))
    {r : ℕ} {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj H}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 r (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S)
      L' ψ A)
    (hcard : 3 ^ 6 ≤ Nat.card A) : False := by
  obtain ⟨hψ, hker, hperf, hAeb, hAI, -, -, -⟩ := hTB
  have hdvd : Nat.card (TypeA.inducedSub ψ A) ∣ Nat.card (GL ι F) :=
    TwoThree.card_dvd_of_subset_matConjImage hS (by
      rintro x ⟨a, ha, hxa⟩
      obtain ⟨φ, hφI, hφa⟩ := hAI a ha
      exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφI)
  have hcardA : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φ, _, hφa⟩ := hAI a ha
      exact ⟨φ, hφa⟩)
  rw [hcardA] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hAeb)
  have hk6 : 6 ≤ k :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by rw [← hk]; exact hcard)
  exact hGL ((pow_dvd_pow 3 hk6).trans (hk ▸ hdvd))

theorem not_dvd_card_GL_four_of_card_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) : ¬ 3 ^ 6 ∣ Nat.card (GL (Fin 4) F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field]
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [hq, Fin.prod_univ_four]
  norm_num

theorem not_dvd_card_GL_two_of_card_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) : ¬ 3 ^ 6 ∣ Nat.card (GL (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field]
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [hq, Fin.prod_univ_two]
  norm_num

theorem not_dvd_card_GL_four_of_card_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) : ¬ 3 ^ 6 ∣ Nat.card (GL (Fin 4) F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field]
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [hq, Fin.prod_univ_four]
  norm_num

theorem card_le_of_tableB_rPlus {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {m r : ℕ} (hm : 1 ≤ m) (hZ : Subgroup.center (OrthRest.RPlus F m) = ⊥)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* OrthRest.RPlus F m}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 r (OrthRest.RPlus F m) (LargeEvenInnSet (OrthRest.RPlus F m))
      L' ψ A) :
    Nat.card A ≤ 3 ^ m := by
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (K := F) (p := 2) (k := 1) Nat.prime_two (by norm_num) (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨hψ, hker, hperf, hAeb, hAI, -, -, -⟩ := hTB
  have hX := TypeA.isElemAbelian_inducedSub hψ hAeb
  have hcard : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φ, _, hφa⟩ := hAI a ha
      exact ⟨φ, hφa⟩)
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut (OrthRest.RPlus F m))) :
      Set (MulAut (OrthRest.RPlus F m))) ⊆
      Set.range (MulAut.conj : OrthRest.RPlus F m →* MulAut (OrthRest.RPlus F m)) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφ
  obtain ⟨E, hE, hEcard⟩ := TableBSymp.exists_of_subset_inn hZ hXI hX
  have hle := OrthRest.card_le_plus hm Nat.prime_three (by norm_num) E hE
  rwa [hEcard, hcard] at hle

theorem card_le_of_tableB_rMinus {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {m r : ℕ} {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hZ : Subgroup.center (OrthRest.RMinus F m b c) = ⊥)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* OrthRest.RMinus F m b c}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 r (OrthRest.RMinus F m b c)
      (LargeEvenInnSet (OrthRest.RMinus F m b c)) L' ψ A) :
    Nat.card A ≤ 3 ^ (m + 1) := by
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (K := F) (p := 2) (k := 1) Nat.prime_two (by norm_num) (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨hψ, hker, hperf, hAeb, hAI, -, -, -⟩ := hTB
  have hX := TypeA.isElemAbelian_inducedSub hψ hAeb
  have hcard : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φ, _, hφa⟩ := hAI a ha
      exact ⟨φ, hφa⟩)
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut (OrthRest.RMinus F m b c))) :
      Set (MulAut (OrthRest.RMinus F m b c))) ⊆
      Set.range (MulAut.conj : OrthRest.RMinus F m b c →* MulAut (OrthRest.RMinus F m b c)) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφ
  obtain ⟨E, hE, hEcard⟩ := TableBSymp.exists_of_subset_inn hZ hXI hX
  have hle := OrthRest.card_le_minus hbc Nat.prime_three (by norm_num) E hE
  rwa [hEcard, hcard] at hle

private theorem orthCoverAux_false_of_matConj {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Finite F] {H : Subgroup (GL ι F)} {S : Set (GL ι F)}
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι F))) (hGL : ¬ 3 ^ 6 ∣ Nat.card (GL ι F))
    (hBs : IsElemAbelian 3 Bs)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hperf : commutator K = ⊤) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj H)
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hrk : Nat.card (ggGamma K hN).range = 3 ^ (n - 1))
    (hA6 : 3 ^ 6 ≤ Nat.card (ggGamma K hN).range) : False := by
  have hTB : GGTorusTBGroup 3 (n - 1) (LargeEvenProj H)
      (LargeEvenMatConjImage (LargeEvenProjMk H) S) K (ggQuotHom θ)
      (ggGamma K hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hBstar hperf θ hN
      (fun b hb => ggLAut_mem_of_induces K θ hN hind hb) (by rw [hrk])
      (le_trans (by norm_num : 3 ^ 3 ≤ 3 ^ 6) hA6)
  exact false_of_tableB_matConj_of_not_dvd (F := F) (H := H) (S := S) hS hGL hTB hA6

private theorem orthCoverAux_nonempty_statedProjOmega_plus {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (m : ℕ) :
    Nonempty (StatedProj (StatedOmega (StatedQuadPlus m F)) ≃*
      ↥(StatedOmega (StatedQuadPlus m (ZMod 2)))) :=
  ⟨CFSG.HardMathSupport.Foote.E27.Q2.statedProjOmegaEquiv (StatedQuadPlus m F) hF
    (StatedQuadPlus m (ZMod 2))
    (fun v σ => CFSG.HardMathSupport.Foote.E27.Q2.quadPlus_comp m σ v)⟩

private theorem orthCoverAux_nonempty_statedProjOmega_minus {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (m : ℕ) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (StatedProj (StatedOmega (StatedQuadMinus m F b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))) :=
  ⟨CFSG.HardMathSupport.Foote.E27.Q2.statedProjOmegaEquiv (StatedQuadMinus m F b c) hF
    (StatedQuadMinus m (ZMod 2) 1 1)
    (fun v σ => CFSG.HardMathSupport.Foote.E27.Q2.quadMinus_comp m σ hirr v)⟩

theorem native_orth_equiv_of_innerDiagOnLabel
    {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8)
    (hz : z ∈ Bs) (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) :
    (∃ a : ℕ, n - 1 ≤ a ∧ Nonempty (K ≃* StatedOmega (StatedQuadPlus a (ZMod 2))) ∧
        GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = a ∧ lab.n = 1) 3 Bs K) ∨
      ∃ a : ℕ, n - 1 ≤ a ∧ Nonempty (K ≃* StatedOmega (StatedQuadMinus a (ZMod 2) 1 1)) := by
  obtain ⟨hperf, lab, hlab, hraw0⟩ := hK
  obtain ⟨tag, rank, nlab⟩ := lab
  have hSlab : S 3 ⟨tag, rank, nlab⟩ := by
    obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw0
    obtain ⟨-, -, _, hP⟩ := hQ
    exact hP.1
  obtain ⟨htagS, hn1S⟩ := hS ⟨tag, rank, nlab⟩ hSlab
  have hrk := P9_Wa_card_range hBs hcard hz hz1 hN hker
  have hA6 : 3 ^ 6 ≤ Nat.card (ggGamma K hN).range := by
    rw [hrk]
    rcases hn with rfl | rfl <;> norm_num
  rcases htagS with hD | htwD
  · subst hD
    subst hn1S
    have hrawFold := hraw0
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw0
    by_cases h3 : rank = 3
    · rw [if_pos h3] at hraw0
      obtain ⟨K0, hfield, hfin, hKcard, hq⟩ := hraw0
      obtain ⟨-, -, θ, hP⟩ := hq
      obtain ⟨-, hBsN, hind⟩ := hP
      have hKcard2 : Nat.card K0 = 2 := by rw [hKcard]; norm_num
      have hSsub : (Set.univ : Set (GL (Fin 4) K0)) ⊆
          Subgroup.normalizer (LargeEvenSLGroup (Fin 4) K0 : Set (GL (Fin 4) K0)) := by
        intro x _
        rw [Subgroup.normalizer_eq_top_iff.mpr
          (inferInstance : (LargeEvenSLGroup (Fin 4) K0).Normal)]
        exact Subgroup.mem_top x
      exfalso
      exact orthCoverAux_false_of_matConj (F := K0) (H := LargeEvenSLGroup (Fin 4) K0)
        (S := Set.univ) hSsub (not_dvd_card_GL_four_of_card_two hKcard2) hBs hBstar hperf hN
        θ hind hrk hA6
    · have hmark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = rank ∧
          lab.n = 1) 3 Bs K :=
        ⟨hperf, ⟨.D, rank, 1⟩, hlab,
          largeEvenRawDatum_mono (lab := ⟨.D, rank, 1⟩) (fun R' _ I' F'
            ⟨hs, hna, θ', hP'⟩ => ⟨hs, hna, θ', ⟨⟨rfl, rfl, rfl⟩, hP'.2⟩⟩) hrawFold⟩
      rw [if_neg h3] at hraw0
      obtain ⟨K0, hfield, hfin, hKcard, hq⟩ := hraw0
      obtain ⟨hsimple, hnab, θ, hP⟩ := hq
      obtain ⟨-, hBsN, hind⟩ := hP
      have hKcard2 : Nat.card K0 = 2 := by rw [hKcard]; norm_num
      have hr4 : 4 ≤ rank := by
        have h : 3 ≤ rank := by simpa using hlab.2
        omega
      have hTB : GGTorusTBGroup 3 (n - 1) (OrthRest.RPlus K0 rank)
          (LargeEvenInnSet (OrthRest.RPlus K0 rank)) K (ggQuotHom θ)
          (ggGamma K hN).range :=
        ggTorusTBGroup_of_marking Nat.prime_three hBs hBstar hperf θ hN
          (fun b hb => ggLAut_mem_of_induces K θ hBsN hind hb) (by rw [hrk])
          (le_trans (by norm_num : 3 ^ 3 ≤ 3 ^ 6) hA6)
      have hZ : Subgroup.center (OrthRest.RPlus K0 rank) = ⊥ :=
        @TableBUE.center_eq_bot_of_simple (OrthRest.RPlus K0 rank) _ hsimple hnab
      have hAle := card_le_of_tableB_rPlus hKcard2 (m := rank) (r := n - 1)
        (by omega : 1 ≤ rank) hZ hTB
      have hnr : n - 1 ≤ rank :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by rw [← hrk]; exact hAle)
      have hinj := rPlus_injective_of_cover_two hKcard2 (by omega : 5 ≤ rank) ↥K
        (ggQuotHom θ) hTB.1 hTB.2.1 hperf
      let eK : ↥K ≃* StatedProj (StatedOmega (StatedQuadPlus rank K0)) :=
        MulEquiv.ofBijective (ggQuotHom θ) ⟨hinj, hTB.1⟩
      obtain ⟨eField⟩ := orthCoverAux_nonempty_statedProjOmega_plus hKcard2 rank
      exact Or.inl ⟨rank, hnr, ⟨eK.trans eField⟩, hmark⟩
  · subst htwD
    subst hn1S
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw0
    by_cases h2 : rank = 2
    · rw [if_pos h2] at hraw0
      obtain ⟨K0, hfield, hfin, hKcard, hq⟩ := hraw0
      obtain ⟨-, -, θ, hP⟩ := hq
      obtain ⟨-, hBsN, hind⟩ := hP
      have hKcard2 : Nat.card K0 = 4 := by rw [hKcard]; norm_num
      have hSsub : (Set.univ : Set (GL (Fin 2) K0)) ⊆
          Subgroup.normalizer (LargeEvenSLGroup (Fin 2) K0 : Set (GL (Fin 2) K0)) := by
        intro x _
        rw [Subgroup.normalizer_eq_top_iff.mpr
          (inferInstance : (LargeEvenSLGroup (Fin 2) K0).Normal)]
        exact Subgroup.mem_top x
      exfalso
      exact orthCoverAux_false_of_matConj (F := K0) (H := LargeEvenSLGroup (Fin 2) K0)
        (S := Set.univ) hSsub (not_dvd_card_GL_two_of_card_four hKcard2) hBs hBstar hperf hN
        θ hind hrk hA6
    · rw [if_neg h2] at hraw0
      by_cases h3 : rank = 3
      · rw [if_pos h3] at hraw0
        obtain ⟨K0, hfield, hfin, hKcard, hq⟩ := hraw0
        obtain ⟨-, -, θ, hP⟩ := hq
        obtain ⟨-, hBsN, hind⟩ := hP
        have hKcard2 : Nat.card K0 = 4 := by rw [hKcard]; norm_num
        have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K0 :=
          ⟨Nat.prime_two, le_rfl, by rw [hKcard2]; norm_num⟩
        have hSsub : LargeEvenGUSet (Fin 4) K0 (2 ^ 1) ⊆
            Subgroup.normalizer (LargeEvenSUGroup (Fin 4) K0 (2 ^ 1) :
              Set (GL (Fin 4) K0)) :=
          TableBUE.gu_subset_normalizer (n := 1) (d := 4) hUF
        exfalso
        exact orthCoverAux_false_of_matConj (F := K0)
          (H := LargeEvenSUGroup (Fin 4) K0 (2 ^ 1))
          (S := LargeEvenGUSet (Fin 4) K0 (2 ^ 1)) hSsub
          (not_dvd_card_GL_four_of_card_four hKcard2) hBs hBstar hperf hN θ hind hrk hA6
      · rw [if_neg h3] at hraw0
        obtain ⟨K0, hfield, hfin, hKcard, b, c, hirr, hq⟩ := hraw0
        obtain ⟨hsimple, hnab, θ, hP⟩ := hq
        obtain ⟨-, hBsN, hind⟩ := hP
        have hKcard2 : Nat.card K0 = 2 := by rw [hKcard]; norm_num
        have hr4 : 4 ≤ rank := by
          have h : 2 ≤ rank := by simpa using hlab.2
          omega
        have hTB : GGTorusTBGroup 3 (n - 1) (OrthRest.RMinus K0 (rank - 1) b c)
            (LargeEvenInnSet (OrthRest.RMinus K0 (rank - 1) b c)) K (ggQuotHom θ)
            (ggGamma K hN).range :=
          ggTorusTBGroup_of_marking Nat.prime_three hBs hBstar hperf θ hN
            (fun b hb => ggLAut_mem_of_induces K θ hBsN hind hb) (by rw [hrk])
            (le_trans (by norm_num : 3 ^ 3 ≤ 3 ^ 6) hA6)
        have hZ : Subgroup.center (OrthRest.RMinus K0 (rank - 1) b c) = ⊥ :=
          @TableBUE.center_eq_bot_of_simple (OrthRest.RMinus K0 (rank - 1) b c) _ hsimple hnab
        have hAle := card_le_of_tableB_rMinus hKcard2 (m := rank - 1) (r := n - 1)
          hirr hZ hTB
        have hAle' : Nat.card (ggGamma K hN).range ≤ 3 ^ rank := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ rank)] at hAle
          exact hAle
        have hnr : n - 1 ≤ rank :=
          (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by rw [← hrk]; exact hAle')
        have hinj := rMinus_injective_of_cover_two hKcard2 (by omega : 3 ≤ rank - 1) hirr
          ↥K (ggQuotHom θ) hTB.1 hTB.2.1 hperf
        let eK : ↥K ≃* StatedProj (StatedOmega (StatedQuadMinus rank K0 b c)) :=
          (MulEquiv.ofBijective (ggQuotHom θ) ⟨hinj, hTB.1⟩).trans
            (omegaMinusProjEquiv rank b c)
        obtain ⟨eField⟩ := orthCoverAux_nonempty_statedProjOmega_minus hKcard2 rank hirr
        exact Or.inr ⟨rank, hnr, ⟨eK.trans eField⟩⟩

end CFSG.StandardType.FrameRoute

end
