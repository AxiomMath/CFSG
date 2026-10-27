module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitDefs
public import CFSG.LocalAnalysis.StandardType.GGSLBstarFrame
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane
  CFSG.SeitzReduction.LinearPilot

namespace WitSL

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F]

theorem exists_mem_ggInducedPairs {φ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {b : G}
    {D : GL (Fin (m + 1)) F} {t : Fin (m + 1) → F}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (SLRep.slConj (m + 1) F D s)) :
    ∃ d : Fin (m + 1) → Fˣ, (∀ k, (d k : F) = t k) ∧
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs φ := by
  refine ⟨fun k => Units.mk0 (t k) (SLRep.ne_zero_of_diagonal hD k), fun k => rfl, ?_⟩
  have hDd : InnerDiagA.diagGL (fun k => Units.mk0 (t k) (SLRep.ne_zero_of_diagonal hD k)) = D := by
    apply Units.ext
    rw [InnerDiagA.coe_diagGL, hD]
    rfl
  rw [LinFusion.mem_ggInducedPairs]
  intro u
  rw [hb u, hDd]
  congr 1
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL,
    ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]

theorem ggDiagSL_mem_blockSpecialLinear [CharP F 2] {δ : Fin (m + 1) → F} (hδ : ∏ i, δ i = 1)
    {I : Finset (Fin (m + 1))} (hI : ∀ k ∉ I, δ k = 1) :
    ggDiagSL δ hδ ∈ blockSpecialLinear (K := F) I := by
  intro a c hac
  change diagonal δ a c = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a c
  by_cases h : a = c
  · subst h
    rw [diagonal_apply_eq, one_apply_eq]
    exact hI a (by tauto)
  · rw [diagonal_apply_ne _ h, one_apply_ne h]

@[expose] noncomputable def rootDiag (j₁ j₂ : Fin (m + 1)) (ζ : F) : Fin (m + 1) → F :=
  Function.update (Function.update (fun _ => (1 : F)) j₁ ζ) j₂ ζ⁻¹

theorem rootDiag_apply_left {j₁ j₂ : Fin (m + 1)} (h : j₁ ≠ j₂) (ζ : F) :
    rootDiag j₁ j₂ ζ j₁ = ζ := by
  rw [rootDiag, Function.update_of_ne h, Function.update_self]

theorem rootDiag_apply_right (j₁ j₂ : Fin (m + 1)) (ζ : F) : rootDiag j₁ j₂ ζ j₂ = ζ⁻¹ := by
  rw [rootDiag, Function.update_self]

theorem rootDiag_apply_of_ne {j₁ j₂ k : Fin (m + 1)} (h₁ : k ≠ j₁) (h₂ : k ≠ j₂) (ζ : F) :
    rootDiag j₁ j₂ ζ k = 1 := by
  rw [rootDiag, Function.update_of_ne h₂, Function.update_of_ne h₁]

theorem prod_rootDiag {j₁ j₂ : Fin (m + 1)} (h : j₁ ≠ j₂) {ζ : F} (hζ : ζ ≠ 0) :
    ∏ i, rootDiag j₁ j₂ ζ i = 1 := by
  rw [rootDiag, SLRep.prod_update_update_const h, one_pow, mul_one, inv_mul_cancel₀ hζ]

theorem rootDiag_pow {j₁ j₂ : Fin (m + 1)} {p : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (k : Fin (m + 1)) : rootDiag j₁ j₂ ζ k ^ p = 1 := by
  by_cases h₂ : k = j₂
  · subst h₂
    rw [rootDiag_apply_right, inv_pow, hζ.pow_eq_one, inv_one]
  by_cases h₁ : k = j₁
  · subst h₁
    rw [rootDiag_apply_left (Ne.symm (Ne.symm h₂)), hζ.pow_eq_one]
  · rw [rootDiag_apply_of_ne h₁ h₂, one_pow]

end WitSL

section Inputs

theorem ggSixSeventeenWitnessOn_PSLSplit : GGSixSeventeenWitnessOn GGPSLSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  obtain ⟨rfl, hpq⟩ := hP
  have hadm := hctx.2.2.2.1.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  obtain ⟨A₀, hframe⟩ := ggSLBstarFrameInput_holds G p B Bs x L D J m f ψ hctx s1 hpq
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hcardF]; exact hpq
  have hq4 : 4 ≤ 2 ^ f := by
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 := Nat.le_of_dvd (by omega) hpq
    have h3 := hp.two_le
    have h5 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := hcardF ▸ hq4
  have hf2 : 2 ≤ f := by
    by_contra hf2
    interval_cases f
    omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  set φ := SLRep.ggFrame ψ A₀ with hφ
  have hrangeφ : φ.range = ggG0 p B x L D J := (SLRep.range_ggFrame ψ A₀).trans hrange
  have hkerφ := SLRep.ker_ggFrame_le hker A₀
  have hcentφ : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hrangeφ]; exact s1.1
  have hBs : GGBstar p B Bs := hctx.2.1
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hm4 : 4 ≤ m := by
    have hBs' := SLRep.card_le_of_frame hp hpF hkerφ hcentφ (X := Bs)
      (fun c hc => hBs.2.1.2 c hc) hframe (S := {0}) (i₀ := 0)
      (fun c _ D' t' _ _ i hi => by rw [Finset.mem_singleton.mp hi])
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at hBs'
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hBs')
    omega
  obtain ⟨Db, tb, hDb, hbD⟩ := hframe b hpair.1
  obtain ⟨db, -, hbI⟩ := WitSL.exists_mem_ggInducedPairs hDb hbD
  have hL' : IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer (Set.range fun _ : Unit => b)) := by
    rw [Set.range_const, hrangeφ]
    exact hpair.2.2.1
  obtain ⟨i, hi⟩ := LinSemisimple.exists_eq_map_blockSpecialLinear_of_isComponentOf hkerφ
    (d := fun _ : Unit => db) (b := fun _ => b) (fun _ => hbI) hL'
  set I := LinSemisimple.eigClass (fun _ : Unit => db) i with hI
  obtain ⟨hI2, -⟩ := LinSemisimple.two_le_card_of_isQuasisimple_le hL'.2.2 hi.le
  have hI3 : 3 ≤ I.card := by
    by_contra hlt
    have hI2' : I.card = 2 := by omega
    apply hpair.2.2.2
    refine Or.inr (Or.inr (Or.inl ⟨rfl, hpq, ?_⟩))
    rw [hi]
    exact LinTypeAk.lieModel_map_blockSpecialLinear_of_card_two hcardF hf2 hkerφ hI2'
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.mp (show 1 < I.card by omega)
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζi1 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
  set δ := WitSL.rootDiag j₁ j₂ ζ with hδdef
  have hδ : ∏ k, δ k = 1 := WitSL.prod_rootDiag hj hζ0
  set de := ggDiagSL δ hδ with hde
  have hdeδ : (de : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = diagonal δ := rfl
  have heBs : φ de ∈ Bs :=
    SLRep.mem_of_frame_diagonal_inner hBs hframe hdeδ
      (SLRep.ggDiagSL_pow_eq_one hδ (WitSL.rootDiag_pow hζ))
  have hact := SLRep.act_map φ de
  have hDe : ((Matrix.SpecialLinearGroup.toGL de : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = diagonal δ := rfl
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Fin (m + 1), k₀ ∉ ({j₁, j₂} : Finset (Fin (m + 1))) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h := Finset.card_le_card (fun k _ => hall k : (Finset.univ : Finset (Fin (m + 1))) ⊆ _)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h2 := Finset.card_le_two (a := j₁) (b := j₂)
    omega
  have hk₀1 : k₀ ≠ j₁ := fun h => hk₀ (by simp [h])
  have hk₀2 : k₀ ≠ j₂ := fun h => hk₀ (by simp [h])
  have hδk₀ : δ k₀ = 1 := WitSL.rootDiag_apply_of_ne hk₀1 hk₀2 ζ
  have hδj₁ : δ j₁ = ζ := WitSL.rootDiag_apply_left hj ζ
  have hδj₂ : δ j₂ = ζ⁻¹ := WitSL.rootDiag_apply_right j₁ j₂ ζ
  have he1 : φ de ≠ 1 :=
    SLRep.ne_one_of_frame hkerφ hDe hact (i := j₁) (j := k₀) (by rw [hδj₁, hδk₀]; exact hζ1)
  have heL : φ de ∈ L₁ := by
    rw [hi]
    refine ⟨de, WitSL.ggDiagSL_mem_blockSpecialLinear hδ fun k hk => ?_, rfl⟩
    exact WitSL.rootDiag_apply_of_ne (fun h : k = j₁ => hk (h ▸ hj₁))
      (fun h : k = j₂ => hk (h ▸ hj₂)) ζ
  set S : Finset (Fin (m + 1)) := ({j₁, j₂} : Finset (Fin (m + 1)))ᶜ with hSdef
  have hSc2 : Sᶜ.card = 2 := by rw [hSdef, compl_compl, Finset.card_pair hj]
  have hScard : S.card = m - 1 := by
    rw [hSdef, Finset.card_compl, Fintype.card_fin, Finset.card_pair hj]
    omega
  have hS : ∀ k ∈ S, δ k = 1 := fun k hk => by
    rw [hSdef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact WitSL.rootDiag_apply_of_ne hk.1 hk.2 ζ
  have hSc : ∀ k ∉ S, δ k ≠ 1 := fun k hk => by
    rw [hSdef, Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rw [hδj₁]; exact hζ1
    · rw [hδj₂]; exact hζi1
  have hj₁S : j₁ ∉ S := by simp [hSdef]
  have hk₀S : k₀ ∈ S := by rw [hSdef, Finset.mem_compl]; exact hk₀
  have hcomp := SLRep.isComponentOf_map_coordBlockSL h4 hkerφ hDe hact hS hSc
    (by omega) (by omega) hj₁S
  have hcard : Nat.card (Bs ⊓ Subgroup.centralizer
      (((coordBlockSL (GaloisField 2 f) S).map φ : Subgroup G) : Set G) : Subgroup G) ≤ p ^ 2 := by
    have h := SLRep.card_le_of_frame hp hpF hkerφ hcentφ
      (X := Bs ⊓ Subgroup.centralizer
        (((coordBlockSL (GaloisField 2 f) S).map φ : Subgroup G) : Set G))
      (fun c hc => hBs.2.1.2 c hc.1) (fun c hc => hframe c hc.1) (S := S) (i₀ := k₀)
      (fun c hc D' t' hD' hc' k hk =>
        SLRep.eq_of_mem_centralizer_coordBlockSL hkerφ hc.2 hD' hc' hk₀S k hk)
    rwa [hSc2] at h
  rw [hrangeφ] at hcomp
  exact Or.inr ⟨φ de, heL, Or.inl ⟨heBs, he1, Or.inr ⟨_, hcomp, hcard⟩⟩⟩

end Inputs

end CFSG.StandardType
