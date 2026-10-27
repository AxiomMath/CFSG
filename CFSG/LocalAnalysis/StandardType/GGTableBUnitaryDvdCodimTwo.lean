module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoLift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvd

public section

namespace CFSG.StandardType

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SectionRank.OddCover TableBUD TableBUE TableBUR TableBUDT

@[expose] def GGUnitaryFrame (n d : ℕ) (K : Type) [Field K] {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) (A : Subgroup (MulAut L')) :
    Prop :=
  ∃ P : GL (Fin d) K,
    ((P : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n))ᵀ * (P : Matrix (Fin d) (Fin d) K) = 1 ∧
      ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          {M | M ∈ LargeEvenGUSet (Fin d) K (2 ^ n) ∧
            ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag},
        ∀ l, φ (ψ l) = ψ (a l)

@[expose] def GGEndNodeAdmUnitarySixThreeInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
            (LargeEvenGUSet (Fin 6) K (2 ^ n)),
          ∀ l : L', φ (ψ l) = ψ (a l)) →
        3 ^ 3 ≤ Nat.card A → Nat.card A < 3 ^ 4 → GGAdmissible 3 L' A →
        ¬ GGUnitaryFrame n 6 K ψ A →
        ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
          ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

namespace TableBUDT

variable {K : Type} [Field K] [Finite K] {n d : ℕ}

theorem endNode_of_frame
    (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 6 ≤ d) {L' : Type} [Group L']
    [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)),
        ∀ l, φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 3) ≤ Nat.card A) (hs : Nat.card A < p ^ (d - 2)) (hadm : GGAdmissible p L' A)
    (hfr : GGUnitaryFrame n d K ψ A) :
    ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  classical
  have hn : 1 ≤ n := h.one_le
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  obtain ⟨P, hPu, hPA⟩ := hfr
  have hP : P ∈ primeFormUnitary h (idGram K d) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    exact hPu
  have hN := gu_subset_normalizer (d := d) h
  set NN := Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) with hNN
  have hind : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (unitarySU 2 n K d)),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  set σ := conjProj h P hP with hσ
  set ψ' : L' →* LargeEvenProj (unitarySU 2 n K d) := σ.toMonoidHom.comp ψ with hψ'def
  have hψ' : Function.Surjective ψ' := σ.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    have h1 : σ (ψ z) = 1 := hz
    exact (MulEquiv.map_eq_one_iff σ).mp h1
  have hPN : P ∈ NN := hN (mem_guSet_of_mem_primeFormUnitary h hP)
  have hmodel : ∀ a ∈ A, ∃ (τ : Fin d → Kˣ) (hτ : diagHom d τ ∈ NN),
      ∀ l, TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hτ⟩ (ψ' l) = ψ' (a l) := by
    intro a ha
    obtain ⟨φ, hφS, hφ⟩ := hPA a ha
    obtain ⟨M, ⟨hMgu, hdiagM⟩, hφM⟩ := TableB.exists_eq_projConj
      (S := {M | M ∈ LargeEvenGUSet (Fin d) K (2 ^ n) ∧
        ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag})
      (fun M hM => hN hM.1) hφS
    have hφ' : ∀ l, TableB.projConj (unitarySU 2 n K d) ⟨M, hN hMgu⟩ (ψ l) = ψ (a l) := by
      intro l
      have h0 := hφ l
      rw [hφM] at h0
      exact h0
    obtain ⟨τ, hτ⟩ := exists_diagHom_of_isDiag hdiagM
    have hPMP : P⁻¹ * M * P ∈ NN := NN.mul_mem (NN.mul_mem (NN.inv_mem hPN) (hN hMgu)) hPN
    have hτN : diagHom d τ ∈ NN := hτ ▸ hPMP
    refine ⟨τ, hτN, fun l => ?_⟩
    have h1 := conjProj_projConj h P hP ⟨M, hN hMgu⟩ hPMP (ψ l)
    have h2 : (⟨P⁻¹ * M * P, hPMP⟩ : NN) = ⟨diagHom d τ, hτN⟩ := Subtype.ext hτ
    rw [h2, hφ'] at h1
    exact h1.symm
  have hind' : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (unitarySU 2 n K d)),
      ∀ l, φ (ψ' l) = ψ' (a l) := fun a ha => by
    obtain ⟨τ, hτ, hτa⟩ := hmodel a ha
    exact ⟨_, hτa⟩
  have hcard' := TypeA.card_inducedSub hψ' hker' hperf hind'
  obtain ⟨U, hU1, hU2, hAU⟩ := admissible_alpha hK hn (by omega) hdq hp hpq ψ hψ hker hs hadm
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    center_proj_eq_bot hK (by omega) hdq
  have hkc' := ker_eq_center_of_surjective hψ' hker' hZ
  set ι := indAut ψ' hψ' hkc' with hι
  have hUR : ∃ Ū : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d))), Ū ≠ ⊥ ∧
      IsPGroup 2 Ū ∧ TypeA.inducedSub ψ' A ≤
        Subgroup.normalizer (Ū : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))) := by
    refine ⟨U.map ι, fun hbot => hU1 ?_, hU2.map _, ?_⟩
    · exact (Subgroup.map_eq_bot_iff_of_injective U (indAut_injective ψ' hψ' hkc' hperf)).mp hbot
    · rintro φ ⟨a, ha, hφ⟩
      have e : φ = ι a := TypeA.induced_unique ψ' hψ' hφ (indAut_apply ψ' hψ' hkc' a)
      rw [e]
      exact Subgroup.le_normalizer_map ι ⟨a, hAU ha, rfl⟩
  refine endNode_of_induced hψ' hker' hperf hind' ?_
  refine endNode_codimTwo h hK hp hpq hd (TypeA.isElemAbelian_inducedSub hψ' hA) ?_
    (hcard' ▸ hr) hUR
  rintro φ ⟨a, ha, hφ⟩
  obtain ⟨τ, hτ, hτa⟩ := hmodel a ha
  exact ⟨τ, hτ, TypeA.induced_unique ψ' hψ' hφ hτa⟩

omit [Finite K] in
theorem projConj_graph {M : GL (Fin d) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (g g' : ↥(unitarySU 2 n K d)) (hgg' : (g' : GL (Fin d) K) = M * g * M⁻¹) :
    TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩ (LargeEvenProjMk _ g) = LargeEvenProjMk _ g' := by
  rw [projConj_mk_coe]
  congr 1
  exact Subtype.ext hgg'.symm

theorem frame_of_ne (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 6 ≤ d) (hpd : p ∣ d) (hne : ¬(d = 6 ∧ p = 3))
    {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)),
        ∀ l, φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 3) ≤ Nat.card A) : GGUnitaryFrame n d K ψ A := by
  classical
  have hp2 := ne_two_of_dvd h hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hind : ∀ a ∈ A, ∃ φ : MulAut (LargeEvenProj (unitarySU 2 n K d)),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hcardAb := TypeA.card_inducedSub hψ hker hperf hind
  have hAbab : IsElemAbelian p Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ φ ∈ Ab, φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    rintro φ ⟨a, ha, hφ⟩
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    rwa [TypeA.induced_unique ψ hψ hφ hφ']
  have hk : d / p + 2 ≤ d - 3 := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    by_cases hp3' : p = 3
    · subst hp3'
      have h6 : d ≠ 6 := fun h6 => hne ⟨h6, rfl⟩
      obtain ⟨k, hk⟩ := hpd
      subst hk
      omega
    · have h4 : d / p ≤ d / 4 := Nat.div_le_div_left (by omega) (by norm_num)
      omega
  obtain ⟨P, hP, hframe⟩ := exists_unitary_frame h hK (by omega) hdq hp hpq hAbab hAbI
    ((Nat.pow_le_pow_right hp.pos hk).trans (hcardAb ▸ hr))
  refine ⟨P, ?_, fun a ha => ?_⟩
  · have h1 := mem_primeFormUnitary.mp hP
    simp only [idGram, Units.val_one, Matrix.mul_one] at h1
    exact h1
  · obtain ⟨φ, hφ⟩ := hind a ha
    obtain ⟨M, hM, hdiag, hφM⟩ := hframe φ ⟨a, ha, hφ⟩
    refine ⟨φ, ⟨M, ⟨hM, hdiag⟩, ?_⟩, hφ⟩
    intro g g' hgg'
    rw [hφM]
    exact projConj_graph _ g g' hgg'

theorem ggEndNodeAdmBelow_unitary_codimTwo
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hd : 6 ≤ d) (hpd : p ∣ d)
    (h63 : GGEndNodeAdmUnitarySixThreeInput) :
    GGEndNodeAdmBelow p (d - 3) (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hs hadm
  have h := TableBU.unitaryFieldData_of_card hK hn
  by_cases hfr : GGUnitaryFrame n d K ψ A
  · exact endNode_of_frame h hK hp hpq hd ψ hψ hker hperf hA hAI hr hs hadm hfr
  · by_cases hne : d = 6 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hne
      exact h63 n K hK hpq L' ψ hψ hker hperf A hA hAI h3 hs hadm hfr
    · exact absurd (frame_of_ne h hK hp hpq hd hpd hne ψ hψ hker hperf hA hAI hr) hfr

end TableBUDT

theorem ggEndNodeAdmUnitaryDvdCodimTwoInput_of_sixThree
    (h63 : GGEndNodeAdmUnitarySixThreeInput) : GGEndNodeAdmUnitaryDvdCodimTwoInput := by
  intro p lab hp hlab hl hpd h4
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq⟩ := hl
  dsimp only at htag hpq hpd h4 ⊢
  have hn : 1 ≤ n := hlab.1
  rcases htag with rfl | ⟨-, h3⟩
  swap
  · omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  by_cases hd6 : 6 ≤ l + 1
  · exact TableBUDT.ggEndNodeAdmBelow_unitary_codimTwo hK hn hp hpq hd6 hpd h63
  · intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hs hadm
    exfalso
    have hl5 : l + 1 - 2 = 3 := by omega
    rw [hl5] at hs
    omega

theorem ggEndNodeAdmUnitaryDvdInput_of_sixThree
    (h63 : GGEndNodeAdmUnitarySixThreeInput) : GGEndNodeAdmUnitaryDvdInput :=
  ggEndNodeAdmUnitaryDvdInput_of_codimTwo (ggEndNodeAdmUnitaryDvdCodimTwoInput_of_sixThree h63)

end CFSG.StandardType
