module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxRank
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix
  CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem pow_le_card_range_ggGamma_of_aPermutationFull {G : Type} [Group G] [Finite G]
    {p n : ℕ} [NeZero p] {Bs X : Subgroup G} (hn : 0 < n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    p ^ (n - 1) ≤ Nat.card (ggGamma X hN).range := by
  let f : ↥(ggGamma X hN).ker → ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
    fun b => ⟨((b : ↥Bs) : G), (b : ↥Bs).2,
      (ggGamma_eq_one_iff X hN (b : ↥Bs)).mp (MonoidHom.mem_ker.mp b.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) => (c : G)) hab
  have hker : Nat.card (ggGamma X hN).ker ≤ p :=
    (Nat.card_le_card_of_injective f hf).trans
      (card_inf_centralizer_le_of_aPermutationFull hn eta hA)
  have hBs : Nat.card ↥Bs = p ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_multiplicative, ZMod.card, Fintype.card_fin]
  have hprod : p ^ n ≤ p * Nat.card (ggGamma X hN).range := by
    calc
      p ^ n = Nat.card (ggGamma X hN).ker * Nat.card (ggGamma X hN).range :=
        hBs.symm.trans (Subgroup.card_ker_mul_card_range (ggGamma X hN)).symm
      _ ≤ p * Nat.card (ggGamma X hN).range := Nat.mul_le_mul_right _ hker
  have hpow : p * p ^ (n - 1) = p ^ n := by
    conv_rhs => rw [show n = (n - 1) + 1 by omega, Nat.pow_succ]
    exact Nat.mul_comm _ _
  rw [← hpow] at hprod
  exact Nat.le_of_mul_le_mul_left hprod (NeZero.pos p)

theorem exists_unitary_quotient_frame_of_aPermutationFull {G : Type} [Group G] [Finite G]
    {n : ℕ} (hn : 5 ≤ n) {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    (hmark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, n - 1, 1⟩ : LargeEvenLabel)) 3 Bs X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (h : UnitaryFieldData 2 1 F) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (unitarySU 2 1 F n)),
      commutator ↥X = ⊤ ∧
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F n))
        (LargeEvenGUSet (Fin n) F (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ∃ P ∈ primeFormUnitary h (idGram F n), ∀ a ∈ (ggBeta X θ hN).range,
        ∃ (M : GL (Fin n) F) (hM : M ∈ LargeEvenGUSet (Fin n) F (2 ^ 1)),
          ((P⁻¹ * M * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧
            a = TableB.projConj (unitarySU 2 1 F n)
              ⟨M, TableBUE.gu_subset_normalizer h hM⟩ := by
  have hmark' : GGInnerDiagOnLabel
      (fun q lab => q = 3 ∧ lab = (⟨.twA, n - 1, 1⟩ : LargeEvenLabel)) 3 Bs X :=
    GGInnerDiagOnLabel.mono_label (fun _ hlab => ⟨rfl, hlab⟩) hmark
  obtain ⟨F, hFld, hFin, lab, m, θ, hcard, hm, hmrank, hlab, -, hperf, -, hN, hind⟩ :=
    ggNSLieN3A_esuCore hmark' (by
      rintro q lab ⟨rfl, rfl⟩
      exact ⟨Or.inl ⟨rfl, by change 3 ≤ n - 1; omega⟩, by norm_num⟩)
  rcases hlab with ⟨-, rfl⟩
  have hmn : m = n := by
    change m = n - 1 + 1 at hmrank
    omega
  clear hmrank
  subst m
  have hcard' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hcard
  let h := TableBU.unitaryFieldData_of_card hcard' (by omega : 1 ≤ 1)
  letI : CharP F 2 := h.charP
  have hstrong : 3 ^ (n - 1) ≤ Nat.card (ggGamma X hN).range :=
    pow_le_card_range_ggGamma_of_aPermutationFull (by omega) eta hA hN
  have hrank : 3 ^ (n / 3 + 2) ≤ Nat.card (ggGamma X hN).range :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : n / 3 + 2 ≤ n - 1)).trans hstrong
  obtain ⟨P, hP, hframe⟩ := QTwo.qTwoNbrRec_frame h hn hN θ hperf hBs hind hrank
  exact ⟨F, hFld, hFin, inferInstance, h, hN, θ, hperf, hind, P, hP, hframe⟩

theorem exists_unitary_model_of_aPermutationFull_of_B_lt_Bs
    {G : Type} [Group G] [Finite G] {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig 3 B Bs x L D J) (hlt : B < Bs) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    (hmark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, n - 1, 1⟩ : LargeEvenLabel)) 3 Bs X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (φ : ↥(unitarySU 2 1 F n) →* ↥X),
      Nat.card F = 4 ∧ UnitTB.Model φ ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin n → F, LineU.ActsDiagU φ a t := by
  obtain ⟨F, hFld, hFin, hChar, h, hN, θ, hperf, hind, P, hP, hframe⟩ :=
    exists_unitary_quotient_frame_of_aPermutationFull hn hcfg.2.1.2.1 eta hA hmark
  let ψ := ggQuotHom θ
  have hψ : Function.Surjective ψ := ggQuotHom_surjective θ
  have hker : ψ.ker ≤ Subgroup.center ↥X := by
    change (ggQuotHom θ).ker ≤ Subgroup.center ↥X
    rw [ker_ggQuotHom]
  have hoddCard : Odd (Nat.card ψ.ker) :=
    hcfg.odd_card_central_kernel_of_B_lt_Bs hlt hN ψ hker
  have hodd : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1 := by
    intro z hz hz2
    let z' : ψ.ker := ⟨z, hz⟩
    have hz'2 : z' ^ 2 = 1 := Subtype.ext hz2
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz'2) with h1 | h2
    · exact congrArg (fun a : ψ.ker => (a : ↥X)) (orderOf_eq_one_iff.mp h1)
    · have hdiv := orderOf_dvd_natCard z'
      rw [h2] at hdiv
      exact False.elim ((Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdiv)) hoddCard)
  let A : Subgroup (MulAut ↥X) := (ggGamma X hN).range
  have hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F n))
      (LargeEvenGUSet (Fin n) F (2 ^ 1)), ∀ l : ↥X, φ (ψ l) = ψ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggBeta X θ hN b, ggBeta_mem X θ hN hind b,
      fun l => ggBeta_ggQuotHom X hN θ b l⟩
  have hframe' : ∀ a ∈ TypeA.inducedSub ψ A,
      ∃ (M : GL (Fin n) F) (hM : M ∈ LargeEvenGUSet (Fin n) F (2 ^ 1)),
        ((P⁻¹ * M * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧
          a = TableB.projConj (unitarySU 2 1 F n)
            ⟨M, TableBUE.gu_subset_normalizer h hM⟩ := by
    intro a ha
    obtain ⟨α, hα, hrel⟩ := TypeA.mem_inducedSub.mp ha
    obtain ⟨b, rfl⟩ := hα
    have heq : a = ggBeta X θ hN b :=
      TypeA.induced_unique ψ hψ hrel (fun l => ggBeta_ggQuotHom X hN θ b l)
    exact hframe a ⟨b, heq.symm⟩
  obtain ⟨φ, hsurj, hscalar, hdiag⟩ := QTwo.qTwoNbrRec_diagModel h le_rfl (by omega)
    (by
      intro hq
      have hn3 := congrArg Prod.fst hq
      simp only at hn3
      omega : (n, 2 ^ 1) ≠ (3, 2)) hψ hker hperf hodd hAI hP hframe'
  exact ⟨F, hFld, hFin, hChar, hN, φ, by simpa using h.card, ⟨h, hsurj, hscalar⟩, hdiag⟩

end CFSG.StandardType

end
