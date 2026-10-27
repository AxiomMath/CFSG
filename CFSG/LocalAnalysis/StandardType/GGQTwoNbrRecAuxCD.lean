module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxKb
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxDiag
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxRank

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType CFSG.Open

variable {G Q : Type} [Group G] [Finite G] [Group Q] {Bs K : Subgroup G}

theorem qTwoNbrRec_hAI {R : Type} [Group R] (q : ↥(K ⊔ Bs) →* Q)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (ψ : ↥(qTwoNbrRec_Kb q) →* R)
    (hψ : ∀ k : ↥K, ψ (qTwoNbrRec_kappa q k) = ggQuotHom θ k) {I : Set (MulAut R)}
    (hind : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ a ∈ (qTwoNbrRec_gammaB q hN).range, ∃ x ∈ I, ∀ l : ↥(qTwoNbrRec_Kb q), x (ψ l) = ψ (a l) := by
  rintro a ⟨b, rfl⟩
  exact ⟨ggBeta K θ hN b, ggBeta_mem K θ hN hind b,
    fun l => (qTwoNbrRec_psiBar_gamma q hN θ ψ hψ b l).symm⟩

theorem qTwoNbrRec_inducedSub_le {R : Type} [Group R] (q : ↥(K ⊔ Bs) →* Q)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (ψ : ↥(qTwoNbrRec_Kb q) →* R) (hψs : Function.Surjective ψ)
    (hψ : ∀ k : ↥K, ψ (qTwoNbrRec_kappa q k) = ggQuotHom θ k) :
    TypeA.inducedSub ψ (qTwoNbrRec_gammaB q hN).range ≤ (ggBeta K θ hN).range := by
  intro φ hφ
  rw [TypeA.mem_inducedSub] at hφ
  obtain ⟨a, ha, hφa⟩ := hφ
  obtain ⟨b, rfl⟩ := ha
  exact ⟨b, (TypeA.induced_unique ψ hψs hφa
    (fun l => (qTwoNbrRec_psiBar_gamma q hN θ ψ hψ b l).symm)).symm⟩

theorem qTwoNbrRec_coverDiag
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBs : IsElemAbelian 3 Bs) {F : Type} [Field F] [Finite F] {d : ℕ} (h : UnitaryFieldData 2 1 F)
    (hd : 5 ≤ d) (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 1 F d))
    (hperf : commutator ↥K = ⊤)
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
        (LargeEvenGUSet (Fin d) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hrank : 3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma K hN).range)
    (q : ↥(K ⊔ Bs) →* Q) (hq : q.ker = (qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs)) :
    ∃ φ : ↥(unitarySU 2 1 F d) →* ↥(qTwoNbrRec_Kb q), Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 1 F d), φ g = 1 →
        ∃ c : F, ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = diagonal (fun _ => c)) ∧
      ∀ b : ↥Bs, ∃ t : Fin d → F, LineU.ActsDiagU φ (qTwoNbrRec_gammaB q hN b) t := by
  obtain ⟨ψ, hψκ, hψs, hψc, hψodd⟩ := qTwoNbrRec_exists_psiBar q hq θ
  haveI : Finite ↥(qTwoNbrRec_Kb q) :=
    Finite.of_surjective (qTwoNbrRec_kappa q) (qTwoNbrRec_kappa_surjective q)
  have hperfKb : commutator ↥(qTwoNbrRec_Kb q) = ⊤ := qTwoNbrRec_Kb_perfect q hperf
  let A : Subgroup (MulAut ↥(qTwoNbrRec_Kb q)) := (qTwoNbrRec_gammaB q hN).range
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
      (LargeEvenGUSet (Fin d) F (2 ^ 1)), ∀ l : ↥(qTwoNbrRec_Kb q), x (ψ l) = ψ (a l) :=
    qTwoNbrRec_hAI q hN θ ψ hψκ hind
  obtain ⟨P, hP, hframe⟩ := qTwoNbrRec_frame h hd hN θ hperf hBs hind hrank
  have hle : TypeA.inducedSub ψ A ≤ (ggBeta K θ hN).range :=
    qTwoNbrRec_inducedSub_le q hN θ ψ hψs hψκ
  obtain ⟨φ, hφs, hφker, hφdiag⟩ := qTwoNbrRec_diagModel (L' := ↥(qTwoNbrRec_Kb q))
    (n := 1) h le_rfl (by omega)
    (by rw [pow_one]; intro hcon; exact absurd (congrArg Prod.fst hcon) (by omega))
    hψs hψc hperfKb hψodd (A := A) hAI hP (fun a ha => hframe a (hle ha))
  exact ⟨φ, hφs, hφker, fun b => hφdiag (qTwoNbrRec_gammaB q hN b) ⟨b, rfl⟩⟩

end CFSG.StandardType.QTwo

end
