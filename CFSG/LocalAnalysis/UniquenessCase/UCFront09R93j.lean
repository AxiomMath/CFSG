module

import CFSG.Adapters.StatedPSLTwo
import CFSG.Quasithin.Background.DicksonPerfectSL2
import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped MatrixGroups

theorem lieModel_of_mulEquiv_psl {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (e : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ∃ p f : ℕ, CFSG.Blueprint.LieModel Y .PSL 2 p f := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, k, hp, hk⟩ := FiniteField.card' F
  rw [← Nat.card_eq_fintype_card] at hk
  refine ⟨p, k, Or.inl ⟨by decide, ⟨hp, k.one_le, le_rfl, fun h => ?_, fun h => ?_⟩, F,
    inferInstance, inferInstance, hk,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩⟩⟩
  · have h2 := congrArg Prod.snd h
    simp only at h2
    rw [← hk] at h2
    omega
  · have h3 := congrArg Prod.snd h
    simp only at h3
    rw [← hk] at h3
    omega

theorem card_sl_two_le_of_card_le_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F ≤ 3) :
    Nat.card (SL(2, F)) ≤ 24 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : 2 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have h3' : Fintype.card F ≤ 3 := by rwa [← Nat.card_eq_fintype_card]
  rw [Matrix.card_SL_field 2, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  interval_cases Fintype.card F <;> norm_num

theorem exists_lieModel_of_quot_cases {Γ : Type} [Group Γ] [Finite Γ]
    (hS : IsSimpleGroup (Γ ⧸ CFSG.pPrimeCore 3 Γ))
    (hnab : ∃ a b : Γ ⧸ CFSG.pPrimeCore 3 Γ, a * b ≠ b * a)
    {N : Subgroup Γ} [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N)
    (hcases : (∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (Γ ⧸ N ≃* SL(2, F))) ∨
      (∃ n : ℕ, CFSG.Blueprint.LieModel (Γ ⧸ N) .PSL 2 2 n) ∨
      CFSG.Quasithin.IsExt (Γ ⧸ N)
        (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) :
    ∃ p f : ℕ, CFSG.Blueprint.LieModel (Γ ⧸ CFSG.pPrimeCore 3 Γ) .PSL 2 p f := by
  classical
  haveI := hS
  have hNO : N ≤ (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).ker := by
    rw [QuotientGroup.ker_mk']
    exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3⟩
  let ψ : Γ ⧸ N →* Γ ⧸ CFSG.pPrimeCore 3 Γ := QuotientGroup.lift N _ hNO
  have hψ : Function.Surjective ψ :=
    QuotientGroup.lift_surjective_of_surjective N _ (QuotientGroup.mk'_surjective _) hNO
  have hiso : ∀ (P : Type) [Group P] [IsSimpleGroup P] (φ : P →* Γ ⧸ CFSG.pPrimeCore 3 Γ),
      Function.Surjective φ → Nonempty ((Γ ⧸ CFSG.pPrimeCore 3 Γ) ≃* P) := by
    intro P _ _ φ hφ
    have hinj : Function.Injective φ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
      · exact (MonoidHom.ker_eq_bot_iff φ).mp h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        obtain ⟨a', rfl⟩ := hφ a
        obtain ⟨b', rfl⟩ := hφ b
        rw [φ.mem_ker.mp (h ▸ Subgroup.mem_top a'), φ.mem_ker.mp (h ▸ Subgroup.mem_top b')] at hab
        exact hab rfl
    exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm⟩
  have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hS hnab
  rcases hcases with ⟨F, hF, hFin, ⟨e⟩⟩ | ⟨n, hn⟩ | ⟨E, hEn, hE, ⟨eA⟩⟩
  · let φ₁ : SL(2, F) →* Γ ⧸ CFSG.pPrimeCore 3 Γ := ψ.comp e.symm.toMonoidHom
    have hφ₁ : Function.Surjective φ₁ := hψ.comp e.symm.surjective
    have hZ : Subgroup.center (SL(2, F)) ≤ φ₁.ker := by
      intro z hz
      have hc : φ₁ z ∈ Subgroup.center (Γ ⧸ CFSG.pPrimeCore 3 Γ) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨y', rfl⟩ := hφ₁ y
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) y']
      rwa [CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot hnab, Subgroup.mem_bot] at hc
    have h4 : 4 ≤ Nat.card F := by
      by_contra h4
      have hle := Nat.card_le_card_of_surjective φ₁ hφ₁
      have hSL := card_sl_two_le_of_card_le_three (F := F) (by omega)
      omega
    haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    obtain ⟨e₂⟩ := hiso (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
      (QuotientGroup.lift _ φ₁ hZ) (QuotientGroup.lift_surjective_of_surjective _ φ₁ hφ₁ hZ)
    exact lieModel_of_mulEquiv_psl h4 e₂
  · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hn
    obtain ⟨e⟩ := hiso (Γ ⧸ N) ψ hψ
    exact ⟨2, n, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hn⟩
  · have hE32 : Nat.card E = 32 := by
      have h := (CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts hE).1
      rwa [Subgroup.card_top] at h
    have hEψ : E ≤ ψ.ker := by
      haveI : (E.map ψ).Normal := hEn.map ψ hψ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.map ψ) with h | h
      · exact (Subgroup.map_eq_bot_iff E).mp h
      · exfalso
        have hle := Nat.le_of_dvd (by omega) (Subgroup.card_map_dvd E ψ)
        rw [h, Subgroup.card_top] at hle
        omega
    haveI : IsSimpleGroup ((Γ ⧸ N) ⧸ E) := eA.isSimpleGroup
    obtain ⟨e₃⟩ := hiso ((Γ ⧸ N) ⧸ E) (QuotientGroup.lift E ψ hEψ)
      (QuotientGroup.lift_surjective_of_surjective E ψ hψ hEψ)
    obtain ⟨eP⟩ := CFSG.Quasithin.Dickson.nonempty_psl2_five_equiv_alt
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact lieModel_of_mulEquiv_psl (F := ZMod 5) (by rw [Nat.card_zmod]; norm_num)
      ((e₃.trans eA).trans eP.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
