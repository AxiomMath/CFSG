module

public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A3
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93j
import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped MatrixGroups
open CFSG.Blueprint (LieModel)

theorem r95s_lieModel_two_of_mulEquiv_psl {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (h4 : 4 ≤ Nat.card F)
    (e : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ∃ m : ℕ, LieModel Y .PSL 2 2 m := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, k, hp, hk⟩ := FiniteField.card' F
  rw [← Nat.card_eq_fintype_card] at hk
  have hp2 : p = 2 := by
    have hpk : p ^ (k : ℕ) = 2 ^ n := by rw [← hk, hF]
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (hpk ▸ dvd_pow_self p (k.pos).ne'))
  subst p
  refine ⟨(k : ℕ), Or.inl ⟨by decide, ⟨hp, k.one_le, le_rfl, fun h => ?_, fun h => ?_⟩, F,
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

theorem r95s_false_of_quot_sl2 {Γ : Type} [Group Γ] [Finite Γ]
    (hS : IsSimpleGroup (Γ ⧸ CFSG.pPrimeCore 3 Γ))
    (hnab : ∃ a b : Γ ⧸ CFSG.pPrimeCore 3 Γ, a * b ≠ b * a)
    (h32 : LieModel (Γ ⧸ CFSG.pPrimeCore 3 Γ) .PSL 3 2 1) {N : Subgroup Γ} [N.Normal]
    (hN3 : ¬ 3 ∣ Nat.card N) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (e : Nonempty (Γ ⧸ N ≃* SL(2, F))) : False := by
  classical
  haveI := hS
  obtain ⟨e⟩ := e
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
  let φ₁ : SL(2, F) →* Γ ⧸ CFSG.pPrimeCore 3 Γ := ψ.comp e.symm.toMonoidHom
  have hφ₁ : Function.Surjective φ₁ := hψ.comp e.symm.surjective
  have hZ : Subgroup.center (SL(2, F)) ≤ φ₁.ker := by
    intro z hz
    have hc : φ₁ z ∈ Subgroup.center (Γ ⧸ CFSG.pPrimeCore 3 Γ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := hφ₁ y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) y']
    rwa [CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot hnab, Subgroup.mem_bot] at hc
  have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hS hnab
  have h4 : 4 ≤ Nat.card F := by
    by_contra h4
    have hle := Nat.card_le_card_of_surjective φ₁ hφ₁
    have hSL := card_sl_two_le_of_card_le_three (F := F) (by omega)
    omega
  haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  obtain ⟨e₂⟩ := hiso (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (QuotientGroup.lift _ φ₁ hZ) (QuotientGroup.lift_surjective_of_surjective _ φ₁ hφ₁ hZ)
  obtain ⟨m, hm⟩ := r95s_lieModel_two_of_mulEquiv_psl hF h4 e₂
  have h27 := r95_char_seven_of_section hm (E := ⊤)
    (Subgroup.topEquiv (G := Γ ⧸ CFSG.pPrimeCore 3 Γ)).toMonoidHom
    (Subgroup.topEquiv (G := Γ ⧸ CFSG.pPrimeCore 3 Γ)).surjective h32
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
