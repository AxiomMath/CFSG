module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvModelData
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Open (IsElemAbelian)

@[expose] def E6FieldNone
    : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = 2 ^ f →
    ∀ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε < 2 → σ ≠ 1 →
    ∀ β : MulAut (adjointGroup .E6 K),
      β ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
        (AutSt.e6DiagHom K).range → Odd (orderOf β) →
      let α := MulAut.conj g * exactNormalAut .E6 K a σ ε
      α * α = 1 → α * β = β * α → (∀ x, β x = x → α x = x) →
      ∀ L₁ : Subgroup (adjointGroup .E6 K), (∀ x ∈ L₁, β x = x) → Group.IsSolvable L₁

@[expose] def E6GraphNone
    : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = 2 ^ f →
    ∀ (g : adjointGroup .E6 K) (a : Fin Tag.E6.rank → Kˣ) (p : ℕ)
      (β : MulAut (adjointGroup .E6 K)) (E : Subgroup (MulAut (adjointGroup .E6 K))),
      p.Prime → p ≠ 2 → β ≠ 1 → β ∈ E →
      E ≤ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
        (AutSt.e6DiagHom K).range →
      IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
      let α := MulAut.conj g * exactNormalAut .E6 K a 1 1
      E ≤ Subgroup.centralizer {α} → α * α = 1 → ¬ ∀ x, β x = x → α x = x

open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny in
theorem ggOuterInv_e6Marking
    {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
    (ψ : ↥(e6Data_valid.minGroup K) →* G)
    (hker : ψ.ker = Subgroup.center ↥(e6Data_valid.minGroup K)) {c : G}
    (hdiag : GGPsiInnerDiag (e6Datum K) ψ c) :
    ∃ φ ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
        (AutSt.e6DiagHom K).range,
      ∀ u u', c * ψ u * c⁻¹ = ψ u' → φ (e6Isogeny K u) = e6Isogeny K u' := by
  obtain ⟨_, ⟨w, rfl⟩, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker.le hdiag
  have hπker : (e6Isogeny K).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hker.symm
  have key := ggOuterInv_marking_of_closure ψ (e6Isogeny K) (e6Isogeny_surjective K) hπker
    (closure_xm_simple_eq_top e6Data_valid K) (c * ψ w) (AutSt.e6DiagHom K a) (by
      rintro _ ⟨i, t, rfl | rfl⟩
      · refine ⟨_, (ha i t).1, ?_⟩
        show exactNormalAut .E6 K a 1 0 _ = _
        rw [RootCentExc.e6Isogeny_xm_single_eq, RootCentExc.e6Isogeny_xm_single_eq,
          exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply]
        rfl
      · refine ⟨_, (ha i t).2, ?_⟩
        show exactNormalAut .E6 K a 1 0 _ = _
        rw [RootCentExc.e6Isogeny_xm_neg_single_eq, RootCentExc.e6Isogeny_xm_neg_single_eq,
          exactNormalAut_adjY, exactPerm_zero, Equiv.Perm.one_apply]
        rfl)
  refine ⟨(AutSt.e6DiagHom K a)⁻¹ * MulAut.conj (e6Isogeny K w)⁻¹,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right ⟨a, rfl⟩))
      (Subgroup.mem_sup_left ⟨_, rfl⟩), fun u u' hcu => ?_⟩
  have h1 := key u' (w⁻¹ * u * w) (by
    rw [map_mul, map_mul, map_inv, ← hcu]
    group)
  have e : ∀ y, AutSt.e6DiagHom K a ((AutSt.e6DiagHom K a)⁻¹ y) = y := fun y => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [MulAut.mul_apply]
  apply (AutSt.e6DiagHom K a).injective
  rw [e, h1, MulAut.conj_apply]
  simp only [map_mul, map_inv, inv_inv]

open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny in
theorem ggOuterInvModelDataAt_E6_of
    (hD1 : E6FieldNone) (hD2 : E6GraphNone) :
    GGOuterInvModelDataAt .E6 := by
  intro n f hadm _
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨adjointGroup .E6 (GaloisField 2 f), inferInstance, e6Isogeny (GaloisField 2 f),
    (MulAut.conj : adjointGroup .E6 (GaloisField 2 f) →* MulAut _).range ⊔
      (AutSt.e6DiagHom (GaloisField 2 f)).range,
    e6Isogeny_surjective _, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
    le_sup_left, AutSt.odd_relIndex_inn_ker_E6 hf hK rfl, ?_, ?_⟩
  · intro G _ ψ hker c _ hdiag
    exact ggOuterInv_e6Marking ψ hker hdiag
  · intro p β α E hp hp2 hβ1 hβE hEI hEab hEcard hEα hα2 hαI hL hfix
    obtain ⟨L₁, hL₁β, hL₁⟩ := hL
    have hodd : Odd (orderOf β) := by
      have h1 : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one (hEab.2 _ hβE)
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · rw [h]
        exact odd_one
      · rw [h]
        exact hp.odd_of_ne_two hp2
    have hcomm : α * β = β * α := by
      have := hEα hβE
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
    obtain ⟨-, -, hnf⟩ :=
      ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) (GaloisField 2 f)
    obtain ⟨g, a, σ, ε, hga⟩ := hnf α
    have e : α = MulAut.conj g * exactNormalAut .E6 (GaloisField 2 f) a σ ε :=
      eq_conj_mul_exactNormalAut_of_apply hga
    subst e
    have hε : (ε : ℕ) < 2 := ε.isLt
    by_cases hσ : σ = 1
    · subst hσ
      rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by omega) with h0 | h1
      · exact absurd (by
          rw [h0]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, rfl⟩)
            (Subgroup.mem_sup_right ⟨a, rfl⟩)) hαI
      · rw [h1] at hEα hα2 hfix
        exact hD2 f _ hf hK g a p β E hp hp2 hβ1 hβE hEI hEab hEcard hEα hα2 hfix
    · exact hL₁ (hD1 f _ hf hK g a σ ε hε hσ β (hEI hβE) hodd hα2 hcomm hfix L₁ hL₁β)

theorem ggOuterInvAt_E6_of
    (h2 : GGO2CentralizerG0At .E6) (hD1 : E6FieldNone)
    (hD2 : E6GraphNone) : GGOuterInvAt .E6 :=
  ggOuterInvAt_of_modelData ggSteinbergCorrectionAt_E6 h2 (ggOuterInvModelDataAt_E6_of hD1 hD2)

end CFSG.StandardType
