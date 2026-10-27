module

public import CFSG.Quasithin.Background.F7TwoInvU3OddCrit
public import CFSG.Quasithin.Background.F7TwoInvU3OddFix
public import CFSG.Quasithin.Background.F7TwoInvU3OddId
public import CFSG.Quasithin.Background.F7TwoInvU3OddBar
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Quasithin.F7Two.U3Odd

theorem invAutGen_of_statedPSU3 {L : Type} [Group L] {p : ℕ} (hp2 : p ≠ 2)
    (hL : StatedClassicalModel L .PSU 3 p 1) :
    ∀ φ : MulAut L, φ * φ = 1 → φ ≠ 1 → InvAutGen L φ := by
  intro φ hφ2 hφ1
  obtain ⟨hnt, hs⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity L 3 p 1 hL
  obtain ⟨⟨hp, -, hn, hne⟩, K, _, hKfin, hK, ⟨e⟩⟩ := hL
  have : Fact p.Prime := ⟨hp⟩
  have hU : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hU
  let E : hypPSU hU 1 1 ≃* L := (hypPSUEquivStatedProj hU hR (by norm_num)).trans e.symm
  have hsP : IsSimpleGroup (hypPSU hU 1 1) := by
    have := hs
    exact E.isSimpleGroup
  let α : MulAut (hypPSU hU 1 1) := (E.trans φ).trans E.symm
  have hφφ : ∀ y, φ (φ y) = y := fun y => by
    have := MulEquiv.congr_fun hφ2 y
    simpa using this
  have hα2 : α * α = 1 := by
    ext x
    simp [α, hφφ]
  have hα1 : α ≠ 1 := by
    intro h1
    apply hφ1
    ext y
    have := MulEquiv.congr_fun h1 (E.symm y)
    simpa [α] using this
  have hord : orderOf α = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
  obtain ⟨-, -, -, hrep⟩ :=
    odd_unitary_automorphism_semilinear_representation hU hp2 le_rfl le_rfl (by norm_num)
  obtain ⟨A, σ, hx, hAU, hΦ, hσ, hid, hbar⟩ := hrep α hord
  have hkey : ∃ (P₀ : hypSU hU 1 1) (d : HypIndex 1 1 → K),
      ((((P₀ : GL (HypIndex 1 1) K))⁻¹ * A * glAut σ (P₀ : GL (HypIndex 1 1) K) :
        GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d := by
    rcases hσ with hσid | hσbar
    ·
      have hord2 := hid hσid
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨hsq, -⟩ := orderOf_eq_prime_iff.mp hord2
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hsq
      obtain ⟨c, hcN, -, hcA⟩ := hsq
      have hAA : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
          (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = (c : K) • 1 := by
        have h1 := congrArg Units.val hcA
        rw [Subgroup.coe_pow, pow_two, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
        rw [h1, scalar_apply, smul_one_eq_diagonal]
      have hns : ∀ c' : K, (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) ≠ c' • 1 := by
        intro c' hc'
        have hc'0 : c' ≠ 0 := by
          rintro rfl
          have h1 : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
              ((A⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = 1 := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          rw [hc', zero_smul, Matrix.zero_mul] at h1
          exact zero_ne_one h1
        apply hα1
        rw [← hΦ]
        refine (semilinearAutHom_eq_one_iff hU le_rfl le_rfl (by norm_num) _).mpr
          ⟨hσid, Units.mk0 c' hc'0, ?_⟩
        refine Units.ext ?_
        change (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = _
        rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply, hc', smul_one_eq_diagonal]
      obtain ⟨a, b, l₁, l₃, haa, hbb, hab, hla, hlb⟩ :=
        exists_stable_pair_of_sq hp2 hAU hcN hAA hns
      subst hσid
      exact exists_hypSU_diag_of_stable_pair hAU (RingEquiv.refl K) haa hbb hab hla hlb
    ·
      obtain ⟨c, hc0, hAc⟩ := hbar hσbar
      obtain ⟨a, b, haa, hbb, hab, hla, hlb⟩ := exists_stable_pair_of_bar hp2 hAU hc0 hAc
      have hσf : ∀ v : HypIndex 1 1 → K, (fun i => σ (v i)) = fun i => hU.bar (v i) :=
        fun v => funext fun i => hσbar _
      refine exists_hypSU_diag_of_stable_pair hAU σ haa hbb hab (l₁ := 1) (l₃ := 1) ?_ ?_
      · rw [hσf, hla, one_smul]
      · rw [hσf, hlb, one_smul]
  obtain ⟨P₀, d, hd⟩ := hkey
  let X₀ : semilinearSimilitudes hU 1 1 :=
    ⟨SemidirectProduct.inl (P₀ : GL (HypIndex 1 1) K), inl_mem_semilinearSimilitudes P₀⟩
  let X₁ : semilinearSimilitudes hU 1 1 := ⟨⟨A, σ⟩, hx⟩
  let Xd : semilinearSimilitudes hU 1 1 := X₀⁻¹ * X₁ * X₀
  let ψ := (semilinearAutHom hU (le_refl 1) (le_refl 1) X₀)⁻¹
  have hXd : semilinearAutHom hU (le_refl 1) (le_refl 1) Xd = ψ * α * ψ⁻¹ := by
    simp only [Xd, map_mul, map_inv, ψ, X₁, hΦ, inv_inv]
  have hXdl : ((Xd : SemiGL (HypIndex 1 1) K).left : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      diagonal d := by
    rw [← hd]
    congr 1
  have hα'2 : (ψ * α * ψ⁻¹) * (ψ * α * ψ⁻¹) = 1 := by
    calc (ψ * α * ψ⁻¹) * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  have hα'1 : ψ * α * ψ⁻¹ ≠ 1 := by
    intro h1
    apply hα1
    calc α = ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ := by group
      _ = 1 := by rw [h1]; group
  have hPα' : InvAutGen (hypPSU hU 1 1) (ψ * α * ψ⁻¹) := by
    rw [← hXd] at hα'2 hα'1 ⊢
    exact invAutGen_hyp_of_diag hp2 hsP hα'2 hα'1 ⟨d, hXdl⟩ (Xd : SemiGL (HypIndex 1 1) K).right
      fun g => ⟨conj_mem_hypSU Xd.2 g, semilinearAutHom_apply hU _ _ Xd g⟩
  have hPα : InvAutGen (hypPSU hU 1 1) α := (InvAutGen.conj_iff ψ α).mpr hPα'
  have h1 := InvAutGen.congr E hPα
  have e1 : (E.symm.trans α).trans E = φ := MulEquiv.ext fun y => by simp [α]
  rwa [e1] at h1

end CFSG.Quasithin.F7Two
