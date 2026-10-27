module

public import CFSG.RankThree.PartOne.D4RC.RootGroups
public import CFSG.RankThree.PartOne.D4RC.Transport
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec8Projection
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
open CFSG.Timmesfeld.ARS (conjSub)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Gamma

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

variable {F : RclFrame ℓ f K σ ε p L} {S : Sylow p 𝒞[K, σ]} {c : 𝒞[K, σ]}
  {E : Subgroup 𝒞[K, σ]}

theorem rce_factor_conj_of_idx (Ln : RceLines F S c E) [Fact p.Prime] {n : 𝒞[K, σ]}
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ])) {j : Fin 4}
    (hidx : rceIdx Ln n 0 = j) :
    rclPx (Ln.sp j) = (rclPx (Ln.sp 0)).map (MulAut.conj n).toMonoidHom := by
  have hmem := rceIdx_spec Ln hn 0
  rw [hidx] at hmem
  have h1 : n * Ln.x 0 * n⁻¹ ≠ 1 := fun h0 => (Ln.hx 0).2 (by
    have : Ln.x 0 = n⁻¹ * (n * Ln.x 0 * n⁻¹) * n := by group
    rw [this, h0]
    group)
  have hC := rcr_centralizer_eq F.hp (Ln.hEp _ (Ln.hx j).1) (Ln.hx j).2 hmem h1
  rw [← rceR_eq_rclPx (Ln.sp j), ← rceR_eq_rclPx (Ln.sp 0), ← rceR_conj, rceR_congr hC]

theorem rce_transitive_mem (Ln : RceLines F S c E) [Fact p.Prime] (i j : Fin 4) :
    ∃ k, ∃ n ∈ rclPx (Ln.sp k),
      n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]) ∧ rceIdx Ln n i = j := by
  by_cases hij : i = j
  · exact ⟨0, 1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [rceIdx_one, hij]⟩
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
    revert i j
    decide
  obtain ⟨g, hgP, hgN, hk, hmove, h3⟩ := rce_exists_rotation Ln k
  rcases (show ∀ τ : Equiv.Perm (Fin 4), ∀ k i j : Fin 4,
      (k ≠ i ∧ k ≠ j ∧ i ≠ j ∧ τ k = k ∧ (∀ v, v ≠ k → τ v ≠ v) ∧ τ ^ 3 = 1) →
      τ i = j ∨ (τ ^ 2) i = j by decide)
      (rcePerm Ln hgN) k i j ⟨hki, hkj, hij, hk, hmove, h3⟩ with h | h
  · exact ⟨k, g, hgP, hgN, h⟩
  · refine ⟨k, g ^ 2, Subgroup.pow_mem _ hgP 2, Subgroup.pow_mem _ hgN 2, ?_⟩
    rw [← rcePerm_pow_apply Ln hgN]
    exact h

@[expose] def rcgGamma (Ln : RceLines F S c E) : Subgroup 𝒞[K, σ] := ⨆ j, rclPx (Ln.sp j)

theorem rcg_le_gamma (Ln : RceLines F S c E) (j : Fin 4) : rclPx (Ln.sp j) ≤ rcgGamma Ln :=
  le_iSup (fun j => rclPx (Ln.sp j)) j

theorem rcg_sylow_le (Ln : RceLines F S c E) [Fact p.Prime] :
    (S : Subgroup 𝒞[K, σ]) ≤ rcgGamma Ln := by
  obtain ⟨j, hj⟩ := rce_sylow_le_sup Ln
  exact hj.trans (sup_le (rcg_le_gamma Ln 0) (rcg_le_gamma Ln j))

theorem rcg_E_le (Ln : RceLines F S c E) [Fact p.Prime] : E ≤ rcgGamma Ln :=
  Ln.hES.trans (rcg_sylow_le Ln)

theorem rcg_factor_conj (Ln : RceLines F S c E) [Fact p.Prime] (j : Fin 4) :
    ∃ n ∈ rcgGamma Ln, n ∈ Subgroup.normalizer ((S : Subgroup 𝒞[K, σ]) : Set 𝒞[K, σ]) ∧
      rclPx (Ln.sp j) = (rclPx (Ln.sp 0)).map (MulAut.conj n).toMonoidHom := by
  obtain ⟨k, n, hnP, hn, hidx⟩ := rce_transitive_mem Ln 0 j
  exact ⟨n, rcg_le_gamma Ln k hnP, hn, rce_factor_conj_of_idx Ln hn hidx⟩

theorem rcg_iSup_orbit (Ln : RceLines F S c E) [Fact p.Prime] (D : RclAlgData F 0) :
    ⨆ A ∈ rccOrbit (rcgGamma Ln) (rcaA0 (Ln.sp 0) D), A = rcgGamma Ln := by
  have hA₀ : rcaA0 (Ln.sp 0) D ≤ rcgGamma Ln := (rcaA0_le _ D).trans (rcg_le_gamma Ln 0)
  refine le_antisymm (iSup₂_le ?_) (iSup_le fun j => ?_)
  · rintro _ ⟨g, hg, rfl⟩
    exact rca_map_conj_le hA₀ hg
  obtain ⟨n, hnΓ, -, hPj⟩ := rcg_factor_conj Ln j
  rw [hPj, Subgroup.map_le_iff_le_comap, ← rca_iSup_eq (Ln.sp 0) D]
  refine iSup₂_le fun g hg => ?_
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
  have e : (MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (n * g)).toMonoidHom := MonoidHom.ext fun a => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
      mul_assoc]
  rw [e]
  exact le_iSup₂ (f := fun A (_ : A ∈ rccOrbit (rcgGamma Ln) (rcaA0 (Ln.sp 0) D)) => A) _
    ⟨n * g, (rcgGamma Ln).mul_mem hnΓ (rcg_le_gamma Ln 0 hg), rfl⟩

end Gamma

end CFSG.RankThree.PartOne.D4RC
