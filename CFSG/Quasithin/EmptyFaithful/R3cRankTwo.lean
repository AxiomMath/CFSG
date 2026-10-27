module

public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.EmptyFaithful.S153I38
public import CFSG.LocalAnalysis.SectionRank.OddCover.ThreeRank

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover

namespace R3c

section PSLThree

variable {K : Type} [Field K]

private noncomputable def diagOmega (ω : Kˣ) : GL (Fin 3) K :=
  diagHom 3 ![1, ω, ω⁻¹]

private theorem diagOmega_mem (ω : Kˣ) : diagOmega ω ∈ StatedSL 3 K :=
  (monomialData_statedSL (K := K)).diag_mem _ (fun _ => Subgroup.mem_top _) (by simp)

private theorem diagOmega_pow_three {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    (diagOmega ω : GL (Fin 3) K) ^ 3 = 1 := by
  rw [diagOmega, ← map_pow, ← map_one (diagHom (K := K) 3)]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using h3
  · simp [inv_pow, h3]

private theorem cyc_conj_diagOmega {ω : Kˣ} (h3 : ω ^ 3 = 1) :
    (cycGL : GL (Fin 3) K) * diagOmega ω * cycGL⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * diagOmega ω := by
  rw [diagOmega, cycGL_conj_diagHom, scalar_eq_diagHom, ← map_mul]
  congr 1
  funext i
  have h2 : ω⁻¹ * ω⁻¹ = ω := by
    have : ω * ω * ω = 1 := by rw [← pow_three']; exact h3
    calc ω⁻¹ * ω⁻¹ = ω⁻¹ * ω⁻¹ * (ω * ω * ω) := by rw [this, mul_one]
      _ = ω := by group
  fin_cases i
  · simp
  · simp
  · simp [h2]

private theorem scalar_mem_center (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

theorem two_le_pRank_three_statedProj_statedSL_three [Finite K] {ω : Kˣ} (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) := by
  have hcycH : (cycGL : GL (Fin 3) K) ∈ StatedSL 3 K := (monomialData_statedSL (K := K)).cyc_mem
  let dH : ↥(StatedSL 3 K) := ⟨diagOmega ω, diagOmega_mem ω⟩
  let cH : ↥(StatedSL 3 K) := ⟨cycGL, hcycH⟩
  have hdH3 : dH ^ 3 = 1 := Subtype.ext (diagOmega_pow_three h3)
  have hcH3 : cH ^ 3 = 1 := Subtype.ext cycGL_pow_three
  have hD : ∀ x : ↥(StatedSL 3 K), (QuotientGroup.mk x : StatedProj (StatedSL 3 K)) = 1 →
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = (x : GL (Fin 3) K) := by
    intro x hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    exact hx
  refine two_le_pRank_three_of_commuting (a := (QuotientGroup.mk dH : StatedProj (StatedSL 3 K)))
    (b := (QuotientGroup.mk cH : StatedProj (StatedSL 3 K))) ?_ ?_ ?_ ?_ ?_
  · rw [← QuotientGroup.mk_pow, hdH3]
    rfl
  · rw [← QuotientGroup.mk_pow, hcH3]
    rfl
  · show _ * _ = _ * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨ω⁻¹, ?_⟩
    have hconj := cyc_conj_diagOmega (K := K) h3
    have hcd : (cycGL : GL (Fin 3) K) * diagOmega ω =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * diagOmega ω * cycGL := by
      rw [← hconj]
      group
    have hs := Subgroup.mem_center_iff.1 (scalar_mem_center (K := K) ω⁻¹)
      (diagOmega ω * cycGL)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, dH, cH]
    rw [hcd, mul_assoc, ← hs, inv_mul_cancel_left]
  · intro h
    obtain ⟨c, hc⟩ := hD dH h
    have hc' : diagHom 3 (fun _ => c) = diagHom (K := K) 3 ![1, ω, ω⁻¹] := by
      rw [← scalar_eq_diagHom]
      exact hc
    have := diagHom_injective 3 hc'
    have h0 := congrFun this 0
    have h1' := congrFun this 1
    simp at h0 h1'
    exact h1 (h1'.symm.trans h0)
  · intro k hk
    have hk' : (QuotientGroup.mk (dH ^ k) : StatedProj (StatedSL 3 K)) = QuotientGroup.mk cH := by
      rw [QuotientGroup.mk_zpow]
      exact hk
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hk'
    obtain ⟨c, hc⟩ := hk'
    have hdiag : (cycGL : GL (Fin 3) K) = diagHom 3 (![1, ω, ω⁻¹] ^ k * fun _ => c) := by
      rw [map_mul, ← scalar_eq_diagHom, map_zpow, hc]
      simp [dH, cH, diagOmega]
    generalize ![1, ω, ω⁻¹] ^ k * (fun _ => c) = w at hdiag
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
      hdiag) 1) 0
    rw [coe_cycGL, coe_diagHom] at this
    simp [cycMat] at this

end PSLThree

end R3c

theorem rankTwoFamilies153_holds : RankTwoFamilies153 := by
  intro X _ _ hZ hcases
  rw [R3c.pRank_three_top_eq_center_quotient hZ]
  have key : ∀ n : ℕ, Even n → IsPSL 3 2 n (X ⧸ Subgroup.center X) →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
    intro n hn h
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    obtain ⟨ω, h3, h1⟩ := R3c.exists_cube_root_of_card_two_pow hn hK
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact R3c.two_le_pRank_three_statedProj_statedSL_three h3 h1
  rcases hcases with ⟨n, hn, h⟩ | h
  · exact key n hn h
  · exact key 2 (by decide) h

end CFSG.Quasithin
