module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFieldTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFieldLinearCore
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem false_of_fieldAut_five_psl {L : Type} [Group L] [Finite L] {n p f : ℕ}
    (hp : p.Prime) (hn : 5 ≤ n) (hadm : StatedLieAdmissible .PSL n p f)
    (hL : LieModel L .PSL n p f) (hq5 : p ^ f % 5 = 2 ∨ p ^ f % 5 = 3)
    (θ : MulAut L) (hθ : orderOf θ = 5) (hout : θ ∉ (MulAut.conj : L →* MulAut L).range)
    (M : Subgroup L) (hM : M ≠ ⊤) (hfix : ∀ y : L, θ y = y → y ∈ M)
    (hcent : ∀ x ∈ M, orderOf x = 5 → ∀ g : L, Commute g x → g ∈ M) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hn3 : 3 ≤ n := by omega
  have hθ' : orderOf (MulAut.congr e θ) = 5 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have h := congrArg (fun α : MulAut (projectiveSL n K) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  have h5q : ¬ 5 ∣ Nat.card K - 1 := by
    rw [hK]
    generalize p ^ f = q at hq5 ⊢
    omega
  have hθr : MulAut.congr e θ ^ 5 = 1 := hθ' ▸ pow_orderOf_eq_one _
  have hθE : MulAut.congr e θ ∈ semilinearAutGroup n K :=
    mem_semilinearAutGroup_of_pow_odd hn3 (by decide) hθr
  have hθD : MulAut.congr e θ ∉ linearAutGroup n K := fun hD =>
    hout' (KCLinPlane.inner_of_mem_linearAut_of_pow_eq_one hn3
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 fun h =>
        h5q (h.trans (Nat.gcd_dvd_right _ _))) hD hθr)
  obtain ⟨h5f, σ, -, ⟨δ, -, hδ⟩, hcard⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hp hadm.2.1 hn3 hK
      (by norm_num : Nat.Prime 5) hθE hθD hθ'
  have hKk : Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ 5 := by
    rw [hK, hcard, ← pow_mul, Nat.div_mul_cancel h5f]
  let ψ : L ≃* projectiveSL n K := e.trans (MulEquiv.symm δ)
  have hψ : ∀ y, ψ.symm y = e.symm (δ y) := fun _ => rfl
  have hk : (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range ≤
      M.map ψ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_map_equiv, hψ]
    apply hfix
    apply e.injective
    have hσy := fieldAut_linearSubfieldInclusion (k := semilinearFixedSubfield σ) (σ := σ)
      (fun c hc => by
        change σ c = c at hc
        exact hc) y
    have h1 := congrArg (fun α : MulAut (projectiveSL n K) =>
      α (δ (linearSubfieldInclusion n (semilinearFixedSubfield σ) y))) hδ
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hσy] at h1
    simpa [MulAut.congr_apply] using h1
  have hM' : M.map ψ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hM
    rw [eq_top_iff]
    intro y _
    have hy : ψ y ∈ M.map ψ.toMonoidHom := h ▸ Subgroup.mem_top _
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hy
  exact hM' (projectiveSL_eq_top_of_subfield_le hn _ hKk h5q _ hk
    (forall_commute_mem_map ψ hcent))

end Linear

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
