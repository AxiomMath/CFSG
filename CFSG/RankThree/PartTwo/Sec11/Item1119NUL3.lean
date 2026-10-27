module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Pure
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Mat
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUFam
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCenter

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119NU

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.Sec11.KS11LieProof
open CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar
open Matrix

section Model

variable {Z : Type} [Group Z] [Finite Z]
variable {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]

theorem numFamL3_of_model (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Z ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {e : Kfˣ}
    {α σ : MulAut Z} {J : Subgroup Z} {ξ : Z}
    (hα : ∀ m, (MulAut.congr φ α m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹)
    (hJ : ∀ j : Z, j ∈ J ↔ ∃ B : slPi π 2 (p ^ f) Kf, φ j = blockProj hKf hh₀ B)
    (hξ : IsSylowOf 3 (Subgroup.zpowers ξ) J)
    (hLB : ∀ ζ : Z, (∃ k : ℕ, ζ ^ 3 ^ k = 1) → α ζ = ζ → (∀ j ∈ J, ζ * j * ζ⁻¹ = j) →
      orderOf (MulAut.conj ζ) ≤ orderOf σ) :
    orderOf ξ ≤ 3 * orderOf σ := by
  classical
  have hQne : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hKf hq
  have hQ3 : 3 ∣ qSubPi π (p ^ f) := three_dvd_qSubPi hq
  set a := (qSubPi π (p ^ f)).factorization 3 with ha
  have ha1 : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd Nat.prime_three hQne hQ3
  have hcent : Function.Injective (MulAut.conj : Z →* MulAut Z) := by
    intro x y hxy
    apply φ.injective
    apply conj_injective_projImage hKf hq hq2
    have h := congrArg (MulAut.congr φ) hxy
    rwa [congr_conj_eq, congr_conj_eq] at h
  have hJcard : Nat.card J = Nat.card (slPi π 2 (p ^ f) Kf) := by
    have hψinj : Function.Injective
        (φ.symm.toMonoidHom.comp (blockProj hKf hh₀)) :=
      φ.symm.injective.comp (blockProj_injective hKf hh₀)
    have hJψ : J = (φ.symm.toMonoidHom.comp (blockProj hKf hh₀)).range := by
      ext j
      rw [hJ j]
      constructor
      · rintro ⟨B, hB⟩
        refine ⟨B, ?_⟩
        change φ.symm (blockProj hKf hh₀ B) = j
        rw [← hB, MulEquiv.symm_apply_apply]
      · rintro ⟨B, rfl⟩
        refine ⟨B, ?_⟩
        change φ (φ.symm (blockProj hKf hh₀ B)) = _
        rw [MulEquiv.apply_symm_apply]
    rw [hJψ]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hξo : orderOf ξ = 3 ^ a := by
    rw [orderOf_eq_three_pow_of_isSylowOf hξ, hJcard, factorization_card_slPi_two hKf hq]
  have hlow : 3 ^ a ≤ 3 * orderOf σ := by
    obtain ⟨u, hu, huo⟩ := exists_orderOf_eq_three_pow hKf hq
    obtain ⟨x, hx⟩ := exists_mem_projImage_diagE_cube hKf hh₀ hu
    have huo' : orderOf u = 3 ^ a := huo
    have hxo : orderOf (MulAut.conj x) = 3 ^ (a - 1) := by
      rw [orderOf_conj_of_coe_eq hKf hq hq2 x hx,
        orderOf_pow_of_dvd (by norm_num) (by rw [huo']; exact dvd_pow_self 3 (by omega)), huo']
      obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [hb, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      simp
    have hζo : orderOf (MulAut.conj (φ.symm x)) = 3 ^ (a - 1) := by
      rw [← hxo, ← MulEquiv.orderOf_eq (MulAut.congr φ), congr_conj_eq, MulEquiv.apply_symm_apply]
    have hζ3 : ∃ k : ℕ, (φ.symm x) ^ 3 ^ k = 1 := by
      refine ⟨a - 1, hcent ?_⟩
      rw [map_pow, map_one, ← hζo]
      exact pow_orderOf_eq_one _
    have hαζ : α (φ.symm x) = φ.symm x := by
      apply φ.injective
      rw [← congr_apply_apply φ α, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hα, hx, mul_inv_eq_iff_eq_mul]
      exact mk_diagE_commute h₀ e (u ^ 3)
    have hζJ : ∀ j ∈ J, φ.symm x * j * (φ.symm x)⁻¹ = j := by
      intro j hj
      obtain ⟨B, hB⟩ := (hJ j).mp hj
      apply φ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hB]
      exact mul_blockProj_mul_inv_of_coe_eq hKf hh₀ x hx B
    have hle := hLB _ hζ3 hαζ hζJ
    rw [hζo] at hle
    obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [hb, pow_succ, mul_comm]
    rw [hb] at hle
    simpa using Nat.mul_le_mul_left 3 hle
  rw [hξo]
  exact hlow

theorem numFamL3 : NumFamL3 := by
  intro G _ _ Y K c s hcN hsN J ξ γ hZ D
  have hc3 := D.c_cube
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := exists_model hZ hcN hc3 D.K_comp
  obtain ⟨h₀, hh₀, e, -, -, hαc, hKblock⟩ :=
    core_block hcN hc3 D.K_comp D.K_type hKf hq hq2 φ
  have hblk := block_mem_image hcN hc3 D.K_comp D.K_type hKf hq hq2 φ hh₀ hαc hKblock
  have himg := exists_block_of_mem hKf φ hh₀ hKblock
  refine numFamL3_of_model hKf hq hq2 φ hh₀ (e := e) (α := Sec4.Item426.thetaAut Y hcN)
    (σ := Sec4.Item426.thetaAut Y hsN) (J := J) hαc ?_ D.xi_sylow D.lower_bound
  intro j
  rw [D.J_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact himg y (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨B, hB⟩
    obtain ⟨y, hyK, hy⟩ := hblk B
    refine ⟨y, Subgroup.mem_subgroupOf.mpr hyK, ?_⟩
    apply φ.injective
    rw [hB, ← hy]
    rfl

end Model

end CFSG.RankThree.PartTwo.Sec11.Item1119NU

end
