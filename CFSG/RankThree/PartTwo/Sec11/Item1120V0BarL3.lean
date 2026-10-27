module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Pure
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Mat
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCenter

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1120V0Bar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.Sec11.KS11LieProof
open Matrix

section Model

variable {Z : Type} [Group Z] [Finite Z]
variable {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]

theorem congr_pow_form (φ : Z ≃* projImage (slPi π 3 (p ^ f) Kf)) {h₀ : GL (Fin 3) Kf} {l : Kfˣ}
    {σ : MulAut Z}
    (hσ : ∀ m, (MulAut.congr φ σ m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹))⁻¹) (n : ℕ) :
    ∀ m, (MulAut.congr φ (σ ^ n) m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹))⁻¹ := by
  intro m
  rw [map_pow, mulAut_pow_coe hσ n m, ← map_pow, conj_pow_gl, diagE_pow]

theorem mem_range_conj_of_cube (hKf : PiField π p f Kf)
    (φ : Z ≃* projImage (slPi π 3 (p ^ f) Kf)) {h₀ : GL (Fin 3) Kf}
    (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {t u : Kfˣ}
    (hu : u ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf) (ht : t = u ^ 3) {τ : MulAut Z}
    (hτ : ∀ m, (MulAut.congr φ τ m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹))⁻¹) :
    τ ∈ (MulAut.conj : Z →* MulAut Z).range := by
  obtain ⟨x, hx⟩ := exists_mem_projImage_diagE_cube hKf hh₀ hu
  refine ⟨φ.symm x, ?_⟩
  apply (MulAut.congr φ).injective
  rw [congr_conj_eq, MulEquiv.apply_symm_apply]
  ext m
  rw [hτ m, ht, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx]

theorem congr_apply_apply {X : Type} [Group X] (φ : Z ≃* X) (σ : MulAut Z) (z : Z) :
    MulAut.congr φ σ (φ z) = φ (σ z) := by
  show φ (σ (φ.symm (φ z))) = φ (σ z)
  rw [MulEquiv.symm_apply_apply]

theorem v0Concl_of_model (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Z ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {e l : Kfˣ}
    (hl : π = false → (l : Kf) ^ (p ^ f + 1) = 1)
    {α σ : MulAut Z} {J : Subgroup Z} {ξ γ : Z}
    (hα : ∀ m, (MulAut.congr φ α m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹)
    (hσ : ∀ m, (MulAut.congr φ σ m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹))⁻¹)
    (hJ : ∀ j : Z, j ∈ J ↔ ∃ B : slPi π 2 (p ^ f) Kf, φ j = blockProj hKf hh₀ B)
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J))
    (hξJ : ξ ∈ J) (hξ : IsSylowOf 3 (Subgroup.zpowers ξ) J)
    (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1)
    (hσξ : σ * MulAut.conj ξ = MulAut.conj ξ * σ)
    (hP : IsPGroup 3 (Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z))))
    (hLB : ∀ ζ : Z, (∃ k : ℕ, ζ ^ 3 ^ k = 1) → α ζ = ζ → (∀ j ∈ J, ζ * j * ζ⁻¹ = j) →
      orderOf (MulAut.conj ζ) ≤ orderOf σ) :
    V0Concl σ ξ γ := by
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
  have hord : orderOf σ = orderOf l := by
    rw [← MulEquiv.orderOf_eq (MulAut.congr φ) σ]
    exact orderOf_eq_orderOf_iff.mpr (fun n => pow_eq_one_iff_of_conj hKf hq hq2 hσ n)
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
  have hZ : (Nat.card Z).factorization 3 = 2 * a := by
    rw [Nat.card_congr φ.toEquiv, factorization_card_projImage hKf hq]
  have hσJ : ∀ j ∈ J, σ j = j := by
    intro j hj
    obtain ⟨B, hB⟩ := (hJ j).mp hj
    apply φ.injective
    rw [← congr_apply_apply φ σ j]
    apply Subtype.ext
    rw [hσ, hB, mul_inv_eq_iff_eq_mul, mk_diagE_commute_blockProj hKf hh₀ l B]
  have hdisj := zpowers_inf_zpowers_conj_eq_bot hJT hξJ
    ⟨a, by rw [← hξo]; exact pow_orderOf_eq_one ξ⟩ hσJ
  have hlmem : l ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf := mem_rootsOfUnity_qSubPi hKf hl
  have hσcube : σ ^ 3 ∈ (MulAut.conj : Z →* MulAut Z).range :=
    mem_range_conj_of_cube hKf φ hh₀ hlmem rfl (congr_pow_form φ hσ 3)
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
  have houter : σ ∉ (MulAut.conj : Z →* MulAut Z).range → 3 ^ a ≤ orderOf σ := by
    intro hσout
    by_contra hlt
    replace hlt := not_le.mp hlt
    apply hσout
    obtain ⟨k, hk⟩ := hσ3
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    have hja : j < a := by
      rw [hj] at hlt
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    have hl1 : l ^ (qSubPi π (p ^ f) / 3) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hord, hj]
      obtain ⟨r, hr⟩ : 3 ^ a ∣ qSubPi π (p ^ f) := Nat.ordProj_dvd _ 3
      obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hdiv : qSubPi π (p ^ f) / 3 = 3 ^ b * r := by
        rw [hr, hb, pow_succ, mul_comm (3 ^ b) 3, mul_assoc,
          Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hdiv]
      exact Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega)) r
    obtain ⟨u, hu, hul⟩ := exists_cube_root hKf hq hlmem hl1
    exact mem_range_conj_of_cube hKf φ hh₀ hu hul.symm hσ
  exact v0Concl_of_diag hcent hσ3 hσξ hdisj hξo hP hσcube hZ hlow houter

theorem v0FamL3 : V0FamL3 := by
  intro G _ _ Y K c s hcN hsN J ξ γ hZ D
  have hc3 := D.c_cube
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := exists_model hZ hcN hc3 D.K_comp
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn D.K_comp).trans inf_le_left
  obtain ⟨h₀, hh₀, e, -, -, hαc, hKblock⟩ :=
    core_block hcN hc3 D.K_comp D.K_type hKf hq hq2 φ
  have hblk := block_mem_image hcN hc3 D.K_comp D.K_type hKf hq hq2 φ hh₀ hαc hKblock
  have himg := exists_block_of_mem hKf φ hh₀ hKblock
  have hfix := tau_fixes_block hsN hKY D.s_comm_K hKf hq hq2 φ hh₀ hblk himg
  obtain ⟨k, hk⟩ := D.s_three
  have hβk : (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨s, hsN⟩))) ^ 3 ^ k =
      1 := by
    have h1 : (⟨s, hsN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [← map_pow, ← map_pow, ← map_pow, h1, map_one, map_one, map_one]
  obtain ⟨l, hl, hβl⟩ := aut_fix_block hKf hq hq2 hh₀ _ hβk hfix
  refine v0Concl_of_model hKf hq hq2 φ hh₀ hl (e := e) (α := Sec4.Item426.thetaAut Y hcN)
    (σ := Sec4.Item426.thetaAut Y hsN) (J := J) hαc hβl ?_ D.J_type D.xi_mem D.xi_sylow
    D.sigma_three D.sigma_xi D.P_three D.lower_bound
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

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
