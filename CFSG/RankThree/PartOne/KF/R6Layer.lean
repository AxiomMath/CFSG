module

public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.R6Levi
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg Matrix

theorem kf1212LayerRow6 : KF1212LayerRow 6 := by
  intro G _ _ p A c L E ctx hmodel hEA _
  have hEA' : E = A := hEA (by norm_num)
  have h := ctx.hyp
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, hchar, hK, hf1, hpq, ⟨ζ₀, hζ₀⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame (n := 5) (Or.inr rfl) d8Comb_five hcore hmodel
  have : Fact p.Prime := ⟨hp⟩
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by omega)
    omega) hpq
  have hK6 : 6 ≤ 2 ^ f := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u := by
    intro u hu
    have h2 : u ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hu, one_pow]
    show unitaryInvolution K 2 f (u : K) = u
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    have : u ^ 2 ^ f = u := by
      calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = u := by rw [h2, one_mul]
    rw [this]
  have hζp' : ζ₀ ^ p = 1 := hζ₀.pow_eq_one
  have hζ1 : ζ₀ ≠ 1 := hζ₀.ne_one (by omega)
  have hζ2 : ζ₀ ^ 2 ≠ 1 := hζ₀.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
  have hσζ : σ (ζ₀ : K) = ζ₀ := hfix ζ₀ hζp'
  have hq : IsCentralPQuot p (suQ 5 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hbMT : b6 σ ζ₀ hσζ ∈ torus6 σ p := b6_mem_torus6 hσζ hζp'
  have hbMp : b6 σ ζ₀ hσζ ^ p = 1 := torus6_pow_eq_one hbMT
  have hbMne : b6 σ ζ₀ hσζ ≠ 1 := by
    intro h1
    have := congrArg (fun x : ↥(SU σ 5) => gu5 x 0 0) h1
    simp only [gu5_one, Matrix.one_apply_eq] at this
    have h11 : gu5 (b6 σ ζ₀ hσζ) 0 0 = (ζ₀ : K) := by
      show ((diagU (dvec5 ζ₀ ζ₀) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 0 = _
      simp [diagU_val, dvec5]
    exact hζ1 (Units.ext (by rw [← h11]; exact this))
  obtain ⟨x, hx⟩ := hFT₁ (b6 σ ζ₀ hσζ) hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA' ▸ x.2.1
  have hbb : ε ⟨(x : G), hxL⟩ = suQ 5 hK (b6 σ ζ₀ hσζ) := hx
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : suQ 5 hK (b6 σ ζ₀ hσζ) = suQ 5 hK 1 := by
      rw [← hbb, map_one]
      have : (⟨(x : G), hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact hbMne (hq.eq_of_map_eq hbMp (one_pow p) h2)
  have hAL : A ⊓ L = E ⊓ L := by rw [hEA']
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 σ p).map (suQ 5 hK) := by
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hKM := perfectResidual_centralizer_b6 σ hσσ hK4 hσζ hζ1 hζ2
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    calc A = E := hEA'.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := ctx.generic.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε
    (suQ 5 hK) hε hq hxA hxL hbMp hbb
    (T₀ := torus6 σ p) (U := rootU6 σ hσσ) (fun t ht => torus6_pow_eq_one ht) hAT
    (isQuasisimple_perfectResidual_centralizer_b6 σ hσσ hK4 hσζ hζ1 hζ2)
    (by
      rw [hKM, card_center_range_suBlock6]
      exact hp.not_dvd_one)
    (by
      rw [hKM]
      exact card_torus6_inf_range hσσ hp.pos hfix ⟨ζ₀, hζ₀⟩)
    (by rw [hKM]; exact rootU6_le_range hσσ) (isPGroup_rootU6 hσσ)
    (torus6_le_normalizer_rootU6 hσσ)
    ⟨suBlock6 σ hσσ (tr2 1), suBlock6_tr2_mem_rootU6 hσσ 1, rho6 σ hσσ ζ₀,
      rho6_mem_torus6 hσσ hζp' hσζ, suBlock6_tr2_one_not_commute_rho6 hσσ hζ1⟩
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  have hK2 : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hpq2 : p ∣ 2 ^ (2 * f) - 1 := by
    have h1 : 2 ^ f - 1 ∣ (2 ^ (2 * f)) - 1 := by
      have e : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
        have hq2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        have e2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [e2]
        zify [Nat.one_le_pow 2 (2 ^ f) (by omega), hq2]
        ring
      rw [e]
      exact dvd_mul_right _ _
    exact hpq.trans h1
  refine ⟨by norm_num, by norm_num, 2 * f, by omega, hpq2,
    ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩, K, hKf, hKfin, hK2, ?_⟩
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.snd h2
    simp only at this
    omega
  · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
    obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv
      (MonoidHom.ofInjective (suBlock6_injective σ hσσ)).symm
    exact ⟨eqv.trans (e₃.trans (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)))⟩

end CFSG.RankThree.PartOne
