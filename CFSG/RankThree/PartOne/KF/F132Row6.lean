module

public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.F132Sl2
public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.F132AtEx
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KF.R6Levi
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem sec12TwoGeneric_row6 (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : Sec12Facts G p A c L E) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) : Sec12TwoGeneric p c L E := by
  rcases hF.two with hG | hS
  · exact hG
  · exfalso
    have hp5 := hS.p_eq
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h5 : ¬ 5 ∣ 2 ^ f + 1 := by
      intro h5
      rw [hp5] at hpq
      omega
    have hZL : Subgroup.center L = ⊥ := psu_five_center_bot hGA h5 hS.quasisimple hmod
    have hc := hS.center_card
    rw [hZL] at hc
    simp at hc

theorem row6_classB (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x)
    (hK : Nat.card K = 2 ^ (2 * f)) (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {P : Type} [Group P] [Finite P] (ε : ↥L →* P)
    (q : ↥(SU σ 5) →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 σ p).map q)
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L)
    (hb : q (b6 σ ζ (hfix ζ hζ.pow_eq_one)) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E (2 * f) t ∧
      ((kZero p E t).subgroupOf L).map ε = (suBlock6 σ hσσ).range.map q := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hσζ : σ (ζ : K) = ζ := hfix ζ hζp
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    apply hζ.pow_ne_one_of_pos_of_lt (by norm_num)
    omega
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hbmem : b6 σ ζ hσζ ∈ torus6 σ p := b6_mem_torus6 hσζ hζp
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : q (b6 σ ζ hσζ) = q 1 := by
      rw [hb, map_one]
      have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    have hbMne : b6 σ ζ hσζ ≠ 1 := by
      intro h1'
      have := congrArg (fun x : ↥(SU σ 5) => gu5 x 0 0) h1'
      simp only [gu5_one, Matrix.one_apply_eq] at this
      have h00 : gu5 (b6 σ ζ hσζ) 0 0 = (ζ : K) := by
        show ((diagU (dvec5 ζ ζ) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 0 = _
        simp [diagU_val, dvec5]
      exact hζ1 (Units.ext (by rw [← h00]; exact this))
    exact hbMne (hq.eq_of_map_eq (torus6_pow_eq_one hbmem) (one_pow p) h2)
  have hKM := perfectResidual_centralizer_b6 σ hσσ hK4 hσζ hζ1 hζ2
  obtain ⟨K₀, hd, hmod, hmap⟩ := layerCore_of_sl2_cover hp hp2 (IsPGroup.of_card h.A_card)
    h.A_elem h.L_le_centralizer hA ε q hε hq hxA hxL hx1 (torus6_pow_eq_one hbmem) hb.symm
    (fun t ht => torus6_pow_eq_one ht) hAT hK (by omega) (suBlock6 σ hσσ) (suBlock6_injective σ hσσ)
    hKM (card_torus6_inf_range hσσ hp.pos hfix hζex) (rootU6_le_range hσσ) (isPGroup_rootU6 hσσ)
    (torus6_le_normalizer_rootU6 hσσ)
    ⟨suBlock6 σ hσσ (tr2 1), suBlock6_tr2_mem_rootU6 hσσ 1, rho6 σ hσσ ζ,
      rho6_mem_torus6 hσσ hζp hσζ, suBlock6_tr2_one_not_commute_rho6 hσσ hζ1⟩
  obtain ⟨t, htL, hr, hfix', hKF, hKz⟩ := exists_reflection_of_core hGA h hEA hcL hd (by omega) hmod
  refine ⟨t, htL, hr, hfix', hKF, ?_⟩
  rw [hKz, hd.K_eq, hmap]

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.RankThree.PartOne.KF132

theorem kf132AtEx_row6 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132AtEx 6 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_row6 hGA hF hpq hmod
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ⟨ζ₀, hζ₀⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame_of (n := 5) (Or.inr rfl) d8Comb_five hcore hf1 hpq hmod
  let σ : K ≃+* K := unitaryInvolution K 2 f
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hK
  have hK2 : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hq : IsCentralPQuot p (suQ 5 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u := by
    intro u hu
    have h2 : u ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hu, one_pow]
    show unitaryInvolution K 2 f (u : K) = u
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : u ^ 2 ^ f = u := by
      calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = u := by rw [h2, one_mul]
    rw [this]
  have hζp : ζ₀ ^ p = 1 := hζ₀.pow_eq_one
  have hσζ : σ (ζ₀ : K) = ζ₀ := hfix ζ₀ hζp
  have hbMT : b6 σ ζ₀ hσζ ∈ torus6 σ p := b6_mem_torus6 hσζ hζp
  obtain ⟨x, hx⟩ := hFT₁ (b6 σ ζ₀ hσζ) hbMT
  have hxL : (x : G) ∈ L := hcore.F_le x.2
  have hxA : (x : G) ∈ A := hEA ▸ x.2.1
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 σ p).map (suQ 5 hK) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  obtain ⟨t, htL, hr, -, hKF, -⟩ := row6_classB hGA h hEA hcL hA hf3 σ hσσ hK2 hfix hζ₀ ε
    (suQ 5 hK) hε hq hAT hxA hxL hx.symm
  exact ⟨t, ⟨hr, L, hF13.inZeroStar, htL⟩, htL, f, 2 * f, ⟨hf1, hpq, hmod⟩, Or.inr rfl, hKF⟩

end CFSG.RankThree.PartOne.S13K
