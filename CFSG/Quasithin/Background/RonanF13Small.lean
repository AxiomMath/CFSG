module

public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitaryTwo
public import CFSG.Quasithin.Background.GoldschmidtRankOneSmall

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanF13

theorem SelfNormSylow.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : SelfNormSylow K) : SelfNormSylow K' := by
  intro T' hp hodd
  set T : Subgroup K := T'.comap e.toMonoidHom with hT
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hnorm : ∀ x : K, x ∈ Subgroup.normalizer (T : Set K) ↔
      e x ∈ Subgroup.normalizer (T' : Set K') := by
    intro x
    have := Subgroup.comap_normalizer_eq_of_surjective T' hsurj
    change x ∈ Subgroup.normalizer ((T'.comap e.toMonoidHom : Subgroup K) : Set K) ↔ _
    rw [← this]
    exact Iff.rfl
  have hpT : IsPGroup 2 T := hp.comap_of_injective e.toMonoidHom e.injective
  have hoddT : ¬ 2 ∣ T.index := by
    rw [hT, Subgroup.index_comap_of_surjective T' hsurj]
    exact hodd
  have hN : Subgroup.normalizer (T : Set K) = T := h T hpT hoddT
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  calc e x ∈ Subgroup.normalizer (T' : Set K') ↔ x ∈ Subgroup.normalizer (T : Set K) :=
        (hnorm x).symm
    _ ↔ x ∈ T := by rw [hN]
    _ ↔ e x ∈ T' := Iff.rfl

theorem selfNormSylow_of_card_two_pow_mul_prime {K : Type*} [Group K] [Finite K] {a p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a) (hcard : Nat.card K = 2 ^ a * p)
    (hO : CFSG.Open.pCore 2 K = ⊥) : SelfNormSylow K := by
  intro T hT hodd
  obtain ⟨hi, hTc⟩ := CFSG.Quasithin.index_eq_of_card_two_pow_mul_prime hp hp2 hcard hT hodd
  have hnn : ¬ T.Normal := by
    intro hN
    have hle : T ≤ CFSG.Open.pCore 2 K := CFSG.LieType.BorelTits.le_pCore 2 hN hT
    rw [hO, le_bot_iff] at hle
    have h1 : Nat.card T = 1 := by rw [hle]; exact Subgroup.card_bot
    rw [hTc] at h1
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hmax : ∀ M : Subgroup K, T ≤ M → M ≠ ⊤ → M = T := by
    intro M hTM hM
    have h1 : T.relIndex M * M.index = T.index := Subgroup.relIndex_mul_index hTM
    rw [hi] at h1
    have hMi : M.index ≠ 1 := fun h => hM (Subgroup.index_eq_one.mp h)
    have hMd : M.index ∣ p := ⟨T.relIndex M, by rw [← h1]; ring⟩
    have hMp : M.index = p := ((Nat.dvd_prime hp).mp hMd).resolve_left hMi
    rw [hMp] at h1
    have h2 : T.relIndex M = 1 := by
      have : T.relIndex M * p = 1 * p := by rw [h1, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    exact (Subgroup.relIndex_eq_one.mp h2).antisymm hTM
  refine hmax _ Subgroup.le_normalizer ?_
  intro h
  exact hnn (Subgroup.normalizer_eq_top_iff.mp h)

theorem selfNormSylow_perm_three : SelfNormSylow (Equiv.Perm (Fin 3)) := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 2 ^ 1 * 3 := by
    rw [Nat.card_perm]; simp [Nat.factorial]
  have h01 : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have h02 : orderOf (Equiv.swap (0 : Fin 3) 2) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  refine selfNormSylow_of_card_two_pow_mul_prime Nat.prime_three (by norm_num) le_rfl hcard ?_
  exact CFSG.Quasithin.pCore_eq_bot_of_two_involutions Nat.prime_three (by norm_num)
    (by simpa using hcard) h01 h02 (by decide)

theorem selfNormSylow_of_perm_three {K : Type*} [Group K] (e : K ≃* Equiv.Perm (Fin 3)) :
    SelfNormSylow K :=
  SelfNormSylow.of_mulEquiv e.symm selfNormSylow_perm_three

theorem selfNormSylow_of_psl_two_one {K : Type*} [Group K]
    (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)) :
    SelfNormSylow K := by
  obtain ⟨e'⟩ := CFSG.Quasithin.isL2Quot_one_iff_perm3.1 ⟨e⟩
  exact selfNormSylow_of_perm_three e'

theorem selfNormSylow_dihedral_five : SelfNormSylow (DihedralGroup 5) := by
  have hcard : Nat.card (DihedralGroup 5) = 2 ^ 1 * 5 := by
    rw [DihedralGroup.nat_card]; norm_num
  have h0 : orderOf (DihedralGroup.sr (0 : ZMod 5)) = 2 := DihedralGroup.orderOf_sr 0
  have h1 : orderOf (DihedralGroup.sr (1 : ZMod 5)) = 2 := DihedralGroup.orderOf_sr 1
  refine selfNormSylow_of_card_two_pow_mul_prime Nat.prime_five (by norm_num) le_rfl hcard ?_
  exact CFSG.Quasithin.pCore_eq_bot_of_two_involutions Nat.prime_five (by norm_num)
    (by simpa using hcard) h0 h1 (by decide)

theorem selfNormSylow_of_dihedral_five {K : Type*} [Group K] (e : K ≃* DihedralGroup 5) :
    SelfNormSylow K :=
  SelfNormSylow.of_mulEquiv e.symm selfNormSylow_dihedral_five

theorem selfNormSylow_sz_zero : SelfNormSylow ↥(CFSG.Open.Sz 0) := by
  have hcard : Nat.card ↥(CFSG.Open.Sz 0) = 2 ^ 2 * 5 := by
    rw [CFSG.Quasithin.card_sz_zero_eq_twenty]; norm_num
  exact selfNormSylow_of_card_two_pow_mul_prime Nat.prime_five (by norm_num) (by norm_num) hcard
    CFSG.Quasithin.pCore_two_sz_zero_eq_bot

theorem selfNormSylow_of_sz_zero {K : Type*} [Group K] (e : K ≃* CFSG.Open.Sz 0) :
    SelfNormSylow K :=
  SelfNormSylow.of_mulEquiv e.symm selfNormSylow_sz_zero

theorem selfNormSylow_of_two_transitive {G Ω : Type*} [Group G] [Finite G]
    (ρ : G →* Equiv.Perm Ω)
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, ρ g a = c ∧ ρ g b = d)
    (hne : ∃ a b : Ω, a ≠ b) (hρ : Function.Injective ρ) (ω : Ω)
    (hp : IsPGroup 2 (CFSG.Quasithin.pointStab ρ ω))
    (hodd : ¬ 2 ∣ (CFSG.Quasithin.pointStab ρ ω).index)
    (hnt : CFSG.Quasithin.pointStab ρ ω ≠ ⊥) : SelfNormSylow G := by
  have hmax := CFSG.Quasithin.eq_pointStab_of_le ρ h2
  have hexists := CFSG.Quasithin.exists_smul_eq_of_two_transitive ρ h2 hne
  have hsyl : ∀ T : Subgroup G, IsPGroup 2 T → ¬ 2 ∣ T.index →
      ∃ x : Ω, T = CFSG.Quasithin.pointStab ρ x ∧ T ≠ ⊥ := by
    intro T hT hTodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hp.toSylow hodd) (hT.toSylow hTodd)
    have h1 : MulAut.conj g • CFSG.Quasithin.pointStab ρ ω = T := by
      have := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
      simpa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
    have hT' : T = CFSG.Quasithin.pointStab ρ (ρ g ω) := by
      ext h
      rw [← h1, CFSG.Quasithin.mem_pointStab_smul_iff]
    refine ⟨ρ g ω, hT', fun hbot => hnt ?_⟩
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    intro h hh
    have : g * h * g⁻¹ ∈ CFSG.Quasithin.pointStab ρ (ρ g ω) := by
      rw [CFSG.Quasithin.mem_pointStab_apply_iff]
      simpa [mul_assoc] using hh
    rw [← hT'] at this
    have h0 := hbot _ this
    simpa using h0
  have hnn : ∀ x : Ω, CFSG.Quasithin.pointStab ρ x ≠ ⊥ →
      ¬ (CFSG.Quasithin.pointStab ρ x).Normal := by
    intro x hx hN
    apply hx
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    apply hρ
    ext y
    obtain ⟨g, hg⟩ := hexists x y
    have h2' : t ∈ CFSG.Quasithin.pointStab ρ (ρ g x) := by
      rw [CFSG.Quasithin.mem_pointStab_apply_iff]
      have := hN.conj_mem t ht g⁻¹
      simpa using this
    rw [hg] at h2'
    rw [map_one]
    exact (CFSG.Quasithin.mem_pointStab ρ).mp h2'
  intro T hT hTodd
  obtain ⟨x, hx, hTnt⟩ := hsyl T hT hTodd
  subst hx
  have hne' : ¬ Subgroup.normalizer ((CFSG.Quasithin.pointStab ρ x : Subgroup G) : Set G) = ⊤ :=
    fun h => hnn x hTnt (Subgroup.normalizer_eq_top_iff.mp h)
  exact hmax x Subgroup.le_normalizer hne'

theorem selfNormSylow_of_nine_points {G Ω : Type*} [Group G] (ρ : G →* Equiv.Perm Ω)
    (pinf : Ω) (hinj : Function.Injective ρ)
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, ρ g a = c ∧ ρ g b = d)
    (hΩ : Nat.card Ω = 9) (hG : Nat.card G = 72)
    (hU : Nat.card (CFSG.Quasithin.pointStab ρ pinf) = 8) :
    SelfNormSylow G := by
  have hfinG : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hfinΩ : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  have hne : ∃ a b : Ω, a ≠ b := by
    have h1 : 1 < Nat.card Ω := by rw [hΩ]; norm_num
    obtain ⟨a, b, hab⟩ := (Finite.one_lt_card_iff_nontrivial.mp h1).exists_pair_ne
    exact ⟨a, b, hab⟩
  have hp : IsPGroup 2 (CFSG.Quasithin.pointStab ρ pinf) :=
    IsPGroup.of_card (n := 3) (by rw [hU]; norm_num)
  have hidx : (CFSG.Quasithin.pointStab ρ pinf).index = 9 := by
    have hm := (CFSG.Quasithin.pointStab ρ pinf).card_mul_index
    rw [hU, hG] at hm
    omega
  have hnt : CFSG.Quasithin.pointStab ρ pinf ≠ ⊥ := by
    intro hbot
    have := hU
    rw [hbot, Subgroup.card_bot] at this
    omega
  exact selfNormSylow_of_two_transitive ρ h2 hne hinj pinf hp (by rw [hidx]; norm_num) hnt

theorem selfNormSylow_statedProj_one {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) :
    SelfNormSylow (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ 1) F)) := by
  obtain ⟨σ, hσ, hfix, ⟨e⟩⟩ :=
    CFSG.Quasithin.exists_statedProj_equiv_psu (n := 1) one_ne_zero hF
  refine SelfNormSylow.of_mulEquiv e.symm ?_
  have H := CFSG.BenderSuzuki.External.huppert_II_10_12
    (CFSG.RankTwoShapes.antidiagonalHermitianForm σ hσ) (2 ^ 1) hF hfix rfl
  dsimp only at H
  obtain ⟨hΩ, ρ, pinf, hinj, -, hUcard, -, h2, hGcard, -⟩ := H
  refine selfNormSylow_of_nine_points ρ pinf hinj h2 ?_ ?_ ?_
  · rw [hΩ]
    norm_num
  · rw [hGcard]
    norm_num
  · change Nat.card ↥(Subgroup.comap ρ _) = 8
    rw [hUcard]
    norm_num

end CFSG.Quasithin.RonanF13
