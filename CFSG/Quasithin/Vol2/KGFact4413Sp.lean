module

public import CFSG.Quasithin.Vol2.KGFact4413L2
public import CFSG.Quasithin.H13.KGFact22TorSp

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique
  CFSG.Quasithin.H13.KG22

variable {K : Type} [Field K]

local notation "Sp₄" => StatedSp 2 K
local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K

@[expose] noncomputable def spW' : Sp₄ :=
  lam 1 sl2W

theorem spW'_comm_spY (a : Kˣ) : spW' * spY a = spY a * (spW' : Sp₄) := by
  refine (statedSp_commute ?_).eq
  rw [spW', spY_apply, coe_lam, coe_torusHom]
  show _ * _ = _ * _
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairMat, Pi.mulSingle_apply]

theorem spW'_conj_spY (a : Kˣ) : spW' * spY a * (spW' : Sp₄)⁻¹ = spY a := by
  rw [spW'_comm_spY, mul_inv_cancel_right]

theorem spW'_conj_spY' (b : Kˣ) : spW' * spY' b * (spW' : Sp₄)⁻¹ = (spY' b)⁻¹ := by
  have h1 : spY' b = lam 1 (sl2Diag b) := by rw [spY'_apply, lam_sl2Diag]
  have h2 : spY' b⁻¹ = lam 1 (sl2Diag b⁻¹) := by rw [spY'_apply, lam_sl2Diag]
  rw [← map_inv, h1, h2, spW', ← map_inv, ← map_mul, ← map_mul, sl2W_conj_sl2Diag]

theorem spW_comm_spW' : spW * spW' = spW' * (spW : Sp₄) := by
  refine (statedSp_commute ?_).eq
  rw [spW, spW', coe_lam, coe_lam]
  refine (isSupp_pairMat _).commute (isSupp_pairMat _) ?_
  rw [Set.disjoint_left]
  rintro x (rfl | rfl) (h | h) <;> simp at h

variable [CharP K 2]

theorem sl2W_mul_self : (sl2W : SpecialLinearGroup (Fin 2) K) * sl2W = 1 := by
  rw [sl2W_mul_sl2W]
  have h : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [h, map_one]

@[expose] noncomputable def spW₀ : Sp₄ :=
  spW * spW'

theorem spW₀_mul_self : spW₀ * spW₀ = (1 : Sp₄) := by
  rw [spW₀, show spW * spW' * (spW * spW') = (spW * spW) * (spW' * (spW' : Sp₄)) by
    rw [mul_assoc, ← mul_assoc spW', ← spW_comm_spW', mul_assoc, mul_assoc]]
  rw [spW, spW', ← map_mul, ← map_mul, sl2W_mul_self, map_one, map_one, mul_one]

omit [CharP K 2] in
theorem spW₀_conj_spY (a : Kˣ) : spW₀ * spY a * (spW₀ : Sp₄)⁻¹ = (spY a)⁻¹ := by
  rw [spW₀, _root_.mul_inv_rev, show spW * spW' * spY a * (spW'⁻¹ * spW⁻¹) =
    spW * (spW' * spY a * spW'⁻¹) * spW⁻¹ by group, spW'_conj_spY, spW_conj_spY]

omit [CharP K 2] in
theorem spW₀_conj_spY' (b : Kˣ) : spW₀ * spY' b * (spW₀ : Sp₄)⁻¹ = (spY' b)⁻¹ := by
  rw [spW₀, _root_.mul_inv_rev, show spW * spW' * spY' b * (spW'⁻¹ * spW⁻¹) =
    spW * (spW' * spY' b * spW'⁻¹) * spW⁻¹ by group, spW'_conj_spY', ← map_inv,
    spW_conj_spY', map_inv]

omit [CharP K 2] in
theorem spW₀_not_mem_borel : (spW₀ : Sp₄) ∉ borelSubgroup 2 K := by
  intro h
  obtain ⟨A, C, -, -, -, hg⟩ := mem_borelSubgroup_iff.mp h
  have h1 := congrFun (congrFun hg (Sum.inr 0)) (Sum.inl 0)
  rw [blockMat, fromBlocks_apply₂₁] at h1
  have hsupp : IsSupp ({Sum.inl 1, Sum.inr 1} : Set (Fin 2 ⊕ Fin 2))
      (((spW' : Sp₄) : GL (Fin 2 ⊕ Fin 2) K) : M₄) := by
    rw [spW', coe_lam]
    exact isSupp_pairMat _
  have hcol : ∀ M : M₄, (M * (((spW' : Sp₄) : GL (Fin 2 ⊕ Fin 2) K) : M₄)) (Sum.inr 0)
      (Sum.inl 0) = M (Sum.inr 0) (Sum.inl 0) := by
    intro M
    have h2 := hsupp.transpose.mul_apply_of_notMem (x := Sum.inl 0) (by simp) Mᵀ (Sum.inr 0)
    rw [← Matrix.transpose_mul, Matrix.transpose_apply, Matrix.transpose_apply] at h2
    exact h2
  have h3 : (((spW₀ : Sp₄) : GL (Fin 2 ⊕ Fin 2) K) : M₄) (Sum.inr 0) (Sum.inl 0) = 1 := by
    rw [spW₀, Subgroup.coe_mul, Units.val_mul, hcol, spW, coe_lam]
    simp [pairMat]
  rw [h3] at h1
  simp at h1

omit [CharP K 2] in
theorem index_borelSubgroup_sp [Finite K] :
    (borelSubgroup 2 K).index = (Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + 1) := by
  have hSB : Nat.card (borelSubgroup 2 K) * (borelSubgroup 2 K).index =
      Nat.card (StatedSp 2 K) := (borelSubgroup 2 K).card_mul_index
  rw [card_borelSubgroup, card_statedSp] at hSB
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [ha] at hSB ⊢
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at hSB
  have ha1 : 1 ≤ a := by omega
  have e1 : (a + 1) ^ (2 * 1) - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (a + 1) ^ (2 * 2) - 1 = a * (a + 2) * ((a + 1) ^ 2 + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, Nat.add_sub_cancel] at hSB
  have hpos : 0 < (a + 1) ^ (2 ^ 2) * a ^ 2 := by positivity
  have key : ((a + 1) ^ (2 ^ 2) * a ^ 2) * (borelSubgroup 2 K).index =
      ((a + 1) ^ (2 ^ 2) * a ^ 2) * ((a + 2) ^ 2 * ((a + 1) ^ 2 + 1)) := by
    rw [hSB]
    ring
  calc (borelSubgroup 2 K).index = (a + 2) ^ 2 * ((a + 1) ^ 2 + 1) :=
        Nat.eq_of_mul_eq_mul_left hpos key
    _ = (a + 1 + 1) ^ 2 * ((a + 1) ^ 2 + 1) := by ring

@[expose] noncomputable def dSp (F : Type) [Field F] [CharP F 2] :
    Subgroup (StatedProj (StatedSp 2 F)) :=
  ((spY : Fˣ →* StatedSp 2 F).range ⊔ (spY' : Fˣ →* StatedSp 2 F).range).map (proj 2 F)

omit [CharP K 2] in
theorem exists_mul_of_mem_sup {x : Sp₄}
    (hx : x ∈ (spY : Kˣ →* Sp₄).range ⊔ (spY' : Kˣ →* Sp₄).range) :
    ∃ a b : Kˣ, x = spY a * spY' b := by
  have hN : (spY : Kˣ →* Sp₄).range ≤
      Subgroup.normalizer ((spY' : Kˣ →* Sp₄).range : Set Sp₄) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (spY_comm a b).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := hx
  exact ⟨a, b, rfl⟩

theorem pow_eq_one_of_mem_dSp {d : StatedProj Sp₄} (hd : d ∈ dSp K) :
    d ^ (Nat.card K - 1) = 1 := by
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨a, b, rfl⟩ := exists_mul_of_mem_sup hx
  have hc : Commute (spY a) (spY' b) := spY_comm a b
  rw [← map_pow, hc.mul_pow, ← map_pow, ← map_pow, units_pow_card_sub_one, units_pow_card_sub_one,
    map_one, map_one, mul_one, map_one]

theorem proj_spW₀_conj_dSp {d : StatedProj Sp₄} (hd : d ∈ dSp K) :
    proj 2 K spW₀ * d * (proj 2 K spW₀)⁻¹ = d⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨a, b, rfl⟩ := exists_mul_of_mem_sup hx
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  calc spW₀ * (spY a * spY' b) * spW₀⁻¹ =
        (spW₀ * spY a * spW₀⁻¹) * (spW₀ * spY' b * spW₀⁻¹) := by group
    _ = (spY a)⁻¹ * (spY' b)⁻¹ := by rw [spW₀_conj_spY, spW₀_conj_spY']
    _ = (spY a * spY' b)⁻¹ := by
      rw [_root_.mul_inv_rev, ← map_inv, ← map_inv, spY_comm]

variable [Finite K]

theorem normalizer_projUnipotent_two :
    Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj Sp₄)) =
      (borelSubgroup 2 K).map (proj 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnipotent 2 (by norm_num)]
  rfl

omit [Finite K] [CharP K 2] in
theorem proj_spW₀_not_mem : proj 2 K spW₀ ∉ (borelSubgroup 2 K).map (proj 2 K) := by
  intro h
  have h1 : spW₀ ∈ ((borelSubgroup 2 K).map (proj 2 K)).comap (proj 2 K) := h
  rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 ?_] at h1
  · exact spW₀_not_mem_borel h1
  · rw [← isoFlagStabilizer_flag]
    exact spScalars_le_isoFlagStabilizer _

theorem isPGroup_projUnipotent_two : IsPGroup 2 (projUnipotent 2 K) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  rw [← hP]
  exact P.isPGroup'

theorem dSp_complement :
    dSp K ≤ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj Sp₄)) ∧
      Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj Sp₄)) ≤
        dSp K ⊔ projUnipotent 2 K ∧ dSp K ⊓ projUnipotent 2 K = ⊥ := by
  rw [normalizer_projUnipotent_two]
  refine ⟨?_, ?_, ?_⟩
  · refine Subgroup.map_mono (sup_le ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact spY_mem_borel a
    · rintro _ ⟨b, rfl⟩
      exact spY'_mem_borel b
  · have h := Subgroup.map_mono (f := proj 2 K) (borel_le (K := K))
    rw [Subgroup.map_sup] at h
    exact h
  · rw [eq_bot_iff]
    rintro x ⟨hxD, hxU⟩
    obtain ⟨m, hm⟩ := isPGroup_projUnipotent_two ⟨x, hxU⟩
    have hm' : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hodd : Odd (orderOf x) := by
      have h1 := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_dSp hxD)
      exact (RankThree.PartOne.K159.odd_card_sub_one (K := K)).of_dvd_nat h1
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_pow_two_pow hodd hm')

theorem weylOut_projSp4 {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    WeylOut (projUnipotent 2 K) (dSp K) n := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  refine ⟨fun p hp hp2 hpq => ?_, fun d hd => ?_, proj 2 K spW₀, ?_, ?_,
    fun d hd => ⟨fun _ => proj_spW₀_conj_dSp hd, fun h1 => ?_⟩⟩
  · rw [normalizer_projUnipotent_two, Subgroup.index_map_eq _ proj_surjective ?_,
      index_borelSubgroup_sp]
    · rw [← hK] at hpq
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact not_dvd_pow_add_one hp hp2 hq hpq 1 (by rw [pow_one]; exact hp.dvd_of_dvd_pow h1)
      · exact not_dvd_pow_add_one hp hp2 hq hpq 2 h1
    · rw [ker_proj, ← isoFlagStabilizer_flag]
      exact spScalars_le_isoFlagStabilizer _
  · rw [pow_mul, ← hK, pow_eq_one_of_mem_dSp hd, one_pow]
  · rw [normalizer_projUnipotent_two]
    exact proj_spW₀_not_mem
  · rw [← map_mul, spW₀_mul_self, map_one]
  · rw [proj_spW₀_conj_dSp hd]
    have h2 := pow_eq_one_of_mem_dSp hd
    rw [hK] at h2
    have h3 : d ^ 2 = 1 := by
      have e : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rw [e, pow_add, h2, one_mul] at h1
      exact h1
    exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h3)

theorem cartanWeyl_projSp4 {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CartanWeyl (StatedProj (StatedSp 2 K)) n := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hS : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hP ▸ isSylowTwoOf_of_sylow P
  obtain ⟨h1, h2, h3⟩ := dSp_complement (K := K)
  exact cartanWeyl_of_exists hS h1 h2 h3 (weylOut_projSp4 hK)

theorem cartanWeyl_of_isPSp4 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hX : IsPSp4 2 n X) :
    CartanWeyl X n := by
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  exact cartanWeyl_of_mulEquiv (cartanWeyl_projSp4 hK) e.symm

end CFSG.Quasithin.H13.KG4413
