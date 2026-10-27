module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137Opp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

section T2

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

theorem consL_injective : Function.Injective (consL (K := K) m) := fun u v h => by
  simpa using h

theorem blk_eq_of {M : SUid σ (m + 1)} (hM : M • (e0 K m) = e0 K m) {N : SUid σ m}
    (h : ∀ u : Fin m → K, M • consL m u = consL m (N • u)) : blk M hM = N :=
  ext_smul σ fun u => consL_injective (by rw [← smul_consL_eq_consL_blk hM u, h u])

@[expose] noncomputable def blkHom :
    ↥(MulAction.stabilizer (SUid σ (m + 1)) (e0 K m)) →* SUid σ m where
  toFun M := blk M.1 (MulAction.mem_stabilizer_iff.mp M.2)
  map_one' := blk_eq_of _ fun u => by simp
  map_mul' M M' := blk_eq_of _ fun u => by
    rw [Subgroup.coe_mul, mul_smul,
      smul_consL_eq_consL_blk (MulAction.mem_stabilizer_iff.mp M'.2),
      smul_consL_eq_consL_blk (MulAction.mem_stabilizer_iff.mp M.2), mul_smul]

theorem blkHom_injective : Function.Injective (blkHom (σ := σ) (m := m)) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  apply Subtype.ext
  apply ext_smul σ
  intro v
  have hfix : (M : SUid σ (m + 1)) • (e0 K m) = e0 K m := MulAction.mem_stabilizer_iff.mp M.2
  have hb : blk M.1 hfix = 1 := hM
  rw [eq_smul_single_add_consL v, smul_add, smul_add, smul_comm, hfix,
    smul_consL_eq_consL_blk hfix, hb, one_smul, Subgroup.coe_one, one_smul, one_smul]

theorem blkHom_surjective (hσ : IsUnitaryInvolution σ) (hT : T σ m = ⊤) :
    Function.Surjective (blkHom (σ := σ) (m := m)) := by
  intro N
  have hN : N ∈ T σ m := by
    rw [hT]
    exact Subgroup.mem_top N
  obtain ⟨g', -, h1, h2⟩ := transport hσ.invol (consL m) (fun u v => herm_consL u v) hN
  have he : g' • (e0 K m) = e0 K m := h2 _ fun u => herm_consL_single_zero u
  exact ⟨⟨g', he⟩, blk_eq_of he h1⟩

end T2

theorem exists_vecStab_SU4_nonsing_equiv {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {w : Fin 4 → F} (hw : ∑ i, w i ^ (2 ^ n + 1) ≠ 0) :
    Nonempty (↥(KTabC.vecStab (StatedSU 4 (2 ^ n) F).subtype w) ≃* ↥(StatedSU 3 (2 ^ n) F)) := by
  classical
  open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary in
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4,
    ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3]
  have hherm : CFSG.ClassicalGroups.Unitary.herm σ w w = ∑ i, w i ^ (2 ^ n + 1) := by
    simp only [CFSG.ClassicalGroups.Unitary.herm, hσdef,
      CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_succ]
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_smul_norm_one hσ (hherm ▸ hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨t, -, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_mem_T_smul_eq_of_norm_one hσ
    (Or.inl le_rfl) (CFSG.ClassicalGroups.Unitary.herm_e0_e0 (σ := σ) (n := 3)) hc
  have hq2 : 2 ^ n ≠ 2 := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hT : CFSG.ClassicalGroups.Unitary.T σ 3 = ⊤ :=
    CFSG.ClassicalGroups.Unitary.T_eq_top hσ (by norm_num)
      (fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hF hq2)
  have e3 := MulEquiv.ofBijective (blkHom (σ := σ) (m := 3))
    ⟨blkHom_injective, blkHom_surjective hσ hT⟩
  have hstab : KTabC.vecStab (CFSG.LieType.Universal.Unitary.SUid σ 4).subtype w =
      MulAction.stabilizer (CFSG.LieType.Universal.Unitary.SUid σ 4) (c • w) := by
    ext g
    rw [mem_vecStab_subtype, MulAction.mem_stabilizer_iff, smul_comm]
    constructor
    · intro h
      rw [CFSG.ClassicalGroups.Unitary.smul_def, h]
    · intro h
      exact smul_right_injective _ hc0 h
  exact ⟨((MulEquiv.subgroupCongr hstab).trans
    (MulAction.stabilizerEquivStabilizer ht.symm).symm).trans e3⟩

theorem three_two_pow_ne {n : ℕ} (hn : 2 ≤ n) : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ n = 2 := congrArg Prod.snd h
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem isSU3_statedSU_three {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) : IsSU3 ↥(StatedSU 3 (2 ^ n) F) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
    (f := n) hF le_rfl (three_two_pow_ne hn)
  refine ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
    ⟨Nat.prime_two, by omega, le_rfl, three_two_pow_ne hn⟩, F, inferInstance, inferInstance, hF,
    ⟨QuotientGroup.quotientMulEquivOfEq hZ⟩⟩⟩

theorem pCore_two_statedSU_three {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) : CFSG.pCore 2 ↥(StatedSU 3 (2 ^ n) F) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
    (f := n) hF le_rfl (three_two_pow_ne hn)
  have hle := GL83.I243.pCore_le_center Nat.prime_two
    (⟨hq.1.commutator_eq_top, hq.2.1⟩ : CFSG.Open.IsQuasisimple ↥(StatedSU 3 (2 ^ n) F))
  rw [eq_bot_iff]
  intro g hg
  have hgZ := hle hg
  rw [hZ, Subgroup.mem_subgroupOf] at hgZ
  obtain ⟨u, hu⟩ := hgZ
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU g.2
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    rw [Units.val_pow_eq_pow_val, hdet, Units.val_one]
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hu, ← map_pow, hu3, map_one, Subgroup.coe_one]
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(StatedSU 3 (2 ^ n) F))) ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 := pow_gcd_eq_one.mpr ⟨hg3, hk'⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  exact Subgroup.mem_bot.mpr h1

theorem exists_noncentral_statedSU_three {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    ∃ x : ↥(StatedSU 3 (2 ^ n) F), x ∉ Subgroup.center ↥(StatedSU 3 (2 ^ n) F) ∧
      ∃ k : ℕ, orderOf x = p ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : 2 ^ n ≠ 0 := by positivity
  obtain ⟨a, ha⟩ := CFSG.Open.StatedCenterThree.exists_orderOf_eq hF
  obtain ⟨d, hd⟩ := hpq
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd (hd.trans (mul_zero p)) (Nat.succ_ne_zero _)
  set μ : Fˣ := a ^ d with hμ
  have hμord : orderOf μ = p := by
    rw [hμ, orderOf_pow' a hd0, ha, hd, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
  have hμq : μ ^ (2 ^ n + 1) = 1 := by
    rw [hd, ← orderOf_dvd_iff_pow_eq_one, hμord]
    exact dvd_mul_right p d
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hμord
    exact hp.one_lt.ne hμord
  have hμinv : μ ≠ μ⁻¹ := by
    intro h
    have h2 : μ ^ 2 = 1 := by rw [sq]; nth_rw 2 [h]; exact mul_inv_cancel μ
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hμord] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  let x : ↥(StatedSU 3 (2 ^ n) F) :=
    ⟨CFSG.Open.StatedCenterThree.diagGL μ, CFSG.Open.StatedCenterThree.diagGL_mem hq0 hμq⟩
  refine ⟨x, ?_, 1, ?_⟩
  · intro hx
    have hc := Subgroup.mem_center_iff.mp hx
      ⟨CFSG.Open.StatedCenterThree.cyc3GL, CFSG.Open.StatedCenterThree.cyc3GL_mem hq0⟩
    have hc' := congrArg (fun z : ↥(StatedSU 3 (2 ^ n) F) =>
      ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hc
    simp only [Subgroup.coe_mul, Units.val_mul] at hc'
    have h := CFSG.Open.StatedCenterThree.eq_of_diagonal_commute_cyc3 (K := F)
      (x := ![(μ : F), ((μ⁻¹ : Fˣ) : F), 1]) hc'.symm
    apply hμinv
    exact (Units.ext h.1).symm
  · rw [pow_one]
    apply orderOf_eq_prime
    · apply Subtype.ext
      apply Units.ext
      simp only [x, Subgroup.coe_pow, Units.val_pow_eq_pow_val, CFSG.Open.StatedCenterThree.diagGL,
        Matrix.diagonal_pow, Subgroup.coe_one, Units.val_one]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      have h1 : μ ^ p = 1 := hμord ▸ pow_orderOf_eq_one μ
      fin_cases i
      · simp [← Units.val_pow_eq_pow_val, h1]
      · simp [← Units.val_pow_eq_pow_val, inv_pow, h1]
      · simp
    · intro h
      have h' := congrArg (fun z : ↥(StatedSU 3 (2 ^ n) F) =>
        ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) h
      simp [x, CFSG.Open.StatedCenterThree.diagGL] at h'
      exact hμ1 h'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
