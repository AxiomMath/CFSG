module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofField
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartOne.S11d.Common
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof15Res5

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.Sec16.ProofHess

section Heis

variable {G : Type*} [Group G] {a b s : G}

theorem pow_mul_eq_of_heis (hs : ∀ g : G, s * g = g * s) (hba : b * a = s * a * b) (j : ℕ) :
    b ^ j * a = s ^ j * a * b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsb : ∀ n : ℕ, b * s ^ n = s ^ n * b := fun n => ((Commute.pow_left (hs b) n).eq).symm
    calc b ^ (j + 1) * a = b * (b ^ j * a) := by rw [pow_succ', mul_assoc]
      _ = b * (s ^ j * a * b ^ j) := by rw [ih]
      _ = (b * s ^ j) * a * b ^ j := by simp only [mul_assoc]
      _ = s ^ j * (b * a) * b ^ j := by rw [hsb]; simp only [mul_assoc]
      _ = s ^ j * (s * a * b) * b ^ j := by rw [hba]
      _ = s ^ (j + 1) * a * b ^ (j + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]

theorem pow_mul_pow_eq_of_heis (hs : ∀ g : G, s * g = g * s) (hba : b * a = s * a * b)
    (i j : ℕ) : b ^ j * a ^ i = s ^ (j * i) * a ^ i * b ^ j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hsa : ∀ n : ℕ, a ^ i * s ^ n = s ^ n * a ^ i := fun n =>
      ((Commute.pow_left (hs (a ^ i)) n).eq).symm
    calc b ^ j * a ^ (i + 1) = (b ^ j * a ^ i) * a := by rw [pow_succ, mul_assoc]
      _ = s ^ (j * i) * a ^ i * (b ^ j * a) := by rw [ih]; simp only [mul_assoc]
      _ = s ^ (j * i) * a ^ i * (s ^ j * a * b ^ j) := by rw [pow_mul_eq_of_heis hs hba]
      _ = s ^ (j * i) * (a ^ i * s ^ j) * a * b ^ j := by simp only [mul_assoc]
      _ = s ^ (j * i) * (s ^ j * a ^ i) * a * b ^ j := by rw [hsa]
      _ = s ^ (j * (i + 1)) * a ^ (i + 1) * b ^ j := by
          rw [mul_add, mul_one, pow_add, pow_succ]; simp only [mul_assoc]

theorem pow_three_of_heis (hs : ∀ g : G, s * g = g * s) (hba : b * a = s * a * b)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hs3 : s ^ 3 = 1) (i j : ℕ) : (a ^ i * b ^ j) ^ 3 = 1 := by
  have hsg : ∀ (n : ℕ) (g : G), s ^ n * g = g * s ^ n := fun n g =>
    (Commute.pow_left (hs g) n).eq
  have h2 : (a ^ i * b ^ j) ^ 2 = s ^ (j * i) * a ^ (2 * i) * b ^ (2 * j) := by
    calc (a ^ i * b ^ j) ^ 2 = a ^ i * (b ^ j * a ^ i) * b ^ j := by
          rw [sq]; simp only [mul_assoc]
      _ = a ^ i * (s ^ (j * i) * a ^ i * b ^ j) * b ^ j := by rw [pow_mul_pow_eq_of_heis hs hba]
      _ = (a ^ i * s ^ (j * i)) * a ^ i * (b ^ j * b ^ j) := by simp only [mul_assoc]
      _ = s ^ (j * i) * a ^ (2 * i) * b ^ (2 * j) := by
          rw [← hsg, two_mul, two_mul, pow_add, pow_add]; simp only [mul_assoc]
  calc (a ^ i * b ^ j) ^ 3 = (a ^ i * b ^ j) ^ 2 * (a ^ i * b ^ j) := by rw [pow_succ]
    _ = s ^ (j * i) * a ^ (2 * i) * (b ^ (2 * j) * a ^ i) * b ^ j := by
        rw [h2]; simp only [mul_assoc]
    _ = s ^ (j * i) * a ^ (2 * i) * (s ^ (2 * j * i) * a ^ i * b ^ (2 * j)) * b ^ j := by
        rw [pow_mul_pow_eq_of_heis hs hba]
    _ = s ^ (j * i) * (a ^ (2 * i) * s ^ (2 * j * i)) * a ^ i * (b ^ (2 * j) * b ^ j) := by
        simp only [mul_assoc]
    _ = s ^ (j * i) * (s ^ (2 * j * i) * a ^ (2 * i)) * a ^ i * (b ^ (2 * j) * b ^ j) := by
        rw [← hsg]
    _ = s ^ (j * i + 2 * j * i) * a ^ (2 * i + i) * b ^ (2 * j + j) := by
        simp only [pow_add, mul_assoc]
    _ = (s ^ 3) ^ (j * i) * (a ^ 3) ^ i * (b ^ 3) ^ j := by
        have e1 : j * i + 2 * j * i = 3 * (j * i) := by ring
        have e2 : 2 * i + i = 3 * i := by ring
        have e3 : 2 * j + j = 3 * j := by ring
        rw [e1, e2, e3, pow_mul s 3 (j * i), pow_mul a 3 i, pow_mul b 3 j]
    _ = 1 := by rw [ha, hb, hs3]; simp

end Heis

theorem not_two_dvd_card_of_hessian {Γ : Type} [Group Γ] [Finite Γ] {E R : Subgroup Γ}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hcent : ∀ e ∈ E, e ≠ 1 → ∀ z : Γ, z * e = e * z → ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hER : E ≤ Subgroup.normalizer (R : Set Γ)) (hR3 : ¬ 3 ∣ Nat.card R) :
    ¬ 2 ∣ Nat.card R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨S, hS, -, hES⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    (Q := ⊥) Nat.prime_three Nat.prime_two hE3 hR3 hER bot_le IsPGroup.of_bot
    (fun _ _ => Subgroup.mem_normalizer_iff.mpr fun y => by simp)
  have hS1 : S ≤ ⊥ := Sec15.Proof1513Res3.le_of_forall_inf_centralizer_le hS.2.1 hE hE9 hES
    (fun e he he1 => by
      intro x hx
      obtain ⟨hxS, hxe⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨k, hk⟩ := hS.2.1 ⟨x, hxS⟩
      rw [Subgroup.mem_bot]
      rw [Subgroup.mem_centralizer_singleton_iff] at hxe
      exact hcent e he he1 x hxe k (by simpa using congrArg Subtype.val hk))
  intro h2
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
  have hp : IsPGroup 2 (Subgroup.zpowers (y : Γ)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, pow_one])
  have h1 := hS.2.2 (Subgroup.zpowers (y : Γ)) (Subgroup.zpowers_le.mpr y.2) hp
    (hS1.trans bot_le)
  have hy1 : (y : Γ) = 1 := by
    have hmem := Subgroup.mem_zpowers (y : Γ)
    rw [h1] at hmem
    exact Subgroup.mem_bot.mp (hS1 hmem)
  have : orderOf y = 1 := by rw [← Subgroup.orderOf_coe, hy1, orderOf_one]
  omega

variable {K : Type} [Field K] {f : ℕ} {π : Bool}

theorem eq_one_of_commute_of_cube (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    {xh : GL (Fin 3) K} (hxhS : xh ∈ slPi π 3 (2 ^ f) K) (hxh3 : xh ^ 3 = 1)
    (hx1 : ProjGenLinGroup.mk xh ≠ 1) {z : ProjGenLinGroup (Fin 3) K}
    (hzS : z ∈ projImage (slPi π 3 (2 ^ f) K))
    (hzx : z * ProjGenLinGroup.mk xh = ProjGenLinGroup.mk xh * z) {k : ℕ}
    (hz : z ^ 2 ^ k = 1) : z = 1 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdet : (xh : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hxhS).2
  have hxhs : ∀ c : K, (xh : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hx1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet
      exact zero_ne_one hdet
    exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hxh3m : (xh : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxh3, Units.val_one]
  have hzo : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz
  have hcop : Nat.Coprime 3 (orderOf z) :=
    Nat.Coprime.coprime_dvd_right hzo (Nat.Coprime.pow_right _ (by norm_num))
  obtain ⟨s, hsS, hsz, hso⟩ := exists_lift_pow_eq_one hK hzS hcop
  have hsk : s ^ 2 ^ k = 1 := by
    obtain ⟨t, ht⟩ := hzo
    rw [ht, pow_mul, hso, one_pow]
  have hsx : s * xh = xh * s := by
    refine commute_of_mk_commute hK hsS hxhS ?_ hcop.symm hso
    rw [hsz]
    exact hzx.symm
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hxh3m hdet hxhs
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, τ ^ 2, 1] with hD
  set Y : Matrix (Fin 3) (Fin 3) K := τ ^ (j : ℕ) • (xh : Matrix (Fin 3) (Fin 3) K) with hY
  set Q := P⁻¹ with hQ
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hsY : (s : Matrix (Fin 3) (Fin 3) K) * Y = Y * s := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hsx
    simp only [Units.val_mul] at h
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, h]
  set N := Q * (s : Matrix (Fin 3) (Fin 3) K) * P with hN
  have hND : N * D = D * N := conj_commute hPQ hQP hPD hsY
  have hNdiag := eq_diagonal_of_commute hτ hτ1 hND
  have hNk : N ^ 2 ^ k = 1 := by
    rw [hN, conj_pow hPQ hQP, ← Units.val_pow_eq_pow_val, hsk, Units.val_one, Matrix.mul_one,
      hQP]
  have hN1 : N = 1 := by
    rw [hNdiag, ← Matrix.diagonal_one]
    congr 1
    funext i
    apply Sec15.Proof1513Res3.eq_one_of_pow_two_pow hK (k := k)
    have h := congrFun (congrFun hNk i) i
    rw [hNdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact h
  have hs1 : s = 1 := by
    apply Units.ext
    rw [Units.val_one]
    calc (s : Matrix (Fin 3) (Fin 3) K) = P * N * Q := by rw [hN, unconj hPQ]
      _ = 1 := by rw [hN1, Matrix.mul_one, hPQ]
  rw [← hsz, hs1, map_one]

theorem cycThree_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    (cycThree : GL (Fin 3) K) * diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ * cycThree := by
  have h1 : (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ := by
    apply Units.ext
    rw [cycThree_conj_diagTau hτ, Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul,
      Matrix.one_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [← h1]
  group

theorem hessian_pair (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (2 ^ f) K) :
    ∃ a b : projImage (slPi π 3 (2 ^ f) K),
      (a : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * diagTau hτ * h⁻¹) ∧
      (b : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * cycThree * h⁻¹) ∧
      CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup _) = 9 ∧
      ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, e ≠ 1 → ∀ z, z * e = e * z →
        ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
  have := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (2 ^ f) := fun h => by subst h; exact hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set D := diagTau hτ with hDdef
  set P : GL (Fin 3) K := cycThree with hPdef
  have hDL : h * D * h⁻¹ ∈ slPi π 3 (2 ^ f) K :=
    conj_mem_slPi hπ hh (diagTau_mem_slPi hπ hq' hτ)
  have hPL : h * P * h⁻¹ ∈ slPi π 3 (2 ^ f) K := conj_mem_slPi hπ hh (cycThree_mem_slPi hπ)
  set a : projImage (slPi π 3 (2 ^ f) K) := ⟨_, Subgroup.mem_map_of_mem _ hDL⟩ with ha
  set b : projImage (slPi π 3 (2 ^ f) K) := ⟨_, Subgroup.mem_map_of_mem _ hPL⟩ with hb
  have hav : (a : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * D * h⁻¹) := rfl
  have hbv : (b : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (h * P * h⁻¹) := rfl
  have hmkconj : ∀ M : GL (Fin 3) K, ProjGenLinGroup.mk (h * M * h⁻¹) =
      ProjGenLinGroup.mk h * ProjGenLinGroup.mk M * (ProjGenLinGroup.mk h)⁻¹ := fun M => by
    rw [map_mul, map_mul, map_inv]
  have hab : a * b = b * a := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hav, hbv, hmkconj]
    have hc := Sec11.KS11LieProof.mk_diagTau_mul_mk_cycThree hτ hτ0
    calc ProjGenLinGroup.mk h * ProjGenLinGroup.mk D * (ProjGenLinGroup.mk h)⁻¹ *
          (ProjGenLinGroup.mk h * ProjGenLinGroup.mk P * (ProjGenLinGroup.mk h)⁻¹) =
        ProjGenLinGroup.mk h * (ProjGenLinGroup.mk D * ProjGenLinGroup.mk P) *
          (ProjGenLinGroup.mk h)⁻¹ := by group
      _ = ProjGenLinGroup.mk h * (ProjGenLinGroup.mk P * ProjGenLinGroup.mk D) *
          (ProjGenLinGroup.mk h)⁻¹ := by rw [hc]
      _ = _ := by group
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hav, ← map_pow, _root_.conj_pow, diagTau_pow_three, mul_one,
      mul_inv_cancel, map_one, Subgroup.coe_one]
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hbv, ← map_pow, _root_.conj_pow,
      Sec11.KS11LieProof.cycThree_pow_three, mul_one, mul_inv_cancel, map_one, Subgroup.coe_one]
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 : ProjGenLinGroup.mk (h * D * h⁻¹) = 1 := by rw [← hav, h1, Subgroup.coe_one]
    have h3 : ProjGenLinGroup.mk D = 1 := by
      calc ProjGenLinGroup.mk D = (ProjGenLinGroup.mk h)⁻¹ *
            (ProjGenLinGroup.mk h * ProjGenLinGroup.mk D * (ProjGenLinGroup.mk h)⁻¹) *
              ProjGenLinGroup.mk h := by group
        _ = 1 := by rw [← hmkconj, h2]; group
    rw [mk_eq_one_iff_mem_statedScalars] at h3
    obtain ⟨c, hc⟩ := h3
    have e00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    have e22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hc
    simp [hDdef, coe_diagTau] at e00 e22
    subst e22
    simp at e00
    exact hτ1 e00.symm
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
  have hbfin : IsOfFinOrder b := isOfFinOrder_of_finite b
  have hba : b ∉ Subgroup.zpowers a := by
    intro hmem
    rw [← hfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨n, hn⟩ := hmem
    have h2 : ProjGenLinGroup.mk (h * P * h⁻¹) = ProjGenLinGroup.mk (h * D ^ n * h⁻¹) := by
      rw [← hbv, ← hn, Subgroup.coe_pow, hav, ← map_pow, _root_.conj_pow]
    rw [hmkconj, hmkconj] at h2
    have h3 : ProjGenLinGroup.mk P = ProjGenLinGroup.mk (D ^ n) := by
      calc ProjGenLinGroup.mk P = (ProjGenLinGroup.mk h)⁻¹ *
            (ProjGenLinGroup.mk h * ProjGenLinGroup.mk P * (ProjGenLinGroup.mk h)⁻¹) *
              ProjGenLinGroup.mk h := by group
        _ = (ProjGenLinGroup.mk h)⁻¹ *
            (ProjGenLinGroup.mk h * ProjGenLinGroup.mk (D ^ n) * (ProjGenLinGroup.mk h)⁻¹) *
              ProjGenLinGroup.mk h := by rw [h2]
        _ = ProjGenLinGroup.mk (D ^ n) := by group
    exact Sec11.KS11LieProof.mk_cycThree_ne_mk_pow hτ n h3
  refine ⟨a, b, rfl, rfl, Sec13.isElemAbelian_zpowers_sup ha3 hb3 hab,
    card_zpowers_sup_zpowers hb3 hao hba hab.symm, ?_⟩
  intro e he he1 z hze k hz
  obtain ⟨s, t, rfl⟩ := (CFSG.RankThree.PartOne.S11d.mem_zpowers_sup_zpowers_iff hab).mp he
  obtain ⟨i, hi⟩ : ∃ i : ℕ, a ^ i = a ^ s :=
    (Submonoid.mem_powers_iff _ _).mp
      (hfin.mem_powers_iff_mem_zpowers.mpr (Subgroup.zpow_mem_zpowers a s))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, b ^ j = b ^ t :=
    (Submonoid.mem_powers_iff _ _).mp
      (hbfin.mem_powers_iff_mem_zpowers.mpr (Subgroup.zpow_mem_zpowers b t))
  rw [← hi, ← hj] at he1 hze
  set M := h * (D ^ i * P ^ j) * h⁻¹ with hM
  have hML : M ∈ slPi π 3 (2 ^ f) K := conj_mem_slPi hπ hh
    (mul_mem (pow_mem (diagTau_mem_slPi hπ hq' hτ) i) (pow_mem (cycThree_mem_slPi hπ) j))
  have hMv : ((a ^ i * b ^ j : projImage (slPi π 3 (2 ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk M := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hav, hbv, ← map_pow, ← map_pow,
      ← map_mul, _root_.conj_pow, _root_.conj_pow, hM]
    congr 1
    group
  set u : Kˣ := Units.mk0 τ hτ0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hτ,
    Units.val_one])
  have hsc : ∀ g : GL (Fin 3) K, GeneralLinearGroup.scalar (Fin 3) (u ^ 2) * g =
      g * GeneralLinearGroup.scalar (Fin 3) (u ^ 2) := fun g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (u ^ 2) g).eq.symm
  have hs3 : GeneralLinearGroup.scalar (Fin 3) (u ^ 2) ^ 3 = 1 := by
    rw [← map_pow, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hu3, one_pow, map_one]
  have hM3 : M ^ 3 = 1 := by
    rw [hM, _root_.conj_pow, pow_three_of_heis hsc (cycThree_mul_diagTau hτ hτ0)
      (diagTau_pow_three hτ) Sec11.KS11LieProof.cycThree_pow_three hs3 i j, mul_one,
      mul_inv_cancel]
  have hM1 : ProjGenLinGroup.mk M ≠ 1 := fun h1 => he1 (Subtype.ext (by
    rw [hMv, h1, Subgroup.coe_one]))
  have hz' := eq_one_of_commute_of_cube hK hq hML hM3 hM1 z.2
    (by rw [← hMv]; exact congrArg Subtype.val hze) (k := k)
    (by rw [← Subgroup.coe_pow, hz, Subgroup.coe_one])
  exact Subtype.ext hz'

end Proof15Res5

end CFSG.RankThree.PartTwo.Sec15
