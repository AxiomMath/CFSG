module

public import CFSG.RankThree.PartOne.KC.UnitaryLogCalculus
public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentCyclic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.RankThree.PartOne.KCUnitaryRegular

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem eq_one_of_pow_eq_one (h : UnitaryFieldData p f K) {c : K} (hc : c ^ p = 1) : c = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have h1 : (c - 1) ^ p = 0 := by rw [sub_pow_char, hc, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff h.prime.ne_zero |>.mp h1)

theorem eq_of_mk_eq_of_pow_eq_one (h : UnitaryFieldData p f K) (hn : 1 ≤ n)
    (G : Matrix (Fin n) (Fin n) K) {g₁ g₂ : gramSU h G} (hg₁ : g₁ ^ p = 1) (hg₂ : g₂ ^ p = 1)
    (hπ : (g₁ : primeFormP h G) = (g₂ : primeFormP h G)) : g₁ = g₂ := by
  have hz : g₁⁻¹ * g₂ ∈ normOneScalars h (gramSU h G) n := QuotientGroup.eq.mp hπ
  have hcen : g₁⁻¹ * g₂ ∈ Subgroup.center (gramSU h G) := normOneScalars_le_center h _ n hz
  obtain ⟨c, -, -, hc⟩ := hz
  have hg₂' : g₂ = g₁ * (g₁⁻¹ * g₂) := by simp
  have hcomm : Commute g₁ (g₁⁻¹ * g₂) := Subgroup.mem_center_iff.mp hcen g₁
  have hzp : (g₁⁻¹ * g₂) ^ p = 1 := by
    have := hg₂
    rw [hg₂', hcomm.mul_pow, hg₁, one_mul] at this
    exact this
  have hmat : ((((g₁⁻¹ * g₂) ^ p : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) ^ p • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Subgroup.coe_pow, hc, ← map_pow, GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val,
      scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc1 : (c : K) ^ p = 1 := by
    rw [hzp] at hmat
    have := congrFun (congrFun hmat ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this.symm
  have hz1 : g₁⁻¹ * g₂ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, Subgroup.coe_one, Units.val_one,
      show c = 1 from Units.ext (eq_one_of_pow_eq_one h hc1), map_one, Units.val_one]
  rw [hg₂', hz1, mul_one]

theorem conj_injective_of_center_eq_bot {T : Type*} [Group T] (hZ : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  intro g g' e
  have hc : g'⁻¹ * g ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun x => by
    have h1 := congrArg (fun α : MulAut T => α x) e
    simp only [MulAut.conj_apply] at h1
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {T : Type*} [Group T] [IsSimpleGroup T]
    (hperf : Group.IsPerfect T) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    have hcomm : IsMulCommutative T :=
      ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a⟩⟩
    exact Group.IsPerfect.not_isMulCommutative T hcomm

theorem isSimpleGroup_and_isPerfect_primeFormP (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    IsSimpleGroup (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∧
      Group.IsPerfect (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨e₁⟩ := nonempty_primeFormP_mulEquiv h hC
  have e : primeFormP h (C : Matrix (Fin n) (Fin n) K) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU n (p ^ f) K) :=
    e₁.trans (unitaryPSUEquiv h (by omega))
  have hnq : (n, p ^ f) ≠ (3, 2) := fun e' => hq (Prod.mk_inj.1 e')
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f h.card_eq_sq n
    hn hnq
  have hP : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU n (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq hn hnq
  have hP' : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU n (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact ⟨e.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    (MulEquiv.surjective _)⟩

theorem center_primeFormP_eq_bot (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Subgroup.center (primeFormP h (C : Matrix (Fin n) (Fin n) K)) = ⊥ := by
  obtain ⟨hs, hp⟩ := isSimpleGroup_and_isPerfect_primeFormP h hC hn hq
  exact center_eq_bot_of_isSimpleGroup_of_isPerfect hp

theorem conj_injective_primeFormP (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Function.Injective (MulAut.conj : primeFormP h (C : Matrix (Fin n) (Fin n) K) →*
      MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :=
  conj_injective_of_center_eq_bot (center_primeFormP_eq_bot h hC hn hq)

theorem ringEquiv_eq_one_or_eq_bar (h : UnitaryFieldData p f K) (σ : K ≃+* K)
    (hσ : ∀ c : K, h.bar c = c → σ c = c) : (∀ c, σ c = c) ∨ (∀ c, σ c = h.bar c) := by
  have key : ∀ c : K, σ c = c ∨ σ c = h.bar c := by
    intro c
    have hq : (c - c) * (c - h.bar c) = 0 := by ring
    have h1 : (σ c - c) * (σ c - h.bar c) = 0 := by
      have e1 : h.bar (c + h.bar c) = c + h.bar c := by rw [map_add, h.bar_bar, add_comm]
      have e2 : h.bar (c * h.bar c) = c * h.bar c := by rw [map_mul, h.bar_bar, mul_comm]
      have h2 := hσ _ e1
      have h3 := hσ _ e2
      have h4 : c ^ 2 - (c + h.bar c) * c + c * h.bar c = 0 := by ring
      have h5 := congrArg σ h4
      rw [map_add, map_sub, map_mul, map_pow, map_zero, h2, h3] at h5
      linear_combination h5
    rcases mul_eq_zero.mp h1 with h6 | h6
    · exact Or.inl (sub_eq_zero.mp h6)
    · exact Or.inr (sub_eq_zero.mp h6)
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hcon
  have h1 : σ c₁ = h.bar c₁ := (key c₁).resolve_left hc₁
  have h2 : σ c₂ = c₂ := (key c₂).resolve_right hc₂
  rcases key (c₁ + c₂) with h3 | h3
  · rw [map_add, h1, h2] at h3
    exact hc₁ (by
      have : h.bar c₁ = c₁ := add_right_cancel h3
      rw [h1, this])
  · rw [map_add, h1, h2, map_add] at h3
    exact hc₂ (by rw [h2]; exact add_left_cancel h3)

theorem eq_zero_of_isNilpotent_smul_one (hn : 1 ≤ n) {c : K}
    (hc : IsNilpotent (c • (1 : Matrix (Fin n) (Fin n) K))) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  rw [smul_pow, one_pow] at hk
  have := congrFun (congrFun hk ⟨0, hn⟩) ⟨0, hn⟩
  simp at this
  exact this.1

variable (h : UnitaryFieldData p f K) {C : GL (Fin n) K}

theorem unitaryAdjoint_zero : unitaryAdjoint h C (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  have := KCUnitaryLog.unitaryAdjoint_smul h C (0 : K) (0 : Matrix (Fin n) (Fin n) K)
  simpa using this

theorem unitaryAdjoint_one' : unitaryAdjoint h C (1 : Matrix (Fin n) (Fin n) K) = 1 :=
  KCUnitaryLog.unitaryAdjoint_one h C


theorem commute_sub_smul_one (M : Matrix (Fin n) (Fin n) K) (a b : K) :
    Commute (M - a • (1 : Matrix (Fin n) (Fin n) K)) (M - b • (1 : Matrix (Fin n) (Fin n) K)) := by
  have h1 : Commute M (b • (1 : Matrix (Fin n) (Fin n) K)) := (Commute.one_right M).smul_right b
  have h2 : Commute (a • (1 : Matrix (Fin n) (Fin n) K)) M := (Commute.one_left M).smul_left a
  have h3 : Commute (a • (1 : Matrix (Fin n) (Fin n) K)) (b • (1 : Matrix (Fin n) (Fin n) K)) :=
    ((Commute.one_left _).smul_left a).smul_right b
  exact ((Commute.refl M).sub_right h1).sub_left (h2.sub_right h3)

theorem pow_mem_normOneScalars_of_commute (hn : 3 ≤ n) (hnp : n ≤ p)
    {N : Matrix (Fin n) (Fin n) K} (hNn : N ^ n = 0) (hNreg : N ^ (n - 1) ≠ 0)
    {g : gramSU h (C : Matrix (Fin n) (Fin n) K)}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
      N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    g ^ p ∈ normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hn1 : 1 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨l, hl⟩ := exists_isNilpotent_sub_smul_one_of_commute hn1 hNn hNreg hg
  set G : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
  set R := G - l • (1 : Matrix (Fin n) (Fin n) K) with hR
  have hRn : R ^ n = 0 := matrix_pow_eq_zero_of_isNilpotent hl
  have hRp : R ^ p = 0 := pow_eq_zero_of_le hRn hnp
  have hGR : G = l • 1 + R := by rw [hR]; abel
  have hGp : G ^ p = l ^ p • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hGR, add_pow_char_of_commute p (Commute.smul_left (Commute.one_left R) l), smul_pow,
      one_pow, hRp, add_zero]
  have hl0 : l ≠ 0 := by
    intro hl0
    have hRG : R = G := by rw [hR, hl0, zero_smul, sub_zero]
    obtain ⟨k, hk⟩ := hl
    have h1 : (((g ^ k : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 0 := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hG, ← hRG, hk]
    exact Units.ne_zero _ h1
  set c : Kˣ := Units.mk0 (l ^ p) (pow_ne_zero p hl0) with hc
  have hgc : ((g ^ p : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := by
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, ← hG, hGp,
      scalar_apply, Matrix.smul_one_eq_diagonal]
    rfl
  refine ⟨c, ?_, ?_, hgc⟩
  · refine norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 C ?_
    rw [← hgc]
    exact (g ^ p).2.1
  · have hdet := (g ^ p).2.2
    rw [hgc, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)

theorem exists_scalar_mul_of_mem_primeFormUnitary (hn : 3 ≤ n)
    {N : Matrix (Fin n) (Fin n) K} (hNn : N ^ n = 0) (hNreg : N ^ (n - 1) ≠ 0)
    {A : GL (Fin n) K} (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (hAN : (A : Matrix (Fin n) (Fin n) K) * N = N * (A : Matrix (Fin n) (Fin n) K)) :
    ∃ (z : Kˣ) (u : gramSU h (C : Matrix (Fin n) (Fin n) K)),
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      A = GeneralLinearGroup.scalar (Fin n) z * (u : GL (Fin n) K) := by
  have hn1 : 1 ≤ n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  obtain ⟨l, hl⟩ := exists_isNilpotent_sub_smul_one_of_commute hn1 hNn hNreg hAN
  set Am : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hAm
  set M : Matrix (Fin n) (Fin n) K := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hAM : Am * M = 1 := by rw [hAm, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMA : M * Am = 1 := by rw [hAm, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set R := Am - l • (1 : Matrix (Fin n) (Fin n) K) with hR
  have hl0 : l ≠ 0 := by
    intro hl0
    have hRA : R = Am := by rw [hR, hl0, zero_smul, sub_zero]
    obtain ⟨k, hk⟩ := hl
    have h1 : (((A ^ k : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [Units.val_pow_eq_pow_val, ← hAm, ← hRA, hk]
    exact Units.ne_zero _ h1
  have hadj : unitaryAdjoint h C Am = M := by
    have hA' : (Am.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * Am = C := hA
    have h1 : (Am.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) =
        (C : Matrix (Fin n) (Fin n) K) * M := by
      calc (Am.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) =
            (Am.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * (Am * M) := by
            rw [hAM, Matrix.mul_one]
        _ = (Am.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * Am * M := by
            rw [Matrix.mul_assoc _ Am M]
        _ = (C : Matrix (Fin n) (Fin n) K) * M := by rw [hA']
    unfold unitaryAdjoint
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, KCUnitaryLog.coe_inv_mul, Matrix.one_mul]
  have hRadj : unitaryAdjoint h C R = M - h.bar l • 1 := by
    rw [hR, KCUnitaryLog.unitaryAdjoint_sub, KCUnitaryLog.unitaryAdjoint_smul,
      KCUnitaryLog.unitaryAdjoint_one, hadj]
  have hRd : IsNilpotent (M - h.bar l • (1 : Matrix (Fin n) (Fin n) K)) := by
    obtain ⟨k, hk⟩ := hl
    exact ⟨k, by rw [← hRadj, ← KCUnitaryLog.unitaryAdjoint_pow, hk, unitaryAdjoint_zero]⟩
  have hMR : Commute M R := by
    have h1 : Commute M Am := by
      change M * Am = Am * M
      rw [hMA, hAM]
    exact h1.sub_right ((Commute.one_right M).smul_right l)
  have hMn : IsNilpotent (M - l⁻¹ • (1 : Matrix (Fin n) (Fin n) K)) := by
    have hMR' : M - l⁻¹ • (1 : Matrix (Fin n) (Fin n) K) = -(l⁻¹ • (M * R)) := by
      have h1 : M * R = 1 - l • M := by
        rw [hR, Matrix.mul_sub, hMA, Matrix.mul_smul, Matrix.mul_one]
      rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hl0, one_smul]
      abel
    rw [hMR']
    obtain ⟨k, hk⟩ := hMR.isNilpotent_mul_left hl
    exact IsNilpotent.neg ⟨k, by rw [smul_pow, hk, smul_zero]⟩
  have hdiff : IsNilpotent ((h.bar l - l⁻¹) • (1 : Matrix (Fin n) (Fin n) K)) := by
    have := Commute.isNilpotent_sub (commute_sub_smul_one M l⁻¹ (h.bar l)) hMn hRd
    rwa [show (M - l⁻¹ • (1 : Matrix (Fin n) (Fin n) K)) - (M - h.bar l • 1) =
      (h.bar l - l⁻¹) • (1 : Matrix (Fin n) (Fin n) K) by rw [sub_smul]; abel] at this
  have hbar : h.bar l = l⁻¹ := sub_eq_zero.mp (eq_zero_of_isNilpotent_smul_one hn1 hdiff)
  have hdet : Am.det = l ^ n := by
    have h1 : Am = l • (1 + l⁻¹ • R) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hl0, one_smul, hR]
      simp
    have h2 : IsNilpotent (l⁻¹ • R) := by
      obtain ⟨k, hk⟩ := hl
      exact ⟨k, by rw [smul_pow, hk, smul_zero]⟩
    rw [h1, Matrix.det_smul, KCUnitaryLog.det_one_add_of_isNilpotent h2, mul_one,
      Fintype.card_fin]
  set z : Kˣ := Units.mk0 l hl0 with hz
  set u₀ : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) z⁻¹ * A with hu₀
  have hu₀m : ((u₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l⁻¹ • Am := by
    rw [hu₀, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_eq_diagonal_mul]
    rfl
  have hu₀mem : u₀ ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · have hA' : (Am.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * Am = C := hA
      rw [hu₀m, Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [hA', map_inv₀, hbar, inv_inv, inv_mul_cancel₀ hl0, one_smul]
    · rw [hu₀m, Matrix.det_smul, hdet, Fintype.card_fin, ← mul_pow, inv_mul_cancel₀ hl0, one_pow]
  refine ⟨z, ⟨u₀, hu₀mem⟩, ?_, ?_⟩
  · change ((u₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
      N * ((u₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hu₀m, Matrix.smul_mul, Matrix.mul_smul, hAN]
  · change A = GeneralLinearGroup.scalar (Fin n) z * u₀
    rw [hu₀, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem conj_apply_mulAut {G : Type*} [Group G] (s : MulAut G) (x : G) :
    MulAut.conj (s x) = s * MulAut.conj x * s⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem eq_bot_of_pointwise_centralizer {T : Type*} [Group T] [Finite T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {p : ℕ} (hp : p.Prime) {x : T}
    (hCp : ∀ y ∈ Subgroup.centralizer ({x} : Set T), y ^ p = 1)
    (hpt : ∀ α : MulAut T, (∀ y ∈ Subgroup.centralizer ({x} : Set T), α y = y) →
      ∃ y ∈ Subgroup.centralizer ({x} : Set T), α = MulAut.conj y)
    (B : Subgroup (MulAut T)) (hB : (MulAut.conj : T →* MulAut T).range ≤ B)
    (S : Subgroup (MulAut T)) (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj x})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj x})).Normal)
    (hSp : ¬ p ∣ Nat.card S) : S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set T) with hC
  set W := C.map (MulAut.conj : T →* MulAut T) with hW
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  have hCpg : IsPGroup p C := fun y => ⟨1, by
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hCp y y.2⟩
  have hWp : IsPGroup p W := hCpg.map _
  have hfixu : ∀ s ∈ L, s x = x := by
    intro s hs
    apply hinj
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
    rw [conj_apply_mulAut, h1, mul_inv_cancel_right]
  have hWL : W ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.1 hy)]
  have hWnorm : ∀ y ∈ L, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    rintro y hy _ ⟨z, hz, rfl⟩
    have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    refine ⟨y z, Subgroup.mem_centralizer_singleton_iff.2 ?_, by rw [conj_apply_mulAut]⟩
    rw [← hfixu y hy, ← map_mul, hz', map_mul]
  have hSnorm : ∀ y ∈ L, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hdisj : Disjoint S W := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hWp
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp).2 hSp).symm
  have hcomm : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s := by
    intro s hs w hw
    have hsL := hSC hs
    have h1 : s * w * s⁻¹ * w⁻¹ ∈ W := W.mul_mem (hWnorm s hsL w hw) (W.inv_mem hw)
    have h2 : s * w * s⁻¹ * w⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm w (hWL hw) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    have h3 := Subgroup.disjoint_def.1 hdisj h2 h1
    calc s * w = s * w * s⁻¹ * w⁻¹ * (w * s) := by group
      _ = w * s := by rw [h3, one_mul]
  have hSW : S ≤ W := by
    intro s hs
    have hpt' : ∀ y ∈ C, s y = y := by
      intro y hy
      apply hinj
      rw [conj_apply_mulAut, hcomm s hs _ ⟨y, hy, rfl⟩, mul_inv_cancel_right]
    obtain ⟨y, hy, rfl⟩ := hpt s hpt'
    exact ⟨y, hy, rfl⟩
  exact hdisj.eq_bot_of_le hSW

end CFSG.RankThree.PartOne.KCUnitaryRegular
