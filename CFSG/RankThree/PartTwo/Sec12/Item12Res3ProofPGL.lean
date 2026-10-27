module

import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofCube
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec12.Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section Matrices

variable {K : Type} [Field K]

@[expose] def swapNeg : GL (Fin 3) K :=
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapNeg :
    ((swapNeg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, -1, 0; -1, 0, 0; 0, 0, -1] :=
  rfl

theorem swapNeg_inv : (swapNeg : GL (Fin 3) K)⁻¹ = swapNeg := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, coe_swapNeg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem swapNeg_conj_diagUnits (a b c : Kˣ) :
    swapNeg * diagUnits a b c * swapNeg⁻¹ = diagUnits b a c := by
  rw [swapNeg_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapNeg, coe_diagUnits_eq, coe_diagUnits_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem swapNeg_conj_cycThree :
    swapNeg * cycThree * swapNeg⁻¹ = (cycThree : GL (Fin 3) K)⁻¹ := by
  rw [swapNeg_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapNeg, coe_cycThree, coe_cycThree_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

variable {p f : ℕ}

theorem swapNeg_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K) :
    swapNeg ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((swapNeg : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_swapNeg, det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have hb : h.bar (-1 : K) = -1 := by rw [map_neg, map_one]
    rw [coe_swapNeg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, transpose_apply, hb]
  · rw [mem_slPi_true]
    exact hdet

theorem diagUnits_one₃ : diagUnits (1 : Kˣ) 1 1 = (1 : GL (Fin 3) K) := by
  rw [show (1 : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) 1 from (map_one _).symm,
    ← Sec13.Res2Proof.diagUnits_self_eq_scalar]

theorem diagUnits_inv₃ (a b c : Kˣ) : (diagUnits a b c)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel,
    diagUnits_one₃]

@[expose] noncomputable def diagHom (K : Type) [Field K] : Kˣ × Kˣ × Kˣ →* GL (Fin 3) K where
  toFun x := diagUnits x.1 x.2.1 x.2.2
  map_one' := diagUnits_one₃
  map_mul' _ _ := (diagUnits_mul _ _ _ _ _ _).symm

@[expose] noncomputable def diagThree (K : Type) [Field K] : Subgroup (GL (Fin 3) K) :=
  ((CommGroup.primaryComponent Kˣ 3).prod ((CommGroup.primaryComponent Kˣ 3).prod
    (CommGroup.primaryComponent Kˣ 3))).map (diagHom K)

@[expose] noncomputable def monoThree (K : Type) [Field K] : Subgroup (GL (Fin 3) K) :=
  Subgroup.zpowers cycThree ⊔ diagThree K

theorem diagUnits_mem_diagThree {a b c : Kˣ} (ha : ∃ k : ℕ, a ^ 3 ^ k = 1)
    (hb : ∃ k : ℕ, b ^ 3 ^ k = 1) (hc : ∃ k : ℕ, c ^ 3 ^ k = 1) :
    diagUnits a b c ∈ diagThree K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨(a, b, c), ⟨CommGroup.mem_primaryComponent.mpr ha,
    CommGroup.mem_primaryComponent.mpr hb, CommGroup.mem_primaryComponent.mpr hc⟩, rfl⟩

theorem isPGroup_diagThree : IsPGroup 3 (diagThree K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPGroup.map ?_ _
  rintro ⟨⟨a, b, c⟩, ha, hb, hc⟩
  obtain ⟨i, hi⟩ := CommGroup.mem_primaryComponent.mp ha
  obtain ⟨j, hj⟩ := CommGroup.mem_primaryComponent.mp hb
  obtain ⟨l, hl⟩ := CommGroup.mem_primaryComponent.mp hc
  refine ⟨i + j + l, Subtype.ext ?_⟩
  have e1 : ∀ {u : Kˣ} {n : ℕ}, u ^ 3 ^ n = 1 → ∀ m : ℕ, n ≤ m → u ^ 3 ^ m = 1 := by
    intro u n hu m hnm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, pow_mul, hu, one_pow]
  simp only [Subgroup.coe_pow, Prod.pow_mk, Subgroup.coe_one, Prod.mk_eq_one]
  exact ⟨e1 hi _ (by omega), e1 hj _ (by omega), e1 hl _ (by omega)⟩

theorem isPGroup_monoThree [Finite K] : IsPGroup 3 (monoThree K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPGroup.to_sup_of_normal_right' ?_ isPGroup_diagThree ?_
  · intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      cycThree_pow_three, _root_.one_zpow]
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun M hM => ?_
    obtain ⟨⟨a, b, c⟩, ⟨ha, hb, hc⟩, rfl⟩ := hM
    change cycThree * diagUnits a b c * cycThree⁻¹ ∈ diagThree K
    rw [cycThree_conj_diagUnits]
    exact ⟨(c, a, b), ⟨hc, ha, hb⟩, rfl⟩

end Matrices

section Acts

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {𝕂 : Type} [Field 𝕂]

@[expose] def actsBySub (e : X ≃* projImage (slPi π 3 (p ^ f) 𝕂))
    (M : Subgroup (GL (Fin 3) 𝕂)) : Subgroup (MulAut X) where
  carrier := {α | ∃ W ∈ M, ∀ z : X,
    ((e (α z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk W * (e z : ProjGenLinGroup (Fin 3) 𝕂) * (ProjGenLinGroup.mk W)⁻¹}
  mul_mem' := by
    rintro α β ⟨V, hV, hα⟩ ⟨W, hW, hβ⟩
    refine ⟨V * W, mul_mem hV hW, fun z => ?_⟩
    rw [MulAut.mul_apply, hα, hβ, map_mul]
    group
  one_mem' := ⟨1, one_mem M, fun z => by simp⟩
  inv_mem' := by
    rintro α ⟨W, hW, hα⟩
    refine ⟨W⁻¹, inv_mem hW, fun z => ?_⟩
    have h1 := hα (α⁻¹ z)
    rw [show α (α⁻¹ z) = z from by simp] at h1
    rw [map_inv, inv_inv, h1]
    group

theorem pow_apply_of_acts {e : X ≃* projImage (slPi π 3 (p ^ f) 𝕂)} {α : MulAut X}
    {W : GL (Fin 3) 𝕂} (hα : ∀ z : X,
      ((e (α z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
        ProjGenLinGroup.mk W * (e z : ProjGenLinGroup (Fin 3) 𝕂) * (ProjGenLinGroup.mk W)⁻¹)
    (n : ℕ) (z : X) :
    ((e ((α ^ n) z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (W ^ n) * (e z : ProjGenLinGroup (Fin 3) 𝕂) *
        (ProjGenLinGroup.mk (W ^ n))⁻¹ := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ, map_mul]
    group

theorem isPGroup_actsBySub (e : X ≃* projImage (slPi π 3 (p ^ f) 𝕂))
    {M : Subgroup (GL (Fin 3) 𝕂)} (hM : IsPGroup 3 M) : IsPGroup 3 (actsBySub e M) := by
  rintro ⟨α, W, hWM, hα⟩
  obtain ⟨k, hk⟩ := hM ⟨W, hWM⟩
  have hk' : W ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  ext z
  apply e.injective
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, MulAut.one_apply]
  rw [pow_apply_of_acts hα, hk', map_one, one_mul, inv_one, mul_one]

end Acts

theorem exists_three_part {𝕂 : Type} [Field 𝕂] {m : ℕ} (hm : m ≠ 0) (h3 : 3 ∣ m) {u : 𝕂ˣ}
    (hu : u ∈ rootsOfUnity m 𝕂) :
    ∃ u₃ ρ : 𝕂ˣ, u = u₃ * ρ ^ 3 ∧ (∃ k : ℕ, u₃ ^ 3 ^ k = 1) ∧ ρ ∈ rootsOfUnity m 𝕂 := by
  obtain ⟨E, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 3 (by norm_num)
  have hE : 1 ≤ E := by
    by_contra hE
    push Not at hE
    interval_cases E
    simp only [pow_zero, one_mul] at h3
    exact hm' h3
  have hcop : IsCoprime ((3 : ℤ) ^ E) (m' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime (3 ^ E) m' :=
      Nat.Coprime.pow_left E ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm')
    exact_mod_cast this
  obtain ⟨α, β, hαβ⟩ := hcop
  have hum : u ^ (3 ^ E * m') = 1 := (mem_rootsOfUnity _ _).mp hu
  refine ⟨u ^ (β * m'), u ^ (α * 3 ^ (E - 1)), ?_, ⟨E, ?_⟩, ?_⟩
  · have h1 : (3 : ℤ) ^ E = 3 ^ (E - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    calc u = u ^ (α * 3 ^ E + β * m') := by rw [hαβ, zpow_one]
      _ = u ^ (α * 3 ^ E) * u ^ (β * (m' : ℤ)) := _root_.zpow_add _ _ _
      _ = u ^ (β * (m' : ℤ)) * (u ^ (α * 3 ^ (E - 1))) ^ 3 := by
        rw [mul_comm]
        congr 1
        rw [← zpow_natCast, ← _root_.zpow_mul, h1]
        congr 1
        push_cast
        ring
  · rw [← zpow_natCast, ← _root_.zpow_mul,
      show β * (m' : ℤ) * ((3 ^ E : ℕ) : ℤ) = ((3 ^ E * m' : ℕ) : ℤ) * β by push_cast; ring,
      _root_.zpow_mul, zpow_natCast, hum, _root_.one_zpow]
  · exact zpow_mem hu _

section Core

variable {X : Type} [Group X] {π : Bool} {p f : ℕ} {𝕂 : Type} [Field 𝕂]

theorem exists_conj_inv_of_normal_form [Finite 𝕂] (hF : PiField π p f 𝕂) (hq : ModThree π (p ^ f))
    (hXp : Group.IsPerfect X) (e : X ≃* projImage (slPi π 3 (p ^ f) 𝕂)) (σ : MulAut X)
    {y : GL (Fin 3) 𝕂}
    (hni : ¬ ∃ l ∈ slPi π 3 (p ^ f) 𝕂, ∀ m ∈ slPi π 3 (p ^ f) 𝕂, y * m * y⁻¹ = l * m * l⁻¹)
    (hσ : ∀ z : X, ((e (σ z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) 𝕂) * (ProjGenLinGroup.mk y)⁻¹)
    (cb : X) {s z g : GL (Fin 3) 𝕂}
    (hse : ((e cb : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk s)
    (hz : z ∈ StatedScalars (Fin 3) 𝕂) (hg : g ∈ glPi π 3 (p ^ f) 𝕂) {τ : 𝕂} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (hD : g⁻¹ * (s * z) * g = diagTau hτ) {d₀ d₁ d₂ : 𝕂ˣ}
    (hd₀ : d₀ ∈ rootsOfUnity (qSubPi π (p ^ f)) 𝕂) (hd₁ : d₁ ∈ rootsOfUnity (qSubPi π (p ^ f)) 𝕂)
    (hd₂ : d₂ ∈ rootsOfUnity (qSubPi π (p ^ f)) 𝕂)
    (hgy : g⁻¹ * y * g = diagUnits d₀ d₁ d₂ * cycThree) :
    ∃ tb : X, tb * cb * tb⁻¹ = cb⁻¹ ∧
      IsPGroup 3 (Subgroup.closure {MulAut.conj cb, σ,
        MulAut.conj tb * σ * (MulAut.conj tb)⁻¹}) ∧
      σ * (MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) ≠
        (MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) * σ := by
  have hπ : π = false → UnitaryFieldData p f 𝕂 := fun h => by subst h; exact hF.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set m := qSubPi π (p ^ f) with hmdef
  have hm0 : m ≠ 0 := qSubPi_ne_zero hF hq
  have hm3 : 3 ∣ m := three_dvd_qSubPi hq
  have hlmu : d₀ * d₁ * d₂ ∈ rootsOfUnity m 𝕂 := mul_mem (mul_mem hd₀ hd₁) hd₂
  obtain ⟨l₃, ρ, hl, hl₃, hρ⟩ := exists_three_part hm0 hm3 hlmu
  set δ₁ : 𝕂ˣ := ρ * d₁⁻¹ with hδ₁
  set δ₂ : 𝕂ˣ := ρ * d₂⁻¹ with hδ₂
  set u : GL (Fin 3) 𝕂 := diagUnits 1 δ₁ (δ₁ * δ₂) with hu
  have hδ₁μ : δ₁ ∈ rootsOfUnity m 𝕂 := mul_mem hρ (inv_mem hd₁)
  have hδ₂μ : δ₂ ∈ rootsOfUnity m 𝕂 := mul_mem hρ (inv_mem hd₂)
  have huH : u ∈ glPi π 3 (p ^ f) 𝕂 :=
    diagUnits_mem_glPi hF (one_mem _) hδ₁μ (mul_mem hδ₁μ hδ₂μ)
  set y₀ : GL (Fin 3) 𝕂 := diagUnits l₃ 1 1 * cycThree with hy₀
  have hlK : (d₀ : 𝕂) * d₁ * d₂ = l₃ * ρ ^ 3 := by
    have := congrArg Units.val hl
    simpa using this
  have hd₁0 : (d₁ : 𝕂) ≠ 0 := d₁.ne_zero
  have hd₂0 : (d₂ : 𝕂) ≠ 0 := d₂.ne_zero
  have hρ0 : (ρ : 𝕂) ≠ 0 := ρ.ne_zero
  have hkey : u * (diagUnits d₀ d₁ d₂ * cycThree) * u⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ρ * y₀ := by
    calc u * (diagUnits d₀ d₁ d₂ * cycThree) * u⁻¹ =
        u * diagUnits d₀ d₁ d₂ * (cycThree * u⁻¹ * cycThree⁻¹) * cycThree := by group
      _ = diagUnits (1 * d₀ * (δ₁ * δ₂)⁻¹) (δ₁ * d₁ * 1⁻¹) (δ₁ * δ₂ * d₂ * δ₁⁻¹) * cycThree := by
        rw [hu, diagUnits_inv₃, cycThree_conj_diagUnits, diagUnits_mul, diagUnits_mul]
      _ = diagUnits (ρ * l₃) (ρ * 1) (ρ * 1) * cycThree := by
        congr 2
        · apply Units.ext
          simp only [hδ₁, hδ₂, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val]
          field_simp
          linear_combination hlK
        · apply Units.ext
          simp only [hδ₁, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val]
          field_simp
        · apply Units.ext
          simp only [hδ₁, hδ₂, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val]
          field_simp
      _ = GeneralLinearGroup.scalar (Fin 3) ρ * y₀ := by
        rw [hy₀, ← Sec13.Res2Proof.diagUnits_self_eq_scalar, ← mul_assoc, diagUnits_mul]
  set g' : GL (Fin 3) 𝕂 := g * u⁻¹ with hg'
  have hg'H : g' ∈ glPi π 3 (p ^ f) 𝕂 := mul_mem hg (inv_mem huH)
  have hg'y : g'⁻¹ * y * g' = GeneralLinearGroup.scalar (Fin 3) ρ * y₀ := by
    rw [← hkey, ← hgy, hg']
    group
  have hdT : diagTau hτ = diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 :=
    diagTau_eq_diagUnits hτ hτ0
  have hg's : g'⁻¹ * (s * z) * g' = diagTau hτ := by
    have h1 : g'⁻¹ * (s * z) * g' = u * (g⁻¹ * (s * z) * g) * u⁻¹ := by rw [hg']; group
    rw [h1, hD, hdT, hu, Sec13.Res2Proof.diagUnits_commute, mul_inv_cancel_right]
  have hsz : s * z = g' * diagTau hτ * g'⁻¹ := by rw [← hg's]; group
  have hmkz : ProjGenLinGroup.mk z = 1 := mk_eq_one_iff_mem_statedScalars.mpr hz
  have hmks : ProjGenLinGroup.mk s = ProjGenLinGroup.mk (g' * diagTau hτ * g'⁻¹) := by
    rw [← hsz, map_mul, hmkz, mul_one]
  have hyeq : y = GeneralLinearGroup.scalar (Fin 3) ρ * (g' * y₀ * g'⁻¹) := by
    have h2 : y = g' * (g'⁻¹ * y * g') * g'⁻¹ := by group
    rw [h2, hg'y]
    have h3 := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ρ g').eq
    calc g' * (GeneralLinearGroup.scalar (Fin 3) ρ * y₀) * g'⁻¹ =
        (g' * GeneralLinearGroup.scalar (Fin 3) ρ) * y₀ * g'⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ρ * (g' * y₀ * g'⁻¹) := by rw [h3]; group
  have hmky : ProjGenLinGroup.mk y = ProjGenLinGroup.mk (g' * y₀ * g'⁻¹) := by
    rw [hyeq, map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨ρ, rfl⟩, one_mul]
  have htL : g' * swapNeg * g'⁻¹ ∈ slPi π 3 (p ^ f) 𝕂 :=
    conj_mem_slPi hπ hg'H (swapNeg_mem_slPi hπ)
  set tb : X := e.symm (projOf _ ⟨g' * swapNeg * g'⁻¹, htL⟩) with htb
  have het : ((e tb : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g' * swapNeg * g'⁻¹) := by
    rw [htb, MulEquiv.apply_symm_apply, coe_projOf]
  have hmkconj : ∀ w : GL (Fin 3) 𝕂, ProjGenLinGroup.mk (g' * w * g'⁻¹) =
      ProjGenLinGroup.mk g' * ProjGenLinGroup.mk w * (ProjGenLinGroup.mk g')⁻¹ := fun w => by
    rw [map_mul, map_mul, map_inv]
  have hτ3 : Units.mk0 τ hτ0 ^ 3 = 1 := Units.ext (by simp [hτ])
  have htd : swapNeg * diagTau hτ * swapNeg⁻¹ = (diagTau hτ)⁻¹ := by
    rw [hdT, swapNeg_conj_diagUnits, diagUnits_inv₃]
    congr 1
    · rw [eq_inv_iff_mul_eq_one, ← pow_succ, hτ3]
    · rw [eq_inv_iff_mul_eq_one, ← pow_succ', hτ3]
  set y₁ : GL (Fin 3) 𝕂 := swapNeg * y₀ * swapNeg⁻¹ with hy₁
  have hσ' : ∀ w : X, ((e (σ w) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g' * y₀ * g'⁻¹) * (e w : ProjGenLinGroup (Fin 3) 𝕂) *
        (ProjGenLinGroup.mk (g' * y₀ * g'⁻¹))⁻¹ := fun w => by rw [hσ, hmky]
  have hτσ : ∀ w : X, ((e ((MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) w) :
      projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
      ProjGenLinGroup.mk (g' * y₁ * g'⁻¹) * (e w : ProjGenLinGroup (Fin 3) 𝕂) *
        (ProjGenLinGroup.mk (g' * y₁ * g'⁻¹))⁻¹ := by
    intro w
    have e1 : (MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) w = tb * σ (tb⁻¹ * w * tb) * tb⁻¹ := by
      rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
        inv_inv]
    have e2 : ∀ u v : X, ((e (u * v) : projImage (slPi π 3 (p ^ f) 𝕂)) :
        ProjGenLinGroup (Fin 3) 𝕂) = (e u : ProjGenLinGroup (Fin 3) 𝕂) * (e v) := fun u v => by
      rw [map_mul, Subgroup.coe_mul]
    have e3 : ∀ u : X, ((e u⁻¹ : projImage (slPi π 3 (p ^ f) 𝕂)) :
        ProjGenLinGroup (Fin 3) 𝕂) = (e u : ProjGenLinGroup (Fin 3) 𝕂)⁻¹ := fun u => by
      rw [map_inv, Subgroup.coe_inv]
    have hY : ProjGenLinGroup.mk (g' * y₁ * g'⁻¹) = ProjGenLinGroup.mk (g' * swapNeg * g'⁻¹) *
        ProjGenLinGroup.mk (g' * y₀ * g'⁻¹) * (ProjGenLinGroup.mk (g' * swapNeg * g'⁻¹))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [hy₁]
      group
    rw [e1, e2, e2, hσ', e2, e2, e3, het, hY]
    group
  refine ⟨tb, ?_, ?_, ?_⟩
  ·
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [het, hse, hmks, hmkconj, hmkconj]
    have h1 : ProjGenLinGroup.mk swapNeg * ProjGenLinGroup.mk (diagTau hτ) *
        (ProjGenLinGroup.mk swapNeg)⁻¹ = (ProjGenLinGroup.mk (diagTau hτ))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, htd, map_inv]
    calc ProjGenLinGroup.mk g' * ProjGenLinGroup.mk swapNeg * (ProjGenLinGroup.mk g')⁻¹ *
          (ProjGenLinGroup.mk g' * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk g')⁻¹) *
          (ProjGenLinGroup.mk g' * ProjGenLinGroup.mk swapNeg * (ProjGenLinGroup.mk g')⁻¹)⁻¹ =
        ProjGenLinGroup.mk g' * (ProjGenLinGroup.mk swapNeg * ProjGenLinGroup.mk (diagTau hτ) *
          (ProjGenLinGroup.mk swapNeg)⁻¹) * (ProjGenLinGroup.mk g')⁻¹ := by group
      _ = (ProjGenLinGroup.mk g' * ProjGenLinGroup.mk (diagTau hτ) *
          (ProjGenLinGroup.mk g')⁻¹)⁻¹ := by rw [h1]; group
  ·
    set M : Subgroup (GL (Fin 3) 𝕂) := (monoThree 𝕂).map (MulAut.conj g').toMonoidHom with hM
    have hMp : IsPGroup 3 M := isPGroup_monoThree.map _
    refine (isPGroup_actsBySub e hMp).to_le ((Subgroup.closure_le _).mpr ?_)
    have hmemM : ∀ w ∈ monoThree 𝕂, g' * w * g'⁻¹ ∈ M := fun w hw => ⟨w, hw, rfl⟩
    have h0 : ∃ k : ℕ, (1 : 𝕂ˣ) ^ 3 ^ k = 1 := ⟨0, by simp⟩
    have hτ9 : ∃ k : ℕ, (Units.mk0 τ hτ0 ^ 2) ^ 3 ^ k = 1 :=
      ⟨1, by rw [← pow_mul, pow_one, mul_comm, pow_mul, hτ3, one_pow]⟩
    have hdT3 : diagTau hτ ∈ monoThree 𝕂 := by
      rw [hdT]
      exact Subgroup.mem_sup_right (diagUnits_mem_diagThree ⟨1, by rw [pow_one, hτ3]⟩ hτ9 h0)
    have hy₀3 : y₀ ∈ monoThree 𝕂 :=
      mul_mem (Subgroup.mem_sup_right (diagUnits_mem_diagThree hl₃ h0 h0))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hy₁3 : y₁ ∈ monoThree 𝕂 := by
      have e1 : y₁ = (swapNeg * diagUnits l₃ 1 1 * swapNeg⁻¹) * (swapNeg * cycThree * swapNeg⁻¹) :=
        by rw [hy₁, hy₀]; group
      rw [e1, swapNeg_conj_diagUnits, swapNeg_conj_cycThree]
      exact mul_mem (Subgroup.mem_sup_right (diagUnits_mem_diagThree h0 hl₃ h0))
        (Subgroup.mem_sup_left (inv_mem (Subgroup.mem_zpowers _)))
    intro α hα
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl
    · refine ⟨g' * diagTau hτ * g'⁻¹, hmemM _ hdT3, fun w => ?_⟩
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hse, hmks]
    · exact ⟨g' * y₀ * g'⁻¹, hmemM _ hy₀3, hσ'⟩
    · exact ⟨g' * y₁ * g'⁻¹, hmemM _ hy₁3, hτσ⟩
  ·
    intro hcomm
    have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) 𝕂)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    set Y₀ : GL (Fin 3) 𝕂 := g' * y₀ * g'⁻¹ with hY₀
    set Y₁ : GL (Fin 3) 𝕂 := g' * y₁ * g'⁻¹ with hY₁
    set W : GL (Fin 3) 𝕂 := (Y₁ * Y₀)⁻¹ * (Y₀ * Y₁) with hWdef
    have hW : ∀ m ∈ slPi π 3 (p ^ f) 𝕂, W * m * W⁻¹ * m⁻¹ ∈ StatedScalars (Fin 3) 𝕂 := by
      intro m hm
      rw [← mk_eq_one_iff_mem_statedScalars]
      set w : X := e.symm (projOf _ ⟨m, hm⟩) with hwdef
      have hew : ((e w : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
          ProjGenLinGroup.mk m := by rw [hwdef, MulEquiv.apply_symm_apply, coe_projOf]
      have h1 := congrArg (fun α : MulAut X =>
        ((e (α w) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂)) hcomm
      have h1' : ((e (σ ((MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) w)) :
          projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
          ((e ((MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) (σ w)) :
          projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) := h1
      have hL : ((e (σ ((MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) w)) :
          projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
          ProjGenLinGroup.mk Y₀ * (ProjGenLinGroup.mk Y₁ * ProjGenLinGroup.mk m *
            (ProjGenLinGroup.mk Y₁)⁻¹) * (ProjGenLinGroup.mk Y₀)⁻¹ := by
        rw [hσ', hτσ, hew]
      have hR : ((e ((MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) (σ w)) :
          projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
          ProjGenLinGroup.mk Y₁ * (ProjGenLinGroup.mk Y₀ * ProjGenLinGroup.mk m *
            (ProjGenLinGroup.mk Y₀)⁻¹) * (ProjGenLinGroup.mk Y₁)⁻¹ := by
        rw [hτσ, hσ', hew]
      have h2 := h1'
      rw [hL, hR] at h2
      simp only [hWdef, map_mul, map_inv]
      calc (ProjGenLinGroup.mk Y₀)⁻¹ * (ProjGenLinGroup.mk Y₁)⁻¹ *
            (ProjGenLinGroup.mk Y₀ * ProjGenLinGroup.mk Y₁) * ProjGenLinGroup.mk m *
            ((ProjGenLinGroup.mk Y₀)⁻¹ * (ProjGenLinGroup.mk Y₁)⁻¹ *
              (ProjGenLinGroup.mk Y₀ * ProjGenLinGroup.mk Y₁))⁻¹ * (ProjGenLinGroup.mk m)⁻¹ =
          (ProjGenLinGroup.mk Y₀)⁻¹ * (ProjGenLinGroup.mk Y₁)⁻¹ *
            (ProjGenLinGroup.mk Y₀ * (ProjGenLinGroup.mk Y₁ * ProjGenLinGroup.mk m *
              (ProjGenLinGroup.mk Y₁)⁻¹) * (ProjGenLinGroup.mk Y₀)⁻¹) *
            ProjGenLinGroup.mk Y₁ * ProjGenLinGroup.mk Y₀ * (ProjGenLinGroup.mk m)⁻¹ := by group
        _ = (ProjGenLinGroup.mk Y₀)⁻¹ * (ProjGenLinGroup.mk Y₁)⁻¹ *
            (ProjGenLinGroup.mk Y₁ * (ProjGenLinGroup.mk Y₀ * ProjGenLinGroup.mk m *
              (ProjGenLinGroup.mk Y₀)⁻¹) * (ProjGenLinGroup.mk Y₁)⁻¹) *
            ProjGenLinGroup.mk Y₁ * ProjGenLinGroup.mk Y₀ * (ProjGenLinGroup.mk m)⁻¹ := by
          rw [h2]
        _ = 1 := by group
    obtain ⟨ζ, hζ⟩ := mem_statedScalars_of_comm_mod hF hq hW
    have hy₁' : y₁ = diagUnits 1 l₃ 1 * cycThree⁻¹ := by
      rw [hy₁, hy₀, show swapNeg * (diagUnits l₃ 1 1 * cycThree) * swapNeg⁻¹ =
        (swapNeg * diagUnits l₃ 1 1 * swapNeg⁻¹) * (swapNeg * cycThree * swapNeg⁻¹) by group,
        swapNeg_conj_diagUnits, swapNeg_conj_cycThree]
    have e1 : y₀ * y₁ = diagUnits l₃ 1 l₃ := by
      rw [hy₀, hy₁', show diagUnits l₃ 1 1 * cycThree * (diagUnits 1 l₃ 1 * cycThree⁻¹) =
        diagUnits l₃ 1 1 * (cycThree * diagUnits 1 l₃ 1 * cycThree⁻¹) by group,
        cycThree_conj_diagUnits, diagUnits_mul, mul_one, mul_one, one_mul]
    have e2 : y₁ * y₀ = diagUnits 1 l₃ l₃ := by
      rw [hy₀, hy₁', show diagUnits 1 l₃ 1 * cycThree⁻¹ * (diagUnits l₃ 1 1 * cycThree) =
        diagUnits 1 l₃ 1 * (cycThree⁻¹ * diagUnits l₃ 1 1 * cycThree) by group,
        cycThree_inv_conj_diagUnits, diagUnits_mul, mul_one, mul_one, one_mul]
    have hWd : W = g' * diagUnits l₃ l₃⁻¹ 1 * g'⁻¹ := by
      have h1 : W = g' * ((y₁ * y₀)⁻¹ * (y₀ * y₁)) * g'⁻¹ := by
        rw [hWdef, hY₀, hY₁]
        group
      rw [h1, e1, e2, diagUnits_inv₃, diagUnits_mul, inv_one, one_mul, inv_mul_cancel, mul_one]
    have hR : diagUnits l₃ l₃⁻¹ 1 = GeneralLinearGroup.scalar (Fin 3) ζ := by
      have h1 : diagUnits l₃ l₃⁻¹ 1 = g'⁻¹ * W * g' := by rw [hWd]; group
      rw [h1, ← hζ, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ g'⁻¹).eq,
        inv_mul_cancel_right]
    have hl₃1 : l₃ = 1 := by
      have h0 := congrArg (fun M : GL (Fin 3) 𝕂 => (M : Matrix (Fin 3) (Fin 3) 𝕂) 0 0) hR
      have h2 := congrArg (fun M : GL (Fin 3) 𝕂 => (M : Matrix (Fin 3) (Fin 3) 𝕂) 2 2) hR
      simp only [coe_diagUnits_eq, GeneralLinearGroup.coe_scalar] at h0 h2
      simp at h0 h2
      apply Units.ext
      rw [h0, ← h2, Units.val_one]
    apply hni
    refine ⟨g' * cycThree * g'⁻¹, conj_mem_slPi hπ hg'H (cycThree_mem_slPi hπ), fun m _ => ?_⟩
    have hy₀C : y₀ = cycThree := by rw [hy₀, hl₃1, diagUnits_one₃, one_mul]
    have hY₀C : Y₀ = g' * cycThree * g'⁻¹ := by rw [hY₀, hy₀C]
    have hc : ∀ M : GL (Fin 3) 𝕂, M * GeneralLinearGroup.scalar (Fin 3) ρ =
        GeneralLinearGroup.scalar (Fin 3) ρ * M :=
      fun M => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ρ M).eq
    rw [hyeq, hY₀C]
    calc GeneralLinearGroup.scalar (Fin 3) ρ * (g' * cycThree * g'⁻¹) * m *
          (GeneralLinearGroup.scalar (Fin 3) ρ * (g' * cycThree * g'⁻¹))⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) ρ * (g' * cycThree * g'⁻¹ * m *
          (g' * cycThree * g'⁻¹)⁻¹) * (GeneralLinearGroup.scalar (Fin 3) ρ)⁻¹ := by group
      _ = g' * cycThree * g'⁻¹ * m * (g' * cycThree * g'⁻¹)⁻¹ := by
        rw [← hc, mul_inv_cancel_right]

theorem inv_conj_eq_of_conj_eq_scalar_mul {w d : GL (Fin 3) 𝕂} {lam : 𝕂ˣ}
    (h : w * d * w⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * d) :
    w⁻¹ * d * w = (GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ * d := by
  have hsc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar lam w⁻¹).eq
  have h6 : GeneralLinearGroup.scalar (Fin 3) lam * (w⁻¹ * d * w) = d := by
    calc GeneralLinearGroup.scalar (Fin 3) lam * (w⁻¹ * d * w) =
        (GeneralLinearGroup.scalar (Fin 3) lam * w⁻¹) * d * w := by group
      _ = w⁻¹ * (GeneralLinearGroup.scalar (Fin 3) lam * d) * w := by rw [← hsc]; group
      _ = d := by rw [← h]; group
  calc w⁻¹ * d * w = (GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ *
      (GeneralLinearGroup.scalar (Fin 3) lam * (w⁻¹ * d * w)) := by group
    _ = (GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ * d := by rw [h6]

end Core

section Wrap

variable {G : Type} [Group G] [Finite G]

open KS128NotHJTC (false_of_commute_irreducible)

theorem exists_conj_inv_of_type3 {a : G} {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    {c x : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hxc : x * c = c * x)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx : Sec4.InducesTypeOn K x 3) :
    ∃ tb : K ⧸ aschbacherSolvableCore 3 K,
      tb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ * tb⁻¹ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩)⁻¹ ∧
      IsPGroup 3 (Subgroup.closure
        {MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩),
          thetaBarAct K ⟨x, hxN⟩,
          MulAut.conj tb * thetaBarAct K ⟨x, hxN⟩ * (MulAut.conj tb)⁻¹}) ∧
      thetaBarAct K ⟨x, hxN⟩ * (MulAut.conj tb * thetaBarAct K ⟨x, hxN⟩ * (MulAut.conj tb)⁻¹) ≠
        (MulAut.conj tb * thetaBarAct K ⟨x, hxN⟩ * (MulAut.conj tb)⁻¹) *
          thetaBarAct K ⟨x, hxN⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxN', π, p, f, 𝕂, _, hF, hq, e, y, hyH, hy3, hact⟩ := hx
  have := hF.finite
  set σ := thetaBarAct K ⟨x, hxN⟩ with hσdef
  have hσ : ∀ z : K ⧸ aschbacherSolvableCore 3 K,
      ((e (σ z) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) 𝕂) * (ProjGenLinGroup.mk y)⁻¹ :=
    hact
  have hπ : π = false → UnitaryFieldData p f 𝕂 := fun h => by subst h; exact hF.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hF.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hF hq
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have hKp : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  set cb : K ⧸ aschbacherSolvableCore 3 K :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ with hcbdef
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e cb).2
  have hc'3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcb3 : cb ^ 3 = 1 := by rw [hcbdef, ← map_pow, hc'3, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h1
    have h2 := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
      (KS128NotHJTC.isPGroup_zpowers_of_pow_three hc'3) (Subgroup.mem_zpowers _)
      (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact hc1 (congrArg Subtype.val h2)
  have hsH : s ∈ glPi π 3 (p ^ f) 𝕂 := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) 𝕂 := by
    intro hsZ
    apply hcb1
    apply e.injective
    apply Subtype.ext
    rw [← hse, map_one, Subgroup.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) 𝕂 := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse, ← Subgroup.coe_pow, ← map_pow, hcb3,
      map_one, Subgroup.coe_one]
  have hsdet : (s : Matrix (Fin 3) (Fin 3) 𝕂).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  have hfix : σ cb = cb := by
    rw [hσdef, hcbdef, thetaBarAct_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, hxc, mul_inv_cancel_right]
  have h1 := hσ cb
  rw [hfix, ← hse] at h1
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) 𝕂 := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1,
      mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := hysZ
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  have hlam1 : lam ≠ 1 := by
    rintro rfl
    refine false_of_commute_irreducible hτ hτ1 h3 hsdet hs3 hsZ ?_ hy3.2.2
    rw [map_one, one_mul] at hys
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hys]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hys
  have hsZ' : s ∉ zPi π 3 (p ^ f) 𝕂 := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hz)
  have hs3' : s ^ 3 ∈ zPi π 3 (p ^ f) 𝕂 := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3⟩
  have htype : Type123 π (p ^ f) 𝕂 s 1 := by
    rcases type123_exhaust hF hq hsH hsZ' hs3' with h1 | h2 | h3
    · exact h1
    · exact absurd htr (trace_ne_zero_of_type2 hF hq h2)
    · exact absurd ⟨s, hs, fun m _ => rfl⟩ (not_inner_of_type3 hF hq hsH h3)
  obtain ⟨τ', hτ', hτ'1, z, hz, g, hg, hD⟩ := htype
  have hτ'0 : τ' ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ'
    exact zero_ne_one hτ'
  have hzs : z ∈ StatedScalars (Fin 3) 𝕂 := mem_statedScalars_of_mem_zPi hF hq hτ' hτ'1 hz
  have hzc : ∀ M : GL (Fin 3) 𝕂, M * z = z * M := fun M => commute_of_mem_statedScalars hzs M
  have hsc : ∀ (u : 𝕂ˣ) (M : GL (Fin 3) 𝕂),
      M * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * M :=
    fun u M => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u M).eq
  have hsz : s * z = g * diagTau hτ' * g⁻¹ := by rw [← hD]; group
  have hyD : (g⁻¹ * y * g) * diagTau hτ' * (g⁻¹ * y * g)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) lam * diagTau hτ' := by
    have e1 : y * (s * z) * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * (s * z) := by
      calc y * (s * z) * y⁻¹ = (y * s * y⁻¹) * (y * z * y⁻¹) := by group
        _ = (y * s * y⁻¹) * z := by rw [hzc y, mul_inv_cancel_right]
        _ = GeneralLinearGroup.scalar (Fin 3) lam * (s * z) := by rw [hys, mul_assoc]
    calc (g⁻¹ * y * g) * diagTau hτ' * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * (s * z) * y⁻¹) * g := by
          rw [← hD]; group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) lam * (s * z)) * g := by rw [e1]
      _ = GeneralLinearGroup.scalar (Fin 3) lam * diagTau hτ' := by
        rw [← hD, ← mul_assoc, hsc lam g⁻¹]
        group
  have hlam3 : (lam : 𝕂) ^ 3 = 1 := by
    have h2 := congrArg Units.val (pow_three_eq_one_of_conj_eq_scalar_mul hys)
    simpa using h2
  have hnf : ∃ (d₀ d₁ d₂ : 𝕂ˣ), d₀ ∈ rootsOfUnity (qSubPi π (p ^ f)) 𝕂 ∧
      d₁ ∈ rootsOfUnity (qSubPi π (p ^ f)) 𝕂 ∧ d₂ ∈ rootsOfUnity (qSubPi π (p ^ f)) 𝕂 ∧
      ((g⁻¹ * y * g = diagUnits d₀ d₁ d₂ * cycThree) ∨
        (g⁻¹ * y⁻¹ * g = diagUnits d₀ d₁ d₂ * cycThree)) := by
    have hC := cycThree_pow_conj_diagTau hτ' hτ'0
    have hwH : ∀ k : ℕ, g⁻¹ * y * g * (cycThree ^ k)⁻¹ ∈ glPi π 3 (p ^ f) 𝕂 := fun k =>
      mul_mem (mul_mem (mul_mem (inv_mem hg) hyH) hg)
        (inv_mem (pow_mem (slPi_le_glPi hπ (cycThree_mem_slPi hπ)) k))
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ' hτ'1 hlam3 with h1 | h1 | h1
    · exact absurd (Units.ext h1) hlam1
    ·
      have hl : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ' hτ'0 ^ (2 * 2)) =
          GeneralLinearGroup.scalar (Fin 3) lam := by
        congr 1
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, h1, show 2 * 2 = 3 + 1 by rfl, pow_succ,
          hτ', one_mul]
      have hcomm : (g⁻¹ * y * g * (cycThree ^ 2)⁻¹) * diagTau hτ' =
          diagTau hτ' * (g⁻¹ * y * g * (cycThree ^ 2)⁻¹) := by
        have e2 : (cycThree ^ 2)⁻¹ * diagTau hτ' * cycThree ^ 2 =
            (GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ * diagTau hτ' := by
          have := hC 2
          rw [hl] at this
          exact inv_conj_eq_of_conj_eq_scalar_mul this
        have e3 : (g⁻¹ * y * g) * ((GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ * diagTau hτ') *
            (g⁻¹ * y * g)⁻¹ = diagTau hτ' := by
          rw [← map_inv, ← mul_assoc, hsc lam⁻¹, mul_assoc, mul_assoc, ← mul_assoc _ _ _⁻¹,
            hyD, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
        calc (g⁻¹ * y * g * (cycThree ^ 2)⁻¹) * diagTau hτ' =
            (g⁻¹ * y * g) * ((cycThree ^ 2)⁻¹ * diagTau hτ' * cycThree ^ 2) *
              (g⁻¹ * y * g)⁻¹ * (g⁻¹ * y * g * (cycThree ^ 2)⁻¹) := by group
          _ = diagTau hτ' * (g⁻¹ * y * g * (cycThree ^ 2)⁻¹) := by rw [e2, e3]
      obtain ⟨d₀, d₁, d₂, hd₀, hd₁, hd₂, hdw⟩ :=
        Sec13.Res2Proof.exists_diagUnits_of_commute hF hq hτ' hτ'1 (hwH 2) hcomm
      refine ⟨d₂⁻¹, d₀⁻¹, d₁⁻¹, inv_mem hd₂, inv_mem hd₀, inv_mem hd₁, Or.inr ?_⟩
      have hy'' : g⁻¹ * y * g = diagUnits d₀ d₁ d₂ * cycThree ^ 2 := by
        rw [← hdw]
        group
      have hC3 : (cycThree : GL (Fin 3) 𝕂) ^ 2 = cycThree⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, cycThree_pow_three]
      calc g⁻¹ * y⁻¹ * g = (g⁻¹ * y * g)⁻¹ := by group
        _ = cycThree * (diagUnits d₀ d₁ d₂)⁻¹ * cycThree⁻¹ * cycThree := by
          rw [hy'', hC3]
          group
        _ = diagUnits d₂⁻¹ d₀⁻¹ d₁⁻¹ * cycThree := by
          rw [diagUnits_inv₃, cycThree_conj_diagUnits]
    ·
      have hl : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ' hτ'0 ^ (2 * 1)) =
          GeneralLinearGroup.scalar (Fin 3) lam := by
        congr 1
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, h1]
      have hcomm : (g⁻¹ * y * g * (cycThree ^ 1)⁻¹) * diagTau hτ' =
          diagTau hτ' * (g⁻¹ * y * g * (cycThree ^ 1)⁻¹) := by
        have e2 : (cycThree ^ 1)⁻¹ * diagTau hτ' * cycThree ^ 1 =
            (GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ * diagTau hτ' := by
          have := hC 1
          rw [hl] at this
          exact inv_conj_eq_of_conj_eq_scalar_mul this
        have e3 : (g⁻¹ * y * g) * ((GeneralLinearGroup.scalar (Fin 3) lam)⁻¹ * diagTau hτ') *
            (g⁻¹ * y * g)⁻¹ = diagTau hτ' := by
          rw [← map_inv, ← mul_assoc, hsc lam⁻¹, mul_assoc, mul_assoc, ← mul_assoc _ _ _⁻¹,
            hyD, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
        calc (g⁻¹ * y * g * (cycThree ^ 1)⁻¹) * diagTau hτ' =
            (g⁻¹ * y * g) * ((cycThree ^ 1)⁻¹ * diagTau hτ' * cycThree ^ 1) *
              (g⁻¹ * y * g)⁻¹ * (g⁻¹ * y * g * (cycThree ^ 1)⁻¹) := by group
          _ = diagTau hτ' * (g⁻¹ * y * g * (cycThree ^ 1)⁻¹) := by rw [e2, e3]
      obtain ⟨d₀, d₁, d₂, hd₀, hd₁, hd₂, hdw⟩ :=
        Sec13.Res2Proof.exists_diagUnits_of_commute hF hq hτ' hτ'1 (hwH 1) hcomm
      refine ⟨d₀, d₁, d₂, hd₀, hd₁, hd₂, Or.inl ?_⟩
      rw [← hdw]
      group
  obtain ⟨d₀, d₁, d₂, hd₀, hd₁, hd₂, hy | hy⟩ := hnf
  · exact exists_conj_inv_of_normal_form hF hq hKp e σ (not_inner_of_type3 hF hq hyH hy3) hσ cb
      hse.symm hzs hg hτ' hτ'1 hD hd₀ hd₁ hd₂ hy
  ·
    have hni' : ¬ ∃ l ∈ slPi π 3 (p ^ f) 𝕂, ∀ m ∈ slPi π 3 (p ^ f) 𝕂,
        y⁻¹ * m * y⁻¹⁻¹ = l * m * l⁻¹ := by
      rintro ⟨l, hl, hlm⟩
      apply not_inner_of_type3 hF hq hyH hy3
      refine ⟨l⁻¹, inv_mem hl, fun m hm => ?_⟩
      have h1 := hlm _ (conj_mem_slPi hπ hyH hm)
      rw [inv_inv] at h1
      have h2 : m = l * (y * m * y⁻¹) * l⁻¹ := by rw [← h1]; group
      calc y * m * y⁻¹ = l⁻¹ * (l * (y * m * y⁻¹) * l⁻¹) * l⁻¹⁻¹ := by group
        _ = l⁻¹ * m * l⁻¹⁻¹ := by rw [← h2]
    have hσi : ∀ w : K ⧸ aschbacherSolvableCore 3 K,
        ((e (σ⁻¹ w) : projImage (slPi π 3 (p ^ f) 𝕂)) : ProjGenLinGroup (Fin 3) 𝕂) =
          ProjGenLinGroup.mk y⁻¹ * (e w : ProjGenLinGroup (Fin 3) 𝕂) *
            (ProjGenLinGroup.mk y⁻¹)⁻¹ := by
      intro w
      have h1 := hσ (σ⁻¹ w)
      rw [show σ (σ⁻¹ w) = w from by simp] at h1
      rw [map_inv, inv_inv, h1]
      group
    obtain ⟨tb, htb, hP, hnc⟩ := exists_conj_inv_of_normal_form hF hq hKp e σ⁻¹ hni' hσi cb
      hse.symm hzs hg hτ' hτ'1 hD hd₀ hd₁ hd₂ hy
    have hinv : MulAut.conj tb * σ * (MulAut.conj tb)⁻¹ =
        (MulAut.conj tb * σ⁻¹ * (MulAut.conj tb)⁻¹)⁻¹ := by group
    refine ⟨tb, htb, hP.to_le ((Subgroup.closure_le _).mpr ?_), ?_⟩
    · intro α hα
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
      rcases hα with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · have h1 : σ⁻¹ ∈ Subgroup.closure ({MulAut.conj cb, σ⁻¹,
            MulAut.conj tb * σ⁻¹ * (MulAut.conj tb)⁻¹} :
              Set (MulAut (K ⧸ aschbacherSolvableCore 3 K))) := Subgroup.subset_closure (by simp)
        simpa using inv_mem h1
      · rw [SetLike.mem_coe, hinv]
        exact inv_mem (Subgroup.subset_closure (by simp))
    · intro h
      apply hnc
      have h2 := (show Commute σ (MulAut.conj tb * σ * (MulAut.conj tb)⁻¹) from h).inv_inv
      rw [hinv, inv_inv] at h2
      exact h2.eq

end Wrap

end CFSG.RankThree.PartTwo.Sec12.Res3Proof
