module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace KacPt

private theorem lk0xlcact_theta_apply (τ : Tag) (i : Fin τ.rank) :
    theta τ i = (hr τ i : ℤ) := rfl

private theorem lk0xlcact_zsmul_smul {τ : Tag} (z : WeylGroup τ) (n : ℤ)
    (v : Fin τ.rank → ℤ) : z • (n • v) = n • (z • v) := by
  let φ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun w => z • w, map_zero' := smul_zero z, map_add' := fun a b => smul_add z a b }
  exact map_zsmul φ n v

theorem lam_add {τ : Tag} (K : KacPt τ) (γ γ' : Fin τ.rank → ℤ) :
    K.lam (γ + γ') = K.lam γ + K.lam γ' := by
  simp [lam, mul_add, Finset.sum_add_distrib]

theorem lam_smul {τ : Tag} (K : KacPt τ) (n : ℤ) (γ : Fin τ.rank → ℤ) :
    K.lam (n • γ) = n * K.lam γ := by
  simp only [lam, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lam_single {τ : Tag} (K : KacPt τ) (i : Fin τ.rank) :
    K.lam (Pi.single i 1 : Fin τ.rank → ℤ) = K.s i := by
  rw [lam, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne, hb, Ne.symm hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem lam_theta {τ : Tag} (K : KacPt τ) : K.lam (theta τ) = (K.p : ℤ) - K.s0 := by
  have h := congrArg (Nat.cast : ℕ → ℤ) K.weight
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul] at h
  rw [lam]
  simp only [lk0xlcact_theta_apply]
  have hcomm : (∑ i, (K.s i : ℤ) * (hr τ i : ℤ)) =
      ∑ i, (hr τ i : ℤ) * (K.s i : ℤ) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm]
  linarith

theorem lam_nonneg_of_nonneg {τ : Tag} (K : KacPt τ) {γ : Fin τ.rank → ℤ} (h : ∀ i, 0 ≤ γ i) :
    0 ≤ K.lam γ := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (h i)

theorem abs_lam_le {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : |K.lam γ| ≤ (K.p : ℤ) := by
  obtain ⟨hbox, _htheta, _hhr⟩ := hT
  have hspos : ∀ i, 0 ≤ (K.s i : ℤ) := fun i => Int.natCast_nonneg _
  have hlow : -(K.lam (theta τ)) ≤ K.lam γ := by
    rw [lam, lam, ← Finset.sum_neg_distrib]
    simp only [lk0xlcact_theta_apply]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hbox γ hγ i).1 (hspos i)
    simpa [mul_neg] using this
  have hhigh : K.lam γ ≤ K.lam (theta τ) := by
    rw [lam, lam]
    simp only [lk0xlcact_theta_apply]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hbox γ hγ i).2 (hspos i)
  have htheta_eq : K.lam (theta τ) = (K.p : ℤ) - (K.s0 : ℤ) := lam_theta K
  have hs0le : (K.s0 : ℤ) ≤ (K.p : ℤ) := by
    have h : K.s0 ≤ K.p := by
      have hw := K.weight
      omega
    exact_mod_cast h
  rw [abs_le]
  constructor
  · rw [htheta_eq] at hlow
    linarith
  · calc K.lam γ ≤ K.lam (theta τ) := hhigh
      _ = (K.p : ℤ) - (K.s0 : ℤ) := htheta_eq
      _ ≤ (K.p : ℤ) := by linarith

theorem shift_spec {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab)
    (γ : Fin τ.rank → ℤ) : (K.p : ℤ) * K.shift z γ = K.lam γ - K.lam (z • γ) := by
  have hdvd : (K.p : ℤ) ∣ K.lam γ - K.lam (z • γ) := by
    have h := hz γ
    have heq : K.lam γ - K.lam (z • γ) = -(K.lam (z • γ) - K.lam γ) := by ring
    rw [heq]
    exact dvd_neg.mpr h
  rw [shift]
  exact Int.mul_ediv_cancel' hdvd

theorem shift_add {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab)
    (γ γ' : Fin τ.rank → ℤ) : K.shift z (γ + γ') = K.shift z γ + K.shift z γ' := by
  have hp : (K.p : ℤ) ≠ 0 := by exact_mod_cast K.p_pos.ne'
  apply mul_left_cancel₀ hp
  rw [shift_spec K hz, mul_add, shift_spec K hz, shift_spec K hz, smul_add, lam_add, lam_add]
  ring

theorem shift_smul {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab) (n : ℤ)
    (γ : Fin τ.rank → ℤ) : K.shift z (n • γ) = n * K.shift z γ := by
  have hp : (K.p : ℤ) ≠ 0 := by exact_mod_cast K.p_pos.ne'
  apply mul_left_cancel₀ hp
  rw [shift_spec K hz, lk0xlcact_zsmul_smul, lam_smul, lam_smul, ← mul_sub,
    ← shift_spec K hz]
  ring

theorem shift_one {τ : Tag} (K : KacPt τ) (γ : Fin τ.rank → ℤ) : K.shift 1 γ = 0 := by
  simp [shift]

theorem shift_mul {τ : Tag} (K : KacPt τ) {z z' : WeylGroup τ} (hz : z ∈ K.stab)
    (hz' : z' ∈ K.stab) (γ : Fin τ.rank → ℤ) :
    K.shift (z * z') γ = K.shift z' γ + K.shift z (z' • γ) := by
  have hzz' : z * z' ∈ K.stab := K.stab.mul_mem hz hz'
  have hp : (K.p : ℤ) ≠ 0 := by exact_mod_cast K.p_pos.ne'
  apply mul_left_cancel₀ hp
  rw [shift_spec K hzz', mul_add, shift_spec K hz', shift_spec K hz, mul_smul]
  ring

theorem abs_shift_le {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : |K.shift z γ| ≤ 2 := by
  have hp_pos : (0 : ℤ) < (K.p : ℤ) := by exact_mod_cast K.p_pos
  have hspec := shift_spec K hz γ
  have habs : |(K.p : ℤ) * K.shift z γ| = (K.p : ℤ) * |K.shift z γ| := by
    rw [abs_mul, abs_of_pos hp_pos]
  have hbound : |(K.p : ℤ) * K.shift z γ| ≤ 2 * (K.p : ℤ) := by
    rw [hspec]
    calc |K.lam γ - K.lam (z • γ)| ≤ |K.lam γ| + |K.lam (z • γ)| := abs_sub _ _
      _ ≤ (K.p : ℤ) + (K.p : ℤ) :=
          add_le_add (abs_lam_le hT K hγ) (abs_lam_le hT K (IsRoot.smul hγ z))
      _ = 2 * (K.p : ℤ) := by ring
  have key : (K.p : ℤ) * |K.shift z γ| ≤ (K.p : ℤ) * 2 := by
    rw [← habs, mul_comm (K.p : ℤ) 2]
    exact hbound
  exact le_of_mul_le_mul_left key hp_pos

theorem act_one {τ : Tag} (K : KacPt τ) (a : AffPair τ) : K.act 1 a = a := by
  simp [act, shift_one]

theorem act_mul {τ : Tag} (K : KacPt τ) {z z' : WeylGroup τ} (hz : z ∈ K.stab)
    (hz' : z' ∈ K.stab) (a : AffPair τ) : K.act (z * z') a = K.act z (K.act z' a) := by
  apply Prod.ext
  · show (z * z') • a.1 = z • (z' • a.1)
    rw [mul_smul]
  · show a.2 + K.shift (z * z') a.1 = (a.2 + K.shift z' a.1) + K.shift z (z' • a.1)
    rw [shift_mul K hz hz']
    ring

theorem act_add {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab)
    (a b : AffPair τ) : K.act z (a + b) = K.act z a + K.act z b := by
  apply Prod.ext
  · show z • (a.1 + b.1) = z • a.1 + z • b.1
    rw [smul_add]
  · show (a.2 + b.2) + K.shift z (a.1 + b.1) =
      (a.2 + K.shift z a.1) + (b.2 + K.shift z b.1)
    rw [shift_add K hz]
    ring

theorem act_smul {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab) (n : ℤ)
    (a : AffPair τ) : K.act z (n • a) = n • K.act z a := by
  apply Prod.ext
  · show z • (n • a.1) = n • (z • a.1)
    exact lk0xlcact_zsmul_smul z n a.1
  · show (n • a.2) + K.shift z (n • a.1) = n • (a.2 + K.shift z a.1)
    rw [shift_smul K hz n a.1]
    simp only [smul_eq_mul]
    ring

theorem act_neg {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab)
    (a : AffPair τ) : K.act z (-a) = -(K.act z a) := by
  simpa [neg_smul] using act_smul K hz (-1) a

private theorem lk0xlcact_act_zero {τ : Tag} (K : KacPt τ) (z : WeylGroup τ) :
    K.act z 0 = 0 := by
  have hlam : K.lam (0 : Fin τ.rank → ℤ) = 0 := by
    have := lam_smul K 0 (0 : Fin τ.rank → ℤ)
    simpa using this
  have h0 : K.shift z (0 : Fin τ.rank → ℤ) = 0 := by
    simp [shift, hlam]
  apply Prod.ext
  · show z • (0 : Fin τ.rank → ℤ) = 0
    simp
  · show (0 : ℤ) + K.shift z (0 : Fin τ.rank → ℤ) = 0
    rw [h0, add_zero]

theorem act_sum {τ : Tag} (K : KacPt τ) {z : WeylGroup τ} (hz : z ∈ K.stab) {ι : Type}
    (s : Finset ι) (f : ι → AffPair τ) :
    K.act z (∑ i ∈ s, f i) = ∑ i ∈ s, K.act z (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact lk0xlcact_act_zero K z
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add K hz, ih]

end KacPt

end CFSG.StandardType.GGK0LC

end
