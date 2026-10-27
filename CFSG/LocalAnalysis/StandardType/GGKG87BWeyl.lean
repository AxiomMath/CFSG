module

public import CFSG.LocalAnalysis.StandardType.GGKG87BLiftFixed
public import CFSG.LocalAnalysis.StandardType.GGKG87BRadDefs

import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.StandardType.KG87B

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private theorem fix_ker_of_pow_three
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hZk : ∀ w : L', w ∈ Subgroup.center L' → w ∈ ψ.ker)
    {a : MulAut L'} (ha : a ^ 3 = 1) {z : L'} (hz : z ∈ ψ.ker) : a z = z := by
  have h3 := TwE6Delta.card_ker_dvd_three_q8 hn hK hψ hker hperf
  have hmapk : ∀ w ∈ ψ.ker, a w ∈ ψ.ker := fun w hw => hZk _ (by
    rw [Subgroup.mem_center_iff]
    intro l
    have hzc := Subgroup.mem_center_iff.mp (hker hw) (a⁻¹ l)
    have := congrArg a hzc
    simpa only [map_mul, MulAut.apply_inv_self] using this)
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hord : orderOf z = 3 := by
    have hd : orderOf z ∣ 3 := by
      have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ψ.ker)
      rw [Subgroup.orderOf_mk] at h1
      exact h1.trans h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hz3 : z ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  have heq : Subgroup.zpowers z = ψ.ker := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hz) ?_
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd (by norm_num) h3
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ hmapk z hz : a z ∈ Subgroup.zpowers z)
  have hzm : ∀ k : ℤ, z ^ k = z ^ (k % 3) := fun k =>
    zpow_eq_zpow_emod k (by exact_mod_cast hz3 : z ^ (3 : ℤ) = 1)
  rw [hzm] at hm
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm3 with h | h | h
  ·
    rw [h, zpow_zero] at hm
    exact absurd (a.injective (hm.symm.trans (map_one a).symm)) hz1
  · rw [h, zpow_one] at hm
    exact hm.symm
  ·
    rw [h] at hm
    have h2 : a z = z ^ 2 := by rw [← hm]; norm_cast
    have hak : ∀ k : ℕ, a (z ^ k) = z ^ (2 * k) := fun k => by rw [map_pow, h2, ← pow_mul]
    have ha3 : (a ^ 3) z = z ^ 2 := by
      have e3 : (a ^ 3) z = a (a (a z)) := by
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
      rw [e3, h2, hak, hak, show 2 * (2 * 2) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hz3,
        one_pow, one_mul]
    rw [ha, MulAut.one_apply] at ha3
    exfalso
    apply hz1
    have : z * z = z * 1 := by rw [mul_one, ← pow_two, ← ha3]
    exact mul_left_cancel this

theorem exists_ggTorusWeylElt_of_transvection
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (h3 : 3 ∣ Nat.card ψ.ker) {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    {δ : K ≃+* K} (hδ : ∀ c : K, c ^ 3 = 1 → δ c = c) {b : MulAut L'} (hbA : b ∈ A)
    (hb : ∀ l, MulAut.congr ε (fieldActor (t := TwistTag.E6) σ δ) (ψ l) = ψ (b l))
    (hAb : ∀ a ∈ A, ∃ k : L', MulAut.conj k ∈ A ∧ ∃ j : ℕ, a = MulAut.conj k * b ^ j)
    {k₀ ku : L'} (hk₀ : MulAut.conj k₀ ∈ A) (hk₀dim : twE6FixDim K σ (ε.symm (ψ k₀)) = 36)
    (hku : MulAut.conj ku ∈ A) (hkudim : twE6FixDim K σ (ε.symm (ψ ku)) = 36)
    {w : ↥(twistedE6RootGroup K σ)} (hw : fieldActor (t := TwistTag.E6) σ δ w = w)
    (hwT : ∀ k : L', MulAut.conj k ∈ A → w * ε.symm (ψ k) * w⁻¹ * (ε.symm (ψ k))⁻¹ ∈
      Subgroup.closure ({ε.symm (ψ k₀), ε.symm (ψ ku)} : Set _))
    (hmove : w * ε.symm (ψ k₀) * w⁻¹ ∉ Subgroup.zpowers (ε.symm (ψ k₀))) :
    ∃ m : L', GGTorusWeylElt 3 A m ∧
      MulAut.conj m * MulAut.conj k₀ * (MulAut.conj m)⁻¹ ∉ Subgroup.zpowers (MulAut.conj k₀) := by
  classical
  have hcen : ∀ g : TwE6Delta.RecipeR K n, (∀ h, g * h = h * g) → g = 1 := fun g hg => by
    have hc : ε.symm g ∈ Subgroup.center (twistedE6RootGroup K σ) :=
      Subgroup.mem_center_iff.2 fun h => ε.injective (by
        rw [map_mul, map_mul, ε.apply_symm_apply, hg (ε h)])
    rw [center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.toRingHom.injective),
      Subgroup.mem_bot] at hc
    rw [← ε.apply_symm_apply g, hc, map_one]
  have hZk : ∀ z : L', z ∈ Subgroup.center L' → z ∈ ψ.ker := fun z hz => by
    rw [MonoidHom.mem_ker]
    refine hcen _ fun h => ?_
    obtain ⟨l, rfl⟩ := hψ h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]
  have hfixZ : ∀ a ∈ A, ∀ z ∈ ψ.ker, a z = z := fun a ha z hz =>
    fix_ker_of_pow_three hn hK hψ hker hperf hZk (hA.2 a ha) hz
  have hZ3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := fun z hz => by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ψ.ker)
    rw [Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.1
      (h1.trans (TwE6Delta.card_ker_dvd_three_q8 hn hK hψ hker hperf))
  have hpsi : ∀ x y : L', MulAut.conj x = MulAut.conj y → ψ x = ψ y := fun x y h => by
    have hc : x⁻¹ * y ∈ Subgroup.center L' := Subgroup.mem_center_iff.2 fun g => by
      have h1 : x * g * x⁻¹ = y * g * y⁻¹ := by
        have := congrArg (fun φ : MulAut L' => φ g) h
        simpa only [MulAut.conj_apply] using this
      calc g * (x⁻¹ * y) = x⁻¹ * (x * g * x⁻¹) * y := by group
        _ = x⁻¹ * (y * g * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * g := by group
    have h2 := MonoidHom.mem_ker.1 (hZk _ hc)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hk3 : ∀ k : L', MulAut.conj k ∈ A → ψ k ^ 3 = 1 := fun k hk => by
    have h1 : MulAut.conj (k ^ 3) = MulAut.conj 1 := by rw [map_pow, hA.2 _ hk, map_one]
    rw [← map_pow, hpsi _ _ h1, map_one]
  have hψcomm : ∀ k k' : L', MulAut.conj k ∈ A → MulAut.conj k' ∈ A →
      ψ k * ψ k' = ψ k' * ψ k := fun k k' hk hk' => by
    rw [← map_mul, ← map_mul]
    exact hpsi _ _ (by rw [map_mul, map_mul, hAcomm _ hk _ hk'])
  have hbfix : ∀ k : L', MulAut.conj k ∈ A → ψ (b k) = ψ k := fun k hk => by
    have hconj : b * MulAut.conj k * b⁻¹ = MulAut.conj (b k) := by
      ext g
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
        map_mul, map_inv, MulAut.apply_inv_self]
    exact hpsi _ _ (by rw [← hconj, hAcomm _ hbA _ hk, mul_inv_cancel_right])
  have hk₀3 := pow_three_eq_one_of_fixDim_36 hn hK σ hσ ε hψ hker hperf h3 (hk3 k₀ hk₀) hk₀dim
  have hku3 := pow_three_eq_one_of_fixDim_36 hn hK σ hσ ε hψ hker hperf h3 (hk3 ku hku) hkudim
  have hk₀c : ∀ k : L', MulAut.conj k ∈ A → k₀ * k = k * k₀ := fun k hk =>
    commute_of_fixDim_36 hn hK σ hσ ε hψ hker hperf h3 (hk3 k₀ hk₀) hk₀dim
      (hψcomm k₀ k hk₀ hk)
  have hkuc : ∀ k : L', MulAut.conj k ∈ A → ku * k = k * ku := fun k hk =>
    commute_of_fixDim_36 hn hK σ hσ ε hψ hker hperf h3 (hk3 ku hku) hkudim
      (hψcomm ku k hku hk)
  have hbk₀ := apply_eq_self_of_fixDim_36 hn hK σ hσ ε hψ hker hperf h3 hδ hb (hk3 k₀ hk₀)
    (hbfix k₀ hk₀) hk₀dim
  have hbku := apply_eq_self_of_fixDim_36 hn hK σ hσ ε hψ hker hperf h3 hδ hb (hk3 ku hku)
    (hbfix ku hku) hkudim
  have hbpow : ∀ (j : ℕ) (x : L'), b x = x → (b ^ j) x = x := fun j x hx => by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ b j, MulAut.mul_apply, hx, ih]
  have hAfix : ∀ a ∈ A, ∀ x : L', (∀ k : L', MulAut.conj k ∈ A → x * k = k * x) → b x = x →
      a x = x := fun a ha x hxk hbx => by
    obtain ⟨k, hk, j, rfl⟩ := hAb a ha
    rw [MulAut.mul_apply, hbpow j x hbx, MulAut.conj_apply, ← hxk k hk, mul_inv_cancel_right]
  have hpair : ({k₀, ku} : Set L').Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hk₀c _ hku
    · exact (hk₀c _ hku).symm
    · exact Commute.refl _
  have hcl := Subgroup.isMulCommutative_closure hpair
  have hcl3 : ∀ c ∈ Subgroup.closure ({k₀, ku} : Set L'), c ^ 3 = 1 := fun c hc => by
    induction hc using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := congrArg Subtype.val (hcl.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  have hclA : ∀ a ∈ A, ∀ c ∈ Subgroup.closure ({k₀, ku} : Set L'), a c = c := fun a ha c hc => by
    induction hc using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hAfix a ha _ hk₀c hbk₀
      · exact hAfix a ha _ hkuc hbku
    | one => exact map_one a
    | mul x y _ _ ihx ihy => rw [map_mul, ihx, ihy]
    | inv x _ ih => rw [map_inv, ih]
  obtain ⟨m, hm⟩ := hψ (ε w)
  have hψbm : ψ (b m) = ψ m := by
    rw [← hb, hm, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hw]
  obtain ⟨zm, hzm⟩ : ∃ zm, zm = m⁻¹ * b m := ⟨_, rfl⟩
  have hzmk : zm ∈ ψ.ker := by
    rw [hzm, MonoidHom.mem_ker, map_mul, map_inv, hψbm, inv_mul_cancel]
  have hbm : b m = m * zm := by rw [hzm, mul_inv_cancel_left]
  have hbjm : ∀ j : ℕ, (b ^ j) m = m * zm ^ j := fun j => by
    induction j with
    | zero => rw [pow_zero, pow_zero, MulAut.one_apply, mul_one]
    | succ j ih =>
      rw [pow_succ b j, MulAut.mul_apply, hbm, map_mul, ih, hbpow j zm (hfixZ b hbA zm hzmk),
        pow_succ zm j, mul_assoc]
  have hcomm_mem : ∀ k : L', MulAut.conj k ∈ A → ∃ c ∈ Subgroup.closure ({k₀, ku} : Set L'),
      ψ (m * k * m⁻¹ * k⁻¹) = ψ c := fun k hk => by
    have h2 : ε (w * ε.symm (ψ k) * w⁻¹ * (ε.symm (ψ k))⁻¹) = ψ (m * k * m⁻¹ * k⁻¹) := by
      simp only [map_mul, map_inv, ε.apply_symm_apply, hm]
    have hsub : (Subgroup.closure ({ε.symm (ψ k₀), ε.symm (ψ ku)} : Set _)).map ε.toMonoidHom ≤
        (Subgroup.closure ({k₀, ku} : Set L')).map ψ := by
      rw [MonoidHom.map_closure, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · exact ⟨k₀, Or.inl rfl, by simp⟩
      · exact ⟨ku, Or.inr rfl, by simp⟩
    obtain ⟨c, hc, hcψ⟩ := hsub ⟨_, hwT k hk, rfl⟩
    exact ⟨c, hc, by rw [hcψ, ← h2]; rfl⟩
  have hmem : ∀ a ∈ A, ∃ c ∈ Subgroup.closure ({k₀, ku} : Set L'), ∃ z ∈ ψ.ker,
      m * (a m)⁻¹ = c * z := fun a ha => by
    obtain ⟨k, hk, j, rfl⟩ := hAb a ha
    obtain ⟨c, hc, hcψ⟩ := hcomm_mem k hk
    refine ⟨c, hc, c⁻¹ * (m * ((MulAut.conj k * b ^ j) m)⁻¹), ?_, by group⟩
    have e : ψ (m * ((MulAut.conj k * b ^ j) m)⁻¹) = ψ (m * k * m⁻¹ * k⁻¹) := by
      rw [MulAut.mul_apply, hbjm, MulAut.conj_apply]
      simp only [map_mul, map_inv, map_pow, MonoidHom.mem_ker.1 hzmk, one_pow, mul_one]
      group
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, hcψ, inv_mul_cancel]
  refine ⟨m, fun a ha => ?_, fun hmv => hmove ?_⟩
  ·
    obtain ⟨c, hc, z, hz, he⟩ := hmem a ha
    rw [he]
    refine ⟨?_, fun a' ha' => by rw [map_mul, hclA a' ha' c hc, hfixZ a' ha' z hz]⟩
    have hcz : Commute c z := Subgroup.mem_center_iff.1 (hker hz) c
    rw [hcz.mul_pow, hcl3 c hc, hZ3 z hz, one_mul]
  ·
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmv
    have h1 : MulAut.conj (k₀ ^ j) = MulAut.conj (m * k₀ * m⁻¹) := by
      rw [map_zpow, hj, map_mul, map_mul, map_inv]
    have h3' : ψ k₀ ^ j = ψ m * ψ k₀ * (ψ m)⁻¹ := by
      rw [← map_zpow, hpsi _ _ h1, map_mul, map_mul, map_inv]
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ε.injective ?_⟩
    simp only [map_zpow, map_mul, map_inv, ε.apply_symm_apply]
    rw [h3', hm]

end CFSG.StandardType.KG87B
