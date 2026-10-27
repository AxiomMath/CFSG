module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
import CFSG.LocalAnalysis.WeakClosure81.SU3RankModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankInvert
import CFSG.LocalAnalysis.WeakClosure81.SU3RankTorusBound
import CFSG.LocalAnalysis.WeakClosure81.SU3RankTorusDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic

theorem orderOf_two_le_modCommRank_permSU_swap {n : ℕ} {F₀ : Type} [Field F₀] [CharP F₀ 2]
    {ℓ k : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hk : 1 ≤ k) {ν : rootsOfUnity (2 ^ n + 1) F₀}
    (hν : orderOf ν = ℓ ^ k) {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Finite F]
    (σ : ↥(StatedSU 3 (2 ^ n) F₀) →* LGL 2 F)
    (hinj : ∀ a b : rootsOfUnity (2 ^ n + 1) F₀, a ^ ℓ = 1 → b ^ ℓ = 1 →
      σ (diagSU n F₀ (a, b)) = 1 → a = 1 ∧ b = 1) :
    orderOf (2 : ZMod (ℓ ^ k)) ≤ modCommRank (σ (permSU n F₀ (Equiv.swap 0 1))) := by
  classical
  let R := rootsOfUnity (2 ^ n + 1) F₀
  let f : R × R →* LGL 2 F := σ.comp (diagSU n F₀)
  let μ : R := ν ^ (ℓ ^ (k - 1))
  let A : Subgroup (R × R) := (Subgroup.zpowers μ).prod (Subgroup.zpowers μ)
  let E : Subgroup (LGL 2 F) := A.map f
  let y : LGL 2 F := f (μ, μ⁻¹)
  let c : LGL 2 F := σ (permSU n F₀ (finRotate 3))
  let t : LGL 2 F := σ (permSU n F₀ (Equiv.swap 0 1))
  let d : ℕ := orderOf (2 : ZMod (ℓ ^ k))
  have hdiv : ℓ ^ k / ℓ ^ (k - 1) = ℓ := by
    rw [Nat.pow_div (show k - 1 ≤ k by omega) hℓ.pos, Nat.sub_sub_self hk, pow_one]
  have hμorder : orderOf μ = ℓ := by
    have h := orderOf_pow_of_dvd (x := ν) (n := ℓ ^ (k - 1)) (pow_ne_zero _ hℓ.ne_zero)
      (by rw [hν]; exact pow_dvd_pow ℓ (show k - 1 ≤ k by omega))
    rw [hν, hdiv] at h
    simpa [μ] using h
  have hμ_ne : μ ≠ 1 := by
    intro h
    have h1 : orderOf μ = 1 := orderOf_eq_one_iff.mpr h
    rw [hμorder] at h1
    exact (hℓ.one_lt.ne') h1
  have hpow_ℓ : ∀ a : R, a ∈ Subgroup.zpowers μ → a ^ ℓ = 1 := by
    intro a ha
    have hdvd : orderOf a ∣ orderOf μ := orderOf_dvd_of_mem_zpowers ha
    rw [hμorder] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hA_mem : ∀ x : R × R, x ∈ A ↔ x.1 ∈ Subgroup.zpowers μ ∧ x.2 ∈ Subgroup.zpowers μ := by
    intro x
    simp only [A, Subgroup.mem_prod]
  have hA_one : ∀ x : R × R, x ∈ A → f x = 1 → x = 1 := by
    intro x hx hfx
    have hx' := (hA_mem x).mp hx
    have h1 : x.1 ^ ℓ = 1 := hpow_ℓ x.1 hx'.1
    have h2 : x.2 ^ ℓ = 1 := hpow_ℓ x.2 hx'.2
    have hσ : σ (diagSU n F₀ (x.1, x.2)) = 1 := hfx
    have hcon := hinj x.1 x.2 h1 h2 hσ
    exact Prod.ext hcon.1 hcon.2
  have hA_inj : ∀ x ∈ A, ∀ w ∈ A, f x = f w → x = w := by
    intro x hx w hw hxw
    have hmem : x * w⁻¹ ∈ A := A.mul_mem hx (A.inv_mem hw)
    have h1 : f (x * w⁻¹) = 1 := by rw [map_mul, map_inv, hxw, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hA_one (x * w⁻¹) hmem h1)
  have hcardA : Nat.card A = ℓ ^ 2 := by
    change Nat.card ↥((Subgroup.zpowers μ).prod (Subgroup.zpowers μ)) = ℓ ^ 2
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv]
    rw [Nat.card_prod, Nat.card_zpowers, hμorder]
    ring
  let φ : ↥A → ↥E := fun x => ⟨f x, by
    change f x ∈ A.map f
    exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
  have hφ_inj : Function.Injective φ := by
    intro x w hxw
    exact Subtype.ext (hA_inj x x.2 w w.2 (congrArg Subtype.val hxw))
  have hφ_surj : Function.Surjective φ := by
    intro e
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp (show e.1 ∈ A.map f from e.2)
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hcardE : Nat.card E = ℓ ^ 2 := by
    have hbij : Nat.card ↥E = Nat.card ↥A :=
      (Nat.card_congr (Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩)).symm
    rw [hbij, hcardA]
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (show a ∈ A.map f from ha)
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (show b ∈ A.map f from hb)
    rw [← map_mul, ← map_mul, mul_comm]
  have hexpE : ∀ e ∈ E, e ^ ℓ = 1 := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (show e ∈ A.map f from he)
    rw [← map_pow]
    have hx' := (hA_mem x).mp hx
    have hxpow : x ^ ℓ = 1 := Prod.ext (hpow_ℓ x.1 hx'.1) (hpow_ℓ x.2 hx'.2)
    rw [hxpow, map_one]
  have hyE : y ∈ E := by
    have hmem : (μ, μ⁻¹) ∈ A := by
      rw [hA_mem]
      exact ⟨Subgroup.mem_zpowers μ, Subgroup.inv_mem _ (Subgroup.mem_zpowers μ)⟩
    change f (μ, μ⁻¹) ∈ A.map f
    exact Subgroup.mem_map.mpr ⟨(μ, μ⁻¹), hmem, rfl⟩
  have hy1 : y ≠ 1 := by
    intro hy
    have h1 : μ ^ ℓ = 1 := hpow_ℓ μ (Subgroup.mem_zpowers μ)
    have h2 : (μ⁻¹) ^ ℓ = 1 := hpow_ℓ μ⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers μ))
    have hσ : σ (diagSU n F₀ (μ, μ⁻¹)) = 1 := by
      change f (μ, μ⁻¹) = 1
      exact hy
    exact hμ_ne (hinj μ μ⁻¹ h1 h2 hσ).1
  have hc_conj : ∀ a b : R, c * f (a, b) * c⁻¹ = f ((a * b)⁻¹, a) := by
    intro a b
    have h := congrArg σ (permSU_finRotate_mul_diagSU_mul_inv (n := n) (F₀ := F₀) a b)
    simpa [c, f, map_mul, map_inv] using h
  have hc3 : c ^ 3 = 1 := by
    change (σ (permSU n F₀ (finRotate 3))) ^ 3 = 1
    rw [← map_pow]
    have hfr : (finRotate 3 : Equiv.Perm (Fin 3)) ^ 3 = 1 := by decide
    have h3 : (permSU n F₀ (finRotate 3)) ^ 3 = 1 := by rw [← map_pow, hfr, map_one]
    rw [h3, map_one]
  have hc3mul : c * (c * c) = 1 := by
    have h : c * c ^ 2 = 1 := by
      rw [← pow_succ' c 2]
      exact hc3
    simpa [pow_two] using h
  have hc_inv : c⁻¹ = c * c := inv_eq_of_mul_eq_one_right hc3mul
  have hc2'' : (c * c)⁻¹ = c := inv_eq_of_mul_eq_one_left hc3mul
  have hcE : ∀ e ∈ E, c * e * c⁻¹ ∈ E := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (show e ∈ A.map f from he)
    rw [hc_conj]
    refine Subgroup.mem_map.mpr ⟨((x.1 * x.2)⁻¹, x.1), ?_, rfl⟩
    rw [hA_mem]
    exact ⟨Subgroup.inv_mem (Subgroup.zpowers μ)
        (Subgroup.mul_mem (Subgroup.zpowers μ) ((hA_mem x).mp hx).1 ((hA_mem x).mp hx).2),
      ((hA_mem x).mp hx).1⟩
  have hcE' : ∀ e ∈ E, c⁻¹ * e * c ∈ E := by
    intro e he
    have h1 : c * e * c⁻¹ ∈ E := hcE e he
    have h2 : c * (c * e * c⁻¹) * c⁻¹ ∈ E := hcE _ h1
    have hstep : c⁻¹ * e * c = c * (c * e * c⁻¹) * c⁻¹ := by
      have hmid : c⁻¹ * e * c = (c * c) * e * (c * c)⁻¹ := by
        rw [hc_inv, hc2'']
      rw [hmid]
      group
    rwa [hstep]
  have hcy : c * y * c⁻¹ = f (1, μ) := by
    have h := hc_conj μ μ⁻¹
    simpa [y] using h
  have hc1 : c * f (1, μ) * c⁻¹ = f (μ⁻¹, 1) := by
    have h := hc_conj 1 μ
    simpa using h
  have hciy : c⁻¹ * y * c = f (μ⁻¹, 1) := by
    have hstep : c⁻¹ * y * c = c * (c * y * c⁻¹) * c⁻¹ := by
      have hmid : c⁻¹ * y * c = (c * c) * y * (c * c)⁻¹ := by
        rw [hc_inv, hc2'']
      rw [hmid]
      group
    rw [hstep, hcy, hc1]
  have hy_zpow : ∀ j : ℤ, y ^ j = f (μ ^ j, μ ^ (-j)) := by
    intro j
    change (f (μ, μ⁻¹)) ^ j = f (μ ^ j, μ ^ (-j))
    rw [← map_zpow]
    congr 1
    ext <;> simp [inv_zpow]
  have hz_zpow : ∀ j : ℤ, (f (μ⁻¹, 1)) ^ j = f (μ ^ (-j), 1) := by
    intro j
    rw [← map_zpow]
    congr 1
    ext <;> simp [inv_zpow]
  have hpair_inj : ∀ a b a' b' : R, a ∈ Subgroup.zpowers μ → b ∈ Subgroup.zpowers μ →
      a' ∈ Subgroup.zpowers μ → b' ∈ Subgroup.zpowers μ →
      f (a, b) = f (a', b') → (a, b) = (a', b') := by
    intro a b a' b' ha hb ha' hb' h
    exact hA_inj (a, b) (by rw [hA_mem]; exact ⟨ha, hb⟩) (a', b')
      (by rw [hA_mem]; exact ⟨ha', hb'⟩) h
  have hzmem : ∀ i : ℤ, μ ^ i ∈ Subgroup.zpowers μ := fun i => Subgroup.zpow_mem_zpowers μ i
  have h1 : Subgroup.zpowers (c * y * c⁻¹) ≠ Subgroup.zpowers y := by
    intro heq
    have hmem : f (1, μ) ∈ Subgroup.zpowers y := by
      rw [← hcy, ← heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpoweq : f (μ ^ j, μ ^ (-j)) = f (1, μ) := by
      rw [← hj]
      exact (hy_zpow j).symm
    have hpair := hpair_inj (μ ^ j) (μ ^ (-j)) 1 μ (hzmem j) (hzmem (-j))
      (Subgroup.one_mem _) (Subgroup.mem_zpowers μ) hpoweq
    have hfst : μ ^ j = 1 := congrArg Prod.fst hpair
    have hsnd : μ ^ (-j) = μ := congrArg Prod.snd hpair
    have hneg : μ ^ (-j) = 1 := by
      rw [zpow_neg, hfst, inv_one]
    exact hμ_ne (hsnd.symm.trans hneg)
  have h2 : Subgroup.zpowers (c⁻¹ * y * c) ≠ Subgroup.zpowers y := by
    intro heq
    have hmem : f (μ⁻¹, 1) ∈ Subgroup.zpowers y := by
      rw [← hciy, ← heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpoweq : f (μ ^ j, μ ^ (-j)) = f (μ⁻¹, 1) := by
      rw [← hj]
      exact (hy_zpow j).symm
    have hpair := hpair_inj (μ ^ j) (μ ^ (-j)) μ⁻¹ 1 (hzmem j) (hzmem (-j))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers μ)) (Subgroup.one_mem _) hpoweq
    have hfst : μ ^ j = μ⁻¹ := congrArg Prod.fst hpair
    have hsnd : μ ^ (-j) = 1 := congrArg Prod.snd hpair
    have hu : μ ^ j = 1 := by
      have h : (μ ^ j)⁻¹ = 1 := by rw [← zpow_neg]; exact hsnd
      exact inv_eq_one.mp h
    exact hμ_ne (inv_eq_one.mp (hfst ▸ hu))
  have h3 : Subgroup.zpowers (c * y * c⁻¹) ≠ Subgroup.zpowers (c⁻¹ * y * c) := by
    intro heq
    have hmem : f (1, μ) ∈ Subgroup.zpowers (f (μ⁻¹, 1)) := by
      have h0 : f (1, μ) ∈ Subgroup.zpowers (c * y * c⁻¹) := by
        rw [hcy]
        exact Subgroup.mem_zpowers _
      rw [heq] at h0
      rwa [hciy] at h0
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpoweq : f (μ ^ (-j), 1) = f (1, μ) := by
      rw [← hj]
      exact (hz_zpow j).symm
    have hpair := hpair_inj (μ ^ (-j)) 1 1 μ (hzmem (-j)) (Subgroup.one_mem _)
      (Subgroup.one_mem _) (Subgroup.mem_zpowers μ) hpoweq
    have hsnd : (1 : R) = μ := congrArg Prod.snd hpair
    exact hμ_ne hsnd.symm
  have hνℓ : ν ^ (ℓ ^ k) = 1 := by rw [← hν]; exact pow_orderOf_eq_one ν
  have hpow_i : ∀ i : ℤ, (ν ^ i) ^ (ℓ ^ (k - 1)) = μ ^ i := by
    intro i
    rw [← zpow_natCast, zpow_comm, zpow_natCast]
  have hd : ∀ B : Subgroup (LGL 2 F), B ≤ E → Nat.card B = ℓ →
      fixSub B ⊓ commSub E ≠ ⊥ →
      d ≤ Module.finrank (ZMod 2) ↥(fixSub B ⊓ commSub E) := by
    intro B hBE hB hne
    have hne' : ¬ E ≤ B := by
      intro hEB
      have heq : E = B := le_antisymm hEB hBE
      have hlt : Nat.card B < Nat.card E := by
        rw [hB, hcardE]
        nlinarith [hℓ.two_le]
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨e, heE, heB⟩ := Set.not_subset.mp hne'
    obtain ⟨x, hxA, hxe⟩ := Subgroup.mem_map.mp (show e ∈ A.map f from heE)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ((hA_mem x).mp hxA).1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((hA_mem x).mp hxA).2
    let τ : LGL 2 F := f (ν ^ i, ν ^ j)
    have hτ1 : τ ^ (ℓ ^ (k - 1)) = e := by
      change (f (ν ^ i, ν ^ j)) ^ (ℓ ^ (k - 1)) = e
      rw [← map_pow]
      have hp : (ν ^ i, ν ^ j) ^ (ℓ ^ (k - 1)) = (μ ^ i, μ ^ j) :=
        Prod.ext (hpow_i i) (hpow_i j)
      rw [hp, show (μ ^ i, μ ^ j) = x from Prod.ext hi hj, hxe]
    have hτ : τ ^ (ℓ ^ k) = 1 := by
      change (f (ν ^ i, ν ^ j)) ^ (ℓ ^ k) = 1
      rw [← map_pow]
      have hpow_k : ∀ i : ℤ, (ν ^ i) ^ (ℓ ^ k) = 1 := by
        intro i
        rw [← zpow_natCast, zpow_comm, zpow_natCast, hνℓ]
        simp
      have hp : (ν ^ i, ν ^ j) ^ (ℓ ^ k) = 1 := Prod.ext (hpow_k i) (hpow_k j)
      rw [hp, map_one]
    have hτE : ∀ e' ∈ E, τ * e' = e' * τ := by
      intro e' he'
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp (show e' ∈ A.map f from he')
      change f (ν ^ i, ν ^ j) * f w = f w * f (ν ^ i, ν ^ j)
      rw [← map_mul, ← map_mul, mul_comm]
    have hτE' : τ ^ (ℓ ^ (k - 1)) ∈ E := by rw [hτ1]; exact heE
    have hτB : τ ^ (ℓ ^ (k - 1)) ∉ B := by rw [hτ1]; exact heB
    have hdvd := orderOf_two_dvd_finrank_fixSub_inf_commSub hℓ hℓ2 hk hcardE hBE hB hτE hτ
      hτE' hτB
    haveI : Module.Finite (ZMod 2) ↥(fixSub B ⊓ commSub E) := Module.Finite.of_finite
    have hpos : 0 < Module.finrank (ZMod 2) ↥(fixSub B ⊓ commSub E) := by
      have hle := Submodule.one_le_finrank_iff.mpr hne
      omega
    exact Nat.le_of_dvd hpos hdvd
  have hbound := two_mul_le_finrank_range_sub_of_conj hℓ hℓ2 hcommE hexpE hcardE hyE hy1
    hcE hcE' h1 h2 h3 hd
  have ht : t * t = 1 := by
    change σ (permSU n F₀ (Equiv.swap 0 1)) * σ (permSU n F₀ (Equiv.swap 0 1)) = 1
    rw [← map_mul, ← map_mul, Equiv.swap_mul_self, map_one, map_one]
  have hty : t * y * t = y⁻¹ := by
    have hσ : t * y * t⁻¹ = f (μ⁻¹, μ) := by
      have h := congrArg σ (permSU_swap_mul_diagSU_mul_inv (n := n) (F₀ := F₀) μ μ⁻¹)
      simpa [t, y, f, map_mul, map_inv] using h
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hyinv : f (μ⁻¹, μ) = y⁻¹ := by
      have hp : (μ⁻¹, μ) = (μ, μ⁻¹)⁻¹ := by ext <;> simp
      rw [hp, map_inv]
    rw [htinv] at hσ
    rw [hσ, hyinv]
  have hyodd : Odd (orderOf y) := by
    have hyd : orderOf y ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr (hexpE y hyE)
    rcases (Nat.dvd_prime hℓ).mp hyd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hℓ.odd_of_ne_two hℓ2
  have hfin : Module.finrank (ZMod 2) (LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id))
      ≤ 2 * modCommRank t := finrank_range_sub_le_two_mul_modCommRank ht hty hyodd
  have : d ≤ modCommRank t := by omega
  simpa [d, t] using this

end CFSG.LocalAnalysis.WeakClosure81

end
