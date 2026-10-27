module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsA

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def ggKGEb_zetaUnit {K : Type} [Field K] {p : ℕ} (ζ : K)
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) : Kˣ :=
  Units.mk0 ζ (hζ.ne_zero hp.ne_zero)

private lemma ggKGEb_zetaUnit_zpow_eq_one_iff {K : Type} [Field K] {p : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (n : ℤ) :
    (ggKGEb_zetaUnit ζ hζ hp) ^ n = 1 ↔ (p : ℤ) ∣ n := by
  rw [← Units.val_eq_one, Units.val_zpow_eq_zpow_val]
  change (ζ ^ n : K) = 1 ↔ (p : ℤ) ∣ n
  exact hζ.zpow_eq_one_iff_dvd n

private lemma ggKGEb_rootChar_zetaUnit {τ : Tag} {K : Type} [Field K]
    (ζu : Kˣ) (e v : Fin τ.rank → ℤ) :
    rootChar (fun i => ζu ^ e i) v = ζu ^ (∑ i, e i * v i) := by
  rw [rootChar]
  simp_rw [← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]

private lemma ggKGEb_rootChar_zetaVec_eq_one_iff {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (e v : Fin τ.rank → ℤ) :
    rootChar (fun i => ggKGEb_zetaUnit ζ hζ hp ^ e i) v = 1 ↔
      (p : ℤ) ∣ ∑ i, e i * v i := by
  rw [ggKGEb_rootChar_zetaUnit, ggKGEb_zetaUnit_zpow_eq_one_iff]

private lemma ggKGEb_zetaVec_pow_eq_one {τ : Tag} {K : Type} [Field K] {p : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (e : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    (ggKGEb_zetaUnit ζ hζ hp ^ e i) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, ggKGEb_zetaUnit_zpow_eq_one_iff]
  exact ⟨e i, by ring⟩

private lemma ggKGEb_sum_single_mul {τ : Tag} (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    (∑ k, (Pi.single j 1 : Fin τ.rank → ℤ) k * v k) = v j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma ggKGEb_sum_two_single_mul {τ : Tag} (i i' : Fin τ.rank) (a b : ℤ)
    (v : Fin τ.rank → ℤ) :
    (∑ k, ((a • (Pi.single i 1 : Fin τ.rank → ℤ) + b • (Pi.single i' 1 : Fin τ.rank → ℤ)) k)
      * v k) = a * v i + b * v i' := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  have h1 : (∑ k, (a * (Pi.single i 1 : Fin τ.rank → ℤ) k) * v k)
      = a * (∑ k, (Pi.single i 1 : Fin τ.rank → ℤ) k * v k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : (∑ k, (b * (Pi.single i' 1 : Fin τ.rank → ℤ) k) * v k)
      = b * (∑ k, (Pi.single i' 1 : Fin τ.rank → ℤ) k * v k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, ggKGEb_sum_single_mul i v, ggKGEb_sum_single_mul i' v]

private lemma ggKGEb_smul_modEq {τ : Tag} {K : Type} [Field K] {p : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Kˣ}
    (hall : ∀ b : Fin τ.rank → Kˣ, (∀ j, b j ^ p = 1) → ∃ i, a i = b)
    {w : WeylGroup τ} (hw : w ∈ familyStabilizer a) (v : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    (p : ℤ) ∣ (w • v) j - v j := by
  let e : Fin τ.rank → ℤ := Pi.single j 1
  let b : Fin τ.rank → Kˣ := fun i => ggKGEb_zetaUnit ζ hζ hp ^ e i
  have hbpow : ∀ i, b i ^ p = 1 := fun i => ggKGEb_zetaVec_pow_eq_one hζ hp e i
  obtain ⟨i, hi⟩ := hall b hbpow
  have hstab : rootChar (a i) (w • v) = rootChar (a i) v := hw i v
  have hb : rootChar b (w • v) = rootChar b v := by rwa [hi] at hstab
  have hL : rootChar b (w • v) = ggKGEb_zetaUnit ζ hζ hp ^ (∑ i, e i * (w • v) i) :=
    ggKGEb_rootChar_zetaUnit (ggKGEb_zetaUnit ζ hζ hp) e (w • v)
  have hR : rootChar b v = ggKGEb_zetaUnit ζ hζ hp ^ (∑ i, e i * v i) :=
    ggKGEb_rootChar_zetaUnit (ggKGEb_zetaUnit ζ hζ hp) e v
  rw [hL, hR, ggKGEb_sum_single_mul j (w • v), ggKGEb_sum_single_mul j v] at hb
  have h2 : ggKGEb_zetaUnit ζ hζ hp ^ ((w • v) j - v j) = 1 := by
    rw [zpow_sub, hb, mul_inv_cancel]
  exact (ggKGEb_zetaUnit_zpow_eq_one_iff hζ hp _).1 h2

private lemma ggKGEb_isRoot_smul {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v)
    (w : WeylGroup τ) : IsRoot τ (w • v) := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => rwa [one_smul]
  | mul_simple_left w i ih => rw [mul_smul, simple_smul]; exact IsRoot.reflect i ih

private lemma ggKGEb_reflect_neg {τ : Tag} (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i (-v) = -reflect τ i v := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [reflect, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      mul_one, mul_neg, Finset.sum_neg_distrib]
    ring
  · simp [reflect, Pi.single_apply, hj, Ne.symm hj]

private lemma ggKGEb_isRoot_neg {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    IsRoot τ (-v) := by
  induction hv using IsRoot.rec with
  | basis j =>
    have h : (-Pi.single j 1 : Fin τ.rank → ℤ) = reflect τ j (Pi.single j 1) := by
      rw [reflect_single_self]
    rw [h]
    exact IsRoot.reflect j (.basis j)
  | reflect i hw ih =>
    have h := IsRoot.reflect i ih
    rwa [ggKGEb_reflect_neg] at h

theorem ggKGExc_familyKernel_allPTorsion {τ : Tag} {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type} (a : ι → Fin τ.rank → kˣ)
    (hall : ∀ b : Fin τ.rank → kˣ, (∀ j, b j ^ p = 1) → ∃ i, a i = b) :
    familyKernel a = ∅ := by
  ext β
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hβroot, hβker⟩
  apply ggKGExc_root_not_dvd (Nat.le_of_succ_le hp3) hβroot
  intro j
  let e : Fin τ.rank → ℤ := Pi.single j 1
  let b : Fin τ.rank → kˣ := fun i => ggKGEb_zetaUnit ζ hζ hp ^ e i
  have hbpow : ∀ i, b i ^ p = 1 := fun i => ggKGEb_zetaVec_pow_eq_one hζ hp e i
  obtain ⟨i, hi⟩ := hall b hbpow
  have h1 : rootChar b β = 1 := by
    have := hβker i
    rwa [hi] at this
  have h2 := (ggKGEb_rootChar_zetaVec_eq_one_iff hζ hp e β).1 h1
  rwa [ggKGEb_sum_single_mul j β] at h2

theorem ggKGExc_familyKernel_killRoot {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type} (a : ι → Fin τ.rank → kˣ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hker : ∀ i, rootChar (a i) γ = 1)
    (hall : ∀ b : Fin τ.rank → kˣ, (∀ j, b j ^ p = 1) → rootChar b γ = 1 → ∃ i, a i = b) :
    familyKernel a = {γ, -γ} := by
  apply Set.Subset.antisymm
  · intro β hβ
    obtain ⟨hβroot, hβker⟩ := hβ
    have hnot : ¬ ∀ i, (p : ℤ) ∣ γ i := ggKGExc_root_not_dvd hp.two_le hγ
    push Not at hnot
    obtain ⟨j₀, hj₀⟩ := hnot
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact p.Prime := ⟨hp⟩
    let cbar : ZMod p := (β j₀ : ZMod p) * (γ j₀ : ZMod p)⁻¹
    let c : ℤ := (cbar.val : ℤ)
    have hγ₀ : (γ j₀ : ZMod p) ≠ 0 := by
      intro h
      exact hj₀ ((ZMod.intCast_zmod_eq_zero_iff_dvd (γ j₀) p).1 h)
    have hc : (c : ZMod p) = cbar := by
      have h := ZMod.natCast_zmod_val cbar
      simpa [c] using h
    have key : ∀ e : Fin τ.rank → ℤ, (p : ℤ) ∣ ∑ k, e k * γ k →
        (p : ℤ) ∣ ∑ k, e k * β k := by
      intro e he
      let b : Fin τ.rank → kˣ := fun i => ggKGEb_zetaUnit ζ hζ hp ^ e i
      have hbpow : ∀ i, b i ^ p = 1 := fun i => ggKGEb_zetaVec_pow_eq_one hζ hp e i
      have hbγ : rootChar b γ = 1 := (ggKGEb_rootChar_zetaVec_eq_one_iff hζ hp e γ).2 he
      obtain ⟨i, hi⟩ := hall b hbpow hbγ
      have h1 : rootChar b β = 1 := by
        have := hβker i
        rwa [hi] at this
      exact (ggKGEb_rootChar_zetaVec_eq_one_iff hζ hp e β).1 h1
    have hmod : ∀ j, (p : ℤ) ∣ β j - c * γ j := by
      intro j
      by_cases hjj : j = j₀
      · rw [hjj]
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hc]
        change (β j₀ : ZMod p) - (β j₀ : ZMod p) * (γ j₀ : ZMod p)⁻¹ * (γ j₀ : ZMod p) = 0
        rw [mul_assoc, inv_mul_cancel₀ hγ₀, mul_one, sub_self]
      · let e : Fin τ.rank → ℤ := γ j • (Pi.single j₀ 1 : Fin τ.rank → ℤ) +
            (-γ j₀) • (Pi.single j 1 : Fin τ.rank → ℤ)
        have he : (p : ℤ) ∣ ∑ k, e k * γ k := by
          have hsum : (∑ k, e k * γ k) = γ j * γ j₀ + (-γ j₀) * γ j :=
            ggKGEb_sum_two_single_mul j₀ j (γ j) (-γ j₀) γ
          rw [hsum]
          have hzero : γ j * γ j₀ + (-γ j₀) * γ j = 0 := by ring
          rw [hzero]
          exact dvd_zero _
        have hβe : (p : ℤ) ∣ ∑ k, e k * β k := key e he
        have hsumβ : (∑ k, e k * β k) = γ j * β j₀ + (-γ j₀) * β j :=
          ggKGEb_sum_two_single_mul j₀ j (γ j) (-γ j₀) β
        rw [hsumβ] at hβe
        have hrel : (γ j : ZMod p) * (β j₀ : ZMod p) = (γ j₀ : ZMod p) * (β j : ZMod p) := by
          have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ j * β j₀ + (-γ j₀) * β j) p).2 hβe
          push_cast at hcast
          linear_combination hcast
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hc]
        have hβj : (β j : ZMod p) =
            (β j₀ : ZMod p) * (γ j₀ : ZMod p)⁻¹ * (γ j : ZMod p) := by
          have h := congrArg (fun x => (γ j₀ : ZMod p)⁻¹ * x) hrel
          have hR : (γ j₀ : ZMod p)⁻¹ * ((γ j₀ : ZMod p) * (β j : ZMod p)) =
              (β j : ZMod p) := by
            rw [← mul_assoc, inv_mul_cancel₀ hγ₀, one_mul]
          rw [hR] at h
          rw [← h]
          ring
        rw [hβj, sub_self]
    have hmem : β = γ ∨ β = -γ := by
      rcases ggKGExc_root_eq_of_modEq hτ hp hp3 hβroot hγ hmod with h | h
      · exact Or.inl h
      · exact Or.inr h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro β hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl
    · exact ⟨hγ, hker⟩
    · refine ⟨ggKGEb_isRoot_neg hγ, fun i => ?_⟩
      rw [← neg_one_smul (R := ℤ) γ, rootChar_zsmul, hker i]
      simp

theorem ggKGExc_familyStabilizer_allPTorsion {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type} (a : ι → Fin τ.rank → kˣ)
    (hall : ∀ b : Fin τ.rank → kˣ, (∀ j, b j ^ p = 1) → ∃ i, a i = b) :
    familyStabilizer a = {1} := by
  ext w
  constructor
  · intro hw
    have hfix : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single i 1 := by
      intro i
      have hmod : ∀ j, (p : ℤ) ∣
          (w • (Pi.single i 1 : Fin τ.rank → ℤ)) j - (Pi.single i 1 : Fin τ.rank → ℤ) j :=
        fun j => ggKGEb_smul_modEq hζ hp hall hw (Pi.single i 1) j
      have hroot : IsRoot τ (w • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
        ggKGEb_isRoot_smul (IsRoot.basis i) w
      rcases ggKGExc_root_eq_of_modEq hτ hp hp3 hroot (IsRoot.basis i) (c := 1)
          (fun j => by simpa using hmod j) with h | h
      · exact h
      · exfalso
        have h2 := hmod i
        rw [h] at h2
        simp only [Pi.neg_apply, Pi.single_eq_same] at h2
        have h3 : (p : ℤ) ∣ 2 := by
          have h2' : (p : ℤ) ∣ -2 := by simpa using h2
          exact Int.dvd_neg.mp h2'
        have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h3
        omega
    exact Set.mem_singleton_iff.2 (ext_single fun i => by rw [hfix i, one_smul])
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    intro i v
    rw [one_smul]

end CFSG.StandardType

