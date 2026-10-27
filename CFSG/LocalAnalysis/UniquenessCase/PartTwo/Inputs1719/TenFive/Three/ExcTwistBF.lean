module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcRootPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistRoot
import CFSG.Mathlib.Algebra.MapAdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

theorem isExtraGood_of_comm_heis_triples {K T : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) [Group T] {xa₁ xb₁ xa₂ xb₂ z : K → T}
    (hxa₁ : ∀ s t, xa₁ (s + t) = xa₁ s * xa₁ t) (hxb₁ : ∀ s t, xb₁ (s + t) = xb₁ s * xb₁ t)
    (hxa₂ : ∀ s t, xa₂ (s + t) = xa₂ s * xa₂ t) (hxb₂ : ∀ s t, xb₂ (s + t) = xb₂ s * xb₂ t)
    (hz : ∀ s t, z (s + t) = z s * z t) (hzi : Function.Injective z)
    (hab₁ : ∀ s t, ⁅xa₁ s, xb₁ t⁆ = z (s * t)) (hab₂ : ∀ s t, ⁅xa₂ s, xb₂ t⁆ = z (s * t))
    (hza₁ : ∀ s t, Commute (z s) (xa₁ t)) (hzb₁ : ∀ s t, Commute (z s) (xb₁ t))
    (hza₂ : ∀ s t, Commute (z s) (xa₂ t)) (hzb₂ : ∀ s t, Commute (z s) (xb₂ t))
    (haa : ∀ s t, Commute (xa₁ s) (xa₂ t)) (hab : ∀ s t, Commute (xa₁ s) (xb₂ t))
    (hba : ∀ s t, Commute (xb₁ s) (xa₂ t)) (hbb : ∀ s t, Commute (xb₁ s) (xb₂ t)) (s : K) :
    IsExtraGood (xa₁ s) := by
  obtain ⟨ι₁, hι₁, ha₁, hb₁, hc₁⟩ := exists_heis_of_comm hxa₁ hxb₁ hz hzi hab₁ hza₁ hzb₁
  obtain ⟨ι₂, hι₂, ha₂, hb₂, hc₂⟩ := exists_heis_of_comm hxa₂ hxb₂ hz hzi hab₂ hza₂ hzb₂
  have hcen : ∀ c : K, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩ := fun c => by rw [hc₁, hc₂]
  have hcomm : ∀ a b : Heis K, Commute (ι₁ a) (ι₂ b) :=
    commute_heis_of_axes hcen
      (fun s t => by rw [ha₁, ha₂]; exact haa s t)
      (fun s t => by rw [ha₁, hb₂]; exact hab s t)
      (fun s t => by rw [hb₁, ha₂]; exact hba s t)
      (fun s t => by rw [hb₁, hb₂]; exact hbb s t)
  have h := isExtraGood_of_heis_pair hK hι₁ hι₂ hcomm hcen (⟨s, 0, 0⟩ : Heis K)
  rwa [ha₁ s] at h

private lemma sign_cube {k : Type*} [Field k] {s : k} (h : s * s = 1) : s ^ 3 = s := by
  have h2 : s ^ 2 = 1 := by rwa [sq]
  rw [pow_succ, h2, one_mul]

private lemma sign_ne_zero {k : Type*} [Field k] {s : k} (h : s * s = 1) : s ≠ 0 := by
  rintro rfl
  rw [zero_mul] at h
  exact zero_ne_one h

private lemma sign_mul_cancel {k : Type*} [Field k] {sa sa' lam i : k}
    (hsa : sa * sa = 1) (hsa' : sa' * sa' = 1) :
    sa' * (sa * (lam * (sa * sa')) * i) = lam * i := by
  have hκ : sa * sa' * (sa * sa') = 1 := by
    calc sa * sa' * (sa * sa') = sa * sa * (sa' * sa') := by ring
      _ = 1 := by rw [hsa, hsa', mul_one]
  calc sa' * (sa * (lam * (sa * sa')) * i)
      = sa' * sa * (sa * sa') * lam * i := by ring
    _ = sa * sa' * (sa * sa') * lam * i := by rw [mul_comm sa' sa]
    _ = lam * i := by rw [hκ, one_mul]

private theorem commutator_mul_mul_of_comm {G : Type*} [Group G] {a a' b b' : G}
    (hab' : Commute a b') (ha'b : Commute a' b)
    (hza : Commute ⁅a', b'⁆ a) (hzb : Commute ⁅a', b'⁆ b) :
    ⁅a * a', b * b'⁆ = ⁅a', b'⁆ * ⁅a, b⁆ := by
  have hz : a' * b' * a'⁻¹ = ⁅a', b'⁆ * b' := by
    rw [commutatorElement_def]; group
  have hzab : Commute ⁅a', b'⁆ (a * b) := hza.mul_right hzb
  have hb'a : Commute b' a⁻¹ := hab'.symm.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc a * a' * (b * b') * (a * a')⁻¹ * (b * b')⁻¹
      = a * (a' * b) * b' * a'⁻¹ * a⁻¹ * b'⁻¹ * b⁻¹ := by group
    _ = a * (b * a') * b' * a'⁻¹ * a⁻¹ * b'⁻¹ * b⁻¹ := by rw [ha'b.eq]
    _ = a * b * (a' * b' * a'⁻¹) * a⁻¹ * b'⁻¹ * b⁻¹ := by group
    _ = a * b * (⁅a', b'⁆ * b') * a⁻¹ * b'⁻¹ * b⁻¹ := by rw [hz]
    _ = (a * b) * ⁅a', b'⁆ * b' * a⁻¹ * b'⁻¹ * b⁻¹ := by group
    _ = ⁅a', b'⁆ * ((a * b) * (b' * a⁻¹)) * b'⁻¹ * b⁻¹ := by
        rw [← hzab.eq]; group
    _ = ⁅a', b'⁆ * ((a * b) * (a⁻¹ * b')) * b'⁻¹ * b⁻¹ := by rw [hb'a.eq]
    _ = ⁅a', b'⁆ * (a * b * a⁻¹ * b⁻¹) := by group
    _ = ⁅a', b'⁆ * ⁅a, b⁆ := by simp only [commutatorElement_def]

private theorem commutator_mul_mul_of_cross {G : Type*} [Group G] {a a' b b' : G}
    (haa' : Commute a a') (hab : Commute a b) (ha'b' : Commute a' b')
    (hza : Commute ⁅a, b'⁆ a') (hzb : Commute ⁅a, b'⁆ b) :
    ⁅a * a', b * b'⁆ = ⁅a, b'⁆ * ⁅a', b⁆ := by
  have h := commutator_mul_mul_of_comm (a := a') (a' := a) (b := b) (b' := b')
    (by exact ha'b') (by exact hab) hza hzb
  rw [← haa'.eq] at h
  exact h

private lemma orbit_pair_fixed {G k : Type*} [Group G] [Field k] {S : G →* G}
    {A A' : k → G} {sa sa' lam : k}
    (hsa : sa * sa = 1) (hsa' : sa' * sa' = 1)
    (hSA : ∀ c, S (A c) = A' (sa * c ^ 3))
    (hSA' : ∀ c, S (A' c) = A (sa' * c ^ 3))
    (hAA' : ∀ c d, Commute (A c) (A' d))
    (hlam : (lam ^ 3) ^ 3 = lam * (sa * sa')) {i : k} (hi : i ^ 3 = i) :
    S (A (lam * i) * A' (sa * lam ^ 3 * i)) =
      A (lam * i) * A' (sa * lam ^ 3 * i) := by
  have hcq : (lam * i) ^ 3 = lam ^ 3 * i := by rw [mul_pow, hi]
  have hdq : (sa * lam ^ 3 * i) ^ 3 = sa * (lam * (sa * sa')) * i := by
    rw [mul_pow, mul_pow, sign_cube hsa, hlam, hi]
  rw [map_mul, hSA, hSA', hcq, hdq]
  have h1 : sa * (lam ^ 3 * i) = sa * lam ^ 3 * i := by ring
  rw [h1, sign_mul_cancel hsa hsa']
  exact (hAA' (lam * i) (sa * lam ^ 3 * i)).eq.symm

private lemma fixed_one {G k : Type*} [Group G] [Field k] {S : G →* G}
    {A : k → G} {sa lam : k} (hsa : sa * sa = 1)
    (hSA : ∀ c, S (A c) = A (sa * c ^ 3))
    (hlam : lam ^ 3 = lam * sa) {i : k} (hi : i ^ 3 = i) :
    S (A (lam * i)) = A (lam * i) := by
  have hcq : (lam * i) ^ 3 = lam ^ 3 * i := by rw [mul_pow, hi]
  rw [hSA, hcq, hlam]
  congr 1
  calc sa * (lam * sa * i) = sa * sa * lam * i := by ring
    _ = lam * i := by rw [hsa, one_mul]

private lemma orbit_pair_add {G k K : Type*} [Group G] [Field k] [Field K]
    (ι : K →+* k) {A A' : k → G}
    (hA : ∀ c d, A (c + d) = A c * A d) (hA' : ∀ c d, A' (c + d) = A' c * A' d)
    (hAA' : ∀ c d, Commute (A c) (A' d)) (sa : k) (c : k) (s t : K) :
    A (c * ι (s + t)) * A' (sa * c ^ 3 * ι (s + t)) =
      (A (c * ι s) * A' (sa * c ^ 3 * ι s)) *
        (A (c * ι t) * A' (sa * c ^ 3 * ι t)) := by
  have h_add : c * ι (s + t) = c * ι s + c * ι t := by rw [map_add, mul_add]
  have h_add' : sa * c ^ 3 * ι (s + t) = sa * c ^ 3 * ι s + sa * c ^ 3 * ι t := by
    rw [map_add]; ring
  rw [h_add, h_add', hA, hA']
  rw [show A (c * ι s) * A (c * ι t) *
        (A' (sa * c ^ 3 * ι s) * A' (sa * c ^ 3 * ι t)) =
      A (c * ι s) * (A (c * ι t) * A' (sa * c ^ 3 * ι s)) *
        A' (sa * c ^ 3 * ι t) by group]
  rw [(hAA' (c * ι t) (sa * c ^ 3 * ι s)).eq]
  group

private lemma orbit_pair_commutator {G k K : Type*} [Group G] [Field k] [Field K]
    (ι : K →+* k) {A A' B B' C C' : k → G} {lam mu sa sb : k} (s t : K)
    (hAA' : ∀ c d, Commute (A c) (A' d))
    (hAB : ∀ c d, Commute (A c) (B d))
    (hA'B' : ∀ c d, Commute (A' c) (B' d))
    (hAB' : ∀ c d, ⁅A c, B' d⁆ = C (c * d))
    (hA'B : ∀ c d, ⁅A' c, B d⁆ = C' (c * d))
    (hCA' : ∀ c d, Commute (C c) (A' d)) (hCB : ∀ c d, Commute (C c) (B d)) :
    ⁅A (lam * ι s) * A' (sa * lam ^ 3 * ι s),
        B (mu * ι t) * B' (sb * mu ^ 3 * ι t)⁆ =
      C ((lam * ι s) * (sb * mu ^ 3 * ι t)) *
        C' ((sa * lam ^ 3 * ι s) * (mu * ι t)) := by
  have hza : Commute ⁅A (lam * ι s), B' (sb * mu ^ 3 * ι t)⁆
      (A' (sa * lam ^ 3 * ι s)) := by
    rw [hAB']
    exact hCA' _ _
  have hzb : Commute ⁅A (lam * ι s), B' (sb * mu ^ 3 * ι t)⁆ (B (mu * ι t)) := by
    rw [hAB']
    exact hCB _ _
  have h := commutator_mul_mul_of_cross (a := A (lam * ι s))
    (a' := A' (sa * lam ^ 3 * ι s)) (b := B (mu * ι t))
    (b' := B' (sb * mu ^ 3 * ι t)) (hAA' _ _) (hAB _ _) (hA'B' _ _) hza hzb
  rw [h, hAB', hA'B]

private lemma two_ne_zero_of_charP_three {k : Type*} [Field k] [CharP k 3] : (2 : k) ≠ 0 := by
  intro h
  have hdvd : 3 ∣ 2 := (CharP.cast_eq_zero_iff k 3 2).mp h
  norm_num at hdvd

private lemma prod_ne_zero_six {k : Type*} [Field k] {a b c d e f : k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    a * b * c * d * e * f ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd) he) hf

private lemma exists_orbit_scalars {k : Type*} [Field k] [IsAlgClosed k] [CharP k 3]
    {sδ sθδ sε sθε N₁ N₂ : k} (hsδ : sδ * sδ = 1) (hsθδ : sθδ * sθδ = 1)
    (hsε : sε * sε = 1) (hsθε : sθε * sθε = 1) (hN₂ : N₂ ≠ 0) :
    ∃ c₀ d₀ : k, c₀ ≠ 0 ∧ (c₀ ^ 3) ^ 3 = c₀ * (sδ * sθδ) ∧
      (d₀ ^ 3) ^ 3 = d₀ * (sε * sθε) ∧
      N₁ * sε * c₀ * d₀ ^ 3 + N₂ * sδ * c₀ ^ 3 * d₀ ≠ 0 := by
  classical
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (sδ * sθδ) (n := 8) (by norm_num)
  obtain ⟨d₁, hd₁⟩ := IsAlgClosed.exists_pow_nat_eq (sε * sθε) (n := 8) (by norm_num)
  have hc₀_ne : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 8 ≠ 0)] at hc₀
    exact (mul_ne_zero (sign_ne_zero hsδ) (sign_ne_zero hsθδ)) hc₀.symm
  have hd₁_ne : d₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 8 ≠ 0)] at hd₁
    exact (mul_ne_zero (sign_ne_zero hsε) (sign_ne_zero hsθε)) hd₁.symm
  have hc₀9 : c₀ ^ 9 = c₀ * (sδ * sθδ) := by
    rw [show 9 = 8 + 1 from rfl, pow_succ, hc₀]
    ring
  have hd₁9 : d₁ ^ 9 = d₁ * (sε * sθε) := by
    rw [show 9 = 8 + 1 from rfl, pow_succ, hd₁]
    ring
  have hc₀9' : (c₀ ^ 3) ^ 3 = c₀ * (sδ * sθδ) := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, hc₀9]
  have hd₁9' : (d₁ ^ 3) ^ 3 = d₁ * (sε * sθε) := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, hd₁9]
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) (n := 2) (by norm_num)
  have hi_ne : i ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 2 ≠ 0)] at hi
    exact neg_ne_zero.mpr one_ne_zero hi.symm
  let hfun : k → k := fun d => N₁ * sε * c₀ * d ^ 3 + N₂ * sδ * c₀ ^ 3 * d
  let d₀ : k := if hfun d₁ = 0 then i * d₁ else d₁
  have hi4 : i ^ 4 = 1 := by
    calc i ^ 4 = (i ^ 2) ^ 2 := by ring
      _ = (-1 : k) ^ 2 := by rw [hi]
      _ = 1 := by norm_num
  have hi8 : i ^ 8 = 1 := by
    calc i ^ 8 = (i ^ 4) ^ 2 := by ring
      _ = 1 := by rw [hi4]; norm_num
  have hd₀8 : d₀ ^ 8 = sε * sθε := by
    by_cases h : hfun d₁ = 0
    · simp only [d₀, if_pos h]
      rw [show (i * d₁) ^ 8 = i ^ 8 * d₁ ^ 8 by rw [mul_pow]]
      rw [hi8, one_mul, hd₁]
    · simp only [d₀, if_neg h]
      exact hd₁
  have hd₀_ne : d₀ ≠ 0 := by
    by_cases h : hfun d₁ = 0
    · simp only [d₀, if_pos h]
      exact mul_ne_zero hi_ne hd₁_ne
    · simp only [d₀, if_neg h]
      exact hd₁_ne
  have hh₀ : hfun d₀ ≠ 0 := by
    by_cases h : hfun d₁ = 0
    · simp only [d₀, if_pos h]
      have hzero : N₁ * sε * c₀ * d₁ ^ 3 + N₂ * sδ * c₀ ^ 3 * d₁ = 0 := by
        simpa only [hfun] using h
      have hcalc : hfun (i * d₁) = 2 * i * N₂ * sδ * c₀ ^ 3 * d₁ := by
        have hi3 : i ^ 3 = -i := by
          calc i ^ 3 = i ^ 2 * i := by rw [pow_succ]
            _ = (-1) * i := by rw [hi]
            _ = -i := by ring
        have hcube : (i * d₁) ^ 3 = - (i * d₁ ^ 3) := by
          rw [mul_pow, hi3]
          ring
        simp only [hfun]
        rw [hcube]
        linear_combination (-i) * hzero
      rw [hcalc]
      exact prod_ne_zero_six two_ne_zero_of_charP_three hi_ne hN₂ (sign_ne_zero hsδ)
        (pow_ne_zero 3 hc₀_ne) hd₁_ne
    · simp only [d₀, if_neg h]
      exact h
  have hd₀9' : (d₀ ^ 3) ^ 3 = d₀ * (sε * sθε) := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, show d₀ ^ 9 = d₀ * (sε * sθε) from by
      rw [show 9 = 8 + 1 from rfl, pow_succ, hd₀8]; ring]
  exact ⟨c₀, d₀, hc₀_ne, hc₀9', hd₀9', hh₀⟩

private lemma fixed_sq_of_fixed_Z {G k : Type*} [Group G] [Field k]
    {S : G →* G} {Z : k → G} {sα : k} (hsα : sα * sα = 1)
    (hSZ : ∀ c, S (Z c) = Z (sα * c ^ 3)) (hZi : Function.Injective Z)
    {ζ : k} (hfix : S (Z ζ) = Z ζ) (hζ : ζ ≠ 0) : ζ ^ 2 = sα := by
  have h := hSZ ζ
  rw [hfix] at h
  have hζ3 : sα * ζ ^ 3 = ζ := hZi h.symm
  have hζ2 : sα * ζ ^ 2 = 1 := by
    apply mul_right_cancel₀ hζ
    calc sα * ζ ^ 2 * ζ = sα * ζ ^ 3 := by ring
      _ = ζ := hζ3
      _ = 1 * ζ := by rw [one_mul]
  have h1 : sα * (sα * ζ ^ 2) = ζ ^ 2 := by rw [← mul_assoc, hsα, one_mul]
  calc ζ ^ 2 = sα * (sα * ζ ^ 2) := h1.symm
    _ = sα * 1 := by rw [hζ2]
    _ = sα := by rw [mul_one]

private lemma isExtraGood_of_comm_heis_triples_mem {K G : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 3) [Group G] (T : Subgroup G) {xa₁ xb₁ xa₂ xb₂ z : K → G}
    (hmem : ∀ t, xa₁ t ∈ T ∧ xb₁ t ∈ T ∧ xa₂ t ∈ T ∧ xb₂ t ∈ T ∧ z t ∈ T)
    (hxa₁ : ∀ s t, xa₁ (s + t) = xa₁ s * xa₁ t) (hxb₁ : ∀ s t, xb₁ (s + t) = xb₁ s * xb₁ t)
    (hxa₂ : ∀ s t, xa₂ (s + t) = xa₂ s * xa₂ t) (hxb₂ : ∀ s t, xb₂ (s + t) = xb₂ s * xb₂ t)
    (hz : ∀ s t, z (s + t) = z s * z t) (hzi : Function.Injective z)
    (hab₁ : ∀ s t, ⁅xa₁ s, xb₁ t⁆ = z (s * t)) (hab₂ : ∀ s t, ⁅xa₂ s, xb₂ t⁆ = z (s * t))
    (hza₁ : ∀ s t, Commute (z s) (xa₁ t)) (hzb₁ : ∀ s t, Commute (z s) (xb₁ t))
    (hza₂ : ∀ s t, Commute (z s) (xa₂ t)) (hzb₂ : ∀ s t, Commute (z s) (xb₂ t))
    (haa : ∀ s t, Commute (xa₁ s) (xa₂ t)) (hab : ∀ s t, Commute (xa₁ s) (xb₂ t))
    (hba : ∀ s t, Commute (xb₁ s) (xa₂ t)) (hbb : ∀ s t, Commute (xb₁ s) (xb₂ t)) (s : K) :
    IsExtraGood (⟨xa₁ s, (hmem s).1⟩ : T) := by
  let xa₁' : K → T := fun t => ⟨xa₁ t, (hmem t).1⟩
  let xb₁' : K → T := fun t => ⟨xb₁ t, (hmem t).2.1⟩
  let xa₂' : K → T := fun t => ⟨xa₂ t, (hmem t).2.2.1⟩
  let xb₂' : K → T := fun t => ⟨xb₂ t, (hmem t).2.2.2.1⟩
  let z' : K → T := fun t => ⟨z t, (hmem t).2.2.2.2⟩
  have hxa₁' : ∀ s t, xa₁' (s + t) = xa₁' s * xa₁' t := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul]; exact hxa₁ s t
  have hxb₁' : ∀ s t, xb₁' (s + t) = xb₁' s * xb₁' t := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul]; exact hxb₁ s t
  have hxa₂' : ∀ s t, xa₂' (s + t) = xa₂' s * xa₂' t := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul]; exact hxa₂ s t
  have hxb₂' : ∀ s t, xb₂' (s + t) = xb₂' s * xb₂' t := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul]; exact hxb₂ s t
  have hz' : ∀ s t, z' (s + t) = z' s * z' t := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul]; exact hz s t
  have hzi' : Function.Injective z' := by
    intro r r' hrr
    exact hzi (Subtype.ext_iff.mp hrr)
  have hab₁' : ∀ s t, ⁅xa₁' s, xb₁' t⁆ = z' (s * t) := by
    intro s t; apply Subtype.ext
    rw [show ((⁅xa₁' s, xb₁' t⁆ : T) : G) = ⁅(xa₁' s : G), (xb₁' t : G)⁆ from by
      simp [commutatorElement_def]]
    exact hab₁ s t
  have hab₂' : ∀ s t, ⁅xa₂' s, xb₂' t⁆ = z' (s * t) := by
    intro s t; apply Subtype.ext
    rw [show ((⁅xa₂' s, xb₂' t⁆ : T) : G) = ⁅(xa₂' s : G), (xb₂' t : G)⁆ from by
      simp [commutatorElement_def]]
    exact hab₂ s t
  have hza₁' : ∀ s t, Commute (z' s) (xa₁' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hza₁ s t).eq
  have hzb₁' : ∀ s t, Commute (z' s) (xb₁' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hzb₁ s t).eq
  have hza₂' : ∀ s t, Commute (z' s) (xa₂' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hza₂ s t).eq
  have hzb₂' : ∀ s t, Commute (z' s) (xb₂' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hzb₂ s t).eq
  have haa' : ∀ s t, Commute (xa₁' s) (xa₂' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (haa s t).eq
  have hab' : ∀ s t, Commute (xa₁' s) (xb₂' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hab s t).eq
  have hba' : ∀ s t, Commute (xb₁' s) (xa₂' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hba s t).eq
  have hbb' : ∀ s t, Commute (xb₁' s) (xb₂' t) := by
    intro s t; apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact (hbb s t).eq
  exact isExtraGood_of_comm_heis_triples hK hxa₁' hxb₁' hxa₂' hxb₂' hz' hzi' hab₁' hab₂'
    hza₁' hzb₁' hza₂' hzb₂' haa' hab' hba' hbb' s

private lemma exists_twist_core {G k : Type*} [Group G] [Field k] [IsAlgClosed k] [CharP k 3]
    (H : Subgroup G) (S : G →* G) {A A' B B' X₁ X₂ Z : k → G}
    (hA : ∀ c d, A (c + d) = A c * A d) (hA' : ∀ c d, A' (c + d) = A' c * A' d)
    (hB : ∀ c d, B (c + d) = B c * B d) (hB' : ∀ c d, B' (c + d) = B' c * B' d)
    (hX₁ : ∀ c d, X₁ (c + d) = X₁ c * X₁ d) (hX₂ : ∀ c d, X₂ (c + d) = X₂ c * X₂ d)
    (hZ : ∀ c d, Z (c + d) = Z c * Z d) (hZi : Function.Injective Z)
    (hH : ∀ c, A c ∈ H ∧ A' c ∈ H ∧ B c ∈ H ∧ B' c ∈ H ∧ X₁ c ∈ H ∧ X₂ c ∈ H ∧ Z c ∈ H)
    {sδ sθδ sε sθε s₁ s₂ sα : k} (hsδ : sδ * sδ = 1) (hsθδ : sθδ * sθδ = 1)
    (hsε : sε * sε = 1) (hsθε : sθε * sθε = 1) (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1)
    (hsα : sα * sα = 1)
    (hSA : ∀ c, S (A c) = A' (sδ * c ^ 3)) (hSA' : ∀ c, S (A' c) = A (sθδ * c ^ 3))
    (hSB : ∀ c, S (B c) = B' (sε * c ^ 3)) (hSB' : ∀ c, S (B' c) = B (sθε * c ^ 3))
    (hSX₁ : ∀ c, S (X₁ c) = X₁ (s₁ * c ^ 3)) (hSX₂ : ∀ c, S (X₂ c) = X₂ (s₂ * c ^ 3))
    (hSZ : ∀ c, S (Z c) = Z (sα * c ^ 3))
    (hAA' : ∀ c d, Commute (A c) (A' d)) (hBB' : ∀ c d, Commute (B c) (B' d))
    (hAB : ∀ c d, Commute (A c) (B d)) (hA'B' : ∀ c d, Commute (A' c) (B' d))
    (hZc : ∀ c d, Commute (Z c) (A d) ∧ Commute (Z c) (A' d) ∧ Commute (Z c) (B d) ∧
      Commute (Z c) (B' d) ∧ Commute (Z c) (X₁ d) ∧ Commute (Z c) (X₂ d))
    (hXc : ∀ c d, Commute (X₁ c) (A d) ∧ Commute (X₁ c) (A' d) ∧ Commute (X₁ c) (B d) ∧
      Commute (X₁ c) (B' d) ∧ Commute (X₂ c) (A d) ∧ Commute (X₂ c) (A' d) ∧
      Commute (X₂ c) (B d) ∧ Commute (X₂ c) (B' d))
    {N₁ N₂ N₃ : k} (hN₂ : N₂ ≠ 0) (hN₃ : N₃ ≠ 0)
    (hAB' : ∀ c d, ⁅A c, B' d⁆ = Z (N₁ * (c * d))) (hA'B : ∀ c d, ⁅A' c, B d⁆ = Z (N₂ * (c * d)))
    (hX₁₂ : ∀ c d, ⁅X₁ c, X₂ d⁆ = Z (N₃ * (c * d))) :
    ∃ c₀ : k, ∃ u : fixedPointsIn H S, orderOf u = 3 ∧ IsExtraGood u ∧
      (u : G) = A c₀ * A' (sδ * c₀ ^ 3) := by
  classical
  let K := ZMod 3
  let ι : K →+* k := ZMod.castHom (dvd_refl 3) k
  have hcardK : Nat.card K = 3 := by simp [K, ZMod.card]
  have hιpow : ∀ t : K, (ι t) ^ 3 = ι t := by
    intro t
    rw [← map_pow]
    exact congrArg ι (@ZMod.pow_card 3 ⟨Nat.prime_three⟩ t)
  have hι_inj : Function.Injective ι := ZMod.castHom_injective (R := k)
  obtain ⟨c₀, d₀, hc₀_ne, hc₀9', hd₀9', hh₀⟩ :=
    exists_orbit_scalars hsδ hsθδ hsε hsθε hN₂
  let h₀ : k := N₁ * sε * c₀ * d₀ ^ 3 + N₂ * sδ * c₀ ^ 3 * d₀
  have hh₀' : h₀ ≠ 0 := by simpa only [h₀] using hh₀
  let Ya : K → G := fun t => A (c₀ * ι t) * A' (sδ * c₀ ^ 3 * ι t)
  let Yb : K → G := fun t => B (d₀ * ι t) * B' (sε * d₀ ^ 3 * ι t)
  let Zc : K → G := fun t => Z (h₀ * ι t)
  have hYa_fix : ∀ t, S (Ya t) = Ya t := fun t =>
    orbit_pair_fixed (S := S) hsδ hsθδ hSA hSA' hAA' hc₀9' (hιpow t)
  have hYb_fix : ∀ t, S (Yb t) = Yb t := fun t =>
    orbit_pair_fixed (S := S) hsε hsθε hSB hSB' hBB' hd₀9' (hιpow t)
  have hYa_add : ∀ s t, Ya (s + t) = Ya s * Ya t := fun s t =>
    orbit_pair_add ι hA hA' hAA' sδ c₀ s t
  have hYb_add : ∀ s t, Yb (s + t) = Yb s * Yb t := fun s t =>
    orbit_pair_add ι hB hB' hBB' sε d₀ s t
  have hZc_add : ∀ s t, Zc (s + t) = Zc s * Zc t := by
    intro s t
    simp only [Zc, map_add, mul_add, hZ]
  have hZc_inj : Function.Injective Zc := by
    intro r r' hrr
    have h : Z (h₀ * ι r) = Z (h₀ * ι r') := by simpa only [Zc] using hrr
    have h' : h₀ * ι r = h₀ * ι r' := hZi h
    have h'' : ι r = ι r' := mul_left_cancel₀ hh₀' h'
    exact hι_inj h''
  have hab₁ : ∀ s t, ⁅Ya s, Yb t⁆ = Zc (s * t) := by
    intro s t
    have h1 : ⁅Ya s, Yb t⁆ =
        Z (N₁ * ((c₀ * ι s) * (sε * d₀ ^ 3 * ι t))) *
          Z (N₂ * ((sδ * c₀ ^ 3 * ι s) * (d₀ * ι t))) :=
      orbit_pair_commutator (C := fun c => Z (N₁ * c)) (C' := fun c => Z (N₂ * c))
        ι (s := s) (t := t) hAA' hAB hA'B' hAB' hA'B
        (fun c d => (hZc (N₁ * c) d).2.1) (fun c d => (hZc (N₁ * c) d).2.2.1)
    rw [h1, ← hZ]
    congr 1
    simp only [h₀, map_mul]
    ring
  obtain ⟨lam₁, hlam₁⟩ := IsAlgClosed.exists_pow_nat_eq s₁ (n := 2) (by norm_num)
  obtain ⟨lam₂, hlam₂⟩ := IsAlgClosed.exists_pow_nat_eq s₂ (n := 2) (by norm_num)
  have hlam₁_ne : lam₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 2 ≠ 0)] at hlam₁
    exact (sign_ne_zero hs₁) hlam₁.symm
  have hlam₂_ne : lam₂ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 2 ≠ 0)] at hlam₂
    exact (sign_ne_zero hs₂) hlam₂.symm
  have hlam₁3 : lam₁ ^ 3 = lam₁ * s₁ := by
    rw [show 3 = 2 + 1 from rfl, pow_succ, hlam₁, mul_comm]
  have hlam₂3 : lam₂ ^ 3 = lam₂ * s₂ := by
    rw [show 3 = 2 + 1 from rfl, pow_succ, hlam₂, mul_comm]
  have hX₁_fix : ∀ t, S (X₁ (lam₁ * ι t)) = X₁ (lam₁ * ι t) := fun t =>
    fixed_one (S := S) hs₁ hSX₁ hlam₁3 (hιpow t)
  have hX₂_fix : ∀ t, S (X₂ (lam₂ * ι t)) = X₂ (lam₂ * ι t) := fun t =>
    fixed_one (S := S) hs₂ hSX₂ hlam₂3 (hιpow t)
  have hfix_h0 : S (Z h₀) = Z h₀ := by
    have hcomm : Z h₀ = ⁅Ya 1, Yb 1⁆ := by
      simpa only [Zc, map_one, mul_one] using (hab₁ 1 1).symm
    rw [hcomm, map_commutatorElement, hYa_fix, hYb_fix]
  have hsq_h0 : h₀ ^ 2 = sα := fixed_sq_of_fixed_Z hsα hSZ hZi hfix_h0 hh₀'
  have hfix_N : S (Z (N₃ * lam₁ * lam₂)) = Z (N₃ * lam₁ * lam₂) := by
    have hcomm : Z (N₃ * lam₁ * lam₂) = ⁅X₁ (lam₁ * ι 1), X₂ (lam₂ * ι 1)⁆ := by
      simpa only [map_one, mul_one, mul_assoc] using
        (hX₁₂ (lam₁ * ι 1) (lam₂ * ι 1)).symm
    rw [hcomm, map_commutatorElement, hX₁_fix, hX₂_fix]
  have hsq_N : (N₃ * lam₁ * lam₂) ^ 2 = sα :=
    fixed_sq_of_fixed_Z hsα hSZ hZi hfix_N
      (mul_ne_zero (mul_ne_zero hN₃ hlam₁_ne) hlam₂_ne)
  have hιneg : ι (-1) = -1 := by
    have hK2 : (-1 : K) = 2 := by decide
    have h2 : ι (2 : K) = (2 : k) := map_ofNat ι 2
    have h3 : (2 : k) = -1 := by
      have h0 : (3 : k) = 0 := CharP.cast_eq_zero k 3
      have h : (2 : k) + 1 = 0 := by rw [← h0]; norm_num
      exact eq_neg_of_add_eq_zero_left h
    rw [hK2, h2, h3]
  obtain ⟨σ, hσ_one, hσ_eq⟩ : ∃ σ : K, (σ = 1 ∨ σ = -1) ∧
      h₀ = ι σ * (N₃ * lam₁ * lam₂) := by
    have hsq_eq : h₀ ^ 2 = (N₃ * lam₁ * lam₂) ^ 2 := by rw [hsq_h0, hsq_N]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq) with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h, map_one, one_mul]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [h, hιneg, neg_mul, one_mul]
  let Xa₂ : K → G := fun t => X₁ (lam₁ * ι (σ * t))
  let Xb₂ : K → G := fun t => X₂ (lam₂ * ι t)
  have hXa₂_add : ∀ s t, Xa₂ (s + t) = Xa₂ s * Xa₂ t := by
    intro s t
    simp only [Xa₂, mul_add, map_add, mul_add, hX₁]
  have hXb₂_add : ∀ s t, Xb₂ (s + t) = Xb₂ s * Xb₂ t := by
    intro s t
    simp only [Xb₂, map_add, mul_add, hX₂]
  have hXa₂_fix : ∀ t, S (Xa₂ t) = Xa₂ t := fun t => hX₁_fix (σ * t)
  have hXb₂_fix : ∀ t, S (Xb₂ t) = Xb₂ t := fun t => hX₂_fix t
  have hZc_fix : ∀ t, S (Zc t) = Zc t := by
    intro t
    have hcomm : Zc t = ⁅Ya t, Yb 1⁆ := by
      simpa only [Zc, mul_one] using (hab₁ t 1).symm
    rw [hcomm, map_commutatorElement, hYa_fix, hYb_fix]
  have hab₂ : ∀ s t, ⁅Xa₂ s, Xb₂ t⁆ = Zc (s * t) := by
    intro s t
    rw [hX₁₂]
    change Z (N₃ * ((lam₁ * ι (σ * s)) * (lam₂ * ι t))) = Z (h₀ * ι (s * t))
    congr 1
    rw [hσ_eq, map_mul, map_mul]
    ring
  have hYa_mem : ∀ t, Ya t ∈ H := by
    intro t
    exact H.mul_mem (hH (c₀ * ι t)).1 (hH (sδ * c₀ ^ 3 * ι t)).2.1
  have hYb_mem : ∀ t, Yb t ∈ H := by
    intro t
    exact H.mul_mem (hH (d₀ * ι t)).2.2.1 (hH (sε * d₀ ^ 3 * ι t)).2.2.2.1
  have hXa₂_mem : ∀ t, Xa₂ t ∈ H := fun t => (hH (lam₁ * ι (σ * t))).2.2.2.2.1
  have hXb₂_mem : ∀ t, Xb₂ t ∈ H := fun t => (hH (lam₂ * ι t)).2.2.2.2.2.1
  have hZc_mem : ∀ t, Zc t ∈ H := fun t => (hH (h₀ * ι t)).2.2.2.2.2.2
  have hmemT : ∀ t, Ya t ∈ fixedPointsIn H S ∧ Yb t ∈ fixedPointsIn H S ∧
      Xa₂ t ∈ fixedPointsIn H S ∧ Xb₂ t ∈ fixedPointsIn H S ∧ Zc t ∈ fixedPointsIn H S := by
    intro t
    exact ⟨mem_fixedPointsIn.2 ⟨hYa_mem t, hYa_fix t⟩,
      mem_fixedPointsIn.2 ⟨hYb_mem t, hYb_fix t⟩,
      mem_fixedPointsIn.2 ⟨hXa₂_mem t, hXa₂_fix t⟩,
      mem_fixedPointsIn.2 ⟨hXb₂_mem t, hXb₂_fix t⟩,
      mem_fixedPointsIn.2 ⟨hZc_mem t, hZc_fix t⟩⟩
  have hza₁ : ∀ s t, Commute (Zc s) (Ya t) := by
    intro s t
    exact ((hZc (h₀ * ι s) (c₀ * ι t)).1.mul_right
      (hZc (h₀ * ι s) (sδ * c₀ ^ 3 * ι t)).2.1).eq
  have hzb₁ : ∀ s t, Commute (Zc s) (Yb t) := by
    intro s t
    exact ((hZc (h₀ * ι s) (d₀ * ι t)).2.2.1.mul_right
      (hZc (h₀ * ι s) (sε * d₀ ^ 3 * ι t)).2.2.2.1).eq
  have hza₂ : ∀ s t, Commute (Zc s) (Xa₂ t) := fun s t =>
    (hZc (h₀ * ι s) (lam₁ * ι (σ * t))).2.2.2.2.1
  have hzb₂ : ∀ s t, Commute (Zc s) (Xb₂ t) := fun s t =>
    (hZc (h₀ * ι s) (lam₂ * ι t)).2.2.2.2.2
  have haa : ∀ s t, Commute (Ya s) (Xa₂ t) := by
    intro s t
    exact (((hXc (lam₁ * ι (σ * t)) (c₀ * ι s)).1.symm).mul_left
      ((hXc (lam₁ * ι (σ * t)) (sδ * c₀ ^ 3 * ι s)).2.1.symm)).eq
  have hab : ∀ s t, Commute (Ya s) (Xb₂ t) := by
    intro s t
    exact (((hXc (lam₂ * ι t) (c₀ * ι s)).2.2.2.2.1.symm).mul_left
      ((hXc (lam₂ * ι t) (sδ * c₀ ^ 3 * ι s)).2.2.2.2.2.1.symm)).eq
  have hba : ∀ s t, Commute (Yb s) (Xa₂ t) := by
    intro s t
    exact (((hXc (lam₁ * ι (σ * t)) (d₀ * ι s)).2.2.1.symm).mul_left
      ((hXc (lam₁ * ι (σ * t)) (sε * d₀ ^ 3 * ι s)).2.2.2.1.symm)).eq
  have hbb : ∀ s t, Commute (Yb s) (Xb₂ t) := by
    intro s t
    exact (((hXc (lam₂ * ι t) (d₀ * ι s)).2.2.2.2.2.2.1.symm).mul_left
      ((hXc (lam₂ * ι t) (sε * d₀ ^ 3 * ι s)).2.2.2.2.2.2.2.symm)).eq
  have hgood : IsExtraGood (⟨Ya 1, (hmemT 1).1⟩ : fixedPointsIn H S) :=
    isExtraGood_of_comm_heis_triples_mem hcardK (fixedPointsIn H S) hmemT
      hYa_add hYb_add hXa₂_add hXb₂_add hZc_add hZc_inj hab₁ hab₂
      hza₁ hzb₁ hza₂ hzb₂ haa hab hba hbb (1 : K)
  let u : fixedPointsIn H S := ⟨Ya 1, (hmemT 1).1⟩
  have hu_eq : (u : G) = A c₀ * A' (sδ * c₀ ^ 3) := by
    change Ya 1 = A c₀ * A' (sδ * c₀ ^ 3)
    simp only [Ya, map_one, mul_one]
  have hu_order : orderOf u = 3 := by
    have hzero : Ya 0 = 1 := CFSG.map_zero_of_map_add hYa_add
    have hpow : ∀ n : ℕ, Ya (n : K) = (Ya 1) ^ n := by
      intro n
      induction n with
      | zero => simpa using hzero
      | succ n ih =>
          have hcast : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
          rw [hcast, hYa_add, ih, pow_succ]
    have h3K : ((3 : ℕ) : K) = 0 := by decide
    have hup : (Ya 1) ^ 3 = 1 := by
      rw [← hpow 3, h3K, hzero]
    have hne : Ya 1 ≠ 1 := by
      intro h
      have hz1 : Zc 1 = 1 := by
        have hcomm : Zc 1 = ⁅Ya 1, Yb 1⁆ := by
          simpa only [Zc, mul_one] using (hab₁ 1 1).symm
        rw [hcomm, h]
        simp [commutatorElement_def]
      have hz0 : Zc 0 = 1 := by
        have hcomm : Zc 0 = ⁅Ya 0, Yb 1⁆ := by
          simpa only [Zc, mul_one] using (hab₁ 0 1).symm
        rw [hcomm, hzero]
        simp [commutatorElement_def]
      have h10 : (1 : K) = 0 := hZc_inj (hz1.trans hz0.symm)
      exact one_ne_zero h10
    have hup' : u ^ 3 = 1 := by
      apply Subtype.ext
      change (Ya 1) ^ 3 = (1 : G)
      exact hup
    have hne' : u ≠ 1 := by
      intro h
      apply hne
      have := congrArg (fun x : fixedPointsIn H S => (x : G)) h
      simpa only [Subgroup.coe_one] using this
    exact orderOf_eq_prime hup' hne'
  exact ⟨c₀, u, hu_order, hgood, hu_eq⟩


theorem exists_twist_inv_extraGood {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {k : Type} [Field k] [IsAlgClosed k] [CharP k 3] (Q : ModGL τ k)
    (θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hQ : ∀ γ, IsRoot τ γ → ∃ s : k, s * s = 1 ∧
      ∀ c, Q * pinnedX τ k γ c * Q⁻¹ = pinnedX τ k (θ γ) (s * c))
    (a : Fin τ.rank → kˣ) {δ ε γ₁ γ₂ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hθδ : IsRoot τ (θ δ)) (hε : IsRoot τ ε) (hθε : IsRoot τ (θ ε))
    (hγ₁ : IsRoot τ γ₁) (hγ₂ : IsRoot τ γ₂)
    (hθθδ : θ (θ δ) = δ) (hθθε : θ (θ ε) = ε) (hθγ₁ : θ γ₁ = γ₁) (hθγ₂ : θ γ₂ = γ₂)
    (hθα : θ (δ + θ ε) = δ + θ ε) (hsum : θ δ + ε = δ + θ ε) (hsum' : γ₁ + γ₂ = δ + θ ε)
    (hδθε : δ ≠ θ ε ∧ δ ≠ -θ ε ∧ IsRoot τ (δ + θ ε)) (hθδε : θ δ ≠ ε ∧ θ δ ≠ -ε)
    (hγ₁₂ : γ₁ ≠ γ₂ ∧ γ₁ ≠ -γ₂)
    (hδθδ : RootsCommute τ δ (θ δ)) (hεθε : RootsCommute τ ε (θ ε))
    (hδε : RootsCommute τ δ ε) (hθδθε : RootsCommute τ (θ δ) (θ ε))
    (hz : ∀ γ ∈ [δ, θ δ, ε, θ ε, γ₁, γ₂], RootsCommute τ (δ + θ ε) γ)
    (hγ : ∀ γ ∈ [γ₁, γ₂], ∀ η ∈ [δ, θ δ, ε, θ ε], RootsCommute τ γ η)
    (hχ : rootChar a δ = -1) (hχ' : rootChar a (θ δ) = -1) :
    ∃ u : fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k 3 1 Q), orderOf u = 3 ∧
      IsExtraGood u ∧
      rootDiagUnit τ a * (u : ModGL τ k) * (rootDiagUnit τ a)⁻¹ = (u : ModGL τ k)⁻¹ := by
  classical
  obtain ⟨sδ, hsδ, hQδ⟩ := hQ δ hδ
  obtain ⟨sθδ, hsθδ, hQθδ⟩ := hQ (θ δ) hθδ
  obtain ⟨sε, hsε, hQε⟩ := hQ ε hε
  obtain ⟨sθε, hsθε, hQθε⟩ := hQ (θ ε) hθε
  obtain ⟨sγ₁, hsγ₁, hQγ₁⟩ := hQ γ₁ hγ₁
  obtain ⟨sγ₂, hsγ₂, hQγ₂⟩ := hQ γ₂ hγ₂
  have hα : IsRoot τ (δ + θ ε) := hδθε.2.2
  obtain ⟨sα, hsα, hQα⟩ := hQ (δ + θ ε) hα
  have hQθδ' : ∀ c, Q * pinnedX τ k (θ δ) c * Q⁻¹ = pinnedX τ k δ (sθδ * c) := by
    intro c; rw [hQθδ c, hθθδ]
  have hQθε' : ∀ c, Q * pinnedX τ k (θ ε) c * Q⁻¹ = pinnedX τ k ε (sθε * c) := by
    intro c; rw [hQθε c, hθθε]
  have hQγ₁' : ∀ c, Q * pinnedX τ k γ₁ c * Q⁻¹ = pinnedX τ k γ₁ (sγ₁ * c) := by
    intro c; rw [hQγ₁ c, hθγ₁]
  have hQγ₂' : ∀ c, Q * pinnedX τ k γ₂ c * Q⁻¹ = pinnedX τ k γ₂ (sγ₂ * c) := by
    intro c; rw [hQγ₂ c, hθγ₂]
  have hQα' : ∀ c, Q * pinnedX τ k (δ + θ ε) c * Q⁻¹ =
      pinnedX τ k (δ + θ ε) (sα * c) := by
    intro c; rw [hQα c, hθα]
  let N₁ : k := (commConst τ δ (θ ε) (1, 1) : k)
  let N₂ : k := (commConst τ (θ δ) ε (1, 1) : k)
  let N₃ : k := (commConst τ γ₁ γ₂ (1, 1) : k)
  have hcf₁ := (simply_laced_root_commutator_unit τ hτ hδ hθε hδθε.1 hδθε.2.1).1 hα
  have hcf₂ := (simply_laced_root_commutator_unit τ hτ hθδ hε hθδε.1 hθδε.2).1
    (by rw [hsum]; exact hα)
  have hcf₃ := (simply_laced_root_commutator_unit τ hτ hγ₁ hγ₂ hγ₁₂.1 hγ₁₂.2).1
    (by rw [hsum']; exact hα)
  have hN₂0 : N₂ ≠ 0 := by
    rcases hcf₂.1 with h | h <;> simp [N₂, h]
  have hN₃0 : N₃ ≠ 0 := by
    rcases hcf₃.1 with h | h <;> simp [N₃, h]
  have hAB' : ∀ c d, ⁅pinnedX τ k δ c, pinnedX τ k (θ ε) d⁆ =
      pinnedX τ k (δ + θ ε) (N₁ * (c * d)) := by
    intro c d
    rw [hcf₁.2 k c d]
    congr 1
    simp only [N₁]
    ring
  have hA'B : ∀ c d, ⁅pinnedX τ k (θ δ) c, pinnedX τ k ε d⁆ =
      pinnedX τ k (δ + θ ε) (N₂ * (c * d)) := by
    intro c d
    rw [hcf₂.2 k c d, hsum]
    congr 1
    simp only [N₂]
    ring
  have hX₁₂ : ∀ c d, ⁅pinnedX τ k γ₁ c, pinnedX τ k γ₂ d⁆ =
      pinnedX τ k (δ + θ ε) (N₃ * (c * d)) := by
    intro c d
    rw [hcf₃.2 k c d, hsum']
    congr 1
    simp only [N₃]
    ring
  have hzδ := hz δ (by simp)
  have hzθδ := hz (θ δ) (by simp)
  have hzε := hz ε (by simp)
  have hzθε := hz (θ ε) (by simp)
  have hzγ₁ := hz γ₁ (by simp)
  have hzγ₂ := hz γ₂ (by simp)
  obtain ⟨c₀, u, hu_order, hu_good, hu_eq⟩ :=
    exists_twist_core (H := adjointGroup τ k) (S := frobTwistGL τ k 3 1 Q)
      (A := fun c => pinnedX τ k δ c) (A' := fun c => pinnedX τ k (θ δ) c)
      (B := fun c => pinnedX τ k ε c) (B' := fun c => pinnedX τ k (θ ε) c)
      (X₁ := fun c => pinnedX τ k γ₁ c) (X₂ := fun c => pinnedX τ k γ₂ c)
      (Z := fun c => pinnedX τ k (δ + θ ε) c)
      (pinnedX_add τ k δ) (pinnedX_add τ k (θ δ))
      (pinnedX_add τ k ε) (pinnedX_add τ k (θ ε))
      (pinnedX_add τ k γ₁) (pinnedX_add τ k γ₂)
      (pinnedX_add τ k (δ + θ ε)) (pinnedX_injective τ k (δ + θ ε))
      (fun c => ⟨pinnedX_mem_adjointGroup δ c, pinnedX_mem_adjointGroup (θ δ) c,
        pinnedX_mem_adjointGroup ε c, pinnedX_mem_adjointGroup (θ ε) c,
        pinnedX_mem_adjointGroup γ₁ c, pinnedX_mem_adjointGroup γ₂ c,
        pinnedX_mem_adjointGroup (δ + θ ε) c⟩)
      hsδ hsθδ hsε hsθε hsγ₁ hsγ₂ hsα
      (fun c => frobTwistGL_pinnedX 3 1 Q hQδ c)
      (fun c => frobTwistGL_pinnedX 3 1 Q hQθδ' c)
      (fun c => frobTwistGL_pinnedX 3 1 Q hQε c)
      (fun c => frobTwistGL_pinnedX 3 1 Q hQθε' c)
      (fun c => frobTwistGL_pinnedX 3 1 Q hQγ₁' c)
      (fun c => frobTwistGL_pinnedX 3 1 Q hQγ₂' c)
      (fun c => frobTwistGL_pinnedX 3 1 Q hQα' c)
      (fun c d => pinnedX_commute_of_rootsCommute hτ hδ hθδ hδθδ c d)
      (fun c d => pinnedX_commute_of_rootsCommute hτ hε hθε hεθε c d)
      (fun c d => pinnedX_commute_of_rootsCommute hτ hδ hε hδε c d)
      (fun c d => pinnedX_commute_of_rootsCommute hτ hθδ hθε hθδθε c d)
      (fun c d => ⟨pinnedX_commute_of_rootsCommute hτ hα hδ hzδ c d,
        pinnedX_commute_of_rootsCommute hτ hα hθδ hzθδ c d,
        pinnedX_commute_of_rootsCommute hτ hα hε hzε c d,
        pinnedX_commute_of_rootsCommute hτ hα hθε hzθε c d,
        pinnedX_commute_of_rootsCommute hτ hα hγ₁ hzγ₁ c d,
        pinnedX_commute_of_rootsCommute hτ hα hγ₂ hzγ₂ c d⟩)
      (fun c d => ⟨
        pinnedX_commute_of_rootsCommute hτ hγ₁ hδ (hγ γ₁ (by simp) δ (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₁ hθδ (hγ γ₁ (by simp) (θ δ) (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₁ hε (hγ γ₁ (by simp) ε (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₁ hθε (hγ γ₁ (by simp) (θ ε) (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₂ hδ (hγ γ₂ (by simp) δ (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₂ hθδ (hγ γ₂ (by simp) (θ δ) (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₂ hε (hγ γ₂ (by simp) ε (by simp)) c d,
        pinnedX_commute_of_rootsCommute hτ hγ₂ hθε (hγ γ₂ (by simp) (θ ε) (by simp)) c d⟩)
      (N₁ := N₁) (N₂ := N₂) (N₃ := N₃) hN₂0 hN₃0 hAB' hA'B hX₁₂
  have hinv : rootDiagUnit τ a * (u : ModGL τ k) * (rootDiagUnit τ a)⁻¹ =
      ((u : ModGL τ k))⁻¹ := by
    rw [hu_eq]
    calc rootDiagUnit τ a * (pinnedX τ k δ c₀ * pinnedX τ k (θ δ) (sδ * c₀ ^ 3)) *
          (rootDiagUnit τ a)⁻¹
        = (rootDiagUnit τ a * pinnedX τ k δ c₀ * (rootDiagUnit τ a)⁻¹) *
          (rootDiagUnit τ a * pinnedX τ k (θ δ) (sδ * c₀ ^ 3) *
            (rootDiagUnit τ a)⁻¹) := by group
      _ = pinnedX τ k δ (-c₀) * pinnedX τ k (θ δ) (-(sδ * c₀ ^ 3)) := by
        rw [rootDiagUnit_conj_pinnedX a hδ c₀, hχ, Units.val_neg, Units.val_one, neg_one_mul,
          rootDiagUnit_conj_pinnedX a hθδ (sδ * c₀ ^ 3), hχ', Units.val_neg, Units.val_one,
          neg_one_mul]
      _ = (pinnedX τ k δ c₀)⁻¹ * (pinnedX τ k (θ δ) (sδ * c₀ ^ 3))⁻¹ := by
        rw [← pinnedX_neg, ← pinnedX_neg]
      _ = (pinnedX τ k δ c₀ * pinnedX τ k (θ δ) (sδ * c₀ ^ 3))⁻¹ := by
        rw [mul_inv_rev]
        exact ((pinnedX_commute_of_rootsCommute hτ hδ hθδ hδθδ c₀
          (sδ * c₀ ^ 3)).inv_left.inv_right).eq
  exact ⟨u, hu_order, hu_good, hinv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
