module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
import CFSG.Mathlib.Algebra.MapAdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.LieType.AlgebraicGroups (fixedPointsIn mem_fixedPointsIn)
open scoped commutatorElement

private lemma sign_pow {k : Type*} [Field k] {q : ℕ} (hq : Odd q) {s : k}
    (hs : s * s = 1) : s ^ q = s := by
  have h2 : s ^ 2 = 1 := by rwa [sq]
  rcases sq_eq_one_iff.mp h2 with h | h
  · rw [h, one_pow]
  · rw [h, hq.neg_one_pow]

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

private lemma pair_fixed {G k : Type*} [Group G] [Field k] {p e : ℕ} (S : G →* G)
    {A A' : k → G} {sa sa' lam : k} (hq : Odd (p ^ e))
    (hsa : sa * sa = 1) (hsa' : sa' * sa' = 1)
    (hSA : ∀ c, S (A c) = A' (sa * c ^ p ^ e))
    (hSA' : ∀ c, S (A' c) = A (sa' * c ^ p ^ e))
    (hAA' : ∀ c d, Commute (A c) (A' d))
    (hlam : (lam ^ p ^ e) ^ p ^ e = lam * (sa * sa')) {i : k} (hi : i ^ p ^ e = i) :
    S (A (lam * i) * A' (sa * lam ^ p ^ e * i)) =
      A (lam * i) * A' (sa * lam ^ p ^ e * i) := by
  have hcq : (lam * i) ^ p ^ e = lam ^ p ^ e * i := by rw [mul_pow, hi]
  have hdq : (sa * lam ^ p ^ e * i) ^ p ^ e = sa * (lam * (sa * sa')) * i := by
    rw [mul_pow, mul_pow, sign_pow hq hsa, hlam, hi]
  rw [map_mul, hSA, hSA', hcq, hdq]
  have h1 : sa * (lam ^ p ^ e * i) = sa * lam ^ p ^ e * i := by ring
  rw [h1, sign_mul_cancel hsa hsa']
  exact (hAA' (lam * i) (sa * lam ^ p ^ e * i)).eq.symm


private lemma fixed_one {G k : Type*} [Group G] [Field k] {p e : ℕ} (S : G →* G)
    {A : k → G} {sa lam : k} (hsa : sa * sa = 1)
    (hSA : ∀ c, S (A c) = A (sa * c ^ p ^ e))
    (hlam : lam ^ p ^ e = lam * sa) {i : k} (hi : i ^ p ^ e = i) :
    S (A (lam * i)) = A (lam * i) := by
  have hcq : (lam * i) ^ p ^ e = lam ^ p ^ e * i := by rw [mul_pow, hi]
  rw [hSA, hcq, hlam]
  congr 1
  calc sa * (lam * sa * i) = sa * sa * lam * i := by ring
    _ = lam * i := by rw [hsa, one_mul]
private lemma pair_commutator {G k K : Type*} [Group G] [Field k] [Field K]
    (ι : K →+* k) (p e : ℕ) {A A' B B' C C' : k → G} {lam sa mu sb : k} (s t : K)
    (hAB' : ∀ c d, Commute (A c) (B' d)) (hA'B : ∀ c d, Commute (A' c) (B d))
    (hAB : ∀ c d, ⁅A c, B d⁆ = C (c * d))
    (hA'B' : ∀ c d, ⁅A' c, B' d⁆ = C' (c * d))
    (hC'A : ∀ c d, Commute (C' c) (A d)) (hC'B : ∀ c d, Commute (C' c) (B d))
    (hCC' : ∀ c d, Commute (C c) (C' d)) :
    ⁅A (lam * ι s) * A' (sa * lam ^ p ^ e * ι s),
        B (mu * ι t) * B' (sb * mu ^ p ^ e * ι t)⁆ =
      C (lam * mu * ι (s * t)) * C' (sa * sb * (lam * mu) ^ p ^ e * ι (s * t)) := by
  have h1 : ⁅A (lam * ι s), B (mu * ι t)⁆ = C (lam * ι s * (mu * ι t)) := hAB _ _
  have h2 : ⁅A' (sa * lam ^ p ^ e * ι s), B' (sb * mu ^ p ^ e * ι t)⁆ =
      C' ((sa * lam ^ p ^ e * ι s) * (sb * mu ^ p ^ e * ι t)) := hA'B' _ _
  have hza : Commute ⁅A' (sa * lam ^ p ^ e * ι s), B' (sb * mu ^ p ^ e * ι t)⁆
      (A (lam * ι s)) := by rw [h2]; exact hC'A _ _
  have hzb : Commute ⁅A' (sa * lam ^ p ^ e * ι s), B' (sb * mu ^ p ^ e * ι t)⁆
      (B (mu * ι t)) := by rw [h2]; exact hC'B _ _
  have hcc := commutator_mul_mul_of_comm (a := A (lam * ι s))
    (a' := A' (sa * lam ^ p ^ e * ι s)) (b := B (mu * ι t))
    (b' := B' (sb * mu ^ p ^ e * ι t)) (hAB' _ _) (hA'B _ _) hza hzb
  rw [hcc, h1, h2]
  have harg1 : lam * ι s * (mu * ι t) = lam * mu * ι (s * t) := by rw [map_mul]; ring
  have harg2 : sa * lam ^ p ^ e * ι s * (sb * mu ^ p ^ e * ι t) =
      sa * sb * (lam * mu) ^ p ^ e * ι (s * t) := by rw [map_mul, mul_pow]; ring
  rw [harg1, harg2]
  exact (hCC' _ _).eq.symm


theorem exists_pair_heis_good_of_mu {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) {A A' B B' C C' : k → G}
    (hA : ∀ c d, A (c + d) = A c * A d) (hA' : ∀ c d, A' (c + d) = A' c * A' d)
    (hB : ∀ c d, B (c + d) = B c * B d) (hB' : ∀ c d, B' (c + d) = B' c * B' d)
    (hC : ∀ c d, C (c + d) = C c * C d) (hC' : ∀ c d, C' (c + d) = C' c * C' d)
    (hAX : ∀ c, A c ∈ X) (hA'X : ∀ c, A' c ∈ X) (hBX : ∀ c, B c ∈ X) (hB'X : ∀ c, B' c ∈ X)
    {sa sa' sb sb' : k} (hsa : sa * sa = 1) (hsa' : sa' * sa' = 1) (hsb : sb * sb = 1)
    (hsb' : sb' * sb' = 1)
    (hSA : ∀ c, S (A c) = A' (sa * c ^ p ^ e)) (hSA' : ∀ c, S (A' c) = A (sa' * c ^ p ^ e))
    (hSB : ∀ c, S (B c) = B' (sb * c ^ p ^ e)) (hSB' : ∀ c, S (B' c) = B (sb' * c ^ p ^ e))
    (hAA' : ∀ c d, Commute (A c) (A' d)) (hBB' : ∀ c d, Commute (B c) (B' d))
    (hAB' : ∀ c d, Commute (A c) (B' d)) (hA'B : ∀ c d, Commute (A' c) (B d))
    (hAB : ∀ c d, ⁅A c, B d⁆ = C (c * d)) (hA'B' : ∀ c d, ⁅A' c, B' d⁆ = C' (c * d))
    (hCA : ∀ c d, Commute (C c) (A d)) (hCA' : ∀ c d, Commute (C c) (A' d))
    (hCB : ∀ c d, Commute (C c) (B d)) (hCB' : ∀ c d, Commute (C c) (B' d))
    (hC'A : ∀ c d, Commute (C' c) (A d)) (hC'A' : ∀ c d, Commute (C' c) (A' d))
    (hC'B : ∀ c d, Commute (C' c) (B d)) (hC'B' : ∀ c d, Commute (C' c) (B' d))
    (hCC' : ∀ c d, Commute (C c) (C' d)) (hCinj : ∀ c d, C c * C' d = 1 → c = 0)
    {mu : k} (hmu0 : mu ≠ 0) (hmu : (mu ^ p ^ e) ^ p ^ e = mu * (sb * sb')) :
    ∃ u : fixedPointsIn X S, (u : G) = B mu * B' (sb * mu ^ p ^ e) ∧ orderOf u = p ∧
      IsSpecialGood p u := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hq_odd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hcard : Fintype.card K = p ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  have hιpow : ∀ s : K, (ι s) ^ p ^ e = ι s := by
    intro s
    rw [← map_pow, ← hcard]
    exact congrArg ι (FiniteField.pow_card s)
  have hι_inj : Function.Injective ι := ι.injective
  have hpos : 0 < (p ^ e) ^ 2 - 1 := by
    have h2 : 1 < (p ^ e) ^ 2 := by nlinarith
    omega
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (sa * sa') (n := (p ^ e) ^ 2 - 1) hpos
  have hsa0 : sa ≠ 0 := by rintro rfl; simp at hsa
  have hsa'0 : sa' ≠ 0 := by rintro rfl; simp at hsa'
  have hκ : sa * sa' ≠ 0 := mul_ne_zero hsa0 hsa'0
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hlam
    exact hκ hlam.symm
  have hlam_q : (lam ^ p ^ e) ^ p ^ e = lam * (sa * sa') := by
    rw [← pow_mul]
    have h2 : 1 ≤ (p ^ e) ^ 2 := by nlinarith
    have h2' : 1 ≤ (p ^ e) * (p ^ e) := by nlinarith
    have hqq : (p ^ e) * (p ^ e) = ((p ^ e) ^ 2 - 1) + 1 := by
      rw [pow_two (p ^ e)]
      exact (Nat.sub_add_cancel h2').symm
    rw [hqq, pow_succ, hlam, mul_comm]
  let Xa : K → G := fun s => A (lam * ι s) * A' (sa * lam ^ p ^ e * ι s)
  let Xb : K → G := fun s => B (mu * ι s) * B' (sb * mu ^ p ^ e * ι s)
  have hXa_def : ∀ s, Xa s = A (lam * ι s) * A' (sa * lam ^ p ^ e * ι s) := fun s => rfl
  have hXb_def : ∀ s, Xb s = B (mu * ι s) * B' (sb * mu ^ p ^ e * ι s) := fun s => rfl
  have hXa_mem : ∀ s, Xa s ∈ X := by
    intro s
    rw [hXa_def]
    exact X.mul_mem (hAX _) (hA'X _)
  have hXb_mem : ∀ s, Xb s ∈ X := by
    intro s
    rw [hXb_def]
    exact X.mul_mem (hBX _) (hB'X _)
  have hXa_fix : ∀ s, S (Xa s) = Xa s := by
    intro s
    rw [hXa_def]
    exact pair_fixed S hq_odd hsa hsa' hSA hSA' hAA' hlam_q (hιpow s)
  have hXb_fix : ∀ s, S (Xb s) = Xb s := by
    intro s
    rw [hXb_def]
    exact pair_fixed S hq_odd hsb hsb' hSB hSB' hBB' hmu (hιpow s)
  have hXcomm : ∀ s t, ⁅Xa s, Xb t⁆ =
      C (lam * mu * ι (s * t)) * C' (sa * sb * (lam * mu) ^ p ^ e * ι (s * t)) := by
    intro s t
    rw [hXa_def, hXb_def]
    exact pair_commutator ι p e s t hAB' hA'B hAB hA'B' hC'A hC'B hCC'
  have hXa_add : ∀ s t, Xa (s + t) = Xa s * Xa t := by
    intro s t
    simp only [hXa_def]
    rw [map_add, mul_add, mul_add, hA, hA']
    rw [show A (lam * ι s) * A (lam * ι t) *
          (A' (sa * lam ^ p ^ e * ι s) * A' (sa * lam ^ p ^ e * ι t)) =
        A (lam * ι s) * (A (lam * ι t) * A' (sa * lam ^ p ^ e * ι s)) *
          A' (sa * lam ^ p ^ e * ι t) by group]
    rw [(hAA' (lam * ι t) (sa * lam ^ p ^ e * ι s)).eq]
    group
  have hXb_add : ∀ s t, Xb (s + t) = Xb s * Xb t := by
    intro s t
    simp only [hXb_def]
    rw [map_add, mul_add, mul_add, hB, hB']
    rw [show B (mu * ι s) * B (mu * ι t) *
          (B' (sb * mu ^ p ^ e * ι s) * B' (sb * mu ^ p ^ e * ι t)) =
        B (mu * ι s) * (B (mu * ι t) * B' (sb * mu ^ p ^ e * ι s)) *
          B' (sb * mu ^ p ^ e * ι t) by group]
    rw [(hBB' (mu * ι t) (sb * mu ^ p ^ e * ι s)).eq]
    group
  let T : Subgroup G := fixedPointsIn X S
  let xa : K → T := fun s => ⟨Xa s, mem_fixedPointsIn.2 ⟨hXa_mem s, hXa_fix s⟩⟩
  let xb : K → T := fun s => ⟨Xb s, mem_fixedPointsIn.2 ⟨hXb_mem s, hXb_fix s⟩⟩
  let z : K → T := fun r => ⁅xa r, xb 1⁆
  have hxa_def : ∀ s, (xa s : G) = Xa s := fun s => rfl
  have hxb_def : ∀ s, (xb s : G) = Xb s := fun s => rfl
  have hz_def : ∀ r, (z r : G) = ⁅Xa r, Xb 1⁆ := by
    intro r
    show ((⁅xa r, xb 1⁆ : T) : G) = ⁅Xa r, Xb 1⁆
    simp [commutatorElement_def, hxa_def, hxb_def]
  have hz_formula : ∀ r, (z r : G) =
      C (lam * mu * ι r) * C' (sa * sb * (lam * mu) ^ p ^ e * ι r) := by
    intro r
    rw [hz_def]
    simpa using hXcomm r 1
  have hxa_add : ∀ s t, xa (s + t) = xa s * xa t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxa_def, hxa_def, hxa_def]
    exact hXa_add s t
  have hxb_add : ∀ s t, xb (s + t) = xb s * xb t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxb_def, hxb_def, hxb_def]
    exact hXb_add s t
  have hz_add : ∀ s t, z (s + t) = z s * z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    simp only [hz_formula]
    have e1 : lam * mu * ι (s + t) = lam * mu * ι s + lam * mu * ι t := by
      rw [map_add]; ring
    have e2 : sa * sb * (lam * mu) ^ p ^ e * ι (s + t) =
        sa * sb * (lam * mu) ^ p ^ e * ι s + sa * sb * (lam * mu) ^ p ^ e * ι t := by
      rw [map_add]; ring
    rw [e1, e2, hC, hC']
    have hcomm : C (lam * mu * ι t) * C' (sa * sb * (lam * mu) ^ p ^ e * ι s) =
        C' (sa * sb * (lam * mu) ^ p ^ e * ι s) * C (lam * mu * ι t) :=
      (hCC' (lam * mu * ι t) (sa * sb * (lam * mu) ^ p ^ e * ι s)).eq
    calc C (lam * mu * ι s) * C (lam * mu * ι t) *
          (C' (sa * sb * (lam * mu) ^ p ^ e * ι s) *
            C' (sa * sb * (lam * mu) ^ p ^ e * ι t))
        = C (lam * mu * ι s) *
          (C (lam * mu * ι t) * C' (sa * sb * (lam * mu) ^ p ^ e * ι s)) *
          C' (sa * sb * (lam * mu) ^ p ^ e * ι t) := by group
      _ = C (lam * mu * ι s) *
          (C' (sa * sb * (lam * mu) ^ p ^ e * ι s) * C (lam * mu * ι t)) *
          C' (sa * sb * (lam * mu) ^ p ^ e * ι t) := by rw [hcomm]
      _ = C (lam * mu * ι s) * C' (sa * sb * (lam * mu) ^ p ^ e * ι s) *
          (C (lam * mu * ι t) * C' (sa * sb * (lam * mu) ^ p ^ e * ι t)) := by group
  have hz_inj : Function.Injective z := by
    intro r r' hrr
    have hδ : z (r - r') = 1 := by
      have h1 : z r' * z (r - r') = z r' * 1 := by
        have h2 : r' + (r - r') = r := by ring
        rw [mul_one, ← hz_add, h2, hrr]
      exact mul_left_cancel h1
    have hG : (z (r - r') : G) = 1 := by rw [hδ]; rfl
    rw [hz_formula] at hG
    have hc : lam * mu * ι (r - r') = 0 := hCinj _ _ hG
    have hlm : lam * mu ≠ 0 := mul_ne_zero hlam0 hmu0
    have hιδ : ι (r - r') = 0 := (mul_eq_zero.mp hc).resolve_left hlm
    have hδ0 : r - r' = 0 := by
      apply hι_inj
      rw [hιδ, map_zero]
    exact sub_eq_zero.mp hδ0
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := by
    intro s t
    apply Subtype.ext
    rw [show ((⁅xa s, xb t⁆ : T) : G) = ⁅(xa s : G), (xb t : G)⁆ from by
      simp [commutatorElement_def]]
    rw [hxa_def, hxb_def, hz_formula]
    exact hXcomm s t
  have hza : ∀ s t, Commute (z s) (xa t) := by
    intro s t
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hz_formula, hxa_def]
    have h1 : Commute (C (lam * mu * ι s)) (Xa t) := by
      rw [hXa_def]
      exact (hCA _ _).mul_right (hCA' _ _)
    have h2 : Commute (C' (sa * sb * (lam * mu) ^ p ^ e * ι s)) (Xa t) := by
      rw [hXa_def]
      exact (hC'A _ _).mul_right (hC'A' _ _)
    exact (h1.mul_left h2).eq
  have hzb : ∀ s t, Commute (z s) (xb t) := by
    intro s t
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hz_formula, hxb_def]
    have h1 : Commute (C (lam * mu * ι s)) (Xb t) := by
      rw [hXb_def]
      exact (hCB _ _).mul_right (hCB' _ _)
    have h2 : Commute (C' (sa * sb * (lam * mu) ^ p ^ e * ι s)) (Xb t) := by
      rw [hXb_def]
      exact (hC'B _ _).mul_right (hC'B' _ _)
    exact (h1.mul_left h2).eq
  have hspec := isSpecialGood_of_comm (K := K) (S := T) hp hp2 hK h3 hxa_add hxb_add
    hz_add hz_inj hab hza hzb (1 : K)
  have hxb0 : xb 0 = 1 := CFSG.map_zero_of_map_add hxb_add
  have hxapow : ∀ n : ℕ, xb (n : K) = (xb 1) ^ n := by
    intro n
    induction n with
    | zero => simpa using hxb0
    | succ n ih =>
        have hcast : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
        rw [hcast, hxb_add, ih, pow_succ]
  have hup : (xb 1) ^ p = 1 := by
    rw [← hxapow p, show (p : K) = 0 from CharP.cast_eq_zero K p, hxb0]
  have hu_ne : xb 1 ≠ 1 := by
    intro h
    have hxa0 : xa 0 = 1 := CFSG.map_zero_of_map_add hxa_add
    have hz1 : z 1 = 1 := by
      change ⁅xa 1, xb 1⁆ = 1
      rw [h]
      simp [commutatorElement_def]
    have hz0 : z 0 = 1 := by
      change ⁅xa 0, xb 1⁆ = 1
      rw [hxa0]
      simp [commutatorElement_def]
    have h10 : (1 : K) = 0 := hz_inj (hz1.trans hz0.symm)
    exact one_ne_zero h10
  refine ⟨xb 1, ?_, orderOf_eq_prime hup hu_ne, hspec.2.1⟩
  rw [hxb_def, hXb_def]
  simp

theorem exists_pair_heis_inv_good {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) {A A' B B' C C' : k → G}
    (hA : ∀ c d, A (c + d) = A c * A d) (hA' : ∀ c d, A' (c + d) = A' c * A' d)
    (hB : ∀ c d, B (c + d) = B c * B d) (hB' : ∀ c d, B' (c + d) = B' c * B' d)
    (hC : ∀ c d, C (c + d) = C c * C d) (hC' : ∀ c d, C' (c + d) = C' c * C' d)
    (hAX : ∀ c, A c ∈ X) (hA'X : ∀ c, A' c ∈ X) (hBX : ∀ c, B c ∈ X) (hB'X : ∀ c, B' c ∈ X)
    {sa sa' sb sb' : k} (hsa : sa * sa = 1) (hsa' : sa' * sa' = 1) (hsb : sb * sb = 1)
    (hsb' : sb' * sb' = 1)
    (hSA : ∀ c, S (A c) = A' (sa * c ^ p ^ e)) (hSA' : ∀ c, S (A' c) = A (sa' * c ^ p ^ e))
    (hSB : ∀ c, S (B c) = B' (sb * c ^ p ^ e)) (hSB' : ∀ c, S (B' c) = B (sb' * c ^ p ^ e))
    (hAA' : ∀ c d, Commute (A c) (A' d)) (hBB' : ∀ c d, Commute (B c) (B' d))
    (hAB' : ∀ c d, Commute (A c) (B' d)) (hA'B : ∀ c d, Commute (A' c) (B d))
    (hAB : ∀ c d, ⁅A c, B d⁆ = C (c * d)) (hA'B' : ∀ c d, ⁅A' c, B' d⁆ = C' (c * d))
    (hCA : ∀ c d, Commute (C c) (A d)) (hCA' : ∀ c d, Commute (C c) (A' d))
    (hCB : ∀ c d, Commute (C c) (B d)) (hCB' : ∀ c d, Commute (C c) (B' d))
    (hC'A : ∀ c d, Commute (C' c) (A d)) (hC'A' : ∀ c d, Commute (C' c) (A' d))
    (hC'B : ∀ c d, Commute (C' c) (B d)) (hC'B' : ∀ c d, Commute (C' c) (B' d))
    (hCC' : ∀ c d, Commute (C c) (C' d)) (hCinj : ∀ c d, C c * C' d = 1 → c = 0)
    {t : G} (htB : ∀ c, t * B c * t⁻¹ = B (-c)) (htB' : ∀ c, t * B' c * t⁻¹ = B' (-c)) :
    ∃ u : fixedPointsIn X S, orderOf u = p ∧ IsSpecialGood p u ∧
      t * (u : G) * t⁻¹ = (u : G)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < (p ^ e) ^ 2 - 1 := by
    have h2 : 1 < (p ^ e) ^ 2 := by nlinarith
    omega
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq (sb * sb') (n := (p ^ e) ^ 2 - 1) hpos
  have hsb0 : sb ≠ 0 := by rintro rfl; simp at hsb
  have hsb'0 : sb' ≠ 0 := by rintro rfl; simp at hsb'
  have hκb : sb * sb' ≠ 0 := mul_ne_zero hsb0 hsb'0
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hmu
    exact hκb hmu.symm
  have hmu_q : (mu ^ p ^ e) ^ p ^ e = mu * (sb * sb') := by
    rw [← pow_mul]
    have h2' : 1 ≤ (p ^ e) * (p ^ e) := by nlinarith
    have hqq : (p ^ e) * (p ^ e) = ((p ^ e) ^ 2 - 1) + 1 := by
      rw [pow_two (p ^ e)]
      exact (Nat.sub_add_cancel h2').symm
    rw [hqq, pow_succ, hmu, mul_comm]
  obtain ⟨u, hu, hord, hspec⟩ :=
    exists_pair_heis_good_of_mu (X := X) (S := S) (ι := ι) (p := p) (e := e) (A := A)
      (A' := A') (B := B) (B' := B') (C := C) (C' := C') (sa := sa) (sa' := sa') (sb := sb)
      (sb' := sb') hp hp2 hK h3 hA hA' hB hB' hC hC' hAX hA'X hBX hB'X hsa hsa' hsb hsb'
      hSA hSA' hSB hSB' hAA' hBB' hAB' hA'B hAB hA'B' hCA hCA' hCB hCB' hC'A hC'A' hC'B
      hC'B' hCC' hCinj hmu0 hmu_q
  have hBinv : ∀ c, B (-c) = (B c)⁻¹ := by
    intro c
    exact eq_inv_of_mul_eq_one_left (by rw [← hB, neg_add_cancel, CFSG.map_zero_of_map_add hB])
  have hB'inv : ∀ c, B' (-c) = (B' c)⁻¹ := by
    intro c
    exact eq_inv_of_mul_eq_one_left (by rw [← hB', neg_add_cancel, CFSG.map_zero_of_map_add hB'])
  have ht : t * (u : G) * t⁻¹ = (u : G)⁻¹ := by
    rw [hu]
    calc t * (B mu * B' (sb * mu ^ p ^ e)) * t⁻¹
        = (t * B mu * t⁻¹) * (t * B' (sb * mu ^ p ^ e) * t⁻¹) := by group
      _ = (B mu)⁻¹ * (B' (sb * mu ^ p ^ e))⁻¹ := by rw [htB, htB', hBinv, hB'inv]
      _ = (B mu * B' (sb * mu ^ p ^ e))⁻¹ := by
            rw [mul_inv_rev]
            exact ((hBB' mu (sb * mu ^ p ^ e)).inv_left.inv_right).eq
  exact ⟨u, hord, hspec, ht⟩

theorem exists_fixed_heis_inv_good {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) {A B C : k → G}
    (hA : ∀ c d, A (c + d) = A c * A d) (hB : ∀ c d, B (c + d) = B c * B d)
    (hC : ∀ c d, C (c + d) = C c * C d) (hAX : ∀ c, A c ∈ X) (hBX : ∀ c, B c ∈ X)
    {sa sb : k} (hsa : sa * sa = 1) (hsb : sb * sb = 1)
    (hSA : ∀ c, S (A c) = A (sa * c ^ p ^ e)) (hSB : ∀ c, S (B c) = B (sb * c ^ p ^ e))
    (hAB : ∀ c d, ⁅A c, B d⁆ = C (c * d))
    (hCA : ∀ c d, Commute (C c) (A d)) (hCB : ∀ c d, Commute (C c) (B d))
    (hCinj : ∀ c, C c = 1 → c = 0) {t : G} (htB : ∀ c, t * B c * t⁻¹ = B (-c)) :
    ∃ u : fixedPointsIn X S, orderOf u = p ∧ IsSpecialGood p u ∧
      t * (u : G) * t⁻¹ = (u : G)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card K = p ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  have hιpow : ∀ s : K, (ι s) ^ p ^ e = ι s := by
    intro s
    rw [← map_pow, ← hcard]
    exact congrArg ι (FiniteField.pow_card s)
  have hι_inj : Function.Injective ι := ι.injective
  have hq1 : 0 < p ^ e - 1 := by omega
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq sa (n := p ^ e - 1) hq1
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq sb (n := p ^ e - 1) hq1
  have hsa0 : sa ≠ 0 := by rintro rfl; simp at hsa
  have hsb0 : sb ≠ 0 := by rintro rfl; simp at hsb
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow hq1.ne'] at hlam
    exact hsa0 hlam.symm
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow hq1.ne'] at hmu
    exact hsb0 hmu.symm
  have hlam_q : lam ^ p ^ e = lam * sa := by
    rw [show p ^ e = (p ^ e - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ, hlam,
      mul_comm]
  have hmu_q : mu ^ p ^ e = mu * sb := by
    rw [show p ^ e = (p ^ e - 1) + 1 from (Nat.sub_add_cancel (by omega)).symm, pow_succ, hmu,
      mul_comm]
  let Xa : K → G := fun s => A (lam * ι s)
  let Xb : K → G := fun s => B (mu * ι s)
  have hXa_def : ∀ s, Xa s = A (lam * ι s) := fun s => rfl
  have hXb_def : ∀ s, Xb s = B (mu * ι s) := fun s => rfl
  have hXa_mem : ∀ s, Xa s ∈ X := fun s => hAX _
  have hXb_mem : ∀ s, Xb s ∈ X := fun s => hBX _
  have hXa_fix : ∀ s, S (Xa s) = Xa s := by
    intro s
    rw [hXa_def]
    exact fixed_one S hsa hSA hlam_q (hιpow s)
  have hXb_fix : ∀ s, S (Xb s) = Xb s := by
    intro s
    rw [hXb_def]
    exact fixed_one S hsb hSB hmu_q (hιpow s)
  have hXa_add : ∀ s t, Xa (s + t) = Xa s * Xa t := by
    intro s t
    simp only [hXa_def]
    rw [map_add, mul_add, hA]
  have hXb_add : ∀ s t, Xb (s + t) = Xb s * Xb t := by
    intro s t
    simp only [hXb_def]
    rw [map_add, mul_add, hB]
  let T : Subgroup G := fixedPointsIn X S
  let xa : K → T := fun s => ⟨Xa s, mem_fixedPointsIn.2 ⟨hXa_mem s, hXa_fix s⟩⟩
  let xb : K → T := fun s => ⟨Xb s, mem_fixedPointsIn.2 ⟨hXb_mem s, hXb_fix s⟩⟩
  let z : K → T := fun r => ⁅xa r, xb 1⁆
  have hxa_def : ∀ s, (xa s : G) = Xa s := fun s => rfl
  have hxb_def : ∀ s, (xb s : G) = Xb s := fun s => rfl
  have hz_def : ∀ r, (z r : G) = ⁅Xa r, Xb 1⁆ := by
    intro r
    show ((⁅xa r, xb 1⁆ : T) : G) = ⁅Xa r, Xb 1⁆
    simp [commutatorElement_def, hxa_def, hxb_def]
  have hz_formula : ∀ r, (z r : G) = C (lam * mu * ι r) := by
    intro r
    rw [hz_def]
    show ⁅Xa r, Xb 1⁆ = C (lam * mu * ι r)
    rw [hXa_def, hXb_def, hAB]
    congr 1
    rw [map_one, mul_one]
    ring
  have hxa_add : ∀ s t, xa (s + t) = xa s * xa t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxa_def, hxa_def, hxa_def]
    exact hXa_add s t
  have hxb_add : ∀ s t, xb (s + t) = xb s * xb t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxb_def, hxb_def, hxb_def]
    exact hXb_add s t
  have hz_add : ∀ s t, z (s + t) = z s * z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    simp only [hz_formula]
    rw [map_add, mul_add, hC]
  have hz_inj : Function.Injective z := by
    intro r r' hrr
    have hδ : z (r - r') = 1 := by
      have h1 : z r' * z (r - r') = z r' * 1 := by
        have h2 : r' + (r - r') = r := by ring
        rw [mul_one, ← hz_add, h2, hrr]
      exact mul_left_cancel h1
    have hG : (z (r - r') : G) = 1 := by rw [hδ]; rfl
    rw [hz_formula] at hG
    have hc : lam * mu * ι (r - r') = 0 := hCinj _ hG
    have hlm : lam * mu ≠ 0 := mul_ne_zero hlam0 hmu0
    have hιδ : ι (r - r') = 0 := (mul_eq_zero.mp hc).resolve_left hlm
    have hδ0 : r - r' = 0 := by
      apply hι_inj
      rw [hιδ, map_zero]
    exact sub_eq_zero.mp hδ0
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := by
    intro s t
    apply Subtype.ext
    rw [show ((⁅xa s, xb t⁆ : T) : G) = ⁅(xa s : G), (xb t : G)⁆ from by
      simp [commutatorElement_def]]
    rw [hxa_def, hxb_def, hz_formula, hAB]
    congr 1
    rw [map_mul]
    ring
  have hza : ∀ s t, Commute (z s) (xa t) := by
    intro s t
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hz_formula, hxa_def]
    exact (hCA (lam * mu * ι s) (lam * ι t)).eq
  have hzb : ∀ s t, Commute (z s) (xb t) := by
    intro s t
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hz_formula, hxb_def]
    exact (hCB (lam * mu * ι s) (mu * ι t)).eq
  have hspec := isSpecialGood_of_comm (K := K) (S := T) hp hp2 hK h3 hxa_add hxb_add
    hz_add hz_inj hab hza hzb (1 : K)
  have hxb0 : xb 0 = 1 := CFSG.map_zero_of_map_add hxb_add
  have hxapow : ∀ n : ℕ, xb (n : K) = (xb 1) ^ n := by
    intro n
    induction n with
    | zero => simpa using hxb0
    | succ n ih =>
        have hcast : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
        rw [hcast, hxb_add, ih, pow_succ]
  have hup : (xb 1) ^ p = 1 := by
    rw [← hxapow p, show (p : K) = 0 from CharP.cast_eq_zero K p, hxb0]
  have hu_ne : xb 1 ≠ 1 := by
    intro h
    have hxa0 : xa 0 = 1 := CFSG.map_zero_of_map_add hxa_add
    have hz1 : z 1 = 1 := by
      change ⁅xa 1, xb 1⁆ = 1
      rw [h]
      simp [commutatorElement_def]
    have hz0 : z 0 = 1 := by
      change ⁅xa 0, xb 1⁆ = 1
      rw [hxa0]
      simp [commutatorElement_def]
    have h10 : (1 : K) = 0 := hz_inj (hz1.trans hz0.symm)
    exact one_ne_zero h10
  have hBinv : ∀ c, B (-c) = (B c)⁻¹ := by
    intro c
    exact eq_inv_of_mul_eq_one_left (by rw [← hB, neg_add_cancel, CFSG.map_zero_of_map_add hB])
  have huG : ((xb 1 : T) : G) = B mu := by
    rw [hxb_def, hXb_def]
    simp
  refine ⟨xb 1, orderOf_eq_prime hup hu_ne, hspec.2.1, ?_⟩
  calc t * ((xb 1 : T) : G) * t⁻¹ = t * B mu * t⁻¹ := by rw [huG]
    _ = B (-mu) := htB mu
    _ = (B mu)⁻¹ := hBinv mu
    _ = (((xb 1 : T) : G))⁻¹ := by rw [huG]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
