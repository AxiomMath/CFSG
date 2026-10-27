module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcRootPair
import CFSG.Mathlib.Algebra.MapAdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.AlgebraicGroups (fixedPointsIn mem_fixedPointsIn)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open scoped commutatorElement

private theorem twHeis_pair_fixed {G k : Type*} [Group G] [Field k] (S : G →* G)
    {B B' : k → G} {sb sb' lam : k} (hsb : sb * sb = 1) (hsb' : sb' * sb' = 1)
    (hSB : ∀ c, S (B c) = B' (sb * c ^ 3)) (hSB' : ∀ c, S (B' c) = B (sb' * c ^ 3))
    (hBB' : ∀ c d, Commute (B c) (B' d)) (hlam : lam ^ 9 = lam * (sb * sb'))
    {i : k} (hi : i ^ 3 = i) :
    S (B (lam * i) * B' (sb * lam ^ 3 * i)) = B (lam * i) * B' (sb * lam ^ 3 * i) := by
  have hcq : sb * (lam * i) ^ 3 = sb * lam ^ 3 * i := by
    rw [mul_pow, hi]
    ring
  have hsb3 : sb ^ 3 = sb := by rw [pow_succ, sq, hsb, one_mul]
  have hdq : (sb * lam ^ 3 * i) ^ 3 = sb * lam ^ 9 * i := by
    rw [mul_pow, mul_pow, hi, hsb3, ← pow_mul]
  have harg : sb' * (sb * lam ^ 9 * i) = lam * i := by
    rw [hlam]
    have hκ : sb' * sb * (sb * sb') = 1 := by
      calc sb' * sb * (sb * sb') = (sb' * sb') * (sb * sb) := by ring
        _ = 1 := by rw [hsb', hsb, mul_one]
    rw [show sb' * (sb * (lam * (sb * sb')) * i) = (sb' * sb * (sb * sb')) * (lam * i) by
      ring, hκ, one_mul]
  rw [map_mul, hSB, hSB', hcq, hdq, harg]
  exact (hBB' (lam * i) (sb * lam ^ 3 * i)).eq.symm

private theorem twHeis_commutator_mul {G k : Type*} [Group G] [Field k] {B B' D D' E : k → G}
    {n n' : k} (hB'D : ∀ c d, Commute (B' c) (D d)) (hBD' : ∀ c d, Commute (B c) (D' d))
    (hE : ∀ c d, E (c + d) = E c * E d)
    (hBD : ∀ c d, ⁅B c, D d⁆ = E (n * (c * d)))
    (hB'D' : ∀ c d, ⁅B' c, D' d⁆ = E (n' * (c * d)))
    (hEB : ∀ c d, Commute (E c) (B d)) (hEB' : ∀ c d, Commute (E c) (B' d))
    (hED : ∀ c d, Commute (E c) (D d)) (hED' : ∀ c d, Commute (E c) (D' d))
    (c₁ b₁ c₂ d₂ : k) :
    ⁅B c₁ * B' b₁, D c₂ * D' d₂⁆ = E (n * (c₁ * c₂) + n' * (b₁ * d₂)) := by
  have hcbd : Commute (D c₂) ⁅B' b₁, D' d₂⁆ := by
    rw [hB'D']
    exact (hED _ _).symm
  have habd : Commute (B c₁) ⁅B' b₁, D' d₂⁆ := by
    rw [hB'D']
    exact (hEB _ _).symm
  have hcomm : Commute ⁅B c₁, D c₂⁆ ⁅B' b₁, D' d₂⁆ := by
    have h1 : Commute (E (n * (c₁ * c₂))) (B' b₁) := hEB' _ _
    have h2 : Commute (E (n * (c₁ * c₂))) (D' d₂) := hED' _ _
    have h3 := ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
    rw [hBD, commutatorElement_def]
    exact h3
  have h := TauCeti.commutatorElement_mul_mul_eq_mul_of_commute (a := B c₁) (b := B' b₁)
    (c := D c₂) (d := D' d₂) (hB'D b₁ c₂) (hBD' c₁ d₂) hcbd habd hcomm
  rw [h, hBD, hB'D', ← hE]

private theorem twHeis_scalar_zero {k : Type*} [Field k] {n n' sb sd se nu e : k}
    (hnrel : n' * (sb * sd) = se * n) (hse : se * se = 1) (hnu : nu * nu = se)
    (he : e * e = -1) :
    n * (e * nu) + n' * (sb * sd) * (e * nu) ^ 3 = 0 := by
  have he3 : e ^ 3 = -e := by
    have h : e ^ 3 = e * (e * e) := by ring
    rw [h, he]
    ring
  have hnu3 : nu ^ 3 = nu * se := by
    have h : nu ^ 3 = nu * (nu * nu) := by ring
    rw [h, hnu]
  have hcube : (e * nu) ^ 3 = -(e * (nu * se)) := by
    rw [mul_pow, he3, hnu3]
    ring
  rw [hcube, hnrel,
    show (se * n) * (-(e * (nu * se))) = -(n * e * nu * (se * se)) by ring, hse, mul_one]
  ring

theorem exists_heis_fixed {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] (ι : K →+* k) (hK : Nat.card K = 3)
    {A B C : k → G} (hA : ∀ c d, A (c + d) = A c * A d) (hB : ∀ c d, B (c + d) = B c * B d)
    (hC : ∀ c d, C (c + d) = C c * C d) (hAX : ∀ c, A c ∈ X) (hBX : ∀ c, B c ∈ X)
    {sa sb : k} (hsa : sa * sa = 1) (hsb : sb * sb = 1)
    (hSA : ∀ c, S (A c) = A (sa * c ^ 3)) (hSB : ∀ c, S (B c) = B (sb * c ^ 3))
    (hAB : ∀ c d, ⁅A c, B d⁆ = C (c * d)) (hCA : ∀ c d, Commute (C c) (A d))
    (hCB : ∀ c d, Commute (C c) (B d)) (hCinj : ∀ c, C c = 1 → c = 0)
    {la lb : k} (hla : la * la = sa) (hlb : lb * lb = sb) :
    ∃ ι' : Heis K →* fixedPointsIn X S, Function.Injective ι' ∧
      (∀ r, (ι' ⟨r, 0, 0⟩ : G) = A (la * ι r)) ∧ (∀ r, (ι' ⟨0, r, 0⟩ : G) = B (lb * ι r)) ∧
      ∀ r, (ι' ⟨0, 0, r⟩ : G) = C (la * lb * ι r) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ r : K, r ^ 3 = r := by
    intro r
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card r
  have hιpow : ∀ r : K, (ι r) ^ 3 = ι r := fun r => by rw [← map_pow, hpow r]
  have hsa0 : sa ≠ 0 := by rintro rfl; simp at hsa
  have hsb0 : sb ≠ 0 := by rintro rfl; simp at hsb
  have hla0 : la ≠ 0 := by rintro rfl; exact hsa0 (by simpa using hla.symm)
  have hlb0 : lb ≠ 0 := by rintro rfl; exact hsb0 (by simpa using hlb.symm)
  have hla3 : sa * la ^ 3 = la := by
    rw [show la ^ 3 = la * la * la from by ring, hla, ← mul_assoc, hsa, one_mul]
  have hlb3 : sb * lb ^ 3 = lb := by
    rw [show lb ^ 3 = lb * lb * lb from by ring, hlb, ← mul_assoc, hsb, one_mul]
  have hAfix : ∀ r : K, S (A (la * ι r)) = A (la * ι r) := by
    intro r
    rw [hSA, mul_pow, hιpow r, ← mul_assoc, hla3]
  have hBfix : ∀ r : K, S (B (lb * ι r)) = B (lb * ι r) := by
    intro r
    rw [hSB, mul_pow, hιpow r, ← mul_assoc, hlb3]
  have hBfix1 : S (B lb) = B lb := by simpa using hBfix 1
  have hCeq : ∀ r : K, C (la * lb * ι r) = ⁅A (la * ι r), B lb⁆ := by
    intro r
    rw [hAB]
    congr 1
    ring
  have hCmem : ∀ r : K, C (la * lb * ι r) ∈ X := by
    intro r
    rw [hCeq r, commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem (hAX _) (hBX _)) (X.inv_mem (hAX _)))
      (X.inv_mem (hBX _))
  have hCfix : ∀ r : K, S (C (la * lb * ι r)) = C (la * lb * ι r) := by
    intro r
    conv_lhs => rw [hCeq r]
    rw [map_commutatorElement, hAfix r, hBfix1, hCeq r]
  let T : Subgroup G := fixedPointsIn X S
  let xa : K → T := fun r => ⟨A (la * ι r), mem_fixedPointsIn.2 ⟨hAX _, hAfix r⟩⟩
  let xb : K → T := fun r => ⟨B (lb * ι r), mem_fixedPointsIn.2 ⟨hBX _, hBfix r⟩⟩
  let z : K → T := fun r => ⟨C (la * lb * ι r), mem_fixedPointsIn.2 ⟨hCmem r, hCfix r⟩⟩
  have hxa_def : ∀ r, (xa r : G) = A (la * ι r) := fun r => rfl
  have hxb_def : ∀ r, (xb r : G) = B (lb * ι r) := fun r => rfl
  have hz_def : ∀ r, (z r : G) = C (la * lb * ι r) := fun r => rfl
  have hxa_add : ∀ s t, xa (s + t) = xa s * xa t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxa_def, hxa_def, hxa_def, map_add, mul_add, hA]
  have hxb_add : ∀ s t, xb (s + t) = xb s * xb t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxb_def, hxb_def, hxb_def, map_add, mul_add, hB]
  have hz_add : ∀ s t, z (s + t) = z s * z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hz_def, hz_def, hz_def, map_add, mul_add, hC]
  have hcoe : ∀ s t, ((⁅xa s, xb t⁆ : T) : G) = ⁅(xa s : G), (xb t : G)⁆ :=
    fun s t => by simp [commutatorElement_def]
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := by
    intro s t
    apply Subtype.ext
    rw [hcoe, hxa_def, hxb_def, hz_def, hAB]
    congr 1
    rw [map_mul]
    ring
  have hza : ∀ s t, Commute (z s) (xa t) := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz_def, hxa_def]
    exact (hCA _ _).eq
  have hzb : ∀ s t, Commute (z s) (xb t) := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz_def, hxb_def]
    exact (hCB _ _).eq
  have hz_inj : Function.Injective z := by
    intro r r' hrr
    have hz1 : z (r - r') = 1 := by
      have h2 : r' + (r - r') = r := by ring
      have h3 : z r' * z (r - r') = z r' * 1 := by rw [mul_one, ← hz_add, h2, hrr]
      exact mul_left_cancel h3
    have hG : (z (r - r') : G) = 1 := by rw [hz1]; rfl
    rw [hz_def] at hG
    have hc : la * lb * ι (r - r') = 0 := hCinj _ hG
    have hlm : la * lb ≠ 0 := mul_ne_zero hla0 hlb0
    have hι0 : ι (r - r') = 0 := (mul_eq_zero.mp hc).resolve_left hlm
    have h0 : r - r' = 0 := by
      apply ι.injective
      rw [hι0, map_zero]
    exact sub_eq_zero.mp h0
  obtain ⟨φ, hφ, ha, hb, hc⟩ :=
    exists_heis_of_comm (K := K) (S := T) hxa_add hxb_add hz_add hz_inj hab hza hzb
  exact ⟨φ, hφ, fun r => by rw [ha r, hxa_def], fun r => by rw [hb r, hxb_def],
    fun r => by rw [hc r, hz_def]⟩

theorem exists_heis_orbit_two {G : Type*} [Group G] (X : Subgroup G) (S : G →* G)
    {K k : Type*} [Field K] [Finite K] [Field k] (ι : K →+* k) (hK : Nat.card K = 3)
    {B B' D D' E : k → G} (hB : ∀ c d, B (c + d) = B c * B d)
    (hB' : ∀ c d, B' (c + d) = B' c * B' d) (hD : ∀ c d, D (c + d) = D c * D d)
    (hD' : ∀ c d, D' (c + d) = D' c * D' d) (hE : ∀ c d, E (c + d) = E c * E d)
    (hBX : ∀ c, B c ∈ X) (hB'X : ∀ c, B' c ∈ X) (hDX : ∀ c, D c ∈ X) (hD'X : ∀ c, D' c ∈ X)
    {sb sb' sd sd' : k} (hsb : sb * sb = 1) (hsb' : sb' * sb' = 1) (hsd : sd * sd = 1)
    (hsd' : sd' * sd' = 1)
    (hSB : ∀ c, S (B c) = B' (sb * c ^ 3)) (hSB' : ∀ c, S (B' c) = B (sb' * c ^ 3))
    (hSD : ∀ c, S (D c) = D' (sd * c ^ 3)) (hSD' : ∀ c, S (D' c) = D (sd' * c ^ 3))
    (hBB' : ∀ c d, Commute (B c) (B' d)) (hDD' : ∀ c d, Commute (D c) (D' d))
    (hBD' : ∀ c d, Commute (B c) (D' d)) (hB'D : ∀ c d, Commute (B' c) (D d))
    {n n' : k} (hBD : ∀ c d, ⁅B c, D d⁆ = E (n * (c * d)))
    (hB'D' : ∀ c d, ⁅B' c, D' d⁆ = E (n' * (c * d)))
    (hEB : ∀ c d, Commute (E c) (B d)) (hEB' : ∀ c d, Commute (E c) (B' d))
    (hED : ∀ c d, Commute (E c) (D d)) (hED' : ∀ c d, Commute (E c) (D' d))
    (hEinj : ∀ c, E c = 1 → c = 0) {lam mu : k} (hlam : lam ^ 9 = lam * (sb * sb'))
    (hmu : mu ^ 9 = mu * (sd * sd'))
    (hw : n * (lam * mu) + n' * (sb * sd) * (lam * mu) ^ 3 ≠ 0) :
    ∃ ι' : Heis K →* fixedPointsIn X S, Function.Injective ι' ∧
      (∀ r, (ι' ⟨r, 0, 0⟩ : G) = B (lam * ι r) * B' (sb * lam ^ 3 * ι r)) ∧
      (∀ r, (ι' ⟨0, r, 0⟩ : G) = D (mu * ι r) * D' (sd * mu ^ 3 * ι r)) ∧
      ∀ r, (ι' ⟨0, 0, r⟩ : G) =
        E ((n * (lam * mu) + n' * (sb * sd) * (lam * mu) ^ 3) * ι r) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ r : K, r ^ 3 = r := by
    intro r
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card r
  have hιpow : ∀ r : K, (ι r) ^ 3 = ι r := fun r => by rw [← map_pow, hpow r]
  let Y : K → G := fun r => B (lam * ι r) * B' (sb * lam ^ 3 * ι r)
  let Z : K → G := fun r => D (mu * ι r) * D' (sd * mu ^ 3 * ι r)
  let w : k := n * (lam * mu) + n' * (sb * sd) * (lam * mu) ^ 3
  have hY_add : ∀ s t, Y (s + t) = Y s * Y t := by
    intro s t
    simp only [Y]
    rw [map_add, mul_add, mul_add, hB, hB']
    rw [show B (lam * ι s) * B (lam * ι t) *
          (B' (sb * lam ^ 3 * ι s) * B' (sb * lam ^ 3 * ι t)) =
        B (lam * ι s) * (B (lam * ι t) * B' (sb * lam ^ 3 * ι s)) *
          B' (sb * lam ^ 3 * ι t) by group]
    rw [(hBB' (lam * ι t) (sb * lam ^ 3 * ι s)).eq]
    group
  have hZ_add : ∀ s t, Z (s + t) = Z s * Z t := by
    intro s t
    simp only [Z]
    rw [map_add, mul_add, mul_add, hD, hD']
    rw [show D (mu * ι s) * D (mu * ι t) *
          (D' (sd * mu ^ 3 * ι s) * D' (sd * mu ^ 3 * ι t)) =
        D (mu * ι s) * (D (mu * ι t) * D' (sd * mu ^ 3 * ι s)) *
          D' (sd * mu ^ 3 * ι t) by group]
    rw [(hDD' (mu * ι t) (sd * mu ^ 3 * ι s)).eq]
    group
  have hY_fix : ∀ r, S (Y r) = Y r := by
    intro r
    have h := twHeis_pair_fixed S hsb hsb' hSB hSB' hBB' hlam (hιpow r)
    simpa only [Y] using h
  have hZ_fix : ∀ r, S (Z r) = Z r := by
    intro r
    have h := twHeis_pair_fixed S hsd hsd' hSD hSD' hDD' hmu (hιpow r)
    simpa only [Z] using h
  have hY_mem : ∀ r, Y r ∈ X := fun r => X.mul_mem (hBX _) (hB'X _)
  have hZ_mem : ∀ r, Z r ∈ X := fun r => X.mul_mem (hDX _) (hD'X _)
  let T : Subgroup G := fixedPointsIn X S
  let xa : K → T := fun r => ⟨Y r, mem_fixedPointsIn.2 ⟨hY_mem r, hY_fix r⟩⟩
  let xb : K → T := fun r => ⟨Z r, mem_fixedPointsIn.2 ⟨hZ_mem r, hZ_fix r⟩⟩
  let z : K → T := fun r => ⁅xa r, xb 1⁆
  have hxa_def : ∀ r, (xa r : G) = Y r := fun r => rfl
  have hxb_def : ∀ r, (xb r : G) = Z r := fun r => rfl
  have hcoe : ∀ s t, ((⁅xa s, xb t⁆ : T) : G) = ⁅(xa s : G), (xb t : G)⁆ :=
    fun s t => by simp [commutatorElement_def]
  have hZ1 : (xb 1 : G) = D mu * D' (sd * mu ^ 3) := by
    show D (mu * ι 1) * D' (sd * mu ^ 3 * ι 1) = D mu * D' (sd * mu ^ 3)
    simp
  have hz_formula : ∀ r, (z r : G) = E (w * ι r) := by
    intro r
    rw [hcoe, hxa_def, hZ1]
    simp only [Y]
    rw [twHeis_commutator_mul hB'D hBD' hE hBD hB'D' hEB hEB' hED hED' (lam * ι r)
      (sb * lam ^ 3 * ι r) mu (sd * mu ^ 3)]
    congr 1
    simp only [w]
    ring
  have hxa_add : ∀ s t, xa (s + t) = xa s * xa t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxa_def, hxa_def, hxa_def]
    exact hY_add s t
  have hxb_add : ∀ s t, xb (s + t) = xb s * xb t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hxb_def, hxb_def, hxb_def]
    exact hZ_add s t
  have hz_add : ∀ s t, z (s + t) = z s * z t := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, hz_formula, hz_formula, hz_formula, map_add, mul_add, hE]
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := by
    intro s t
    apply Subtype.ext
    rw [hcoe, hxa_def, hxb_def, hz_formula]
    simp only [Y, Z]
    rw [twHeis_commutator_mul hB'D hBD' hE hBD hB'D' hEB hEB' hED hED' (lam * ι s)
      (sb * lam ^ 3 * ι s) (mu * ι t) (sd * mu ^ 3 * ι t)]
    congr 1
    simp only [w]
    rw [map_mul]
    ring
  have hza : ∀ s t, Commute (z s) (xa t) := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz_formula, hxa_def]
    simp only [Y]
    exact ((hEB _ _).mul_right (hEB' _ _)).eq
  have hzb : ∀ s t, Commute (z s) (xb t) := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz_formula, hxb_def]
    simp only [Z]
    exact ((hED _ _).mul_right (hED' _ _)).eq
  have hz_inj : Function.Injective z := by
    intro r r' hrr
    have hz1 : z (r - r') = 1 := by
      have h2 : r' + (r - r') = r := by ring
      have h3 : z r' * z (r - r') = z r' * 1 := by rw [mul_one, ← hz_add, h2, hrr]
      exact mul_left_cancel h3
    have hG : (z (r - r') : G) = 1 := by rw [hz1]; rfl
    rw [hz_formula] at hG
    have hw0 : w ≠ 0 := hw
    have hc : w * ι (r - r') = 0 := hEinj _ hG
    have hι0 : ι (r - r') = 0 := (mul_eq_zero.mp hc).resolve_left hw0
    have h0 : r - r' = 0 := by
      apply ι.injective
      rw [hι0, map_zero]
    exact sub_eq_zero.mp h0
  obtain ⟨φ, hφ, ha, hb, hc⟩ :=
    exists_heis_of_comm (K := K) (S := T) hxa_add hxb_add hz_add hz_inj hab hza hzb
  exact ⟨φ, hφ, fun r => by rw [ha r, hxa_def], fun r => by rw [hb r, hxb_def],
    fun r => by rw [hc r, hz_formula]⟩

theorem exists_orbit_two_extraGood {G : Type} [Group G] (X : Subgroup G) (S : G →* G)
    {k : Type*} [Field k] [IsAlgClosed k] [CharP k 3]
    {B B' D D' E : k → G} (hB : ∀ c d, B (c + d) = B c * B d)
    (hB' : ∀ c d, B' (c + d) = B' c * B' d) (hD : ∀ c d, D (c + d) = D c * D d)
    (hD' : ∀ c d, D' (c + d) = D' c * D' d) (hE : ∀ c d, E (c + d) = E c * E d)
    (hBX : ∀ c, B c ∈ X) (hB'X : ∀ c, B' c ∈ X) (hDX : ∀ c, D c ∈ X) (hD'X : ∀ c, D' c ∈ X)
    {sb sb' sd sd' se : k} (hsb : sb * sb = 1) (hsb' : sb' * sb' = 1) (hsd : sd * sd = 1)
    (hsd' : sd' * sd' = 1) (hse : se * se = 1)
    (hSB : ∀ c, S (B c) = B' (sb * c ^ 3)) (hSB' : ∀ c, S (B' c) = B (sb' * c ^ 3))
    (hSD : ∀ c, S (D c) = D' (sd * c ^ 3)) (hSD' : ∀ c, S (D' c) = D (sd' * c ^ 3))
    (hSE : ∀ c, S (E c) = E (se * c ^ 3))
    (hBB' : ∀ c d, Commute (B c) (B' d)) (hDD' : ∀ c d, Commute (D c) (D' d))
    (hBD' : ∀ c d, Commute (B c) (D' d)) (hB'D : ∀ c d, Commute (B' c) (D d))
    {n n' : k} (hn : n * n = 1) (hn' : n' * n' = 1) (hBD : ∀ c d, ⁅B c, D d⁆ = E (n * (c * d)))
    (hB'D' : ∀ c d, ⁅B' c, D' d⁆ = E (n' * (c * d)))
    (hEB : ∀ c d, Commute (E c) (B d)) (hEB' : ∀ c d, Commute (E c) (B' d))
    (hED : ∀ c d, Commute (E c) (D d)) (hED' : ∀ c d, Commute (E c) (D' d))
    (hEinj : ∀ c, E c = 1 → c = 0) {lam : k} (hlam0 : lam ≠ 0)
    (hlam : lam ^ 9 = lam * (sb * sb')) :
    ∃ u : fixedPointsIn X S, (u : G) = B lam * B' (sb * lam ^ 3) ∧ orderOf u = 3 ∧
      IsExtraGood u := by
  classical
  let iota : ZMod 3 →+* k := ZMod.castHom (dvd_refl 3) k
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hn0' : n' ≠ 0 := by rintro rfl; simp at hn'
  have hse0 : se ≠ 0 := by rintro rfl; simp at hse
  have hn3 : n ^ 3 = n := by
    have h : n ^ 3 = n * (n * n) := by ring
    rw [h, hn, mul_one]
  have hn3' : n' ^ 3 = n' := by
    have h : n' ^ 3 = n' * (n' * n') := by ring
    rw [h, hn', mul_one]
  have heinj : Function.Injective E := injective_of_map_add hE hEinj
  have hnrel : n' * (sb * sd) = se * n := by
    have h1 : ⁅B 1, D 1⁆ = E n := by rw [hBD]; congr 1; ring
    have hL : S ⁅B 1, D 1⁆ = E (n' * (sb * sd)) := by
      rw [map_commutatorElement, hSB, hSD, hB'D']
      congr 1
      ring
    have hR : S ⁅B 1, D 1⁆ = E (se * n) := by
      rw [h1, hSE]
      congr 1
      rw [hn3]
    exact heinj (hL.symm.trans hR)
  have hnrel' : n * (sb' * sd') = se * n' := by
    have h1 : ⁅B' 1, D' 1⁆ = E n' := by rw [hB'D']; congr 1; ring
    have hL : S ⁅B' 1, D' 1⁆ = E (n * (sb' * sd')) := by
      rw [map_commutatorElement, hSB', hSD', hBD]
      congr 1
      ring
    have hR : S ⁅B' 1, D' 1⁆ = E (se * n') := by
      rw [h1, hSE]
      congr 1
      rw [hn3']
    exact heinj (hL.symm.trans hR)
  have hprod : (sb * sb') * (sd * sd') = 1 := by
    have h : (n' * (sb * sd)) * (n * (sb' * sd')) = (se * n) * (se * n') := by
      rw [hnrel, hnrel']
    rw [show (n' * (sb * sd)) * (n * (sb' * sd')) = (n' * n) * ((sb * sb') * (sd * sd')) by
        ring,
      show (se * n) * (se * n') = (se * se) * (n * n') by ring, hse, one_mul] at h
    have hnprod : n' * n ≠ 0 := mul_ne_zero hn0' hn0
    refine mul_left_cancel₀ hnprod ?_
    rw [h, mul_one, mul_comm n n']
  obtain ⟨nu, hnu⟩ := IsAlgClosed.exists_pow_nat_eq se (n := 2) (by norm_num)
  have hnu2 : nu * nu = se := by rw [← hnu]; ring
  have hnu0 : nu ≠ 0 := by rintro rfl; exact hse0 (by simpa using hnu2.symm)
  have hnu9 : nu ^ 9 = nu := by
    have h : nu ^ 9 = nu * (nu * nu) ^ 4 := by ring
    have hse4 : se ^ 4 = 1 := by
      rw [show se ^ 4 = (se * se) * (se * se) by ring, hse, mul_one]
    rw [h, hnu2, hse4, mul_one]
  let mu : k := nu / lam
  have hlam_mu : lam * mu = nu := by
    show lam * (nu / lam) = nu
    exact mul_div_cancel₀ nu hlam0
  have hsd_inv : sd * sd' = (sb * sb')⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  have hmu9 : mu ^ 9 = mu * (sd * sd') := by
    show (nu / lam) ^ 9 = (nu / lam) * (sd * sd')
    rw [div_eq_mul_inv, mul_pow, inv_pow, hnu9, hlam, hsd_inv, mul_inv_rev]
    ring
  have hnu3 : nu ^ 3 = nu * se := by
    have h : nu ^ 3 = nu * (nu * nu) := by ring
    rw [h, hnu2]
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h3 := (CharP.cast_eq_zero_iff k 3 2).1 h
    norm_num at h3
  have hw0 : n * (lam * mu) + n' * (sb * sd) * (lam * mu) ^ 3 ≠ 0 := by
    rw [hlam_mu, hnu3, hnrel]
    have hval : n * nu + (se * n) * (nu * se) = 2 * (n * nu) := by
      rw [show (se * n) * (nu * se) = (se * se) * (n * nu) by ring, hse, one_mul]
      ring
    rw [hval]
    exact mul_ne_zero h2 (mul_ne_zero hn0 hnu0)
  obtain ⟨i, hi2'⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) (n := 2) (by norm_num)
  have hi2 : i * i = -1 := by rw [← hi2']; ring
  have hnegi : (-i) * (-i) = -1 := by rw [show (-i) * (-i) = i * i by ring, hi2]
  have hcross1 : lam * (-(i * mu)) = -i * nu := by
    rw [← hlam_mu]
    ring
  have hcross2 : (i * lam) * mu = i * nu := by
    rw [← hlam_mu]
    ring
  have hcross3 : (i * lam) * (-(i * mu)) = nu := by
    rw [← hlam_mu]
    rw [show (i * lam) * (-(i * mu)) = -((i * i) * (lam * mu)) by ring, hi2]
    ring
  have hi9 : i ^ 9 = i := by
    have h : i ^ 9 = i * (i * i) ^ 4 := by ring
    rw [h, hi2]
    norm_num
  have hlam2 : (i * lam) ^ 9 = (i * lam) * (sb * sb') := by
    rw [mul_pow, hi9, hlam]
    ring
  have hmu2 : (-(i * mu)) ^ 9 = (-(i * mu)) * (sd * sd') := by
    have hneg9 : (-(i * mu)) ^ 9 = -((i * mu) ^ 9) := by
      rw [neg_pow]
      norm_num
    rw [hneg9, mul_pow, hi9, hmu9]
    ring
  have hw2 : n * ((i * lam) * (-(i * mu))) +
      n' * (sb * sd) * ((i * lam) * (-(i * mu))) ^ 3 ≠ 0 := by
    simpa only [hcross3, hlam_mu] using hw0
  have hcard3 : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  obtain ⟨ι₁, hι₁, ha₁, hb₁, hc₁⟩ :=
    exists_heis_orbit_two (X := X) (S := S) (K := ZMod 3) (ι := iota)
      hcard3 hB hB' hD hD' hE hBX hB'X hDX hD'X hsb hsb' hsd hsd' hSB hSB' hSD hSD'
      hBB' hDD' hBD' hB'D hBD hB'D' hEB hEB' hED hED' hEinj hlam hmu9 hw0
  obtain ⟨ι₂, hι₂, ha₂, hb₂, hc₂⟩ :=
    exists_heis_orbit_two (X := X) (S := S) (K := ZMod 3) (ι := iota)
      hcard3 hB hB' hD hD' hE hBX hB'X hDX hD'X hsb hsb' hsd hsd' hSB hSB' hSD hSD'
      hBB' hDD' hBD' hB'D hBD hB'D' hEB hEB' hED hED' hEinj hlam2 hmu2 hw2
  have hcen : ∀ c : ZMod 3, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩ := by
    intro c
    apply Subtype.ext
    rw [hc₁ c, hc₂ c, hcross3, hlam_mu]
  have hsc_ab : ∀ s t : ZMod 3,
      n * ((lam * iota s) * (-(i * mu) * iota t)) +
        n' * ((sb * lam ^ 3 * iota s) * (sd * (-(i * mu)) ^ 3 * iota t)) = 0 := by
    intro s t
    calc n * ((lam * iota s) * (-(i * mu) * iota t)) +
          n' * ((sb * lam ^ 3 * iota s) * (sd * (-(i * mu)) ^ 3 * iota t))
        = (n * (lam * (-(i * mu))) + n' * (sb * sd) * (lam * (-(i * mu))) ^ 3) *
            (iota s * iota t) := by ring
      _ = 0 := by
        rw [hcross1, twHeis_scalar_zero hnrel hse hnu2 hnegi, zero_mul]
  have hsc_ba : ∀ s t : ZMod 3,
      n * (((i * lam) * iota s) * (mu * iota t)) +
        n' * ((sb * (i * lam) ^ 3 * iota s) * (sd * mu ^ 3 * iota t)) = 0 := by
    intro s t
    calc n * (((i * lam) * iota s) * (mu * iota t)) +
          n' * ((sb * (i * lam) ^ 3 * iota s) * (sd * mu ^ 3 * iota t))
        = (n * ((i * lam) * mu) + n' * (sb * sd) * ((i * lam) * mu) ^ 3) * (iota s * iota t) := by
          ring
      _ = 0 := by
        rw [hcross2, twHeis_scalar_zero hnrel hse hnu2 hi2, zero_mul]
  have hcoe_t : ∀ x y : fixedPointsIn X S,
      ((⁅x, y⁆ : fixedPointsIn X S) : G) = ⁅(x : G), (y : G)⁆ :=
    fun x y => by simp [commutatorElement_def]
  have haa : ∀ s t, Commute (ι₁ ⟨s, 0, 0⟩) (ι₂ ⟨t, 0, 0⟩) := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha₁ s, ha₂ t]
    exact ((commute_of_map_add hB _ _).mul_right (hBB' _ _)).mul_left
      ((hBB' _ _).symm.mul_right (commute_of_map_add hB' _ _))
  have hbb : ∀ s t, Commute (ι₁ ⟨0, s, 0⟩) (ι₂ ⟨0, t, 0⟩) := by
    intro s t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hb₁ s, hb₂ t]
    exact ((commute_of_map_add hD _ _).mul_right (hDD' _ _)).mul_left
      ((hDD' _ _).symm.mul_right (commute_of_map_add hD' _ _))
  have hab : ∀ s t, Commute (ι₁ ⟨s, 0, 0⟩) (ι₂ ⟨0, t, 0⟩) := by
    intro s t
    refine commutatorElement_eq_one_iff_commute.mp ?_
    apply Subtype.ext
    rw [hcoe_t, Subgroup.coe_one, ha₁ s, hb₂ t,
      twHeis_commutator_mul hB'D hBD' hE hBD hB'D' hEB hEB' hED hED'
        (lam * iota s) (sb * lam ^ 3 * iota s) (-(i * mu) * iota t)
        (sd * (-(i * mu)) ^ 3 * iota t),
      hsc_ab s t, map_zero_of_map_add hE]
  have hba : ∀ s t, Commute (ι₁ ⟨0, s, 0⟩) (ι₂ ⟨t, 0, 0⟩) := by
    intro s t
    have h : Commute (ι₂ ⟨t, 0, 0⟩) (ι₁ ⟨0, s, 0⟩) := by
      refine commutatorElement_eq_one_iff_commute.mp ?_
      apply Subtype.ext
      rw [hcoe_t, Subgroup.coe_one, ha₂ t, hb₁ s,
        twHeis_commutator_mul hB'D hBD' hE hBD hB'D' hEB hEB' hED hED'
          (i * lam * iota t) (sb * (i * lam) ^ 3 * iota t) (mu * iota s) (sd * mu ^ 3 * iota s),
        hsc_ba t s, map_zero_of_map_add hE]
    exact h.symm
  have hcommι : ∀ a b, Commute (ι₁ a) (ι₂ b) := commute_heis_of_axes hcen haa hab hba hbb
  have hgood : IsExtraGood (ι₁ (⟨1, 0, 0⟩ : Heis (ZMod 3))) :=
    isExtraGood_of_heis_pair hcard3 hι₁ hι₂ hcommι hcen ⟨1, 0, 0⟩
  have hu3 : (ι₁ (⟨1, 0, 0⟩ : Heis (ZMod 3))) ^ 3 = 1 := by
    rw [← map_pow, Heis.pow_prime_eq_one Nat.prime_three (by norm_num), map_one]
  have hune : (ι₁ (⟨1, 0, 0⟩ : Heis (ZMod 3))) ≠ 1 := by
    intro h
    have h2 : (⟨1, 0, 0⟩ : Heis (ZMod 3)) = 1 := hι₁ (by rw [h, map_one])
    have h3 : (1 : ZMod 3) = 0 := by simpa using congrArg Heis.a h2
    exact one_ne_zero h3
  exact ⟨ι₁ ⟨1, 0, 0⟩, by simpa using ha₁ 1, orderOf_eq_prime hu3 hune, hgood⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
