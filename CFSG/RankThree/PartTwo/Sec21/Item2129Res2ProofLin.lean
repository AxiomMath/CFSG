module

public import Mathlib.GroupTheory.Index
import CFSG.RankThree.PartTwo.Sec21.Item2119End7ProofKGamma

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof

theorem nine_le_card_fixed {W : Type*} [Group W] [Finite W] (hWc : ∀ a b : W, a * b = b * a)
    (hW3 : ∀ a : W, a ^ 3 = 1) (hW81 : Nat.card W = 81) (φ : W →* W)
    (hφ3 : ∀ a : W, φ (φ (φ a)) = a) :
    9 ≤ Nat.card (MonoidHom.eqLocus φ (MonoidHom.id W)) := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hWc }
  let ψ : W →* W :=
    { toFun := fun y => y⁻¹ * φ y
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev]
        simp only [mul_assoc, mul_comm, mul_left_comm] }
  have hψ : ∀ y : W, ψ y = y⁻¹ * φ y := fun y => rfl
  have hψ3 : ∀ x : W, ψ (ψ (ψ x)) = 1 := by
    intro x
    simp only [hψ, map_mul, map_inv, hφ3]
    exact Item2119End7Proof.cube_comm hW3 (φ x) (φ (φ x)) x
  have htop : ((ψ.comp ψ).comp ψ).ker = ⊤ := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_top,
      iff_true]
    exact hψ3 x
  have hk1 := Item2119End7Proof.card_ker_comp_le ψ (ψ.comp ψ)
  have hk2 := Item2119End7Proof.card_ker_comp_le ψ ψ
  rw [htop, Subgroup.card_top, hW81] at hk1
  set k := Nat.card ψ.ker with hk
  have hk81 : 81 ≤ k * (k * k) := hk1.trans (Nat.mul_le_mul_left _ hk2)
  have hkdvd : k ∣ 3 ^ 4 := by
    rw [hk, show (3 : ℕ) ^ 4 = 81 by norm_num, ← hW81]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj, hkj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hkdvd
  have hk9 : 9 ≤ k := by
    rw [hkj]
    interval_cases j
    · rw [hkj] at hk81
      norm_num at hk81
    · rw [hkj] at hk81
      norm_num at hk81
    all_goals norm_num
  refine hk9.trans (Nat.card_le_card_of_injective
    (fun x : ψ.ker => (⟨(x : W), ?_⟩ : MonoidHom.eqLocus φ (MonoidHom.id W))) ?_)
  · have hx : ψ (x : W) = 1 := x.2
    rw [hψ, inv_mul_eq_one] at hx
    exact hx.symm
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z : MonoidHom.eqLocus φ (MonoidHom.id W) => (z : W)) hxy)

variable {G : Type*} [Group G] [Finite G]

theorem exists_le_comm_mem_zpowers {Q : Subgroup G} {d r : G} (hQ243 : Nat.card Q = 243)
    (hdQ : d ∈ Q) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hdc : ∀ q ∈ Q, q * d * q⁻¹ = d)
    (hcomm : ∀ x ∈ Q, ∀ q ∈ Q, x⁻¹ * (q * x * q⁻¹) ∈ Subgroup.zpowers d)
    (hQ3 : ∀ q ∈ Q, q ^ 3 = 1) (hrQ : r ∈ Subgroup.normalizer (Q : Set G))
    (hrd : r * d * r⁻¹ = d) (hr3 : r ^ 3 ∈ Q) :
    ∃ X : Subgroup G, X ≤ Q ∧ 27 ≤ Nat.card X ∧
      ∀ y ∈ X, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzc : ∀ z ∈ Subgroup.zpowers d, ∀ q ∈ Q, q * z * q⁻¹ = z := by
    intro z hz q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hdc q hq]
  have hc : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers d := by
    intro a ha b hb
    have h := hcomm b hb a ha
    have e : a * b * a⁻¹ * b⁻¹ = b * (b⁻¹ * (a * b * a⁻¹)) * b⁻¹ := by group
    rw [e, hzc _ h b hb]
    exact h
  set N : Subgroup Q := (Subgroup.zpowers d).subgroupOf Q with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hzc _ hn _ g.2]
    exact hn
  have hmemN : ∀ a b : Q, (QuotientGroup.mk a : Q ⧸ N) = QuotientGroup.mk b ↔
      ((a : G)⁻¹ * b) ∈ Subgroup.zpowers d := by
    intro a b
    rw [QuotientGroup.eq, hNdef, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hWc : ∀ a b : Q ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmemN]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have h := hc _ (Q.inv_mem y.2) _ (Q.inv_mem x.2)
    simp only [inv_inv] at h
    rw [show (y : G)⁻¹ * (x : G)⁻¹ * ((y : G) * x) = (y : G)⁻¹ * (x : G)⁻¹ * y * x by group]
    exact h
  have hW3 : ∀ a : Q ⧸ N, a ^ 3 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
    rw [← QuotientGroup.mk_pow, show x ^ 3 = 1 from Subtype.ext (by simpa using hQ3 x x.2),
      QuotientGroup.mk_one]
  have hN3 : Nat.card N = 3 := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hdQ)).toEquiv, Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hW81 : Nat.card (Q ⧸ N) = 81 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hQ243, hN3] at h
    omega
  set φ : Q →* Q := (Q.normalizerMonoidHom ⟨r, hrQ⟩ : MulAut Q).toMonoidHom with hφdef
  have hφ : ∀ x : Q, (φ x : G) = r * x * r⁻¹ := fun x => rfl
  have hφN : N ≤ N.comap φ := by
    intro n hn
    rw [Subgroup.mem_comap, hNdef, Subgroup.mem_subgroupOf, hφ]
    rw [hNdef, Subgroup.mem_subgroupOf] at hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← hk, ← conj_zpow, hrd]
    exact Subgroup.zpow_mem_zpowers d k
  set φ' : Q ⧸ N →* Q ⧸ N := QuotientGroup.map N N φ hφN with hφ'def
  have hφ'mk : ∀ x : Q, φ' (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := fun x =>
    QuotientGroup.map_mk N N φ hφN x
  have hφ3 : ∀ a : Q ⧸ N, φ' (φ' (φ' a)) = a := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
    rw [hφ'mk, hφ'mk, hφ'mk, hmemN, hφ, hφ, hφ]
    have h := hc _ hr3 _ (Q.inv_mem x.2)
    have e : (r * (r * (r * (x : G) * r⁻¹) * r⁻¹) * r⁻¹)⁻¹ * x =
        r ^ 3 * (x : G)⁻¹ * (r ^ 3)⁻¹ * ((x : G)⁻¹)⁻¹ := by
      rw [inv_inv]
      group
    rw [e]
    exact h
  have h9 := nine_le_card_fixed hWc hW3 hW81 φ' hφ3
  set K := MonoidHom.eqLocus φ' (MonoidHom.id (Q ⧸ N)) with hK
  set X₀ : Subgroup Q := K.comap (QuotientGroup.mk' N) with hX₀
  refine ⟨X₀.map Q.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    have h1 := Subgroup.card_mul_index X₀
    have h2 := Subgroup.card_mul_index K
    have hidx : X₀.index = K.index :=
      Subgroup.index_comap_of_surjective (H := K) (QuotientGroup.mk'_surjective N)
    rw [hidx, hQ243] at h1
    rw [hW81] at h2
    have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h3 : Nat.card X₀ * K.index = (3 * Nat.card K) * K.index := by
      rw [h1, mul_assoc, h2]
      norm_num
    have h4 := Nat.eq_of_mul_eq_mul_right hpos h3
    omega
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : φ' (QuotientGroup.mk q) = QuotientGroup.mk q := hq
    rw [hφ'mk, hmemN, hφ] at hq'
    have e : r * (q : G) * r⁻¹ * (q : G)⁻¹ =
        (q : G) * ((r * (q : G) * r⁻¹)⁻¹ * q)⁻¹ * (q : G)⁻¹ := by group
    change r * (q : G) * r⁻¹ * (q : G)⁻¹ ∈ Subgroup.zpowers d
    rw [e, hzc _ (Subgroup.inv_mem _ hq') _ q.2]
    exact Subgroup.inv_mem _ hq'

end CFSG.RankThree.PartTwo.Sec21.Item2129Res2Proof
