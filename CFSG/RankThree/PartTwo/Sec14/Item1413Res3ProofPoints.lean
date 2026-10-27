module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofDefs
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.GroupTheory.SubnormalCores
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M22
public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProof
public import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1417
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofFrame
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofRoute
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2Proof1420
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res3

section Frame

variable {G : Type} [Group G]

structure Frame2 (L : Subgroup G) (c a : G) : Prop where
  comm : Commute c a
  hc : orderOf c = 3
  hcL : c ∉ L
  haL : a ∈ L
  ha : orderOf a = 3

namespace Frame2

variable {L : Subgroup G} {c a : G}

theorem hc3 (h : Frame2 L c a) : c ^ 3 = 1 := by rw [← h.hc]; exact pow_orderOf_eq_one c

theorem ha3 (h : Frame2 L c a) : a ^ 3 = 1 := by rw [← h.ha]; exact pow_orderOf_eq_one a

theorem mul_pow (h : Frame2 L c a) (i j k l : ℕ) :
    c ^ i * a ^ j * (c ^ k * a ^ l) = c ^ (i + k) * a ^ (j + l) := by
  have hcomm : a ^ j * c ^ k = c ^ k * a ^ j := ((h.comm.pow_pow k j).eq).symm
  calc c ^ i * a ^ j * (c ^ k * a ^ l) = c ^ i * (a ^ j * c ^ k) * a ^ l := by group
    _ = c ^ i * (c ^ k * a ^ j) * a ^ l := by rw [hcomm]
    _ = c ^ (i + k) * a ^ (j + l) := by rw [pow_add, pow_add]; group

theorem pow_pow (h : Frame2 L c a) (i j n : ℕ) :
    (c ^ i * a ^ j) ^ n = c ^ (i * n) * a ^ (j * n) := by
  rw [(h.comm.pow_pow i j).mul_pow, pow_mul, pow_mul]

theorem pow_eq_mod [Finite G] (h : Frame2 L c a) {i j k l : ℕ}
    (he : c ^ i * a ^ j = c ^ k * a ^ l) :
    i % 3 = k % 3 ∧ j % 3 = l % 3 := by
  have h1 : c ^ (i + 2 * k) * a ^ (j + 2 * l) = 1 := by
    rw [← h.mul_pow, he, h.mul_pow, show k + 2 * k = 3 * k by ring,
      show l + 2 * l = 3 * l by ring, pow_mul, pow_mul, h.hc3, h.ha3, one_pow, one_pow, one_mul]
  have hcm : c ^ (i + 2 * k) ∈ L := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem (pow_mem h.haL _)
  obtain ⟨r, hr⟩ := Proof1413.three_dvd_of_pow_mem h.hc h.hcL hcm
  rw [hr, pow_mul, h.hc3, one_pow, one_mul] at h1
  have h2 : 3 ∣ j + 2 * l := by rw [← h.ha]; exact orderOf_dvd_of_pow_eq_one h1
  omega

end Frame2

theorem zpowers_sq_eq {x : G} (hx : x ^ 3 = 1) : Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers x 2))
    (Subgroup.zpowers_le.mpr ?_)
  have h2 : (x ^ 2) ^ 2 ∈ Subgroup.zpowers (x ^ 2) := Subgroup.npow_mem_zpowers _ 2
  rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one] at h2

namespace Frame2

variable {L : Subgroup G} {c a : G}

theorem zpowers_ca2 (h : Frame2 L c a) :
    Subgroup.zpowers (c * a ^ 2) = Subgroup.zpowers (c ^ 2 * a) := by
  have h3 : (c ^ 2 * a ^ 1) ^ 3 = 1 := by
    rw [h.pow_pow, show 2 * 3 = 3 * 2 by norm_num, show 1 * 3 = 3 by norm_num, pow_mul, h.hc3,
      h.ha3, one_pow, one_mul]
  have h2 : (c ^ 2 * a ^ 1) ^ 2 = c ^ 1 * a ^ 2 := by
    rw [h.pow_pow, show 2 * 2 = 3 + 1 by norm_num, pow_add, h.hc3, one_mul]
  calc Subgroup.zpowers (c * a ^ 2) = Subgroup.zpowers ((c ^ 2 * a ^ 1) ^ 2) := by
        rw [h2, pow_one]
    _ = Subgroup.zpowers (c ^ 2 * a ^ 1) := zpowers_sq_eq h3
    _ = Subgroup.zpowers (c ^ 2 * a) := by rw [pow_one]

theorem zpowers_c2a2 (h : Frame2 L c a) :
    Subgroup.zpowers (c ^ 2 * a ^ 2) = Subgroup.zpowers (c * a) := by
  have h3 : (c ^ 1 * a ^ 1) ^ 3 = 1 := by
    rw [h.pow_pow]
    simp only [one_mul, h.hc3, h.ha3]
  have h2 : (c ^ 1 * a ^ 1) ^ 2 = c ^ 2 * a ^ 2 := by
    rw [h.pow_pow]
  rw [← h2, zpowers_sq_eq h3, pow_one, pow_one]

theorem zpowers_cases (h : Frame2 L c a) {i j : ℕ} (hne : c ^ i * a ^ j ≠ 1) :
    Subgroup.zpowers (c ^ i * a ^ j) = Subgroup.zpowers c ∨
      Subgroup.zpowers (c ^ i * a ^ j) = Subgroup.zpowers a ∨
      Subgroup.zpowers (c ^ i * a ^ j) = Subgroup.zpowers (c * a) ∨
      Subgroup.zpowers (c ^ i * a ^ j) = Subgroup.zpowers (c ^ 2 * a) := by
  have hci : c ^ i = c ^ (i % 3) := by rw [← h.hc, pow_mod_orderOf]
  have haj : a ^ j = a ^ (j % 3) := by rw [← h.ha, pow_mod_orderOf]
  rw [hci, haj] at hne ⊢
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (i % 3) <;> interval_cases (j % 3)
  · exact absurd (by simp) hne
  · simp
  · right; left
    rw [pow_zero, one_mul, zpowers_sq_eq h.ha3]
  · simp
  · simp
  · right; right; right
    rw [pow_one]
    exact h.zpowers_ca2
  · left
    rw [pow_zero, mul_one, zpowers_sq_eq h.hc3]
  · right; right; right
    rw [pow_one]
  · right; right; left
    exact h.zpowers_c2a2

theorem zpowers_ne [Finite G] (h : Frame2 L c a) :
    Subgroup.zpowers (c * a) ≠ Subgroup.zpowers (c ^ 2 * a) := by
  intro heq
  have hmem : c ^ 2 * a ∈ Subgroup.zpowers (c * a) := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (c * a) ^ n = c ^ 2 * a := by
    have h1 : c ^ 2 * a ∈ (Submonoid.powers (c * a) : Set G) := by
      rw [powers_eq_zpowers]
      exact hmem
    exact Submonoid.mem_powers_iff _ _ |>.mp h1
  have h2 : c ^ (1 * n) * a ^ (1 * n) = c ^ 2 * a ^ 1 := by
    rw [← h.pow_pow, pow_one, pow_one, hn]
  have := h.pow_eq_mod h2
  omega

theorem map_conj_ca (h : Frame2 L c a) {t : G} (htc : t * c * t⁻¹ = c)
    (hta : t * a * t⁻¹ = a⁻¹) :
    (Subgroup.zpowers (c * a)).map (MulAut.conj t).toMonoidHom = Subgroup.zpowers (c ^ 2 * a) := by
  rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : t * (c * a) * t⁻¹ = c * a ^ 2 := by
    rw [show t * (c * a) * t⁻¹ = (t * c * t⁻¹) * (t * a * t⁻¹) by group, htc, hta,
      inv_eq_of_mul_eq_one_right (show a * a ^ 2 = 1 by rw [← pow_succ', h.ha3])]
  rw [h1, h.zpowers_ca2]

theorem map_conj_c2a (h : Frame2 L c a) {t : G} (htc : t * c * t⁻¹ = c)
    (hta : t * a * t⁻¹ = a⁻¹) :
    (Subgroup.zpowers (c ^ 2 * a)).map (MulAut.conj t).toMonoidHom = Subgroup.zpowers (c * a) := by
  rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : t * (c ^ 2 * a) * t⁻¹ = c ^ 2 * a ^ 2 := by
    rw [show t * (c ^ 2 * a) * t⁻¹ = (t * c ^ 2 * t⁻¹) * (t * a * t⁻¹) by group, ← conj_pow,
      htc, hta, inv_eq_of_mul_eq_one_right (show a * a ^ 2 = 1 by rw [← pow_succ', h.ha3])]
  rw [h1, h.zpowers_c2a2]

end Frame2

end Frame

variable {G : Type} [Group G] [Finite G]

theorem exists_point_of_hyperplane {A L B : Subgroup G} {c : G}
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hcA : c ∈ A)
    (hc : orderOf c = 3) (hcL : c ∉ L) (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hB : IsHyperplane A B) (hcB : c ∈ B) :
    ∃ a ∈ B ⊓ L, orderOf a = 3 ∧ B ⊓ L = Subgroup.zpowers a ∧
      ∀ f ∈ B, ∃ i j : ℕ, f = c ^ i * a ^ j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9 : Nat.card B = 9 := by
    have h := hB.2
    rw [h27] at h
    omega
  have hdec : ∀ f ∈ B, ∃ i : ℕ, ∃ y ∈ B ⊓ L, f = c ^ i * y := by
    intro f hf
    obtain ⟨i, -, y, hy, rfl⟩ := exists_pow_mul_of_mem hAel hcA hAa (hB.1 hf)
    refine ⟨i, y, ⟨?_, hy.2⟩, rfl⟩
    have h1 := mul_mem (inv_mem (pow_mem hcB i)) hf
    rwa [inv_mul_cancel_left] at h1
  obtain ⟨a, haBL, ha1⟩ : ∃ a ∈ B ⊓ L, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have hle : B ≤ Subgroup.zpowers c := by
      intro f hf
      obtain ⟨i, y, hy, rfl⟩ := hdec f hf
      rw [hall y hy, mul_one]
      exact Subgroup.npow_mem_zpowers c i
    have := Subgroup.card_le_of_le hle
    rw [hB9, Nat.card_zpowers, hc] at this
    omega
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAel.2 a (hB.1 haBL.1)) ha1
  have hBL : B ⊓ L = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haBL) ?_).symm
    rw [Nat.card_zpowers, ha3]
    have hdvd : Nat.card (B ⊓ L : Subgroup G) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exfalso
      have h1 : B ⊓ L = ⊥ := Subgroup.eq_bot_of_card_eq _ (by simpa using hk')
      apply ha1
      have h2 := haBL
      rw [h1] at h2
      exact h2
    · simpa using hk'.le
    · exfalso
      have h1 : B ⊓ L = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hB9]; norm_num)
      apply hcL
      have h2 : c ∈ B ⊓ L := by rw [h1]; exact hcB
      exact h2.2
  refine ⟨a, haBL, ha3, hBL, fun f hf => ?_⟩
  obtain ⟨i, y, hy, rfl⟩ := hdec f hf
  rw [hBL] at hy
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ^ n = y := by
    have h1 : y ∈ (Submonoid.powers a : Set G) := by
      rw [powers_eq_zpowers]
      exact hy
    exact Submonoid.mem_powers_iff _ _ |>.mp h1
  exact ⟨i, n, by rw [hn]⟩

theorem not_mem_of_type
    {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    c ∉ L := by
  rcases htype with hA7 | hL3 | hM12 | hM22
  · obtain ⟨φ⟩ := hA7
    exact Sec13.not_mem_of_center_eq_bot hD
      (Sec13.center_eq_bot_of_mulEquiv φ Sec13.isPerfect_center_alt7.2)
  · have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
    have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      obtain ⟨-, -, a, b, hab⟩ := hq
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hab (by
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        rw [Subsingleton.elim a' b'])
    exact Sec13.not_mem_of_center_eq_bot hD (center_eq_bot_of_isLThreePi hL3 hq.1)
  · obtain ⟨φ⟩ := hM12
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact Proof1413.not_mem_of_mulEquiv_simple hD
      (by rw [KFacts.KS14.card_nativeM12]; norm_num) φ
  · obtain ⟨φ⟩ := hM22
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact Proof1413.not_mem_of_mulEquiv_simple hD
      (by rw [KFacts.KS14.card_nativeM22]; norm_num) φ

theorem facts_of_type
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hcL : c ∉ L) (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, h9, -, -⟩ | ⟨-, h9, -, -⟩ |
      ⟨-, hP, -⟩ | ⟨hcL', -⟩
  · exact ⟨h9, eq_sup_of_card_nine hD h9 (fun h => hcL h.2)⟩
  · exact ⟨h9, eq_sup_of_card_nine hD h9 (fun h => hcL h.2)⟩
  · exact absurd hP hPGL
  · exact absurd hcL' hcL

omit [Finite G] in
theorem three_dvd_card_of_card_inf {A L : Subgroup G} (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    3 ∣ Nat.card L := by
  have h1 : Nat.card (A ⊓ L : Subgroup G) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_right
  rw [h9] at h1
  exact (show (3 : ℕ) ∣ 9 by norm_num).trans h1

theorem nonempty_thetaQuot_map_conj (L : Subgroup G) (w : G) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      ↥(L.map (MulAut.conj w).toMonoidHom) ⧸
        aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (L.equivMapOfInjective _ (MulAut.conj w).injective)
    (aschbacherSolvableCore_map_mulEquiv Nat.prime_three _)⟩

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
