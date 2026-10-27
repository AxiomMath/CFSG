module

public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82Item1116

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1117Proof

section Elementary

variable {X : Type*} [Group X]

theorem isPGroup_zpowers {y : X} {k : ℕ} (hy : y ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  rintro ⟨z, hz⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem commute_of_isPGroup_of_sylow [Finite X]
    (hS : ∀ Q : Sylow 3 X, IsMulCommutative (Q : Subgroup X)) {S : Subgroup X}
    (hSp : IsPGroup 3 S) {u v : X} (hu : u ∈ S) (hv : v ∈ S) : u * v = v * u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hSp.exists_le_sylow
  exact congrArg Subtype.val ((hS Q).is_comm.comm ⟨u, hQ hu⟩ ⟨v, hQ hv⟩)

end Elementary

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sylow_commutative_of_field (h82 : Sec8.Item82One) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) (hf : KFacts.InducesStdKind Y c .field) :
    ∀ Q : Sylow 3 (Y ⧸ aschbacherSolvableCore 3 Y),
      IsMulCommutative (Q : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro Q
  have hpsl : ∀ (p n : ℕ) [Fact p.Prime], p ≠ 3 → n ≠ 0 → 4 ≤ p ^ n →
      (Y ⧸ aschbacherSolvableCore 3 Y) ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p n) →
        IsMulCommutative (Q : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    intro p n _ hp hn h4 e
    obtain ⟨h3, h4'⟩ := ringChar_ne_three_and_four_le hp hn h4
    have hcyc : IsCyclic (Q : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :=
      isCyclic_sylow_of_mulEquiv_of_isCyclic (e.trans (Sec4.projSLEquivPSL _))
        (KFacts.isCyclic_sylow_three_psl2 h3 h4') Q
    infer_instance
  rcases h.isList82One_of_field h82 h118 hf with ⟨⟨e⟩⟩ | ⟨p, n, hp, hp3, hn, ⟨e⟩⟩ |
    ⟨m, hm, ⟨⟨e⟩⟩ | hL | hL⟩
  · obtain ⟨hEA, -⟩ := KFacts.isElemAbelian_of_isPGroup_three_of_mulEquiv (K := GaloisField 3 3)
      (n := 3) (GaloisField.card 3 3 (by norm_num)) (e.trans (Sec4.projSLEquivPSL _))
      Q.isPGroup'
    exact hEA.1
  · refine hpsl p (3 * n) (by omega) (by omega) ?_ e
    calc 4 ≤ p := by omega
      _ ≤ p ^ (3 * n) := Nat.le_self_pow (by omega) p
  · refine hpsl 2 (3 * m) (by norm_num) (by omega) ?_ e
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hcyc : IsCyclic (Q : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :=
      KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi hm hL Q
    infer_instance
  · exact (FieldCentRigid82.false_of_isSLThreePiAt hm hL hf (pow_three_of_mem_A h h.mem_A)
      (mem_thetaComponentsIn_sec11K_inf h.toSec11Std)
      (kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq)).elim

theorem x_cube_mem_sec11K (h : Sec11Data G A c L a R Y d x s r g) : x ^ 3 ∈ sec11K L a := by
  obtain ⟨haN, ha3, -, hQ⟩ := h.toSec11Std.a_facts
  obtain ⟨k, hk⟩ := x_pow_eq_one h
  have hxL : x ∈ L := by
    have hx : x ∈ R ⊓ L := by
      rw [h.inf_L_eq]
      exact Subgroup.mem_zpowers x
    exact hx.2
  have hx3a : x ^ 3 ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * a = (a * x ^ 3 * a⁻¹) * a := by rw [conj_a_x_cube h]
      _ = a * x ^ 3 := by group
  refine mem_sec11K_of_pow_eq_one haN ha3 hQ.1 ⟨L.pow_mem hxL 3, hx3a⟩ (k := k) ?_
  rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]

theorem conj_g_x_cube_of_field (h82 : Sec8.Item82One) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hf : KFacts.InducesStdKind Y c .field) : g * x ^ 3 * g⁻¹ = x ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyY : x ^ 3 ∈ Y := h.sec11K_le (x_cube_mem_sec11K h)
  have hgY : g ∈ Y := h.g_mem.1
  obtain ⟨k, hk⟩ := x_pow_eq_one h
  obtain ⟨k', hk'⟩ := h.pow_eq_one
  set θY := aschbacherSolvableCore 3 Y with hθY
  set q := QuotientGroup.mk' θY with hq
  set y' : Y := ⟨x ^ 3, hyY⟩ with hy'
  set g' : Y := ⟨g, hgY⟩ with hg'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (conj_pow_three_mem h hsc hrs)
  have hconj : g' * y' * g'⁻¹ = y' ^ i := Subtype.ext (by simp [hy', hg', hi])
  have hqconj : q g' * q y' * (q g')⁻¹ ∈ Subgroup.zpowers (q y') := by
    rw [← map_inv, ← map_mul, ← map_mul, hconj, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ i
  have hy3 : (q y') ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : y' ^ 3 ^ k = 1 := Subtype.ext (by
      simp only [hy', SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])
    rw [this, map_one]
  have hg3 : (q g') ^ 3 ^ k' = 1 := by
    rw [← map_pow]
    have : g' ^ 3 ^ k' = 1 := Subtype.ext (by simpa [hg'] using hk')
    rw [this, map_one]
  have hS : IsPGroup 3 ↥(Subgroup.zpowers (q g') ⊔ Subgroup.zpowers (q y')) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers hg3) (isPGroup_zpowers hy3)
      (Subgroup.zpowers_le.mpr (Sec10.mem_normalizer_zpowers_of_conj_mem hqconj))
  have hcomm := commute_of_isPGroup_of_sylow (sylow_commutative_of_field h82 h118 h hf) hS
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers (q g')))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers (q y')))
  have hw : g' * y' * g'⁻¹ * y'⁻¹ ∈ aschbacherSolvableCore 3 Y := by
    rw [← QuotientGroup.eq_one_iff]
    change q (g' * y' * g'⁻¹ * y'⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_inv_cancel_right,
      mul_inv_cancel]
  have hθ : g * x ^ 3 * g⁻¹ * (x ^ 3)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y :=
    ⟨_, hw, by simp [hy', hg']⟩
  have hR : g * x ^ 3 * g⁻¹ * (x ^ 3)⁻¹ ∈ R := by
    have hxR := (Item1116Proof.mem_R h).2.1
    refine R.mul_mem ?_ (R.inv_mem (R.pow_mem hxR 3))
    exact (Subgroup.mem_normalizer_iff.mp h.g_mem_normalizer _).mp (R.pow_mem hxR 3)
  have h1 := eq_one_of_mem_R_of_mem_theta h.isSylowOf.isPGroup hR hθ
  calc g * x ^ 3 * g⁻¹ = (g * x ^ 3 * g⁻¹ * (x ^ 3)⁻¹) * x ^ 3 := by group
    _ = x ^ 3 := by rw [h1, one_mul]

end Data

end Item1117Proof

end CFSG.RankThree.PartTwo.Sec11
