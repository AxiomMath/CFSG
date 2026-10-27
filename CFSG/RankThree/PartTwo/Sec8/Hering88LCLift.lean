module

public import CFSG.RankThree.PartTwo.KFacts.K71Item119
public import CFSG.RankThree.PartTwo.KFacts.K71Residual

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open scoped MatrixGroups commutatorElement

namespace SL2Two

@[expose] def T : SL(2, ZMod 2) := ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def W : SL(2, ZMod 2) := ⟨!![0, 1; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

theorem T_sq : T ^ 2 = 1 := by decide

theorem W_cube : W ^ 3 = 1 := by decide

theorem W_ne_one : W ≠ 1 := by decide

theorem T_conj_W : T * W * T⁻¹ = W⁻¹ := by decide

end SL2Two

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_theta_of_pow {K : Subgroup G} {x : K}
    (hx : x ∈ aschbacherSolvableCore 3 K) {e : ℕ} (hxe : x ^ 3 ^ e = 1) : x = 1 := by
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  have h1 : orderOf x ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hxe
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have h2 : orderOf x ∣ Nat.card (aschbacherSolvableCore 3 K) := by
    have e' : orderOf x = orderOf (⟨x, hx⟩ : aschbacherSolvableCore 3 K) :=
      Subgroup.orderOf_coe (⟨x, hx⟩ : aschbacherSolvableCore 3 K)
    rw [e']
    exact orderOf_dvd_natCard _
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    apply hθ3
    rw [hj] at h2
    exact (dvd_pow_self 3 hj0.ne').trans h2

theorem exists_lift_of_mem_barCentralizer {K : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1)
    {y : K ⧸ aschbacherSolvableCore 3 K} (hy : y ∈ barCentralizer (Subgroup.zpowers a) K) :
    ∃ k : K, (k : G) ∈ Subgroup.centralizer ({a} : Set G) ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) k = y := by
  rw [← KFacts.imageModTheta_centralizer_eq haN ⟨1, by rwa [pow_one]⟩] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨k, (Subgroup.mem_subgroupOf.mp hk).2, rfl⟩

theorem coe_pow_mem_centralizer {K : Subgroup G} {a : G} {k : K}
    (hk : (k : G) ∈ Subgroup.centralizer ({a} : Set G)) (r : ℕ) :
    ((k ^ r : K) : G) ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.coe_pow]
  exact Subgroup.pow_mem _ hk r

theorem exists_threePart {K : Subgroup G} (k : K)
    (hk3 : (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) ^ 3 = 1) :
    ∃ r : ℕ, ¬ 3 ∣ r ∧ (k ^ r) ^ 3 = 1 := by
  obtain ⟨e, r, hr, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k).ne' 3 (by norm_num)
  refine ⟨r, hr, ?_⟩
  apply eq_one_of_mem_theta_of_pow (e := e)
  · have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ((k ^ r) ^ 3) = 1 := by
      rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hk3, one_pow]
    exact (QuotientGroup.eq_one_iff _).mp h1
  · rw [← pow_mul, ← pow_mul, show r * (3 * 3 ^ e) = 3 * (3 ^ e * r) by ring, ← hn,
      pow_mul', pow_orderOf_eq_one, one_pow]

theorem pow_ne_one_of_cube {M : Type*} [Group M] {w : M} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) {r : ℕ}
    (hr : ¬ 3 ∣ r) : w ^ r ≠ 1 := by
  intro h
  have ho : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  exact hr (ho ▸ orderOf_dvd_of_pow_eq_one h)

theorem mem_zpowers_pow_of_cube {M : Type*} [Group M] {w : M} (hw3 : w ^ 3 = 1) {r : ℕ}
    (hr : ¬ 3 ∣ r) : w ∈ Subgroup.zpowers (w ^ r) := by
  have hr' : r % 3 = 1 ∨ r % 3 = 2 := by omega
  have hw : ∀ n : ℕ, w ^ n = w ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hw3, one_pow, one_mul]
  rcases hr' with h | h
  · rw [hw r, h, pow_one]
    exact Subgroup.mem_zpowers w
  · refine ⟨2, ?_⟩
    change (w ^ r) ^ (2 : ℤ) = w
    rw [zpow_ofNat, ← pow_mul, hw, show r * 2 % 3 = 1 by omega, pow_one]

theorem lift_inverting_pair {K : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1)
    {t₀ w₀ : K ⧸ aschbacherSolvableCore 3 K}
    (ht₀ : t₀ ∈ barCentralizer (Subgroup.zpowers a) K)
    (hw₀ : w₀ ∈ barCentralizer (Subgroup.zpowers a) K)
    (ht2 : t₀ ^ 2 = 1) (hw3 : w₀ ^ 3 = 1) (hw1 : w₀ ≠ 1) (hconj : t₀ * w₀ * t₀⁻¹ = w₀⁻¹) :
    ∃ t u : K, (t : G) ∈ Subgroup.centralizer ({a} : Set G) ∧
      (u : G) ∈ Subgroup.centralizer ({a} : Set G) ∧ (∃ e : ℕ, t ^ 2 ^ e = 1) ∧ u ^ 3 = 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) u ≠ 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) t *
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) u *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) t)⁻¹ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) u)⁻¹ := by
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hq
  obtain ⟨t₁, ht₁a, ht₁⟩ := exists_lift_of_mem_barCentralizer haN ha3 ht₀
  obtain ⟨w₁, hw₁a, hw₁⟩ := exists_lift_of_mem_barCentralizer haN ha3 hw₀
  obtain ⟨e, s, hs, hsn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t₁).ne' 2 (by norm_num)
  have hs2 : s % 2 = 1 := by omega
  have hqt : q (t₁ ^ s) = t₀ := by
    rw [map_pow, ht₁, ← Nat.div_add_mod s 2, hs2, pow_add, pow_mul, ht2, one_pow, one_mul,
      pow_one]
  have hw₁3 : q w₁ ^ 3 = 1 := by rw [hw₁, hw3]
  obtain ⟨r, hr, hu3⟩ := exists_threePart w₁ hw₁3
  refine ⟨t₁ ^ s, w₁ ^ r, coe_pow_mem_centralizer ht₁a s, coe_pow_mem_centralizer hw₁a r,
    ⟨e, ?_⟩, hu3, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hsn, pow_orderOf_eq_one]
  · rw [map_pow, hw₁]
    exact pow_ne_one_of_cube hw3 hw1 hr
  · rw [hqt, map_pow, hw₁, ← conj_pow, hconj, inv_pow]

theorem lift_noncomm_three {K : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1)
    {w₀ p₀ : K ⧸ aschbacherSolvableCore 3 K} (hw₀ : w₀ ∈ barCentralizer (Subgroup.zpowers a) K)
    (hw3 : w₀ ^ 3 = 1) (hwp : w₀ * p₀ ≠ p₀ * w₀) :
    ∃ u : K, (u : G) ∈ Subgroup.centralizer ({a} : Set G) ∧ u ^ 3 = 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) u * p₀ ≠
        p₀ * QuotientGroup.mk' (aschbacherSolvableCore 3 K) u := by
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hq
  obtain ⟨w₁, hw₁a, hw₁⟩ := exists_lift_of_mem_barCentralizer haN ha3 hw₀
  have hw₁3 : q w₁ ^ 3 = 1 := by rw [hw₁, hw3]
  obtain ⟨r, hr, hu3⟩ := exists_threePart w₁ hw₁3
  refine ⟨w₁ ^ r, coe_pow_mem_centralizer hw₁a r, hu3, fun hcomm => hwp ?_⟩
  rw [map_pow, hw₁] at hcomm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_pow_of_cube hw3 hr)
  rw [← hk]
  exact ((Commute.zpow_left hcomm k) : _)

theorem commutator_not_mem_theta {K : Subgroup G} {u p : K}
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3 K) u *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) p ≠
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) p *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) u) :
    ⁅(u : G), (p : G)⁆ ∉ inSubgroup (aschbacherSolvableCore 3) K := by
  rintro ⟨x, hx, hxu⟩
  apply h
  have hx' : x = ⁅u, p⁆ := Subtype.ext (by rw [Subgroup.coe_subtype] at hxu; rw [hxu]; rfl)
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⁅u, p⁆ = 1 := by
    rw [← hx']
    exact (QuotientGroup.eq_one_iff _).mpr hx
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem exists_inverting_pair_of_projSL {K : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1)
    (hout : ¬ KFacts.IsInnerAut (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haN⟩)))
    (e : K ⧸ aschbacherSolvableCore 3 K ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 (3 * 1))) :
    ∃ t₀ w₀ : K ⧸ aschbacherSolvableCore 3 K,
      t₀ ∈ barCentralizer (Subgroup.zpowers a) K ∧ w₀ ∈ barCentralizer (Subgroup.zpowers a) K ∧
      t₀ ^ 2 = 1 ∧ w₀ ^ 3 = 1 ∧ w₀ ≠ 1 ∧ t₀ * w₀ * t₀⁻¹ = w₀⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, ← map_pow]
    have : (⟨a, haN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext (by simpa)
    rw [this, map_one, map_one]
  obtain ⟨ι⟩ := KFacts.nonempty_eqLocus_mulEquiv_projSL_two (p := 2) (m := 1) le_rfl e hα3 hout
  obtain ⟨φ⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := ZMod 2) (f := 1)
    (by rw [Nat.card_zmod, pow_one])
  have heq : barCentralizer (Subgroup.zpowers a) K = α.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext z
    rw [KFacts.mem_barCentralizer_zpowers_iff haN]
    rfl
  set ψ : SL(2, ZMod 2) ≃* α.toMonoidHom.eqLocus (MonoidHom.id _) := φ.trans ι.symm with hψ
  have hmem : ∀ s : SL(2, ZMod 2), ((ψ s : K ⧸ aschbacherSolvableCore 3 K)) ∈
      barCentralizer (Subgroup.zpowers a) K := fun s => by rw [heq]; exact (ψ s).2
  have hval : ∀ s s' : SL(2, ZMod 2), s = s' →
      ((ψ s : K ⧸ aschbacherSolvableCore 3 K)) = ((ψ s' : K ⧸ aschbacherSolvableCore 3 K)) :=
    fun s s' h => by rw [h]
  refine ⟨ψ SL2Two.T, ψ SL2Two.W, hmem _, hmem _, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, SL2Two.T_sq, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ← map_pow, SL2Two.W_cube, map_one, Subgroup.coe_one]
  · intro h
    apply SL2Two.W_ne_one
    apply ψ.injective
    rw [map_one]
    exact Subtype.ext h
  · have := hval _ _ SL2Two.T_conj_W
    rwa [map_mul, map_mul, map_inv, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv] at this

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
