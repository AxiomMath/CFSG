module

public import CFSG.LocalAnalysis.StandardType.FS81.WeakClosureFusion
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_sup_zpowers_of_commute {x y : G} (hxy : Commute x y) {i j : ℕ}
    (hx : x ^ 3 ^ i = 1) (hy : y ^ 3 ^ j = 1) :
    IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  intro g
  obtain ⟨a, ha, b, hb, hg⟩ := fs81Sp_mem_sup_of_commute (A := Subgroup.zpowers x)
    (B := Subgroup.zpowers y) (fun a ha b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((hxy.zpow_left k).zpow_right l).eq) g.2
  refine ⟨i + j, Subtype.ext ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [Subgroup.coe_pow, hg, ((hxy.zpow_left k).zpow_right l).mul_pow, Subgroup.coe_one]
  have h1 : (x ^ k) ^ 3 ^ (i + j) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_add, pow_mul, hx,
      one_pow, one_zpow]
  have h2 : (y ^ l) ^ 3 ^ (i + j) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_add, mul_comm,
      pow_mul, hy, one_pow, one_zpow]
  rw [h1, h2, one_mul]

theorem mem_zpowers_of_isCyclic_sup {x b₀ y : G} (hb₀ : orderOf b₀ = 3)
    (hcyc : IsCyclic ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers b₀)) (hy : y ∈ Subgroup.zpowers x)
    (hy3 : y ^ 3 = 1) : y ∈ Subgroup.zpowers b₀ := by
  let yH : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers b₀) := ⟨y, Subgroup.mem_sup_left hy⟩
  let bH : ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers b₀) :=
    ⟨b₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)⟩
  have hbH : orderOf bH = 3 := by
    rw [← Subgroup.orderOf_coe bH]
    exact hb₀
  have hyH : yH ^ 3 = 1 := Subtype.ext (by simp [yH, hy3])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (fs81Sp_order3_unique hbH hyH)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa [yH, bH] using congrArg Subtype.val hk⟩

theorem fs81_three_elem_decomp {b₀ : G} {K E : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hOut : ¬ 3 ∣ Nat.card (Outer K)) (hb0E : b₀ ∈ E)
    (hCK : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K)
    (hEel : IsElemAbelian 3 E) {y : G} (hyE : y ∈ Subgroup.centralizer (E : Set G)) {k : ℕ}
    (hy : y ^ 3 ^ k = 1) :
    ∃ a ∈ E ⊓ K, ∃ d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G),
      y = a * d ∧ d ^ 3 ^ (k + 1) = 1 := by
  set C := Subgroup.centralizer ({b₀} : Set G) with hC
  set D := C ⊓ Subgroup.centralizer (K : Set G) with hD
  have hyC : y ∈ C := Subgroup.mem_centralizer_iff.mpr fun g hg => by
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact Subgroup.mem_centralizer_iff.mp hyE b₀ hb0E
  have hnormal : ((K ⊔ D).subgroupOf C).Normal := fs81Fus_sup_normal hKC hKn
  have hidx : ¬ 3 ∣ ((K ⊔ D).subgroupOf C).index := fs81Sp_no_three_index hKC hKn hOut
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers (⟨y, hyC⟩ : C)) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (⟨y, hyC⟩ : C) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hy)
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1,
      one_zpow, Subgroup.coe_one]
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow (p := 3) (G := C) hP
  have hyKD : y ∈ K ⊔ D := fs81Sp_sylow_le_normal hidx P (hPle (Subgroup.mem_zpowers _))
  obtain ⟨a, ha, d, hd, hyad⟩ := fs81Sp_mem_sup_of_commute fs81Sp_comm hyKD
  have haA : a ∈ E ⊓ K := by
    rw [← hCK]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, ha⟩
    have h1 : x * y = y * x := Subgroup.mem_centralizer_iff.mp hyE x hx.1
    have h2 : x * d = d * x := (Subgroup.mem_centralizer_iff.mp hd.2 x hx.2)
    have ha' : a = y * d⁻¹ := by rw [hyad]; group
    rw [ha']
    have h2' : x * d⁻¹ = d⁻¹ * x := ((show Commute x d from h2).inv_right).eq
    calc x * (y * d⁻¹) = y * (x * d⁻¹) := by rw [← mul_assoc, h1, mul_assoc]
      _ = y * (d⁻¹ * x) := by rw [h2']
      _ = y * d⁻¹ * x := by rw [mul_assoc]
  refine ⟨a, haA, d, hd, hyad, ?_⟩
  have hcomm : Commute a y := Subgroup.mem_centralizer_iff.mp hyE a haA.1
  have hda : d = a⁻¹ * y := by rw [hyad]; group
  rw [hda, hcomm.inv_left.mul_pow, inv_pow, pow_succ, pow_mul y (3 ^ k) 3, hy, one_pow, mul_one,
    mul_comm (3 ^ k) 3, pow_mul, hEel.2 a haA.1, one_pow, inv_one]

theorem fs81_three_elem_mem_E {b₀ : G} {K E : Subgroup G} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hCK : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K)
    (hEel : IsElemAbelian 3 E)
    (hnorm : ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)))
    {y : G} (hyE : y ∈ Subgroup.centralizer (E : Set G)) {k : ℕ} (hy : y ^ 3 ^ k = 1) :
    y ∈ E := by
  have hb0E : b₀ ∈ E := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  set D := Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) with hD
  have hDE : ∀ d ∈ D, d ∈ Subgroup.centralizer (E : Set G) := by
    intro d hd
    have hle : E ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [← hsup]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun x hx => ?_
      · exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
          rw [Set.mem_singleton_iff] at hg
          rw [hg]
          exact (Subgroup.mem_centralizer_iff.mp hd.1 b₀ (Set.mem_singleton b₀)).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
          rw [Set.mem_singleton_iff] at hg
          rw [hg]
          exact (Subgroup.mem_centralizer_iff.mp hd.2 x hx.2).symm
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hle hx) d (Set.mem_singleton d)).symm
  have hcyc : ∀ d ∈ D, ∀ {j : ℕ}, d ^ 3 ^ j = 1 →
      IsCyclic ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) := by
    intro d hd j hj
    refine hA2 _ (sup_le (Subgroup.zpowers_le.mpr hd.2) (Subgroup.zpowers_le.mpr ?_)) ?_
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (Subgroup.mem_centralizer_iff.mp (hKC hx) b₀ (Set.mem_singleton b₀)).symm
    · have hcomm : Commute d b₀ :=
        (Subgroup.mem_centralizer_iff.mp hd.1 b₀ (Set.mem_singleton b₀)).symm
      exact isPGroup_sup_zpowers_of_commute (i := j) (j := 1) hcomm hj (by rw [pow_one]; exact hb₀3)
  by_contra hyn
  obtain ⟨a, ha, d, hd, hyad, hd3⟩ := fs81_three_elem_decomp hKC hKn hOut hb0E hCK hEel hyE hy
  have hdn : d ∉ Subgroup.zpowers b₀ := by
    intro hdb
    apply hyn
    rw [hyad]
    exact E.mul_mem ha.1 (hsup ▸ Subgroup.mem_sup_left hdb)
  have hex : ∃ c : ℕ, d ^ 3 ^ c = 1 := ⟨k + 1, hd3⟩
  classical
  set c := Nat.find hex with hc
  have hdc : d ^ 3 ^ c = 1 := Nat.find_spec hex
  have hd3' : ¬ d ^ 3 = 1 := fun h =>
    hdn (mem_zpowers_of_isCyclic_sup hb₀ (hcyc d hd hd3) (Subgroup.mem_zpowers d) h)
  have hc2 : 2 ≤ c := by
    by_contra hlt
    push Not at hlt
    interval_cases hc' : c
    · rw [pow_zero, pow_one] at hdc
      exact hd3' (by rw [hdc, one_pow])
    · rw [pow_one] at hdc
      exact hd3' hdc
  set z := d ^ 3 ^ (c - 2) with hz
  set e := z ^ 3 with he
  have he_eq : e = d ^ 3 ^ (c - 1) := by
    rw [he, hz, ← pow_mul, ← pow_succ, show c - 2 + 1 = c - 1 by omega]
  have he3 : e ^ 3 = 1 := by
    rw [he_eq, ← pow_mul, ← pow_succ, show c - 1 + 1 = c by omega, hdc]
  have he1 : e ≠ 1 := by
    intro h
    rw [he_eq] at h
    exact absurd (Nat.find_min hex (show c - 1 < c by omega)) (not_not.mpr h)
  have heb : e ∈ Subgroup.zpowers b₀ := mem_zpowers_of_isCyclic_sup hb₀ (hcyc d hd hd3)
    (by rw [he_eq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) _) he3
  have hzpe : Subgroup.zpowers e = Subgroup.zpowers b₀ := by
    have hle : Subgroup.zpowers e ≤ Subgroup.zpowers b₀ := Subgroup.zpowers_le.mpr heb
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hb₀,
      orderOf_eq_prime he3 he1]
  apply hnorm
  intro n hn
  have hzE : z ∈ Subgroup.centralizer (E : Set G) := Subgroup.pow_mem _ (hDE d hd) _
  have hwE : n * z * n⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
    rw [inv_inv] at hx'
    have h1 := Subgroup.mem_centralizer_iff.mp hzE _ hx'
    calc x * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * x := by group
  have hz3 : z ^ 3 ^ (c + 1) = 1 := by
    rw [hz, ← pow_mul, show 3 ^ (c - 2) * 3 ^ (c + 1) = 3 ^ c * 3 ^ (c - 1) by
      rw [← pow_add, ← pow_add]; congr 1; omega, pow_mul, hdc, one_pow]
  have hw3 : (n * z * n⁻¹) ^ 3 ^ (c + 1) = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
  obtain ⟨a', ha', d', hd', hwad, hd'3⟩ :=
    fs81_three_elem_decomp hKC hKn hOut hb0E hCK hEel hwE hw3
  have hcomm' : Commute a' d' := Subgroup.mem_centralizer_iff.mp hd'.2 a' ha'.2
  have hne : n * e * n⁻¹ = d' ^ 3 := by
    rw [he, ← conj_pow, hwad, hcomm'.mul_pow, hEel.2 a' ha'.1, one_mul]
  have hne3 : (n * e * n⁻¹) ^ 3 = 1 := by rw [conj_pow, he3, mul_one, mul_inv_cancel]
  have hnb : n * e * n⁻¹ ∈ Subgroup.zpowers b₀ := by
    refine mem_zpowers_of_isCyclic_sup hb₀ (hcyc d' hd' hd'3) ?_ hne3
    rw [hne]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d') _
  have := Basis3.mem_normalizer_zpowers_of_conj (a := e) (g := n) (by rw [hzpe]; exact hnb)
  rwa [hzpe] at this

end CFSG.StandardType.FrameRoute.FS81

end
