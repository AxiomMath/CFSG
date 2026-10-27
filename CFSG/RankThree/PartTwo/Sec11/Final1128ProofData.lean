module

public import CFSG.RankThree.PartTwo.Sec11.Final1128ProofCore
public import CFSG.RankThree.PartTwo.Sec11.Skeleton
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.Sec11.Item1133Proof
import CFSG.RankThree.PartTwo.Sec11.Final1128Item1130
public import CFSG.RankThree.PartTwo.Sec11.RFacts

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Final1128Proof

structure Data (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g e : G) : Prop extends Sec11Data G A c L a R Y d x s r g where
  zpowers_s_eq : Subgroup.zpowers s = Subgroup.zpowers c
  closure_eq_closure : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  orderOf_x : orderOf x = 9
  e_mem : e ∈ A
  e_not_mem : e ∉ Subgroup.closure {c, d}
  commutator_eq' : ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {e, d}

namespace Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g e : G}

theorem A_le_R (h : Data G A c L a R Y d x s r g e) : A ≤ R :=
  Item1115Proof.A_le_R h.toHyp91

theorem A_le_P (h : Data G A c L a R Y d x s r g e) : A ≤ sec11P R g :=
  h.A_le_R.trans le_sup_left

theorem d_mem_A (h : Data G A c L a R Y d x s r g e) : d ∈ A :=
  (Item1115Proof.d_mem h.toSec11Data).1

theorem orderOf_d (h : Data G A c L a R Y d x s r g e) : orderOf d = 3 :=
  (Item1115Proof.orderOf_c_d h.toSec11Data).2

theorem pow_three_A (h : Data G A c L a R Y d x s r g e) : ∀ y ∈ A, y ^ 3 = 1 :=
  h.mem_partTwoF.1.2

theorem mul_comm_A (h : Data G A c L a R Y d x s r g e) : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y :=
  fun y hy z hz => congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)

theorem x_mem_R (h : Data G A c L a R Y d x s r g e) : x ∈ R := by
  rw [h.R_eq]
  exact Subgroup.subset_closure (by simp)

theorem s_mem_R (h : Data G A c L a R Y d x s r g e) : s ∈ R := by
  rw [h.R_eq]
  exact Subgroup.subset_closure (by simp)

theorem x_mem_P (h : Data G A c L a R Y d x s r g e) : x ∈ sec11P R g :=
  (le_sup_left : R ≤ sec11P R g) h.x_mem_R

theorem orderOf_s (h : Data G A c L a R Y d x s r g e) : orderOf s = 3 := by
  rw [← Nat.card_zpowers, h.zpowers_s_eq, Nat.card_zpowers]
  exact (Item1115Proof.orderOf_c_d h.toSec11Data).1

theorem s_mem_zpowers (h : Data G A c L a R Y d x s r g e) : s ∈ Subgroup.zpowers c := by
  rw [← h.zpowers_s_eq]
  exact Subgroup.mem_zpowers s

theorem c_x (h : Data G A c L a R Y d x s r g e) : c * x = x * c := by
  obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨x, h.x_mem_R⟩
  have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact (Sec12.commute_of_conj_mem_zpowers (Item1115Proof.orderOf_c_d h.toSec11Data).1
    ((Subgroup.mem_normalizer_iff.mp (h.isSylowOf.le h.x_mem_R) c).mp (Subgroup.mem_zpowers c))
    hxk).symm

theorem mem_normalizer_A (h : Data G A c L a R Y d x s r g e) {y : G}
    (hy : y ∈ sec11P R g) : y ∈ Subgroup.normalizer (A : Set G) := by
  refine Item1133Proof.le_normalizer_of_commutator_le h.A_le_P ?_ hy
  rw [h.commutator_eq', Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨h.e_mem, h.d_mem_A⟩

theorem commutator_x_a (h : Data G A c L a R Y d x s r g e) : ⁅x, a⁆ ∈ Subgroup.zpowers d := by
  have hxL : x ∈ L := (show x ∈ R ⊓ L by rw [h.inf_L_eq]; exact Subgroup.mem_zpowers x).2
  have hxA := h.mem_normalizer_A h.x_mem_P
  rw [← h.inf_eq, commutatorElement_def]
  refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxA a).mp h.a_mem) (A.inv_mem h.a_mem), ?_⟩
  have haL : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp91.toHyp81.a_mem_normalizer
  have h1 : a * x⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL x⁻¹).mp (L.inv_mem hxL)
  have e1 : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
  rw [e1]
  exact L.mul_mem hxL h1

theorem closure_eq_e (h : Data G A c L a R Y d x s r g e) : A = Subgroup.closure {c, e, d} :=
  h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq h.e_mem h.e_not_mem

theorem c_not_mem (h : Data G A c L a R Y d x s r g e) : c ∉ Subgroup.closure {e, d} := by
  intro hc
  refine Item1133Proof.not_le_closure_pair h.card_eq (h.mul_comm_A e h.e_mem d h.d_mem_A)
    (h.pow_three_A e h.e_mem) (h.pow_three_A d h.d_mem_A) ?_
  rw [h.closure_eq_e, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨hc, Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩

theorem commutator_g_c (h : Data G A c L a R Y d x s r g e) : ⁅g, c⁆ ∈ Subgroup.zpowers d := by
  have hcd : c * d = d * c := h.mul_comm_A c h.mem_A d h.d_mem_A
  have hP : ⁅g, c⁆ ∈ Subgroup.closure {e, d} := by
    rw [← h.commutator_eq']
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
      (h.A_le_P h.mem_A)
  have hcd' : ⁅g, c⁆ ∈ Subgroup.closure {c, d} := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h.conj_mem (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hcd'
  have hci : c ^ i ∈ Subgroup.closure {e, d} := by
    have e1 : c ^ i = ⁅g, c⁆ * (d ^ j)⁻¹ := by rw [hij, mul_inv_cancel_right]
    rw [e1]
    exact Subgroup.mul_mem _ hP (Subgroup.inv_mem _ (Subgroup.zpow_mem _
      (Subgroup.subset_closure (by simp)) j))
  rw [hij, Item1133Proof.zpow_eq_one_of_mem (h.pow_three_A c h.mem_A) h.c_not_mem hci, one_mul]
  exact Subgroup.zpow_mem_zpowers d j

theorem g_c (h : Data G A c L a R Y d x s r g e) : g * c ≠ c * g := fun hgc =>
  h.g_not_mem (Item1133Proof.mem_normalizer_zpowers_of_commute hgc)

theorem g_d (h117 : Item117) (h : Data G A c L a R Y d x s r g e) : g * d = d * g := by
  have hcard : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, h.orderOf_d]
  have hN := (h117 G A c L a R Y h.toSec11Std d h.inf_eq (Subgroup.zpowers d)
    (Subgroup.zpowers_le.mpr h.d_mem_A) hcard).mpr rfl
  have hgd : g * d * g⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (hN h.g_mem.2) d).mp (Subgroup.mem_zpowers d)
  obtain ⟨k, hk⟩ := h.pow_eq_one
  exact Sec12.commute_of_conj_mem_zpowers h.orderOf_d hgd hk

theorem g_a (h : Data G A c L a R Y d x s r g e) : g * a = a * g :=
  Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)

theorem card_T (h : Data G A c L a R Y d x s r g e) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup G) = 27 := by
  have hsx : s * x = x * s := h.toSec11Data.commute_s_x
  have hN : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    Subgroup.zpowers_le.mpr (Item1133Proof.mem_normalizer_zpowers_of_commute hsx)
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers s) := by
    rw [disjoint_iff, inf_comm]
    exact Item1115Proof.inf_zpowers_eq_bot h.toSec11Data
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
    Nat.card_zpowers, Nat.card_zpowers, h.orderOf_x, h.orderOf_s]

theorem T_le_centralizer (h : Data G A c L a R Y d x s r g e) :
    (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup G) ≤
      Subgroup.centralizer ({x} : Set G) := by
  have hsx : s * x = x * s := h.toSec11Data.commute_s_x
  exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hsx))

theorem a_mem_normalizer_T (h : Data G A c L a R Y d x s r g e) :
    a ∈ Subgroup.normalizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
  have hax : a * x * a⁻¹ ∈ Subgroup.zpowers x := by
    have h1 : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers x :=
      Subgroup.zpowers_le.mpr (Item1115Proof.d_mem_zpowers_x h.toSec11Data) h.commutator_x_a
    have e1 : a * x * a⁻¹ = (x⁻¹ * (x * a * x⁻¹ * a⁻¹))⁻¹ := by group
    rw [e1]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) h1)
  have has : a * s * a⁻¹ = s := by
    rw [Item1133Proof.commute_of_mem_zpowers (h.mul_comm_A a h.a_mem c h.mem_A) h.s_mem_zpowers,
      mul_inv_cancel_right]
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hmap : (Subgroup.zpowers x ⊔ Subgroup.zpowers s).map (MulAut.conj a).toMonoidHom ≤
      Subgroup.zpowers x ⊔ Subgroup.zpowers s := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le_sup (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · simpa [MulAut.conj_apply] using hax
    · simp [MulAut.conj_apply, has]
  exact hmap ⟨z, hz, rfl⟩

theorem a_not_mem_T (h : Data G A c L a R Y d x s r g e) :
    a ∉ (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup G) := fun haT =>
  Item1115Proof.not_commute_a_x h.toSec11Data
    (Subgroup.mem_centralizer_singleton_iff.mp (h.T_le_centralizer haT))

theorem R_eq_sup (h : Data G A c L a R Y d x s r g e) :
    R = (Subgroup.zpowers x ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers a := by
  have haR : a ∈ R := h.A_le_R h.a_mem
  have hx : x ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hs : s ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have ha : a ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hr : r ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers a := by
    have hr' : r ∈ Subgroup.closure ({a, s} : Set G) := by
      rw [← h.closure_eq_closure]
      exact Subgroup.subset_closure (by simp)
    refine (Subgroup.closure_le _).mpr ?_ hr'
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨ha, hs⟩
  apply le_antisymm
  · rw [h.R_eq, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨hr, hx, hs⟩
  · exact sup_le (sup_le (Subgroup.zpowers_le.mpr h.x_mem_R) (Subgroup.zpowers_le.mpr h.s_mem_R))
      (Subgroup.zpowers_le.mpr haR)

theorem card_R (h : Data G A c L a R Y d x s r g e) : Nat.card R = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := h.pow_three_A a h.a_mem
  have hN : Subgroup.zpowers a ≤ Subgroup.normalizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr h.a_mem_normalizer_T
  have hdisj : Disjoint (Subgroup.zpowers x ⊔ Subgroup.zpowers s : Subgroup G)
      (Subgroup.zpowers a) := by
    rw [Subgroup.disjoint_def]
    intro z hzT hza
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hza
    exact Item1133Proof.zpow_eq_one_of_mem ha3 h.a_not_mem_T hzT
  rw [h.R_eq_sup, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
    h.card_T, Nat.card_zpowers, orderOf_eq_prime ha3 h.a_ne_one]

theorem pow_three_mem_R (h : Data G A c L a R Y d x s r g e) {g' : G}
    (hg'R : g' ∈ Subgroup.normalizer (R : Set G)) (hg'3 : ∃ k : ℕ, g' ^ 3 ^ k = 1)
    (hg'c : ⁅g', c⁆ ∈ Subgroup.zpowers d) (hg'd : g' * d = d * g') : g' ^ 3 ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcom : g' * ⁅g', c⁆ = ⁅g', c⁆ * g' := Item1133Proof.commute_of_mem_zpowers hg'd hg'c
  have hδ3 : ⁅g', c⁆ ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg'c
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_d,
      pow_orderOf_eq_one, one_zpow]
  have h3 : ⁅g' ^ 3, c⁆ = 1 := by
    rw [Final1128Proof.commutatorElement_pow_left_of_commute hcom, hδ3]
  have hg3c : g' ^ 3 * c = c * g' ^ 3 := commutatorElement_eq_one_iff_mul_comm.mp h3
  have hg3H : g' ^ 3 ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Item1133Proof.mem_normalizer_zpowers_of_commute hg3c
  have hgP3 : IsPGroup 3 (Subgroup.zpowers g') := by
    obtain ⟨k, hk⟩ := hg'3
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hg3P : IsPGroup 3 (Subgroup.zpowers (g' ^ 3)) :=
    hgP3.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g') 3))
  have hgN : Subgroup.zpowers (g' ^ 3) ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hg'R 3)
  have hQ := hg3P.to_sup_of_normal_right' h.isSylowOf.isPGroup hgN
  rw [sup_comm] at hQ
  have hQH : R ⊔ Subgroup.zpowers (g' ^ 3) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le h.isSylowOf.le (Subgroup.zpowers_le.mpr hg3H)
  have heq := h.isSylowOf.eq_of_le le_sup_left hQH hQ
  have hmem : g' ^ 3 ∈ R ⊔ Subgroup.zpowers (g' ^ 3) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rwa [heq] at hmem

theorem card_P (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    Nat.card (sec11P R g) = 3 ^ 5 := by
  have hgR : g ∉ R := fun hg => h.g_not_mem (h.isSylowOf.le hg)
  show Nat.card (R ⊔ Subgroup.zpowers g : Subgroup G) = 3 ^ 5
  rw [Item1130Proof.card_sup_zpowers_eq h.g_mem_normalizer hgR
    (h.pow_three_mem_R h.g_mem_normalizer h.pow_eq_one h.commutator_g_c (h.g_d h117)), h.card_R]
  norm_num

theorem le_closure (h : Data G A c L a R Y d x s r g e) :
    sec11P R g ≤ Subgroup.closure {c, a, x, g} := by
  have hsC : s ∈ Subgroup.closure ({c, a, x, g} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h.s_mem_zpowers
  show R ⊔ Subgroup.zpowers g ≤ _
  refine sup_le ?_ ?_
  · rw [h.R_eq, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨?_, Subgroup.subset_closure (by simp), hsC⟩
    have hr : r ∈ Subgroup.closure ({a, s} : Set G) := by
      rw [← h.closure_eq_closure]
      exact Subgroup.subset_closure (by simp)
    refine (Subgroup.closure_le _).mpr ?_ hr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Subgroup.subset_closure (by simp), hsC⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)

theorem closure_le_centralizer_d (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    Subgroup.closure ({c, a, x, g} : Set G) ≤ Subgroup.centralizer {d} := by
  rw [Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨h.mul_comm_A c h.mem_A d h.d_mem_A, h.mul_comm_A a h.a_mem d h.d_mem_A,
    Item1133Proof.commute_of_mem_zpowers rfl (Item1115Proof.d_mem_zpowers_x h.toSec11Data),
    h.g_d h117⟩

theorem d_comm (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    ∀ y ∈ sec11P R g, y * d = d * y := fun _ hy =>
  Subgroup.mem_centralizer_singleton_iff.mp (h.closure_le_centralizer_d h117 (h.le_closure hy))

theorem closure_le_normalizer_d (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    Subgroup.closure ({c, a, x, g} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun _ hy =>
  Item1133Proof.mem_normalizer_zpowers_of_commute
    (Subgroup.mem_centralizer_singleton_iff.mp (h.closure_le_centralizer_d h117 hy))

theorem A_le_normalizer_d (h : Data G A c L a R Y d x s r g e) :
    Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  rw [← h.closure_eq]
  exact fun y hy => Item1133Proof.mem_normalizer_zpowers_of_commute
    (h.mul_comm_A y hy d h.d_mem_A)

theorem commutator_mem (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    ∀ y ∈ sec11P R g, ∀ z ∈ A, ⁅y, z⁆ ∈ Subgroup.zpowers d := by
  intro y hy z hz
  have hzA : z ∈ Subgroup.closure ({c, a, d} : Set G) := h.closure_eq ▸ hz
  have hone : ∀ u v : G, u * v = v * u → ⁅u, v⁆ ∈ Subgroup.zpowers d := fun u v huv => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr huv]
    exact Subgroup.one_mem _
  have hxz : ⁅x, z⁆ ∈ Subgroup.zpowers d := by
    refine Item1133Proof.commutator_mem_of_mem_closure h.A_le_normalizer_d ?_ hzA
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hone _ _ h.c_x.symm
    · exact h.commutator_x_a
    · exact hone _ _ (Item1133Proof.commute_of_mem_zpowers rfl
        (Item1115Proof.d_mem_zpowers_x h.toSec11Data))
  have hgz : ⁅g, z⁆ ∈ Subgroup.zpowers d := by
    refine Item1133Proof.commutator_mem_of_mem_closure h.A_le_normalizer_d ?_ hzA
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact h.commutator_g_c
    · exact hone _ _ h.g_a
    · exact hone _ _ (h.g_d h117)
  have hzy : ⁅z, y⁆ ∈ Subgroup.zpowers d := by
    refine Item1133Proof.commutator_mem_of_mem_closure (h.closure_le_normalizer_d h117) ?_
      (h.le_closure hy)
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hone _ _ (h.mul_comm_A z hz _ h.mem_A)
    · exact hone _ _ (h.mul_comm_A z hz _ h.a_mem)
    · rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hxz
    · rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hgz
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ hzy

theorem x_e_ne (h : Data G A c L a R Y d x s r g e) : ⁅x, e⁆ ≠ 1 := by
  intro h1
  have hxe : x * e = e * x := commutatorElement_eq_one_iff_mul_comm.mp h1
  have hle : A ≤ Subgroup.centralizer {x} := by
    rw [h.closure_eq_e, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨h.c_x, hxe.symm, (Item1133Proof.commute_of_mem_zpowers rfl
      (Item1115Proof.d_mem_zpowers_x h.toSec11Data)).symm⟩
  exact Item1115Proof.not_commute_a_x h.toSec11Data
    (Subgroup.mem_centralizer_singleton_iff.mp (hle h.a_mem))

theorem pow_x_comm (h : Data G A c L a R Y d x s r g e) {δ : G} (hδ : δ ∈ Subgroup.zpowers d)
    (m : ℕ) : x ^ m * δ = δ * x ^ m :=
  ((show Commute x δ from Item1133Proof.commute_of_mem_zpowers rfl
    (Subgroup.zpowers_le.mpr (Item1115Proof.d_mem_zpowers_x h.toSec11Data) hδ)).pow_left m).eq

theorem exists_pow_mul_comm (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    ∃ m : ℕ, x ^ m * g * e = e * (x ^ m * g) := by
  have hge := h.commutator_mem h117 g (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)) e h.e_mem
  have hxe := h.commutator_mem h117 x h.x_mem_P e h.e_mem
  obtain ⟨m, hm⟩ := Final1128Proof.exists_pow_eq_of_orderOf_eq_three h.orderOf_d hxe h.x_e_ne
    (Subgroup.inv_mem _ hge)
  refine ⟨m, commutatorElement_eq_one_iff_mul_comm.mp ?_⟩
  rw [Final1128Proof.commutatorElement_mul_left', h.pow_x_comm hge, mul_inv_cancel_right,
    Final1128Proof.commutatorElement_pow_left_of_commute (Item1133Proof.commute_of_mem_zpowers rfl
      (Subgroup.zpowers_le.mpr (Item1115Proof.d_mem_zpowers_x h.toSec11Data) hxe)), hm,
    mul_inv_cancel]

theorem commutator_g₁_c (h : Data G A c L a R Y d x s r g e) (m : ℕ) :
    ⁅x ^ m * g, c⁆ = ⁅g, c⁆ := by
  rw [Final1128Proof.commutatorElement_mul_left', h.pow_x_comm h.commutator_g_c,
    mul_inv_cancel_right, commutatorElement_eq_one_iff_mul_comm.mpr
      ((show Commute x c from h.c_x.symm).pow_left m).eq, mul_one]

theorem g₁_mem (h : Data G A c L a R Y d x s r g e) (m : ℕ) : x ^ m * g ∈ sec11P R g :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ h.x_mem_P m)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

theorem g₁_not_mem (h : Data G A c L a R Y d x s r g e) (m : ℕ) : x ^ m * g ∉ A := by
  intro hg
  apply h.g_c
  rw [← commutatorElement_eq_one_iff_mul_comm, ← h.commutator_g₁_c m]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (h.mul_comm_A _ hg c h.mem_A)

theorem R_inf_centralizer_e (h : Data G A c L a R Y d x s r g e) :
    R ⊓ Subgroup.centralizer {e} = A := by
  refine Item1130Proof.eq_of_le_of_ne (le_inf h.A_le_R fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.mul_comm_A y hy e h.e_mem)) inf_le_left ?_ ?_
  · intro heq
    have hx : x ∈ R := h.x_mem_R
    rw [← heq] at hx
    exact h.x_e_ne (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2))
  · rw [h.card_R, h.card_eq]

theorem g₁_pow_three (h117 : Item117) (h : Data G A c L a R Y d x s r g e) {m : ℕ}
    (hm : x ^ m * g * e = e * (x ^ m * g)) : (x ^ m * g) ^ 3 ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : x ^ m * g ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.le_normalizer h.x_mem_R) m)
      h.g_mem_normalizer
  obtain ⟨k, hk⟩ := h.toSec11Data.isPGroup_sec11P ⟨_, h.g₁_mem m⟩
  have hk' : (x ^ m * g) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd : x ^ m * g * d = d * (x ^ m * g) := by
    rw [mul_assoc, h.g_d h117, ← mul_assoc, h.pow_x_comm (Subgroup.mem_zpowers d), mul_assoc]
  have h3 := h.pow_three_mem_R hR ⟨k, hk'⟩ (by rw [h.commutator_g₁_c]; exact h.commutator_g_c) hd
  rw [← h.R_inf_centralizer_e]
  exact ⟨h3, Subgroup.mem_centralizer_singleton_iff.mpr
    (((show Commute (x ^ m * g) e from hm).pow_left 3).eq)⟩

theorem e_not_mem_zpowers (h : Data G A c L a R Y d x s r g e) : e ∉ Subgroup.zpowers d :=
  fun he => h.e_not_mem (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) he)

theorem card_D (h : Data G A c L a R Y d x s r g e) :
    Nat.card (Subgroup.closure ({e, d} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he3 : e ^ 3 = 1 := h.pow_three_A e h.e_mem
  have he1 : e ≠ 1 := fun he => h.e_not_mem (he ▸ Subgroup.one_mem _)
  have hed : e * d = d * e := h.mul_comm_A e h.e_mem d h.d_mem_A
  have heq : Subgroup.closure ({e, d} : Set G) = Subgroup.zpowers d ⊔ Subgroup.zpowers e := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers e),
        Subgroup.mem_sup_left (Subgroup.mem_zpowers d)⟩
    · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hN : Subgroup.zpowers e ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    Subgroup.zpowers_le.mpr (Item1133Proof.mem_normalizer_zpowers_of_commute hed)
  have hdisj : Disjoint (Subgroup.zpowers d) (Subgroup.zpowers e) := by
    rw [Subgroup.disjoint_def]
    intro z hzd hze
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hze
    exact Item1133Proof.zpow_eq_one_of_mem he3 h.e_not_mem_zpowers hzd
  rw [heq, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
    Nat.card_zpowers, Nat.card_zpowers, h.orderOf_d, orderOf_eq_prime he3 he1]

theorem centralizer_e_eq (h117 : Item117) (h : Data G A c L a R Y d x s r g e) {m : ℕ}
    (hm : x ^ m * g * e = e * (x ^ m * g)) :
    sec11P R g ⊓ Subgroup.centralizer {e} = A ⊔ Subgroup.zpowers (x ^ m * g) := by
  have hcard : Nat.card (A ⊔ Subgroup.zpowers (x ^ m * g) : Subgroup G) = 81 := by
    rw [Item1130Proof.card_sup_zpowers_eq (h.mem_normalizer_A (h.g₁_mem m)) (h.g₁_not_mem m)
      (h.g₁_pow_three h117 hm), h.card_eq]
  refine Item1130Proof.eq_of_le_of_ne ?_ inf_le_left ?_ ?_
  · refine sup_le (le_inf h.A_le_P fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.mul_comm_A y hy e h.e_mem)) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨h.g₁_mem m, Subgroup.mem_centralizer_singleton_iff.mpr hm⟩
  · intro heq
    have hx : x ∈ sec11P R g := h.x_mem_P
    rw [← heq] at hx
    exact h.x_e_ne (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2))
  · rw [h.card_P h117, hcard]
    norm_num

theorem centralizer_c_le (h117 : Item117) (h : Data G A c L a R Y d x s r g e) {m : ℕ}
    (hm : x ^ m * g * e = e * (x ^ m * g)) :
    sec11P R g ⊓ Subgroup.centralizer {e} ⊓ Subgroup.centralizer {c} ≤ A := by
  have hAC : A ≤ sec11P R g ⊓ Subgroup.centralizer {e} ⊓ Subgroup.centralizer {c} :=
    fun y hy => ⟨⟨h.A_le_P hy, Subgroup.mem_centralizer_singleton_iff.mpr
      (h.mul_comm_A y hy e h.e_mem)⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (h.mul_comm_A y hy c h.mem_A)⟩
  refine (Item1130Proof.eq_of_le_of_ne hAC inf_le_left ?_ ?_).le
  · intro heq
    have hg : x ^ m * g ∈ sec11P R g ⊓ Subgroup.centralizer {e} :=
      ⟨h.g₁_mem m, Subgroup.mem_centralizer_singleton_iff.mpr hm⟩
    rw [← heq] at hg
    apply h.g_c
    rw [← commutatorElement_eq_one_iff_mul_comm, ← h.commutator_g₁_c m]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2)
  · rw [h.centralizer_e_eq h117 hm, Item1130Proof.card_sup_zpowers_eq
      (h.mem_normalizer_A (h.g₁_mem m)) (h.g₁_not_mem m) (h.g₁_pow_three h117 hm)]

theorem centralizer_g₁_le (h117 : Item117) (h : Data G A c L a R Y d x s r g e) {m : ℕ}
    (hm : x ^ m * g * e = e * (x ^ m * g)) :
    A ⊓ Subgroup.centralizer {x ^ m * g} ≤ Subgroup.closure {e, d} := by
  have hd : x ^ m * g * d = d * (x ^ m * g) := by
    rw [mul_assoc, h.g_d h117, ← mul_assoc, h.pow_x_comm (Subgroup.mem_zpowers d), mul_assoc]
  have hDA : Subgroup.closure ({e, d} : Set G) ≤ A ⊓ Subgroup.centralizer {x ^ m * g} := by
    rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨⟨h.e_mem, Subgroup.mem_centralizer_singleton_iff.mpr hm.symm⟩,
      ⟨h.d_mem_A, Subgroup.mem_centralizer_singleton_iff.mpr hd.symm⟩⟩
  refine (Item1130Proof.eq_of_le_of_ne hDA inf_le_left ?_ ?_).le
  · intro heq
    have hc : c ∈ A := h.mem_A
    rw [← heq] at hc
    apply h.g_c
    rw [← commutatorElement_eq_one_iff_mul_comm, ← h.commutator_g₁_c m]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2).symm
  · rw [h.card_eq, h.card_D]

theorem centralizer_x_le (h : Data G A c L a R Y d x s r g e) :
    Subgroup.closure {e, d} ⊓ Subgroup.centralizer {x} ≤ Subgroup.zpowers d := by
  have hdD : Subgroup.zpowers d ≤ Subgroup.closure ({e, d} : Set G) ⊓ Subgroup.centralizer {x} :=
    le_inf (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Item1133Proof.commute_of_mem_zpowers rfl
          (Item1115Proof.d_mem_zpowers_x h.toSec11Data)).symm))
  refine (Item1130Proof.eq_of_le_of_ne hdD inf_le_left ?_ ?_).le
  · intro heq
    have he : e ∈ Subgroup.closure ({e, d} : Set G) := Subgroup.subset_closure (by simp)
    rw [← heq] at he
    exact h.x_e_ne (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp he).2).symm)
  · rw [h.card_D, Nat.card_zpowers, h.orderOf_d]

theorem theta_ne (h117 : Item117) (h : Data G A c L a R Y d x s r g e) {m : ℕ}
    (hm : x ^ m * g * e = e * (x ^ m * g)) : ⁅x, ⁅x, x ^ m * g⁆⁆ ≠ 1 := by
  intro h1
  set g₁ := x ^ m * g with hg₁
  have hg₁P := h.g₁_mem m
  have hwD : ⁅x, g₁⁆ ∈ Subgroup.closure {e, d} := by
    rw [← h.commutator_eq']
    exact Subgroup.commutator_mem_commutator h.x_mem_P hg₁P
  have hw : ⁅x, g₁⁆ ∈ Subgroup.zpowers d := h.centralizer_x_le ⟨hwD,
    Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp h1).symm⟩
  have hd : g₁ * d = d * g₁ := by
    rw [hg₁, mul_assoc, h.g_d h117, ← mul_assoc, h.pow_x_comm (Subgroup.mem_zpowers d), mul_assoc]
  have hle : sec11P R g ≤ Subgroup.closure ({c, a, x, g₁} : Set G) := by
    refine h.le_closure.trans ?_
    rw [Subgroup.closure_le]
    have hx : x ∈ Subgroup.closure ({c, a, x, g₁} : Set G) := Subgroup.subset_closure (by simp)
    have hg₁c : g₁ ∈ Subgroup.closure ({c, a, x, g₁} : Set G) :=
      Subgroup.subset_closure (by simp)
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp), hx, ?_⟩
    have e1 : g = (x ^ m)⁻¹ * g₁ := by rw [hg₁, inv_mul_cancel_left]
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hx m)) hg₁c
  have hN : Subgroup.closure ({c, a, x, g₁} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Item1133Proof.mem_normalizer_zpowers_of_commute (h.mul_comm_A c h.mem_A d h.d_mem_A),
      Item1133Proof.mem_normalizer_zpowers_of_commute (h.mul_comm_A a h.a_mem d h.d_mem_A),
      Item1133Proof.mem_normalizer_zpowers_of_commute (Item1133Proof.commute_of_mem_zpowers rfl
        (Item1115Proof.d_mem_zpowers_x h.toSec11Data)),
      Item1133Proof.mem_normalizer_zpowers_of_commute hd⟩
  have hPA := h.commutator_mem h117
  have hAP : ∀ u ∈ A, ∀ v ∈ sec11P R g, ⁅u, v⁆ ∈ Subgroup.zpowers d := fun u hu v hv => by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hPA v hv u hu)
  have hcP := h.A_le_P h.mem_A
  have haP := h.A_le_P h.a_mem
  have hself : ∀ u : G, ⁅u, u⁆ ∈ Subgroup.zpowers d := fun u => by
    rw [commutatorElement_self]
    exact Subgroup.one_mem _
  have hw' : ⁅g₁, x⁆ ∈ Subgroup.zpowers d := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ hw
  have hPP : ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.zpowers d := by
    refine (Subgroup.commutator_mono hle hle).trans (commutator_closure_le hN ?_)
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      first
      | exact hself _
      | exact hPA _ hcP _ h.mem_A
      | exact hPA _ haP _ h.a_mem
      | exact hPA _ h.x_mem_P _ h.mem_A
      | exact hPA _ h.x_mem_P _ h.a_mem
      | exact hPA _ hg₁P _ h.mem_A
      | exact hPA _ hg₁P _ h.a_mem
      | exact hPA _ hcP _ h.a_mem
      | exact hPA _ haP _ h.mem_A
      | exact hAP _ h.mem_A _ h.x_mem_P
      | exact hAP _ h.a_mem _ h.x_mem_P
      | exact hAP _ h.mem_A _ hg₁P
      | exact hAP _ h.a_mem _ hg₁P
      | exact hw
      | exact hw'
  have he : e ∈ ⁅sec11P R g, sec11P R g⁆ := by
    rw [h.commutator_eq']
    exact Subgroup.subset_closure (by simp)
  exact h.e_not_mem_zpowers (hPP he)

theorem exists_core (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    ∃ g₁ : G, Final1128Proof.Core (sec11P R g) A c e d x g₁ := by
  obtain ⟨m, hm⟩ := h.exists_pow_mul_comm h117
  exact ⟨x ^ m * g,
    { d_mem := h.A_le_P h.d_mem_A
      d_comm := h.d_comm h117
      orderOf_d := h.orderOf_d
      le_P := h.A_le_P
      c_mem := h.mem_A
      e_mem := h.e_mem
      d_mem_A := h.d_mem_A
      mul_comm_A := h.mul_comm_A
      commutator_mem := h.commutator_mem h117
      x_mem := h.x_mem_P
      g_mem := h.g₁_mem m
      commutator_eq := h.commutator_eq'
      x_e := h.x_e_ne
      g_e := hm
      theta_ne := h.theta_ne h117 hm
      centralizer_le := by rw [h.centralizer_e_eq h117 hm, sup_comm]
      centralizer_c_le := h.centralizer_c_le h117 hm
      centralizer_g_le := h.centralizer_g₁_le h117 hm
      centralizer_x_le := h.centralizer_x_le }⟩

end Data

end Final1128Proof

end CFSG.RankThree.PartTwo.Sec11
