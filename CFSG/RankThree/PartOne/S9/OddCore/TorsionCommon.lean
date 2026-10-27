module

public import CFSG.RankThree.PartOne.S9.Defs
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_forall {R Y : Subgroup G} (h : ∀ r ∈ R, ∀ y ∈ Y, r * y * r⁻¹ ∈ Y) :
    R ≤ Subgroup.normalizer (Y : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h r hr y hy, fun hy => ?_⟩
  have h1 := h r⁻¹ (R.inv_mem hr) _ hy
  have e : r⁻¹ * (r * y * r⁻¹) * r⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem omegaOne_eq_of_forall {q : ℕ} {Q D : Subgroup G} (hDQ : D ≤ Q) (hDe : ∀ x ∈ D, x ^ q = 1)
    (h : ∀ x ∈ Q, x ^ q = 1 → x ∈ D) : omegaOne q Q = D :=
  le_antisymm ((Subgroup.closure_le D).2 fun x hx => h x hx.1 hx.2)
    fun d hd => Subgroup.subset_closure ⟨hDQ hd, hDe d hd⟩

theorem commutator_commutator_eq_bot_of_central {W Q : Subgroup G} (hWQ : W ≤ Q)
    (h : ∀ w ∈ W, ∀ g ∈ Q, ∀ u ∈ Q, u * ⁅w, g⁆ = ⁅w, g⁆ * u) : ⁅⁅W, W⁆, W⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
  intro w hw g hg
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact h w hw g (hWQ hg) u (hWQ hu)

theorem isElementaryAbelian_of_forall {p : ℕ} {X : Subgroup G}
    (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hp : ∀ x ∈ X, x ^ p = 1) :
    IsElementaryAbelian p X := CFSG.IsElementaryAbelian.of_forall hc hp

theorem mul_comm_of_isElementaryAbelian {p : ℕ} {X : Subgroup G} (h : IsElementaryAbelian p X)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x :=
  congrArg Subtype.val (h.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : X) ⟨y, hy⟩)

theorem exists_mul_of_mem_sup_of_commute {K L : Subgroup G}
    (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) {x : G} (hx : x ∈ K ⊔ L) :
    ∃ k ∈ K, ∃ l ∈ L, x = k * l := by
  have comm : ∀ (m : K) (n : L), Commute (K.subtype m) (L.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hrange := MonoidHom.noncommCoprod_range K.subtype L.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem isElementaryAbelian_sup_of_commute {p : ℕ} {K L : Subgroup G}
    (hK : IsElementaryAbelian p K) (hL : IsElementaryAbelian p L)
    (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) : IsElementaryAbelian p ↥(K ⊔ L) := by
  have hKe : ∀ x ∈ K, x ^ p = 1 := fun x hx => by
    have := hK
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hLe : ∀ x ∈ L, x ^ p = 1 := fun x hx => by
    have := hL
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    obtain ⟨k', hk', l', hl', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 : Commute k k' := mul_comm_of_isElementaryAbelian hK hk hk'
    have h2 : Commute l l' := mul_comm_of_isElementaryAbelian hL hl hl'
    have h3 : Commute k l' := hcomm k hk l' hl'
    have h4 : Commute l k' := (hcomm k' hk' l hl).symm
    exact ((h1.mul_right h3).mul_left (h4.mul_right h2)).eq
  · obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    rw [(show Commute k l from hcomm k hk l hl).mul_pow, hKe k hk, hLe l hl, one_mul]

theorem card_sup_of_commute_disjoint {K L : Subgroup G}
    (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hdisj : Disjoint K L) :
    Nat.card ↥(K ⊔ L) = Nat.card K * Nat.card L := by
  have comm : ∀ (m : K) (n : L), Commute (K.subtype m) (L.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hinj := (MonoidHom.noncommCoprod_injective K.subtype L.subtype comm).2
    ⟨K.subtype_injective, L.subtype_injective, by simpa [Subgroup.range_subtype] using hdisj⟩
  have hrange := MonoidHom.noncommCoprod_range K.subtype L.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem zpowers_eq_of_mem_of_ne_one {q : ℕ} (hq : q.Prime) [Finite G] {x y : G}
    (hx : orderOf x = q) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = Subgroup.zpowers x := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
  have hdvd : orderOf y ∣ q := hx ▸ orderOf_dvd_of_mem_zpowers hy
  have hy' : orderOf y = q := by
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy']

theorem three_le_pRank_of_commuting {q : ℕ} (hq : q.Prime) [Finite G] {H : Subgroup G}
    {x z c : G} (hx : x ∈ H) (hz : z ∈ H) (hc : c ∈ H)
    (hxz : x * z = z * x) (hxc : x * c = c * x) (hzc : z * c = c * z)
    (hxq : x ^ q = 1) (hzq : z ^ q = 1) (hcq : c ^ q = 1)
    (hx1 : x ≠ 1) (hz1 : z ≠ 1) (hzx : z ∉ Subgroup.zpowers x)
    (hcxz : c ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers z) : 3 ≤ CFSG.pRank q ↥H := by
  have : Fact q.Prime := ⟨hq⟩
  have hc1 : c ≠ 1 := fun h => hcxz (by rw [h]; exact one_mem _)
  have hox : orderOf x = q := orderOf_eq_prime hxq hx1
  have hoz : orderOf z = q := orderOf_eq_prime hzq hz1
  have hoc : orderOf c = q := orderOf_eq_prime hcq hc1
  have hKel : IsElementaryAbelian q (Subgroup.zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hxq
  have hLel : IsElementaryAbelian q (Subgroup.zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hzq
  have hMel : IsElementaryAbelian q (Subgroup.zpowers c) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hcq
  have hcomm : ∀ {a b : G}, a * b = b * a → ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b,
      u * v = v * u := by
    intro a b hab u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((show Commute a b from hab).zpow_zpow i j).eq
  have hKL := hcomm hxz
  have hdisj1 : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro y hyx hyz
    by_contra hy1
    apply hzx
    have h1 := zpowers_eq_of_mem_of_ne_one hq hoz hyz hy1
    have h2 : z ∈ Subgroup.zpowers y := by rw [h1]; exact Subgroup.mem_zpowers z
    exact Subgroup.zpowers_le.2 hyx h2
  have hE₂el := isElementaryAbelian_sup_of_commute hKel hLel hKL
  have hE₂card : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) = q ^ 2 := by
    rw [card_sup_of_commute_disjoint hKL hdisj1, Nat.card_zpowers, Nat.card_zpowers, hox, hoz]
    ring
  have hE₂c : ∀ e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, ∀ m ∈ Subgroup.zpowers c,
      e * m = m * e := by
    intro e he m hm
    obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hKL he
    have h1 := hcomm hxc k hk m hm
    have h2 := hcomm hzc l hl m hm
    calc k * l * m = k * (l * m) := by rw [mul_assoc]
      _ = k * (m * l) := by rw [h2]
      _ = (k * m) * l := by rw [mul_assoc]
      _ = (m * k) * l := by rw [h1]
      _ = m * (k * l) := by rw [mul_assoc]
  have hdisj2 : Disjoint (Subgroup.zpowers x ⊔ Subgroup.zpowers z) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro y hyE hyc
    by_contra hy1
    apply hcxz
    have h1 := zpowers_eq_of_mem_of_ne_one hq hoc hyc hy1
    have h2 : c ∈ Subgroup.zpowers y := by rw [h1]; exact Subgroup.mem_zpowers c
    exact Subgroup.zpowers_le.2 hyE h2
  have hFel := isElementaryAbelian_sup_of_commute hE₂el hMel hE₂c
  have hFcard : Nat.card ↥((Subgroup.zpowers x ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers c) =
      q ^ 3 := by
    rw [card_sup_of_commute_disjoint hE₂c hdisj2, hE₂card, Nat.card_zpowers, hoc]
    ring
  have hFH : (Subgroup.zpowers x ⊔ Subgroup.zpowers z) ⊔ Subgroup.zpowers c ≤ H :=
    sup_le (sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hz))
      (Subgroup.zpowers_le.2 hc)
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq H]
  exact CFSG.SectionRank.le_pRank hq.one_lt hFH
    ⟨hFel.toIsMulCommutative, fun y hy => elemPow_eq_one_of_isElementaryAbelian y hy⟩ hFcard

end CFSG.RankThree.PartOne.Torsion37
