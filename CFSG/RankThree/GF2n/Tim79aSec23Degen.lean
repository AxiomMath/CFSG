module

public import CFSG.RankThree.GF2n.Tim79aSec22Ti
public import CFSG.RankThree.GF2n.Tim79aSec23Defs
public import CFSG.RankThree.GF2n.Tim79aSec2Root

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

theorem isPGroup_zpowers_two {K : Type*} [Group K] {x : K} (h : x ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : orderOf x ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem isPGroup_zpowers_sup_zpowers {K : Type*} [Group K] {a b : K} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a * b) ^ 4 = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha4 : a ^ 4 = 1 := by
    have : a ^ 4 = (a * a) * (a * a) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [this, ha, one_mul]
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, hainv, hbinv]
    calc a * (a * b) * a = (a * a) * b * a := by simp only [mul_assoc]
      _ = b * a := by rw [ha, one_mul]
  have hkey : ∀ x ∈ Subgroup.zpowers (a * b), a * x * a⁻¹ ∈ Subgroup.zpowers (a * b) := by
    rintro x ⟨n, rfl⟩
    rw [← conj_zpow, h1]
    exact (Subgroup.zpowers (a * b)).zpow_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) n
  have hnorm : Subgroup.zpowers a ≤
      Subgroup.normalizer (Subgroup.zpowers (a * b) : Set K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hkey x hx, fun hx => ?_⟩
    have := hkey _ hx
    have e : a * (a * x * a⁻¹) * a⁻¹ = x := by
      rw [hainv]
      calc a * (a * x * a) * a = (a * a) * x * (a * a) := by simp only [mul_assoc]
        _ = x := by rw [ha]; simp
    rwa [e] at this
  have hP := (isPGroup_zpowers_two ha4).to_sup_of_normal_right' (isPGroup_zpowers_two hab) hnorm
  refine hP.to_le (sup_le le_sup_left (Subgroup.zpowers_le.2 ?_))
  have := mul_mem (inv_mem (le_sup_left (a := Subgroup.zpowers a) (b := Subgroup.zpowers (a * b))
    (Subgroup.mem_zpowers a))) (le_sup_right (a := Subgroup.zpowers a)
    (b := Subgroup.zpowers (a * b)) (Subgroup.mem_zpowers (a * b)))
  simpa using this


variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem degenerate_of_card_two (hd : Sec23Data V H) (h2 : Nat.card (barOf V H V) = 2) :
    ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4 := by
  intro d hdD e heD h4
  obtain ⟨⟨v, hvV⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.barOf_V_ne_bot
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hvX : v ∈ barOf V H (xOf V H) := barOf_V_le V H hvV
  set v' : Xbar V H := ⟨v, hvX⟩ with hv'
  have hv'D : v' ∈ Dy V H := hc.barOf_V_subset_dbarOf hvV hv1
  obtain ⟨d₀, hd₀⟩ := hd.isClass
  have hcl : ∀ g ∈ Dy V H, IsConj v' g := fun g hg => by
    have h1 : IsConj d₀ v' := by rw [hd₀] at hv'D; exact hv'D
    have h2' : IsConj d₀ g := by rw [hd₀] at hg; exact hg
    exact h1.symm.trans h2'
  obtain ⟨x, hx⟩ := isConj_iff.mp (hcl d hdD)
  obtain ⟨y, hy⟩ := isConj_iff.mp (hcl e heD)
  set z : Xbar V H := x⁻¹ * y with hz
  set w : Xbar V H := z * v' * z⁻¹ with hw
  have hv'2 : v' * v' = 1 := by
    rw [← sq]
    have := hd.root.1 v' hv'D
    rw [← this]; exact pow_orderOf_eq_one v'
  have hw2 : w * w = 1 := by
    calc w * w = z * (v' * v') * z⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hv'2]; group
  have hde : d * e = x * (v' * w) * x⁻¹ := by
    rw [← hx, ← hy, hw, hz]; group
  have hvw4 : orderOf (v' * w) = 4 := by
    have : orderOf (d * e) = orderOf (v' * w) := by
      rw [hde]
      exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective (v' * w)
    rw [← this]; exact h4
  have hvw4' : (v' * w) ^ 4 = 1 := by rw [← hvw4]; exact pow_orderOf_eq_one _
  obtain ⟨x', -, hx'z⟩ := mem_barOf_iff.mp z.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : v * v = 1 := by
    have := congrArg Subtype.val hv'2
    simpa using this
  have hov : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hVv : barOf V H V = Subgroup.zpowers v := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hvV) ?_).symm
    rw [Nat.card_zpowers, h2, hov]
  set wt : Hbar V H := z.1 * v * z.1⁻¹ with hwt
  have hbarconj : barOf V H (conjSubgroup (x' : G) V) = Subgroup.zpowers wt := by
    rw [← conjSubgroup_piBar_barOf, hx'z, hVv]
    unfold conjSubgroup
    rw [MonoidHom.map_zpowers]
    rfl
  have hwt2 : wt * wt = 1 := by
    have := congrArg Subtype.val hw2
    simpa [hw, hz, hv', hwt] using this
  have hvwh : (v * wt) ^ 4 = 1 := by
    have := congrArg Subtype.val hvw4'
    simpa [hw, hz, hv', hwt] using this
  have h2g : IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup (x' : G) V)) := by
    rw [hVv, hbarconj]
    exact isPGroup_zpowers_sup_zpowers hv2 hwt2 hvwh
  have hcomm := hc.commute_of_isPGroup_barOf_sup x'.2 h2g
  obtain ⟨u₀', hu₀V, hu₀v⟩ := mem_barOf_iff.mp hvV
  have hv₂ : (x' : G) * (u₀' : G) * (x' : G)⁻¹ ∈ conjSubgroup (x' : G) V := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hu₀V
  have hc2 := hcomm (u₀' : G) hu₀V _ hv₂
  have hc2' : u₀' * (x' * u₀' * x'⁻¹) = (x' * u₀' * x'⁻¹) * u₀' :=
    Subtype.ext (by simpa using hc2)
  have hc3 := congrArg (piBar V H) hc2'
  simp only [map_mul, map_inv, hu₀v, hx'z] at hc3
  have hvwc : v' * w = w * v' := Subtype.ext (by simpa [hv', hw, hz, hwt] using hc3)
  have hsq : (v' * w) * (v' * w) = 1 := by
    calc (v' * w) * (v' * w) = v' * (w * v') * w := by group
      _ = v' * (v' * w) * w := by rw [← hvwc]
      _ = (v' * v') * (w * w) := by group
      _ = 1 := by rw [hv'2, hw2, mul_one]
  have hdvd : orderOf (v' * w) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  rw [hvw4] at hdvd
  norm_num at hdvd

end MinCex

end CFSG.RankThree.GF2n.Tim79a
