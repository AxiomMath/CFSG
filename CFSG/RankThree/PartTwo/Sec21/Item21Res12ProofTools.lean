module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res10ProofLift
import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2InvolNine
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res12Proof

open CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_sq {t x : G} (ht : t ^ 2 = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ht]
  rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    rw [hr, ← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [hr, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem four_of_commute [Finite G] {t w : G} (ht : t ^ 2 = 1) (hw : w ^ 2 = 1) (ht1 : t ≠ 1)
    (hw1 : w ≠ 1) (hne : t ≠ w) (htw : t * w = w * t) :
    CFSG.Assembly.IsElemAbelian 2 (closure ({t, w} : Set G)) ∧
      Nat.card (closure ({t, w} : Set G)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : closure ({t, w} : Set G) ≤ centralizer (closure ({t, w} : Set G) : Set G) := by
    rw [centralizer_closure, closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
      rintro y (rfl | rfl) <;> simp [htw]
  refine ⟨⟨le_centralizer_iff_isMulCommutative.mp hle, fun x hx => ?_⟩, ?_⟩
  · induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ht
      · exact hw
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := (mem_centralizer_iff.mp (hle hy)) x hx
      rw [Commute.mul_pow hxy 2, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  · have hcl : closure ({t, w} : Set G) = zpowers t ⊔ zpowers w := by
      rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
    rw [hcl]
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers t)
      (zpowers w) (fun x hx y hy => by
        rcases eq_one_or_eq_of_mem_zpowers_of_sq ht hx with rfl | rfl <;>
          rcases eq_one_or_eq_of_mem_zpowers_of_sq hw hy with rfl | rfl <;> simp [htw])
    have hinf : zpowers t ⊓ zpowers w = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxt, hxw⟩
      rcases eq_one_or_eq_of_mem_zpowers_of_sq ht hxt with rfl | rfl
      · exact one_mem _
      · exfalso
        rcases eq_one_or_eq_of_mem_zpowers_of_sq hw hxw with h | h
        · exact ht1 h
        · exact hne h
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ht ht1,
      orderOf_eq_prime hw hw1] at hcard
    exact hcard

theorem mem_or_exists_commute [Finite G] {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) {t s : G} (htX : t ∈ X) (hsX : s ∈ X)
    (ht2 : t ^ 2 = 1) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hsN : s ∈ N) :
    t ∈ N ∨ ∃ w ∈ X, w ^ 2 = 1 ∧ w ≠ 1 ∧ w ≠ t ∧ t * w = w * t := by
  by_cases hts : t = s
  · exact Or.inl (hts ▸ hsN)
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have hss : s * s = 1 := by rw [← pow_two, hs2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  obtain ⟨u, hu⟩ : ∃ u : G, u = t * s := ⟨_, rfl⟩
  have huX : u ∈ X := hu ▸ mul_mem htX hsX
  have htu : t * u * t⁻¹ = u⁻¹ := by
    rw [hu, htinv, mul_inv_rev, hsinv, htinv]
    calc t * (t * s) * t = (t * t) * s * t := by group
      _ = s * t := by rw [htt, one_mul]
  have hconj : ∀ n : ℕ, t * u ^ n * t⁻¹ = (u ^ n)⁻¹ := by
    intro n
    have h := map_pow (MulAut.conj t) u n
    simp only [MulAut.conj_apply] at h
    rw [h, htu, inv_pow]
  have hu1 : u ≠ 1 := by
    intro h
    apply hts
    calc t = t * (s * s) := by rw [hss, mul_one]
      _ = u * s := by rw [hu, mul_assoc]
      _ = s := by rw [h, one_mul]
  have hum : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  have hm0 : 0 < orderOf u := orderOf_pos u
  rcases Nat.even_or_odd (orderOf u) with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    right
    have hk0 : k ≠ 0 := by omega
    have hkm : k < orderOf u := by omega
    have hw2 : (u ^ k) ^ 2 = 1 := by
      rw [← pow_mul, show k * 2 = orderOf u by omega, hum]
    have hw1 : u ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hkm
    have hwinv : (u ^ k)⁻¹ = u ^ k := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hw2])
    have htw : t * u ^ k = u ^ k * t := by
      have h := hconj k
      rw [hwinv] at h
      calc t * u ^ k = t * u ^ k * t⁻¹ * t := by group
        _ = u ^ k * t := by rw [h]
    refine ⟨u ^ k, pow_mem huX k, hw2, hw1, fun hwt => ?_, htw⟩
    have hc : t * u = u * t := by
      rw [← hwt]
      exact ((Commute.self_pow u k).eq).symm
    have h2 : t * u * t⁻¹ = u := by rw [hc, mul_inv_cancel_right]
    have hu2 : u ^ 2 = 1 := by
      have h3 : u⁻¹ = u := htu.symm.trans h2
      rw [pow_two]
      calc u * u = u * u⁻¹ := by rw [h3]
        _ = 1 := mul_inv_cancel u
    have hm2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
    have hk1 : k = 1 := by
      have := Nat.le_of_dvd (by norm_num) hm2
      omega
    apply hs1
    rw [hk1, pow_one, hu] at hwt
    calc s = t⁻¹ * (t * s) := by group
      _ = 1 := by rw [hwt, inv_mul_cancel]
  ·
    left
    have hts' : t * (u ^ k)⁻¹ = u ^ k * t := by
      have h := hconj k
      have h' : t * (u ^ k)⁻¹ * t⁻¹ = u ^ k := by
        calc t * (u ^ k)⁻¹ * t⁻¹ = (t * u ^ k * t⁻¹)⁻¹ := by group
          _ = u ^ k := by rw [h, inv_inv]
      calc t * (u ^ k)⁻¹ = t * (u ^ k)⁻¹ * t⁻¹ * t := by group
        _ = u ^ k * t := by rw [h']
    have hsu : s = t * u := by
      rw [hu, ← mul_assoc, htt, one_mul]
    have key : u ^ (k + 1) * s * (u ^ (k + 1))⁻¹ = t := by
      calc u ^ (k + 1) * s * (u ^ (k + 1))⁻¹
          = u ^ (k + 1) * t * (u * (u ^ (k + 1))⁻¹) := by rw [hsu]; group
        _ = u ^ (k + 1) * t * (u ^ k)⁻¹ := by
            rw [pow_succ, mul_inv_rev, mul_inv_cancel_left]
        _ = u ^ (k + 1) * (t * (u ^ k)⁻¹) := by group
        _ = u ^ (k + 1) * (u ^ k * t) := by rw [hts']
        _ = u ^ orderOf u * t := by
            rw [← mul_assoc, ← pow_add, show k + 1 + k = orderOf u by omega]
        _ = t := by rw [hum, one_mul]
    rw [← key]
    exact (mem_normalizer_iff.mp (hXN (pow_mem huX (k + 1))) s).mp hsN

theorem conj_mul_inv_mem_theta_of_j2
    [Finite G]
    {L F : Subgroup G} (hJ2 : Nonempty (lBar L ≃* NativeSporadic.J2)) (hFL : F ≤ L)
    (hF3 : IsPGroup 3 F) (hF9 : Nat.card F = 9) {t : G}
    (htN : t ∈ normalizer (L : Set G)) (ht2 : t ^ 2 = 1) (htF : ∀ x ∈ F, t * x * t⁻¹ = x) :
    ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set F' := F.subgroupOf L with hF'
  have hF'3 : IsPGroup 3 F' := hF3.comap_subtype
  have hinj : Set.InjOn (QuotientGroup.mk' θ) (F' : Set ↥L) :=
    injOn_mk_of_isPGroup Nat.prime_three hF'3
  have hcard : Nat.card (F'.map (QuotientGroup.mk' θ)) = 9 := by
    rw [Item21Res10Proof.card_map_eq_of_injOn' _ hinj, hF',
      Nat.card_congr (subgroupOfEquivOfLe hFL).toEquiv, hF9]
  set σ := Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨t, htN⟩) with hσ
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : (⟨t, htN⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσF : ∀ e ∈ F'.map (QuotientGroup.mk' θ), σ e = e := by
    rintro _ ⟨β, hβ, rfl⟩
    have hβF : (β : G) ∈ F := mem_subgroupOf.mp hβ
    change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨t, htN⟩ β) = QuotientGroup.mk' θ β
    congr 1
    exact Subtype.ext (htF _ hβF)
  have hσ1 : σ = 1 := KFacts.ks152J2InvolNine (lBar L) hJ2 _ hcard σ hσ2 hσF
  intro l hl
  have h1 := congrArg (fun f : MulAut (lBar L) => f (QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩))
    hσ1
  change QuotientGroup.mk' θ (L.normalizerMonoidHom ⟨t, htN⟩ ⟨l⁻¹, inv_mem hl⟩) =
    QuotientGroup.mk' θ ⟨l⁻¹, inv_mem hl⟩ at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  refine ⟨_, h1, ?_⟩
  simp [mul_assoc]

theorem exists_involution_of_even [Finite G] {A : Subgroup G} (hS : A ∈ partTwoS G) {a : G}
    (haA : a ∈ A) (ha1 : a ≠ 1) {X : Subgroup G} (hXa : X ∈ thetaComponentsAt 3 a)
    (hAX : A ≤ normalizer (X : Set G)) (hev : ¬ Odd (Nat.card (aschbacherSolvableCore 3 ↥X))) :
    ∃ t : G, t ∈ inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set G)) ∧
      t ∈ centralizer (A : Set G) ∧ t ^ 2 = 1 ∧ t ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hT3, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set Γ : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X with hΓ
  have hcardΓ : Nat.card Γ = Nat.card (aschbacherSolvableCore 3 X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hΓ3 : ¬ 3 ∣ Nat.card Γ := hcardΓ ▸ hT3
  have hAΓ : A ≤ normalizer (Γ : Set G) := le_normalizer_theta hAX
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hS.1.1
  obtain ⟨P, hP⟩ := Item21Res10Proof.exists_sylow_two_normalized hAΓ hA3 hΓ3
  have h2 : 2 ∣ Nat.card Γ := by
    rw [hcardΓ]
    exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (P.dvd_card_of_dvd_card h2)
  set P' : Subgroup G := (P : Subgroup Γ).map Γ.subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map Γ.subtype
  have hAP' : A ≤ normalizer (P' : Set G) := by
    intro e he
    refine mem_normalizer_fintype fun p hp => ?_
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨y', hy', hy'e⟩ := hP e he y hy
    exact ⟨y', hy', hy'e⟩
  have hP'θ : P' ≤ inSubgroup (aschbacherSolvableCore 3) (centralizer ({a} : Set G)) :=
    (map_subtype_le _).trans (theta_le_theta_centralizer hXa)
  have hcomm : ⁅P', A⁆ = ⊥ :=
    Sec6.commutator_eq_bot_of_mem_partTwoS hS haA ha1 le_rfl hP'θ hP'2 hAP'
  have hxP' : ((x : Γ) : G) ∈ P' := ⟨(x : Γ), x.2, rfl⟩
  have hord : orderOf ((x : Γ) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  refine ⟨((x : Γ) : G), hP'θ hxP', ?_, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro y hy
    have h1 := commutator_mem_commutator hxP' hy
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · have h1 := pow_orderOf_eq_one ((x : Γ) : G)
    rwa [hord] at h1
  · intro h
    rw [h, orderOf_one] at hord
    norm_num at hord

end CFSG.RankThree.PartTwo.Sec21.Item21Res12Proof
