module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SL14
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Frame

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

private theorem frame611_mem_normalizer_of_commute_forall {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x = x * g) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy, mul_inv_cancel_right]
    exact hy
  · intro hz
    have hc := h _ hz
    have e : g * y * g⁻¹ = y := mul_left_cancel (a := g) (by rw [hc, inv_mul_cancel_right])
    exact e ▸ hz

theorem Frame611.cd_inf_L (F : Frame611 G A c L E T d) :
    (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊓ L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcd : Commute c d := F.comm_of_mem F.c_mem F.d_mem_A
  have hPA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr F.c_mem) (Subgroup.zpowers_le.mpr F.d_mem_A)
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := by
    have hc : c ∈ A ⊓ Sec4.thetaQuotCentralizer L := by
      rw [F.cent_L]
      exact Subgroup.mem_zpowers c
    exact hc.2
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Sec12.thetaQuotCentralizer_le_normalizer' L hcC
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L F.d_field (by decide)
  have hρc : Sec12.thetaBarAct L ⟨c, hcN⟩ = 1 :=
    (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hcN).mp hcC
  have hdcube : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact Subtype.ext (by simpa using F.d_pow_three)
  have hρd3 : Sec12.thetaBarAct L ⟨d, hdN⟩ ^ (3 : ℤ) = 1 := by
    rw [← map_zpow, hdcube, map_one]
  have hmono : ∀ (s t : ℤ) (hN : c ^ s * d ^ t ∈ Subgroup.normalizer (L : Set G)),
      Sec12.thetaBarAct L ⟨c ^ s * d ^ t, hN⟩ =
        Sec12.thetaBarAct L ⟨c, hcN⟩ ^ s * Sec12.thetaBarAct L ⟨d, hdN⟩ ^ t := by
    intro s t hN
    have e : (⟨c ^ s * d ^ t, hN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨c, hcN⟩ ^ s * ⟨d, hdN⟩ ^ t := Subtype.ext (by simp)
    rw [e, map_mul, map_zpow, map_zpow]
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxL⟩
  have hxA : x ∈ A := hPA hxP
  have hle : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    refine Subgroup.zpowers_le.mpr (frame611_mem_normalizer_of_commute_forall ?_)
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hcd.zpow_right m).eq
  have hxM : x ∈ (Subgroup.zpowers c : Set G) * (Subgroup.zpowers d : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hxP
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxM
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  subst hab
  have hxN : c ^ s * d ^ t ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hxL
  have hρx : Sec12.thetaBarAct L ⟨c ^ s * d ^ t, hxN⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c ^ s * d ^ t, hxL⟩) :=
    Sec12.thetaBarAct_of_mem hxL
  have hρx' : Sec12.thetaBarAct L ⟨c ^ s * d ^ t, hxN⟩ = Sec12.thetaBarAct L ⟨d, hdN⟩ ^ t := by
    rw [hmono, hρc, one_zpow, one_mul]
  have h3t : 3 ∣ t := by
    by_contra hnd
    obtain ⟨a', b', hab'⟩ : ∃ a' b' : ℤ, t * a' + 3 * b' = 1 := by
      rcases (show t % 3 = 1 ∨ t % 3 = 2 by omega) with h | h
      · exact ⟨1, -(t / 3), by omega⟩
      · exact ⟨2, -(2 * (t / 3) + 1), by omega⟩
    have hd1 : Sec12.thetaBarAct L ⟨d, hdN⟩ = MulAut.conj
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c ^ s * d ^ t, hxL⟩ ^ a') := by
      calc Sec12.thetaBarAct L ⟨d, hdN⟩
          = Sec12.thetaBarAct L ⟨d, hdN⟩ ^ (t * a' + 3 * b') := by rw [hab', zpow_one]
        _ = (Sec12.thetaBarAct L ⟨d, hdN⟩ ^ t) ^ a' *
              (Sec12.thetaBarAct L ⟨d, hdN⟩ ^ (3 : ℤ)) ^ b' := by
          rw [zpow_add, zpow_mul, zpow_mul]
        _ = (MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c ^ s * d ^ t, hxL⟩)) ^
              a' := by
          rw [← hρx', hρx, hρd3, one_zpow, mul_one]
        _ = MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c ^ s * d ^ t, hxL⟩ ^
              a') := by
          rw [map_zpow]
    exact hnot ⟨_, hd1.symm⟩
  obtain ⟨k, rfl⟩ := h3t
  have hρ1 : Sec12.thetaBarAct L ⟨c ^ s * d ^ (3 * k), hxN⟩ = 1 := by
    rw [hρx', zpow_mul, hρd3, one_zpow]
  have hconj1 : MulAut.conj
      (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c ^ s * d ^ (3 * k), hxL⟩) = 1 := by
    rw [← hρx]
    exact hρ1
  have hπ := Sec12.mem_center_of_conj_eq_one hconj1
  rw [F.center_L_bot, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hπ
  have hθ : c ^ s * d ^ (3 * k) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
    Subgroup.mem_map_of_mem L.subtype hπ
  have hx3 : (c ^ s * d ^ (3 * k)) ^ 3 = 1 := F.isElemAbelian.2 _ hxA
  have hθ3 := Sec11.not_three_dvd_card_inSubgroup_theta L
  have hord : orderOf (c ^ s * d ^ (3 * k)) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hordθ : orderOf (c ^ s * d ^ (3 * k)) ∣
      Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    have h := orderOf_dvd_natCard (⟨c ^ s * d ^ (3 * k), hθ⟩ :
      inSubgroup (aschbacherSolvableCore 3) L)
    rwa [Subgroup.orderOf_mk] at h
  rw [Subgroup.mem_bot]
  rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
  · exact orderOf_eq_one_iff.mp h1
  · rw [h3] at hordθ
    exact absurd hordθ hθ3

theorem Frame611.card_cd (F : Frame611 G A c L E T d) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcd : Commute c d := F.comm_of_mem F.c_mem F.d_mem_A
  have hcardc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime F.c_pow_three F.c_ne_one]
  have hcardd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime F.d_pow_three F.d_ne_one]
  have hdisj : Disjoint (Subgroup.zpowers c) (Subgroup.zpowers d) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers d) ∣ 3 := by
      rw [← hcardd]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ Subgroup.zpowers d = Subgroup.zpowers d :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hcardd, h3]))
      have hdc : Subgroup.zpowers d ≤ Subgroup.zpowers c := by
        rw [← heq]
        exact inf_le_left
      exact F.d_not_mem (hdc (Subgroup.mem_zpowers d))
  have hnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Subgroup.zpowers_le.mpr (frame611_mem_normalizer_of_commute_forall ?_)
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((hcd.symm).zpow_right m).eq
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    hcardc, hcardd]

theorem Frame611.A_eq_sup (h45 : Sec4.Item4_5) (F : Frame611 G A c L E T d) :
    A = (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊔ (A ⊓ L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPA : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr F.c_mem) (Subgroup.zpowers_le.mpr F.d_mem_A)
  have hnorm : A ⊓ L ≤ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro k hk
    refine frame611_mem_normalizer_of_commute_forall ?_
    intro x hx
    exact F.comm_of_mem (Subgroup.mem_inf.mp hk).1 (hPA hx)
  have hdisj : Disjoint (Subgroup.zpowers c ⊔ Subgroup.zpowers d) (A ⊓ L) := by
    rw [disjoint_iff]
    have h0 := inf_le_inf_left (Subgroup.zpowers c ⊔ Subgroup.zpowers d)
      (inf_le_right : A ⊓ L ≤ L)
    rw [F.cd_inf_L] at h0
    exact le_bot_iff.mp h0
  have hcard : Nat.card ↥((Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊔ (A ⊓ L)) = 81 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      F.card_cd, F.card_inf_L h45]
  have hle : (Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊔ (A ⊓ L) ≤ A :=
    sup_le hPA inf_le_left
  have hge : Nat.card A ≤ Nat.card ↥((Subgroup.zpowers c ⊔ Subgroup.zpowers d) ⊔ (A ⊓ L)) :=
    le_of_eq (by rw [F.card_A, hcard])
  exact (Subgroup.eq_of_le_of_card_ge hle hge).symm

end Frame

end CFSG.RankThree.PartTwo.Sec8.Hering611
