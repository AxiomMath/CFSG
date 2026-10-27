module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec8.Hering611S3Step4bProof
  (not_mem_aschbacherSolvableCore_of_pow_three)
open scoped Bracket

variable {G : Type} [Group G] [Finite G]

private theorem glueC_mem_normalizer {S : Subgroup G} {g : G} (h : ∀ s ∈ S, g * s = s * g) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have hcomm := h _ hx
    have key : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hcomm]
        _ = g * x * g⁻¹ := by group
    rw [key]
    exact hx

private def glueCStab (K : Subgroup G) (W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
    Subgroup G where
  carrier := {x : G | ∃ hx : x ∈ Subgroup.normalizer (K : Set G),
    ∀ w : K ⧸ aschbacherSolvableCore 3 K, w ∈ W ↔ Sec12.thetaBarAct K ⟨x, hx⟩ w ∈ W}
  one_mem' := by
    show ∃ hx : (1 : G) ∈ Subgroup.normalizer (K : Set G),
      ∀ w : K ⧸ aschbacherSolvableCore 3 K, w ∈ W ↔ Sec12.thetaBarAct K ⟨1, hx⟩ w ∈ W
    refine ⟨Subgroup.one_mem _, fun w => ?_⟩
    have e : (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer (K : Set G)) = 1 := rfl
    rw [e, map_one, MulAut.one_apply]
  mul_mem' := by
    rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
    show ∃ hz : x * y ∈ Subgroup.normalizer (K : Set G),
      ∀ w : K ⧸ aschbacherSolvableCore 3 K, w ∈ W ↔ Sec12.thetaBarAct K ⟨x * y, hz⟩ w ∈ W
    refine ⟨Subgroup.mul_mem _ hx hy, fun w => (hyW w).trans ?_⟩
    have e : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, MulAut.mul_apply]
    exact hxW _
  inv_mem' := by
    rintro x ⟨hx, hxW⟩
    show ∃ hz : x⁻¹ ∈ Subgroup.normalizer (K : Set G),
      ∀ w : K ⧸ aschbacherSolvableCore 3 K, w ∈ W ↔ Sec12.thetaBarAct K ⟨x⁻¹, hz⟩ w ∈ W
    refine ⟨Subgroup.inv_mem _ hx, fun w => ?_⟩
    have e : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : Subgroup.normalizer (K : Set G)) =
        (⟨x, hx⟩ : Subgroup.normalizer (K : Set G))⁻¹ := rfl
    have key : ∀ u : K ⧸ aschbacherSolvableCore 3 K,
        Sec12.thetaBarAct K ⟨x, hx⟩ ((Sec12.thetaBarAct K ⟨x, hx⟩)⁻¹ u) = u := by
      intro u
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [e, map_inv]
    exact ⟨fun hw => (hxW _).mpr (by rwa [key]), fun hw => by
      have h2 := (hxW _).mp hw
      rwa [key] at h2⟩

private theorem mem_glueCStab {K : Subgroup G} {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)}
    {x : G} : x ∈ glueCStab K W ↔ ∃ hx : x ∈ Subgroup.normalizer (K : Set G),
      ∀ w : K ⧸ aschbacherSolvableCore 3 K, w ∈ W ↔ Sec12.thetaBarAct K ⟨x, hx⟩ w ∈ W :=
  Iff.rfl

section Act


variable {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G} {S K : Subgroup G}

theorem Cfg611.d_not_mem_K (C : Cfg611 G A c L E T d S K)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) : d ∉ K := by
  intro hdK
  have hd3 := C.toFrame611.d_pow_three
  have hd1 := C.toFrame611.d_ne_one
  have hcomm : ∀ g : K, g * (⟨d, hdK⟩ : K) = (⟨d, hdK⟩ : K) * g := by
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp (C.K_le_centralizer g.2)
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨d, hdK⟩ : K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) x
    rw [← map_mul, ← map_mul, hcomm g]
  rw [hZ, Subgroup.mem_bot] at hcen
  have hθ : (⟨d, hdK⟩ : K) ∈ aschbacherSolvableCore 3 K := (QuotientGroup.eq_one_iff _).mp hcen
  have h3 : (⟨d, hdK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have h1 : (⟨d, hdK⟩ : K) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  exact not_mem_aschbacherSolvableCore_of_pow_three h3 h1 hθ

theorem Cfg611.card_inf_K (C : Cfg611 G A c L E T d S K)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hAdec : ∀ x ∈ A, ∃ k ∈ A ⊓ K, x * k⁻¹ ∈ Subgroup.zpowers d) :
    Nat.card (A ⊓ K : Subgroup G) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 := C.toFrame611.d_pow_three
  have hd1 := C.toFrame611.d_ne_one
  have hdA := C.toFrame611.d_mem_A
  have hdK : d ∉ K := C.d_not_mem_K hZ
  have hd_ord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hM : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => C.toFrame611.comm_of_mem hx hy
  have hinf : Subgroup.zpowers d ⊓ (A ⊓ K) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxd, hxAK⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hdvd : orderOf x ∣ 3 := by
      have h := orderOf_dvd_of_mem_zpowers hxd
      rwa [hd_ord] at h
    have hord3 : orderOf x = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have heq : Subgroup.zpowers x = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxd)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord3, hd_ord]))
    have hdx : d ∈ Subgroup.zpowers x := by
      rw [heq]
      exact Subgroup.mem_zpowers d
    exact hdK (Subgroup.zpowers_le.mpr hxAK.2 hdx)
  have hsup : Subgroup.zpowers d ⊔ (A ⊓ K) = A := by
    apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.mpr hdA) inf_le_left
    · intro x hx
      obtain ⟨k, hk, hxk⟩ := hAdec x hx
      have h := Subgroup.mul_mem_sup hxk hk
      rwa [inv_mul_cancel_right] at h
  have hnorm : A ⊓ K ≤ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) :=
    fun g hg => glueC_mem_normalizer fun s hs =>
      hM g (Subgroup.mem_inf.mp hg).1 s (Subgroup.zpowers_le.mpr hdA hs)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers d) (A ⊓ K) hnorm (disjoint_iff.mpr hinf)
  rw [hsup, C.toFrame611.card_A, Nat.card_zpowers, hd_ord] at hcard
  omega

theorem Cfg611.invariant_of_gens (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) {k : K} {j : ℤ}
    (hkA : (k : G) ∈ A) (hck : c = d ^ j * (k : G))
    {a : G} (haA : a ∈ A) (haK : a ∈ K) {W : Subgroup (K ⧸ aschbacherSolvableCore 3 K)}
    (hk : QuotientGroup.mk' (aschbacherSolvableCore 3 K) k ∈
      Subgroup.normalizer (W : Set (K ⧸ aschbacherSolvableCore 3 K)))
    (ha : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩ ∈
      Subgroup.normalizer (W : Set (K ⧸ aschbacherSolvableCore 3 K)))
    (hE'K : Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ≤
      Subgroup.normalizer (K : Set G)) :
    ∀ (x : G) (hx : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a),
      ∀ w ∈ W, Sec12.thetaBarAct K ⟨x, hE'K hx⟩ w ∈ W := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := C.A_le_normalizer_K h45
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hAN C.toFrame611.d_mem_A
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAN C.c_mem
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hAN haA
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hd1 : Sec12.thetaBarAct K ⟨d, hdN⟩ = 1 := by
    have hmem : d ∈ A ⊓ thetaQuotCentralizer K := by
      rw [C.cent_K]
      exact Subgroup.mem_zpowers d
    exact (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hdN).mp hmem.2
  have hc1 : Sec12.thetaBarAct K ⟨c, hcN⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k) := by
    have e : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) =
        (⟨d, hdN⟩ : Subgroup.normalizer (K : Set G)) ^ j * ⟨(k : G), hkN⟩ := by
      apply Subtype.ext
      show c = d ^ j * (k : G)
      exact hck
    rw [e, map_mul, map_zpow, hd1, one_zpow, one_mul, Sec12.thetaBarAct_of_mem k.2]
  have ha1 : Sec12.thetaBarAct K ⟨a, haN⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) :=
    Sec12.thetaBarAct_of_mem haK
  have hdS : d ∈ glueCStab K W :=
    mem_glueCStab.mpr ⟨hdN, fun w => by rw [hd1, MulAut.one_apply]⟩
  have hcS : c ∈ glueCStab K W := mem_glueCStab.mpr ⟨hcN, fun w => by
    rw [hc1, MulAut.conj_apply]
    exact Subgroup.mem_normalizer_iff.mp hk w⟩
  have haS : a ∈ glueCStab K W := mem_glueCStab.mpr ⟨haN, fun w => by
    rw [ha1, MulAut.conj_apply]
    exact Subgroup.mem_normalizer_iff.mp ha w⟩
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a ≤ glueCStab K W :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hcS) (Subgroup.zpowers_le.mpr hdS))
      (Subgroup.zpowers_le.mpr haS)
  intro x hx w hw
  obtain ⟨hxN, hxW⟩ := mem_glueCStab.mp (hle hx)
  exact (hxW w).mp hw

theorem Cfg611.thetaBarAct_y (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) {k : K} {j : ℤ}
    (hkA : (k : G) ∈ A) (hck : c = d ^ j * (k : G)) {a : G} (haA : a ∈ A) (haK : a ∈ K)
    (m : ℕ) (hyN : c * a ^ m ∈ Subgroup.normalizer (K : Set G)) :
    Sec12.thetaBarAct K ⟨c * a ^ m, hyN⟩ = MulAut.conj
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) k *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨a, haK⟩) ^ m) := by
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := C.A_le_normalizer_K h45
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := hAN C.toFrame611.d_mem_A
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hAN haA
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hd1 : Sec12.thetaBarAct K ⟨d, hdN⟩ = 1 := by
    have hmem : d ∈ A ⊓ thetaQuotCentralizer K := by
      rw [C.cent_K]
      exact Subgroup.mem_zpowers d
    exact (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hdN).mp hmem.2
  have e : (⟨c * a ^ m, hyN⟩ : Subgroup.normalizer (K : Set G)) =
      (⟨d, hdN⟩ : Subgroup.normalizer (K : Set G)) ^ j *
        ((⟨(k : G), hkN⟩ : Subgroup.normalizer (K : Set G)) *
          (⟨a, haN⟩ : Subgroup.normalizer (K : Set G)) ^ m) := by
    apply Subtype.ext
    show c * a ^ m = d ^ j * ((k : G) * a ^ m)
    rw [hck, mul_assoc]
  rw [e, map_mul (Sec12.thetaBarAct K), map_zpow, hd1, one_zpow, one_mul,
    map_mul (Sec12.thetaBarAct K), map_pow (Sec12.thetaBarAct K),
    Sec12.thetaBarAct_of_mem k.2, Sec12.thetaBarAct_of_mem haK,
    map_mul (MulAut.conj), map_pow (MulAut.conj)]

end Act

end CFSG.RankThree.PartTwo.Sec8.Hering611
