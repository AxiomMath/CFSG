module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier

open CFSG.Assembly.RankThreeEven

@[expose] def ThreeRankLeOne (X : Type*) [Group X] : Prop :=
  ∀ a b : X, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∈ Subgroup.zpowers a

section Transfer

variable {X Y : Type*} [Group X] [Group Y]

theorem ThreeRankLeOne.of_injective {f : X →* Y} (hf : Function.Injective f)
    (h : ThreeRankLeOne Y) : ThreeRankLeOne X := by
  intro a b ha hb hab ha1
  have hfa : f a ≠ 1 := fun h1 => ha1 (hf (h1.trans (map_one f).symm))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (h (f a) (f b) (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
      (by rw [← map_mul, ← map_mul, hab]) hfa)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hf (by rw [map_zpow, hk])⟩

theorem ThreeRankLeOne.of_mulEquiv (e : X ≃* Y) (h : ThreeRankLeOne Y) : ThreeRankLeOne X :=
  ThreeRankLeOne.of_injective (f := e.toMonoidHom) e.injective h

theorem ThreeRankLeOne.centralizer_of_isConj {s t : X} (hst : IsConj s t)
    (h : ThreeRankLeOne (Subgroup.centralizer {t} : Subgroup X)) :
    ThreeRankLeOne (Subgroup.centralizer {s} : Subgroup X) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hst
  let f : (Subgroup.centralizer {s} : Subgroup X) →* (Subgroup.centralizer {t} : Subgroup X) :=
    ((MulAut.conj c).toMonoidHom.comp (Subgroup.centralizer {s}).subtype).codRestrict _
      fun x => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hx : (x : X) * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
          MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hc]
        calc c * x * c⁻¹ * (c * s * c⁻¹) = c * (x * s) * c⁻¹ := by group
          _ = c * (s * x) * c⁻¹ := by rw [hx]
          _ = c * s * c⁻¹ * (c * x * c⁻¹) := by group
  refine ThreeRankLeOne.of_injective (f := f) (fun x y hxy => Subtype.ext ?_) h
  have := congrArg Subtype.val hxy
  simpa [f] using this

theorem ThreeRankLeOne.centralizer_of_le {H X : Subgroup Y} {s : H}
    (hX : H ⊓ Subgroup.centralizer {(s : Y)} ≤ X) (h : ThreeRankLeOne X) :
    ThreeRankLeOne (Subgroup.centralizer {s} : Subgroup H) := by
  let f : (Subgroup.centralizer {s} : Subgroup H) →* X :=
    (H.subtype.comp (Subgroup.centralizer {s}).subtype).codRestrict X fun x => hX
      (Subgroup.mem_inf.mpr ⟨(x : H).2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2))⟩)
  refine ThreeRankLeOne.of_injective (f := f) (fun x y hxy => ?_) h
  have := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext (by simpa [f] using this))

theorem ThreeRankLeOne.of_eq {A B : Subgroup Y} (hAB : A = B) (h : ThreeRankLeOne B) :
    ThreeRankLeOne A :=
  ThreeRankLeOne.of_mulEquiv (MulEquiv.subgroupCongr hAB) h

end Transfer

theorem threeRankLeOne_of_not_dvd {X : Type*} [Group X] [Finite X] (h : ¬ 3 ∣ Nat.card X) :
    ThreeRankLeOne X := by
  intro a b ha hb hab ha1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : orderOf a = 3 := orderOf_eq_prime ha ha1
  exact absurd (h3 ▸ orderOf_dvd_natCard a) h

section SL2

variable {K : Type*} [Field K] [CharP K 2]

theorem sq_add_self_add_one_eq_zero {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) K) ^ 2 + (g : Matrix (Fin 2) (Fin 2) K) + 1 = 0 := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = g := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨t, ht⟩ : ∃ t : K, t = M 0 0 + M 1 1 := ⟨_, rfl⟩
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two, hM]
    exact g.2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hCH : M * M = t • M + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht] <;>
      first | linear_combination (-1 : K) * hdet - h2 | ring
  have hM3 : M ^ 3 = 1 := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow, hg, Matrix.SpecialLinearGroup.coe_one]
  have hlin : (t * t + 1) • M + t • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have h3 : M ^ 3 = (t * t + 1) • M + t • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [pow_succ', pow_two, hCH, mul_add, mul_one, Matrix.mul_smul, hCH, smul_add, smul_smul,
        add_smul, one_smul]
      abel
    exact h3.symm.trans hM3
  by_cases ht1 : t = 1
  · rw [pow_two, hCH, ht1, one_smul]
    calc M + 1 + M + 1 = (M + M) + (1 + 1) := by abel
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  exfalso
  have ht1' : t + 1 ≠ 0 := by
    intro h
    apply ht1
    have := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this
  have hsq : t * t + 1 = (t + 1) * (t + 1) := by linear_combination (-t) * h2
  have hscal : M = (t + 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : ((t + 1) * (t + 1)) • M = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hsq]
      have e := congrArg (· + t • (1 : Matrix (Fin 2) (Fin 2) K)) hlin
      simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero] at e
      rw [e, add_smul, one_smul, add_comm]
    have h2' := congrArg (((t + 1) * (t + 1))⁻¹ • ·) h1
    simp only [smul_smul] at h2'
    rw [inv_mul_cancel₀ (mul_ne_zero ht1' ht1'), one_smul] at h2'
    rw [h2', mul_inv, mul_assoc, inv_mul_cancel₀ ht1', mul_one]
  obtain ⟨c, hc⟩ : ∃ c : K, c = (t + 1)⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hscal
  have hc2 : c * c = 1 := by
    have h := hdet
    rw [hscal] at h
    simpa using h
  have hc1 : c = 1 := by
    have h0 : (c + 1) * (c + 1) = 0 := by linear_combination hc2 + (c + 1) * h2
    have := eq_neg_of_add_eq_zero_left (mul_self_eq_zero.mp h0)
    rwa [CharTwo.neg_eq] at this
  apply hg1
  ext i j
  have h := congrFun (congrFun hscal i) j
  rw [hc1, one_smul, hM] at h
  simpa using h

theorem threeRankLeOne_SL2 : ThreeRankLeOne (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro a b ha hb hab ha1
  by_cases hb1 : b = 1
  · rw [hb1]
    exact Subgroup.one_mem _
  by_cases hab1 : a * b = 1
  · rw [eq_inv_of_mul_eq_one_right hab1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hc : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hc.mul_pow, ha, hb, one_mul]
  have hA := sq_add_self_add_one_eq_zero ha ha1
  have hB := sq_add_self_add_one_eq_zero hb hb1
  have hAB := sq_add_self_add_one_eq_zero hab3 hab1
  set A : Matrix (Fin 2) (Fin 2) K := (a : Matrix (Fin 2) (Fin 2) K)
  set B : Matrix (Fin 2) (Fin 2) K := (b : Matrix (Fin 2) (Fin 2) K)
  have hcAB : Commute A B := by
    change A * B = B * A
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hab]
  have hsq : ∀ X : Matrix (Fin 2) (Fin 2) K, X ^ 2 + X + 1 = 0 → X ^ 2 = X + 1 := by
    intro X hX
    have := eq_neg_of_add_eq_zero_left (show X ^ 2 + (X + 1) = 0 by rw [← add_assoc]; exact hX)
    rwa [CharTwo.neg_eq] at this
  rw [Matrix.SpecialLinearGroup.coe_mul, hcAB.mul_pow, hsq A hA, hsq B hB] at hAB
  have hsum : A + B = 0 := by
    have e : A + B + ((A * B + A * B) + (1 + 1)) = (A + 1) * (B + 1) + A * B + 1 := by
      noncomm_ring
    rw [hAB, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero] at e
    exact e
  have hBA : B = A := by
    have := eq_neg_of_add_eq_zero_right hsum
    rwa [CharTwo.neg_eq] at this
  rw [show b = a from Subtype.ext hBA]
  exact Subgroup.mem_zpowers a

end SL2

theorem eq_one_of_mem_of_pow_three {G : Type*} [Group G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {x : G} (hx : x ∈ Q) (h3 : x ^ 3 = 1) : x = 1 := by
  have hco := hQ.orderOf_coprime (n := 3) (by norm_num) ⟨x, hx⟩
  have hdvd : orderOf (⟨x, hx⟩ : Q) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h3))
  have h1 := Nat.Coprime.eq_one_of_dvd hco hdvd
  have := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val this

theorem ThreeRankLeOne.sup {G : Type*} [Group G] {Q R : Subgroup G} (hQ : IsPGroup 2 Q)
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hQR : Q ⊓ R = ⊥) (hR : ThreeRankLeOne R) :
    ThreeRankLeOne (Q ⊔ R : Subgroup G) := by
  have hCN : Q ⊔ R ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hRQ
  have : (Q.subgroupOf (Q ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hCN
  set N := Q.subgroupOf (Q ⊔ R) with hNdef
  let π : (Q ⊔ R : Subgroup G) →* (Q ⊔ R : Subgroup G) ⧸ N := QuotientGroup.mk' N
  let φ : R →* (Q ⊔ R : Subgroup G) ⧸ N := π.comp (Subgroup.inclusion le_sup_right)
  have hmemN : ∀ x : (Q ⊔ R : Subgroup G), π x = 1 → (x : G) ∈ Q := fun x hx =>
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp hx)
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hQr : (r : G) ∈ Q := hmemN _ hr
    have : (r : G) ∈ Q ⊓ R := ⟨hQr, r.2⟩
    rw [hQR, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hφs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    have htop : (⊤ : Subgroup (Q ⊔ R : Subgroup G)) = N ⊔ R.subgroupOf (Q ⊔ R) := by
      rw [hNdef, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    rw [← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N), htop,
      Subgroup.map_sup]
    have hNbot : N.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hNbot, bot_sup_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  let e : R ≃* (Q ⊔ R : Subgroup G) ⧸ N := MulEquiv.ofBijective φ ⟨hφi, hφs⟩
  intro a b ha hb hab ha1
  have hpa : π a ≠ 1 := by
    intro h1
    exact ha1 (Subtype.ext (eq_one_of_mem_of_pow_three hQ (hmemN a h1)
      (by rw [← Subgroup.coe_pow, ha, Subgroup.coe_one])))
  have key := hR (e.symm (π a)) (e.symm (π b)) (by rw [← map_pow, ← map_pow, ha, map_one,
    map_one]) (by rw [← map_pow, ← map_pow, hb, map_one, map_one])
    (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hab])
    (fun h1 => hpa (by simpa using congrArg e h1))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp key
  have hk' : π (a ^ k) = π b := by
    have := congrArg e hk
    rw [map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    rw [map_zpow, this]
  have hx : ((a ^ k)⁻¹ * b : (Q ⊔ R : Subgroup G)) ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (π (a ^ k))⁻¹ * π b = 1
    rw [hk', inv_mul_cancel]
  have hc : Commute ((a ^ k)⁻¹) b := ((Commute.zpow_left hab k).inv_left)
  have h3 : ((a ^ k)⁻¹ * b) ^ 3 = 1 := by
    rw [hc.mul_pow, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha,
      one_zpow, inv_one, one_mul, hb]
  have h1 : (a ^ k)⁻¹ * b = 1 := Subtype.ext (eq_one_of_mem_of_pow_three hQ
    (Subgroup.mem_subgroupOf.mp hx) (by rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, (inv_mul_eq_one.mp h1)⟩

theorem localRank_three_le_two_of_centralizers {H : Type} [Group H] [Finite H]
    (h : ∀ s : H, orderOf s = 2 → ThreeRankLeOne (Subgroup.centralizer {s} : Subgroup H)) :
    localRank 3 H ≤ 2 := by
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
    Nat.prime_three H (by change 0 < localRank 3 H; omega)
  change CFSG.Assembly.pRank 3 L = localRank 3 H at hLr
  obtain ⟨E, hEL, hE, hEc⟩ : ∃ E : Subgroup H, E ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ CFSG.Assembly.pRank 3 L :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three L
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomp : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hr : 3 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (P : Set H)) := by omega
  have hVk : 3 ^ (2 + 1) ≤ Nat.card E := by
    rw [hEc]
    exact Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨Hs, hHE, hHc, hW⟩ : ∃ Hs : Subgroup H, Hs ≤ E ∧ Nat.card Hs = 3 ^ 2 ∧
      P ⊓ Subgroup.centralizer (Hs : Set H) ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hP
    exact le_bot_iff.mp (CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_sub_le
      (M := ⊥) Nat.prime_three hE hVk hEL hcomp fun Hs hHs hc => (hno Hs hHs hc).le)
  set W := P ⊓ Subgroup.centralizer (Hs : Set H) with hWdef
  have hW2 : IsPGroup 2 W := hP2.to_le inf_le_left
  have h2W : 2 ∣ Nat.card W := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW2
    rcases k with _ | k
    · exact absurd ((Subgroup.eq_bot_iff_card W).mpr (by simpa using hk)) hW
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2W
  have hw2 : orderOf (w : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hw
  have hwc : ∀ x ∈ Hs, x * (w : H) = (w : H) * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp w.2).2 x hx
  have hpow : ∀ x ∈ Hs, x ^ 3 = 1 := fun x hx => hE.2 x (hHE hx)
  have hcomm : ∀ x ∈ Hs, ∀ y ∈ Hs, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hHE hx⟩ ⟨y, hHE hy⟩)
  obtain ⟨a, haH, ha1⟩ : ∃ a ∈ Hs, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Hs = ⊥ := (Subgroup.eq_bot_iff_forall Hs).mpr hno
    rw [this, Subgroup.card_bot] at hHc
    norm_num at hHc
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hpow a haH) ha1
  obtain ⟨b, hbH, hba⟩ : ∃ b ∈ Hs, b ∉ Subgroup.zpowers a := by
    by_contra hno
    push Not at hno
    have hle := Subgroup.card_le_of_le (H := Hs) (K := Subgroup.zpowers a) hno
    rw [hHc, Nat.card_zpowers, ha3] at hle
    norm_num at hle
  have hmem : ∀ x ∈ Hs, x ∈ Subgroup.centralizer {(w : H)} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hwc x hx)
  have key := h (w : H) hw2 ⟨a, hmem a haH⟩ ⟨b, hmem b hbH⟩
    (Subtype.ext (by simpa using hpow a haH)) (Subtype.ext (by simpa using hpow b hbH))
    (Subtype.ext (by simpa using hcomm a haH b hbH))
    (fun h1 => ha1 (congrArg Subtype.val h1))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp key
  exact hba (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)

end CFSG.RankThree.PartTwo.Census.Carrier
