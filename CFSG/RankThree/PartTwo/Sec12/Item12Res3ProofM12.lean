module

import CFSG.RankThree.PartTwo.Sec12.Item128BarProofBar
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJM12
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLM12
public import CFSG.Sporadic.Suz.Simple
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local

public section

namespace CFSG.RankThree.PartTwo.Sec12.Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_centralizer {a c : G} {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 a) (hcK : c ∈ K)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {y : G} (hya : y ∈ Subgroup.centralizer ({a} : Set G))
    (hyc : y ∈ Subgroup.centralizer ({c} : Set G)) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  have hya' : y * a * y⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hya, mul_inv_cancel_right]
  have hyc' : y * c * y⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hyc, mul_inv_cancel_right]
  have hK' := KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hK y
  rw [hya'] at hK'
  have hcK' : c ∈ K.map (MulAut.conj y).toMonoidHom := ⟨c, hcK, by simp [hyc']⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hcC := Sec13.mem_thetaQuotCentralizer_of_ne_mem_thetaComponentsAt hK' hK hne hcK'
    (Subgroup.le_normalizer hcK)
  rw [mem_thetaQuotCentralizer_iff_thetaBarAct (Subgroup.le_normalizer hcK),
    thetaBarAct_of_mem hcK] at hcC
  have hcZ := mem_center_of_conj_eq_one hcC
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcZ
  exact hc1 (Sec13.eq_one_of_mem_inSubgroup_theta_of_pow_three ⟨_, hcZ, rfl⟩ hc3)



theorem m12_delta_cases
    {W : Type} [Group W] [Finite W]
    (hW : Nonempty (W ≃* CFSG.Blueprint.NativeSporadic.M12)) (P : Sylow 3 W) {z : W}
    (hz : z ∈ (P : Subgroup W) ⊓ Subgroup.centralizer ((P : Subgroup W) : Set W)) (hz1 : z ≠ 1)
    {D : Subgroup W} (hDP : D ≤ (P : Subgroup W)) (hD9 : Nat.card D = 9) (hzD : z ∈ D) :
    (∃ n ∈ Subgroup.normalizer (D : Set W), n * z * n⁻¹ ∉ Subgroup.zpowers z) ∨
      ∃ t ∈ Subgroup.normalizer ((P : Subgroup W) : Set W), t * z * t⁻¹ = z⁻¹ ∧
        t ∉ Subgroup.normalizer (D : Set W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hHeis, -, E, F, A', t, ht, hinv, hΔ, ⟨eE⟩, ⟨eF⟩, -, -⟩ :=
    Sec4.Sporadic.rank3II_4_14_local W hW P
  have hncard : ({E, F, A', CFSG.conjugate A' t} : Set (Subgroup W)).ncard = 4 := by
    rw [← hΔ]
    exact (CFSG.RankThree.PartTwo.Toolkit.m12ThreeLocalData W hW P).2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hAA'⟩ := Sec4.Sporadic.ne_of_ncard_four hncard
  have hDmem : D ∈ ({E, F, A', CFSG.conjugate A' t} : Set (Subgroup W)) := hΔ ▸ ⟨hDP, hD9⟩
  have hP3 : ∀ x ∈ (P : Subgroup W), x ^ 3 = 1 := by
    intro x hx
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : (P : Subgroup W))
    rw [hHeis.2.2] at h1
    exact congrArg Subtype.val h1
  have hD9' : Nat.card D = 3 ^ 2 := by rw [hD9]; norm_num
  have hDab : CFSG.Assembly.IsElemAbelian 3 D :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hD9', fun x hx => hP3 x (hDP hx)⟩
  have hz3 : z ^ 3 = 1 := hP3 z hz.1
  obtain ⟨v, hvD, hvz⟩ : ∃ v ∈ D, v ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers z from hcon)
    rw [hD9, Nat.card_zpowers, orderOf_eq_prime hz3 hz1] at this
    norm_num at this
  have hv1 : v ≠ 1 := fun h1 => hvz (h1 ▸ Subgroup.one_mem _)
  have hGL : ∀ X : Subgroup W, Nonempty (Sec4.autIn ⊤ X ≃* GL (Fin 2) (ZMod 3)) → X = D →
      ∃ n ∈ Subgroup.normalizer (D : Set W), n * z * n⁻¹ ∉ Subgroup.zpowers z := by
    rintro X ⟨eX⟩ rfl
    have h48 : Nat.card (Sec4.autIn ⊤ X) = 48 := by
      rw [Nat.card_congr eX.toEquiv]
      exact CFSG.RankThree.Asc83Table.card_GL23
    obtain ⟨n, hn, hnz⟩ :=
      KS128NotHJSL.exists_conj_of_card_autIn hDab hD9 h48 hzD hz1 hvD hv1
    exact ⟨n, hn, hnz ▸ hvz⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hDmem
  rcases hDmem with hDE | hDF | hDA | hDA
  · exact Or.inl (hGL E ⟨eE⟩ hDE.symm)
  · exact Or.inl (hGL F ⟨eF⟩ hDF.symm)
  · refine Or.inr ⟨t, ht, hinv z hz, fun htD => hAA' ?_⟩
    rw [hDA] at htD
    exact (Sec4.Sporadic.conjugate_eq_self_iff.mpr htD).symm
  · refine Or.inr ⟨t, ht, hinv z hz, fun htD => hAA' ?_⟩
    rw [hDA] at htD
    have h1 := Sec4.Sporadic.conjugate_eq_self_iff.mpr htD
    exact (Sec4.Sporadic.conjugate_injective t h1).symm

theorem not_three_dvd_orderOf_of_mem_theta {H : Subgroup G} {n : G}
    (hn : n ∈ inSubgroup (aschbacherSolvableCore 3) H) : ¬ 3 ∣ orderOf n := by
  obtain ⟨m, hm, rfl⟩ := hn
  intro h3
  apply three_not_dvd_card_aschbacherSolvableCore (G := H)
  refine h3.trans ?_
  rw [orderOf_injective H.subtype H.subtype_injective m]
  have h2 := orderOf_dvd_natCard (⟨m, hm⟩ : aschbacherSolvableCore 3 H)
  rwa [Subgroup.orderOf_mk] at h2

theorem eq_one_of_thetaBarAct_eq_conj {K : Subgroup G}
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) {n : G}
    (hnN : n ∈ Subgroup.normalizer (K : Set G)) (hn3 : ¬ 3 ∣ orderOf n)
    {y : K ⧸ aschbacherSolvableCore 3 K} (hy3 : y ^ 3 = 1)
    (h : thetaBarAct K ⟨n, hnN⟩ = MulAut.conj y) : y = 1 := by
  have h1 : orderOf (MulAut.conj y) ∣ orderOf n := by
    rw [← h]
    have := orderOf_map_dvd (thetaBarAct K) ⟨n, hnN⟩
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (MulAut.conj y) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy3, map_one])
  have h3 : orderOf (MulAut.conj y) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h' | h'
    · exact h'
    · exact absurd (h' ▸ h1) hn3
  rw [orderOf_eq_one_iff] at h3
  have := mem_center_of_conj_eq_one h3
  rw [hZ, Subgroup.mem_bot] at this
  exact this

theorem thetaBarAct_zpow_mul {K : Subgroup G} {a : G}
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) (j : ℤ) {k : G} (hk : k ∈ K)
    (hx : a ^ j * k ∈ Subgroup.normalizer (K : Set G)) :
    thetaBarAct K ⟨a ^ j * k, hx⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨k, hk⟩) := by
  have haN : a ∈ Subgroup.normalizer (K : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    rw [show a * l * a⁻¹ = l by
      rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hKa hl)), mul_inv_cancel_right]]
    exact hl
  have ha1 : thetaBarAct K ⟨a, haN⟩ = 1 := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) q
    rw [thetaBarAct_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change a * (l : G) * a⁻¹ = l
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hKa l.2)), mul_inv_cancel_right]
  have e : (⟨a ^ j * k, hx⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨a, haN⟩ ^ j * ⟨k, Subgroup.le_normalizer hk⟩ := Subtype.ext (by simp)
  rw [e, map_mul, map_zpow, ha1, one_zpow, one_mul, thetaBarAct_of_mem hk]

omit [Finite G] in
theorem thetaComponentsAt_inv' (c : G) : thetaComponentsAt 3 c⁻¹ = thetaComponentsAt 3 c := by
  have h : Subgroup.centralizer ({c⁻¹} : Set G) = Subgroup.centralizer {c} := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff (a := z) (b := c)
  unfold thetaComponentsAt
  rw [h]

theorem card_zpowers_sup_eq_nine {b c : G} (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hbc : b * c = c * b) (hb : b ∉ Subgroup.zpowers c) :
    Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
  have hb1 : b ≠ 1 := fun h1 => hb (h1 ▸ Subgroup.one_mem _)
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute b c from hbc) i j).eq
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  have hcb : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hbb : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hbot : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have hdvd : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) ∣ 3 := by
      rw [← hcb]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact h1
    · exfalso
      apply hb
      have heq : Subgroup.zpowers b ⊓ Subgroup.zpowers c = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hbb])
      have hmem : b ∈ Subgroup.zpowers b ⊓ Subgroup.zpowers c := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact hmem.2
  rw [hbot, Subgroup.card_bot, mul_one, hbb, hcb] at hcard
  exact hcard

theorem le_normalizer_of_sec12StdBar {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) :
    A ≤ Subgroup.normalizer (L : Set G) := by
  rw [← h.sup_eq]
  exact sup_le (fun x hx => (Sec6.mem_thetaQuotCentralizer_iff.mp hx.2).1)
    (fun x hx => Subgroup.le_normalizer hx.2)

theorem conj_mem_sup_theta_of_mem_normalizer {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L)) {a : G} (haA : a ∈ A)
    (haB : a ∉ Sec4.thetaQuotCentralizer L) (haL : a ∉ L) {t : G} (hta : t * a = a * t)
    (htc : t * c * t⁻¹ = c⁻¹) (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    ∀ x ∈ A, t * x * t⁻¹ ∈ A ⊔ inSubgroup (aschbacherSolvableCore 3) L := by
  have hL := h.mem_thetaComponentsAt
  have hcL := h.mem_L
  have hc1 := h.ne_one
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (A ⊓ Sec4.thetaQuotCentralizer L) (A ⊓ L) (fun x hx y hy => hAc x hx.1 y hy.1)
  have ha' : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L ⊔ A ⊓ L : Subgroup G) : Set G) := by
    rw [h.sup_eq]
    exact haA
  rw [hset] at ha'
  obtain ⟨b, hb, d, hd, hbd⟩ := ha'
  have hbd : b * d = a := hbd
  have hbA : b ∈ A := hb.1
  have hbC : b ∈ Sec4.thetaQuotCentralizer L := hb.2
  have hdL : d ∈ L := hd.2
  have hbt : t * b * t⁻¹ ∈ A ⊔ θL := by
    set w := b⁻¹ * (t * b * t⁻¹) with hw
    have hw' : w = d * (t * d * t⁻¹)⁻¹ := by
      have h1 : t * (b * d) * t⁻¹ = b * d := by rw [hbd, hta, mul_inv_cancel_right]
      calc w = b⁻¹ * (t * (b * d) * t⁻¹) * (t * d * t⁻¹)⁻¹ := by rw [hw]; group
        _ = b⁻¹ * (b * d) * (t * d * t⁻¹)⁻¹ := by rw [h1]
        _ = d * (t * d * t⁻¹)⁻¹ := by group
    have hwL : w ∈ L := by
      rw [hw']
      exact L.mul_mem hdL (L.inv_mem ((Subgroup.mem_normalizer_iff.mp htL d).mp hdL))
    have hwC : w ∈ Sec4.thetaQuotCentralizer L :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hbC) (conj_mem_thetaQuotCentralizer htL hbC)
    have hwZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨w, hwL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      apply mem_center_of_conj_eq_one
      rw [← thetaBarAct_of_mem hwL]
      exact (mem_thetaQuotCentralizer_iff_thetaBarAct _).mp hwC
    have hcLZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      apply mem_center_of_conj_eq_one
      rw [← thetaBarAct_of_mem hcL]
      exact (mem_thetaQuotCentralizer_iff_thetaBarAct _).mp hcC
    have hcL1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ≠ 1 := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hc1 (Sec13.eq_one_of_mem_inSubgroup_theta_of_pow_three ⟨_, h1, rfl⟩ hc3)
    have hcL3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
      rw [this, map_one]
    have hZL : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) =
        Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hcL⟩) :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcLZ) (by
        rw [card_center_eq_three_of_isSLThreePi hSL, Nat.card_zpowers,
          orderOf_eq_prime hcL3 hcL1])).symm
    rw [hZL] at hwZ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwZ
    have hn₁ : w * c ^ (-j) ∈ θL := by
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L)
          (⟨w, hwL⟩ * (⟨c, hcL⟩ : L) ^ (-j)) = 1 := by
        rw [map_mul, map_zpow, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, by simp⟩
    have e : t * b * t⁻¹ = b * (w * c ^ (-j)) * c ^ j := by
      rw [hw]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hbA)
      (Subgroup.mem_sup_right hn₁)) (Subgroup.mem_sup_left (Subgroup.zpow_mem _ h.mem_A j))
  have hbc : b * c = c * b := hAc b hbA c h.mem_A
  have hbz : b ∉ Subgroup.zpowers c := by
    intro hbz
    apply haL
    rw [← hbd]
    exact L.mul_mem (Subgroup.zpowers_le.mpr hcL hbz) hdL
  have hB9' := card_zpowers_sup_eq_nine (hAe.2 b hbA) hc3 hc1 hbc hbz
  have haBc : a ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers c := fun h1 =>
    haB ((sup_le (Subgroup.zpowers_le.mpr hbC) (Subgroup.zpowers_le.mpr hcC)) h1)
  have hAeq : Subgroup.zpowers a ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) = A :=
    eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr haA)
      (sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr h.mem_A))) le_sup_right
      hB9' (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) haBc
  have hAt : ∀ x ∈ A, t * x * t⁻¹ ∈ A ⊔ θL := by
    intro x hx
    have hle : Subgroup.zpowers a ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) ≤
        (A ⊔ θL).comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le (Subgroup.zpowers_le.mpr ?_)
        (Subgroup.zpowers_le.mpr ?_))
      · show t * a * t⁻¹ ∈ A ⊔ θL
        rw [hta, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left haA
      · exact hbt
      · show t * c * t⁻¹ ∈ A ⊔ θL
        rw [htc]
        exact Subgroup.mem_sup_left (inv_mem h.mem_A)
    have hx' : x ∈ Subgroup.zpowers a ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) := by
      rw [hAeq]
      exact hx
    exact hle hx'
  exact hAt

theorem exists_zpow_mul_mem_inf {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hAE : A ∈ partTwoE G) (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L)) {a : G}
    (haA : a ∈ A) (haL : a ∉ L) : ∀ k ∈ A, ∃ i : ℤ, a ^ (-i) * k ∈ A ⊓ L := by
  have hL := h.mem_thetaComponentsAt
  have hcL := h.mem_L
  have hc1 := h.ne_one
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (A ⊓ Sec4.thetaQuotCentralizer L) (A ⊓ L) (fun x hx y hy => hAc x hx.1 y hy.1)
    rw [h.sup_eq, h27, h.card_B] at hcard
    have hle3 : Nat.card ((A ⊓ Sec4.thetaQuotCentralizer L) ⊓ (A ⊓ L) : Subgroup G) ≤ 3 := by
      have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer
        (hAp.to_le inf_le_left) (inf_le_right : A ⊓ Sec4.thetaQuotCentralizer L ≤ _) (L := L)
      rw [card_center_eq_three_of_isSLThreePi hSL] at h1
      refine le_trans (Subgroup.card_le_of_le ?_) h1
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have hne1 : Nat.card ((A ⊓ Sec4.thetaQuotCentralizer L) ⊓ (A ⊓ L) : Subgroup G) ≠ 1 := by
      intro h1
      have hb' := Subgroup.eq_bot_of_card_eq _ h1
      have hmem : c ∈ (A ⊓ Sec4.thetaQuotCentralizer L) ⊓ (A ⊓ L) :=
        ⟨⟨h.mem_A, hcC⟩, ⟨h.mem_A, hcL⟩⟩
      rw [hb', Subgroup.mem_bot] at hmem
      exact hc1 hmem
    have hdvd : Nat.card ((A ⊓ Sec4.thetaQuotCentralizer L) ⊓ (A ⊓ L) : Subgroup G) ∣ 27 := by
      rw [← h27]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
    have hpos := Nat.card_pos (α := ((A ⊓ Sec4.thetaQuotCentralizer L) ⊓ (A ⊓ L) : Subgroup G))
    interval_cases hm : Nat.card ((A ⊓ Sec4.thetaQuotCentralizer L) ⊓ (A ⊓ L) : Subgroup G)
      <;> omega
  have hALsup : Subgroup.zpowers a ⊔ (A ⊓ L) = A :=
    eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left) le_sup_right hAL9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h1 => haL h1.2)
  have hALset : ((Subgroup.zpowers a ⊔ (A ⊓ L) : Subgroup G) : Set G) =
      (Subgroup.zpowers a : Set G) * ((A ⊓ L : Subgroup G) : Set G) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ fun x hx y hy =>
      hAc x (Subgroup.zpowers_le.mpr haA hx) y (Subgroup.mem_inf.mp hy).1).2
  have hdec : ∀ k ∈ A, ∃ i : ℤ, a ^ (-i) * k ∈ A ⊓ L := by
    intro k hk
    have hk' : k ∈ ((Subgroup.zpowers a ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
      rw [hALsup]
      exact hk
    rw [hALset] at hk'
    obtain ⟨u, hu, x₁, hx₁, rfl⟩ := hk'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine ⟨i, ?_⟩
    rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    exact hx₁
  exact hdec

theorem mem_of_m12
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) (haB : a ∉ Sec4.thetaQuotCentralizer L)
    {K : Subgroup G} (hK : K ∈ lA422 A a) (hcK : c ∈ K)
    (φ : lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) :
    a ∈ L := by
  by_contra haL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := h.mem_thetaComponentsAt
  have hcL := h.mem_L
  have hc1 := h.ne_one
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨haA, ha3', -⟩ := Sec13.zpowers_mem_omegaA_iff.mp ha
  have ha1 : a ≠ 1 := ne_one_of_card_zpowers_eq_three ha3'
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have hAH := Proof128.le_normalizer_zpowers_of_isElemAbelian hAe haA
  obtain ⟨-, ⟨hMp, hMZ⟩, -⟩ := Sec13.sporadicModels131
  obtain ⟨ψ⟩ := Proof128.nonempty_thetaQuot_equiv hAe hK.1 hK.2.1 hAH hMp φ
  have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv ψ hMZ
  have haK : a ∉ K := Proof128.not_mem_of_center_eq_bot hK.1 hZ ha3 ha1
  have h9 : Nat.card (A ⊓ K : Subgroup G) = 9 :=
    Proof128.card_inf_eq_nine hAe h27 hK.1 hK.2.1 hAH hMp φ
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hAsup : Subgroup.zpowers a ⊔ (A ⊓ K) = A :=
    eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left) le_sup_right h9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h1 => haK h1.2)
  have hAKset : ((Subgroup.zpowers a ⊔ (A ⊓ K) : Subgroup G) : Set G) =
      (Subgroup.zpowers a : Set G) * ((A ⊓ K : Subgroup G) : Set G) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ fun x hx y hy =>
      hAc x (Subgroup.zpowers_le.mpr haA hx) y (Subgroup.mem_inf.mp hy).1).2
  have hN12 := normalizer_le_of_sec12StdBar_of_list h45 hK2 h (Or.inl hSL)
  have hNK : ∀ n : G, n * a = a * n → n * c = c * n → n ∈ Subgroup.normalizer (K : Set G) :=
    fun n hna hnc => mem_normalizer_of_mem_centralizer hK.1 hcK hZ hc3 hc1
      (Subgroup.mem_centralizer_singleton_iff.mpr hna)
      (Subgroup.mem_centralizer_singleton_iff.mpr hnc)
  have hmove : ∀ n : G, n ∈ K → n ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) →
      n * c * n⁻¹ ∈ Subgroup.zpowers c := by
    intro n hnK hnAK
    have hna : n * a = a * n := Subgroup.mem_centralizer_singleton_iff.mp (hKa hnK)
    have hnA : n ∈ Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnAK ⊢
      rw [← hAsup, Subgroup.map_sup, hnAK, MonoidHom.map_zpowers]
      congr 2
      change n * a * n⁻¹ = a
      rw [hna, mul_inv_cancel_right]
    exact (Subgroup.mem_normalizer_iff.mp (hN12 hnA) c).mp (Subgroup.mem_zpowers c)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set B : Subgroup K := (A ⊓ K).subgroupOf K with hBdef
  have hB9 : Nat.card B = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  obtain ⟨S, hBS⟩ := hBp.exists_le_sylow
  set Sb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    S.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
  have hSb : (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = (S : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨hHeis, -⟩ := Sec4.Sporadic.rank3II_4_14_local _ ⟨ψ⟩ Sb
  have hinjS := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three S.isPGroup'
  have hSb3 : ∀ x ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)), x ^ 3 = 1 := fun x hx =>
    congrArg Subtype.val (Sec13.pow_three_eq_one_of_mulEquiv (MulEquiv.refl _) hHeis.2.2 ⟨x, hx⟩)
  have hSb27 : Nat.card (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = 27 := hHeis.2.1
  have hSbmem : ∀ s ∈ (S : Subgroup K), π s ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
    fun s hs => hSb ▸ Subgroup.mem_map_of_mem π hs
  set c' : K := ⟨c, hcK⟩ with hc'def
  have hc'B : c' ∈ B := Subgroup.mem_subgroupOf.mpr ⟨h.mem_A, hcK⟩
  have hc'S : c' ∈ (S : Subgroup K) := hBS hc'B
  have hcbS : π c' ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) := hSbmem c' hc'S
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcb3 : π c' ^ 3 = 1 := by rw [← map_pow, hc'3, map_one]
  have hcb1 : π c' ≠ 1 := by
    intro h1
    apply hc1
    have : c' = 1 := hinjS hc'S (Subgroup.one_mem _) (by rw [h1, map_one])
    exact congrArg Subtype.val this
  set Bb : Subgroup (K ⧸ aschbacherSolvableCore 3 K) := B.map π with hBbdef
  have hinjB : Set.InjOn π (B : Set K) := hinjS.mono hBS
  have hBb9 : Nat.card Bb = 9 := by rw [Sec13.card_map_eq_of_injOn π hinjB, hB9]
  have hBbS : Bb ≤ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
    hSb ▸ Subgroup.map_mono hBS
  have hliftB : ∀ nb ∈ Subgroup.normalizer (Bb : Set (K ⧸ aschbacherSolvableCore 3 K)),
      nb * π c' * nb⁻¹ ∈ Subgroup.zpowers (π c') := by
    intro nb hnb
    rw [hBbdef, Sec13.normalizer_map_mk_eq hBp] at hnb
    obtain ⟨n, hn, rfl⟩ := hnb
    have hnAK : (n : G) ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
      have h1 := Sec13.mem_normalizer_map_subtype hn
      rwa [hBdef, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmove n n.2 hnAK)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have e1 : c' ^ k = n * c' * n⁻¹ := Subtype.ext (by simpa using hk)
    rw [← map_zpow, e1, map_mul, map_mul, map_inv]
  by_cases hZc : ∀ x ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)), x * π c' = π c' * x
  swap
  ·
    push Not at hZc
    obtain ⟨s, hsS, hsc⟩ := hZc
    have hsN := KS128NotHJTC.le_normalizer_of_card_nine hBbS hBb9 hSb27 hsS
    exact hsc (KS128NotHJTC.mul_comm_of_conj_mem_zpowers (hSb3 s hsS) hcb3 (hliftB s hsN))
  have hcZ : π c' ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) ⊓
      Subgroup.centralizer ((Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) : Set _) :=
    ⟨hcbS, Subgroup.mem_centralizer_iff.mpr fun x hx => hZc x hx⟩
  rcases m12_delta_cases ⟨ψ⟩ Sb hcZ hcb1 hBbS hBb9 (Subgroup.mem_map_of_mem π hc'B) with
    ⟨nb, hnb, hnbc⟩ | ⟨tb, htbS, htbc, htbB⟩
  · exact hnbc (hliftB nb hnb)
  have htbS' := htbS
  rw [hSb, Sec13.normalizer_map_mk_eq S.isPGroup'] at htbS'
  obtain ⟨t₁, ht₁S, rfl⟩ := htbS'
  set t : G := (t₁ : G) with htdef
  have htK : t ∈ K := t₁.2
  have hta : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp (hKa htK)
  have htc' : t₁ * c' * t₁⁻¹ = c'⁻¹ := by
    apply hinjS ((Subgroup.mem_normalizer_iff.mp ht₁S c').mp hc'S) (inv_mem hc'S)
    rw [map_mul, map_mul, map_inv, map_inv]
    exact htbc
  have htc : t * c * t⁻¹ = c⁻¹ := by
    have := congrArg Subtype.val htc'
    simpa [htdef, hc'def] using this
  have ht₁k : ∀ k ∈ (S : Subgroup K), t₁ * k * t₁⁻¹ ∈ (S : Subgroup K) := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp ht₁S k).mp hk
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_sec12StdBar h
  have hπt : thetaBarAct K ⟨t, Subgroup.le_normalizer htK⟩ = MulAut.conj (π t₁) :=
    thetaBarAct_of_mem htK
  have haNK : a ∈ Subgroup.normalizer (K : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    rw [show a * l * a⁻¹ = l by
      rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hKa hl)), mul_inv_cancel_right]]
    exact hl
  have hzN : ∀ (j : ℤ) {k : G}, k ∈ K → a ^ j * k ∈ Subgroup.normalizer (K : Set G) :=
    fun j k hk => mul_mem (zpow_mem haNK j) (Subgroup.le_normalizer hk)
  by_cases htL : t ∈ Subgroup.normalizer (L : Set G)
  ·
    apply htbB
    have hAt := conj_mem_sup_theta_of_mem_normalizer h hAE hSL haA haB haL hta htc htL
    set θL : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hθL
    have hAθ : A ≤ Subgroup.normalizer (θL : Set G) := fun x hx =>
      Subgroup.mem_normalizer_fintype fun n hn => conj_mem_inSubgroup_theta (hAL hx) hn
    have hAθset : ((A ⊔ θL : Subgroup G) : Set G) = (A : Set G) * (θL : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A θL hAθ
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k', hk'B, rfl⟩ := hx
    have hk' : (k' : G) ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hk'B
    have hmemX := hAt k' hk'.1
    rw [← SetLike.mem_coe, hAθset] at hmemX
    obtain ⟨x, hxA, n, hn, hxn⟩ := hmemX
    have hx' : x ∈ ((Subgroup.zpowers a ⊔ (A ⊓ K) : Subgroup G) : Set G) := by
      rw [hAsup]
      exact hxA
    rw [hAKset] at hx'
    obtain ⟨u, hu, x₀, hx₀, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hkt : t * k' * t⁻¹ ∈ K := K.mul_mem (K.mul_mem htK k'.2) (K.inv_mem htK)
    have hnL : n ∈ L := Subgroup.map_subtype_le _ hn
    have hna : n * a = a * n := by
      have e : n = (a ^ i * x₀)⁻¹ * (t * k' * t⁻¹) := by rw [← hxn]; group
      have hc1' : Commute (t * k' * t⁻¹) a := Subgroup.mem_centralizer_singleton_iff.mp (hKa hkt)
      have hc2 : Commute x₀ a := hAc x₀ hx₀.1 a haA
      have hc3' : Commute (a ^ i) a := Commute.zpow_left (Commute.refl a) i
      rw [e]
      exact ((hc3'.mul_left hc2).inv_left.mul_left hc1').eq
    have hnc : n * c = c * n := Subgroup.mem_centralizer_singleton_iff.mp (hLc hnL)
    have hnN := hNK n hna hnc
    have hn3 := not_three_dvd_orderOf_of_mem_theta hn
    have hx₀K : x₀ ∈ K := hx₀.2
    have eN : (⟨t * k' * t⁻¹, Subgroup.le_normalizer hkt⟩ : Subgroup.normalizer (K : Set G)) =
        ⟨a ^ i * x₀, hzN i hx₀K⟩ * ⟨n, hnN⟩ := Subtype.ext (by simp [← hxn])
    have hact := congrArg (thetaBarAct K) eN
    rw [map_mul, thetaBarAct_of_mem hkt, thetaBarAct_zpow_mul hKa i hx₀K (hzN i hx₀K)] at hact
    have hn' : thetaBarAct K ⟨n, hnN⟩ =
        MulAut.conj ((π ⟨x₀, hx₀K⟩)⁻¹ * π ⟨t * k' * t⁻¹, hkt⟩) := by
      rw [map_mul, map_inv, hact, inv_mul_cancel_left]
    have ekt : (⟨t * k' * t⁻¹, hkt⟩ : K) = t₁ * k' * t₁⁻¹ := Subtype.ext rfl
    have hyS : (π ⟨x₀, hx₀K⟩)⁻¹ * π ⟨t * k' * t⁻¹, hkt⟩ ∈
        (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) := by
      refine mul_mem (inv_mem (hSbmem _ (hBS (Subgroup.mem_subgroupOf.mpr hx₀)))) ?_
      rw [ekt]
      exact hSbmem _ (ht₁k k' (hBS hk'B))
    have hy1 := eq_one_of_thetaBarAct_eq_conj hZ hnN hn3 (hSb3 _ hyS) hn'
    refine ⟨⟨x₀, hx₀K⟩, Subgroup.mem_subgroupOf.mpr hx₀, ?_⟩
    rw [inv_mul_eq_one.mp hy1, ekt, map_mul, map_mul, map_inv]
  ·
    set L' := L.map (MulAut.conj t).toMonoidHom with hL'def
    have hL' : L' ∈ thetaComponentsAt 3 c := by
      have h1 := KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hL t
      rwa [htc, thetaComponentsAt_inv'] at h1
    have hne : L ≠ L' := by
      intro h1
      apply htL
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h1.symm
    have hdec := exists_zpow_mul_mem_inf h hAE hSL haA haL
    have hcomm : ∀ k₁ ∈ B, ∀ k₂ ∈ B,
        π k₁ * (π t₁ * π k₂ * (π t₁)⁻¹) = (π t₁ * π k₂ * (π t₁)⁻¹) * π k₁ := by
      intro k₁ hk₁B k₂ hk₂B
      have hk₁ : (k₁ : G) ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hk₁B
      have hk₂ : (k₂ : G) ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hk₂B
      obtain ⟨i₁, hx₁⟩ := hdec k₁ hk₁.1
      obtain ⟨i₂, hx₂⟩ := hdec k₂ hk₂.1
      set x₁ := a ^ (-i₁) * (k₁ : G) with hx₁def
      set x₂ := a ^ (-i₂) * (k₂ : G) with hx₂def
      set y := t * x₂ * t⁻¹ with hydef
      have hyL' : y ∈ L' := ⟨x₂, hx₂.2, rfl⟩
      have hnθ := Sec10.commutator_mem_theta_of_ne hL hL' hne hx₁.2 hyL'
      have hx₁a : Commute x₁ a := hAc x₁ hx₁.1 a haA
      have hya : Commute y a := by
        have hx₂a : Commute x₂ a := hAc x₂ hx₂.1 a haA
        have hta' : Commute t a := hta
        exact (hta'.mul_left hx₂a).mul_left hta'.inv_left
      have hna : x₁ * y * x₁⁻¹ * y⁻¹ * a = a * (x₁ * y * x₁⁻¹ * y⁻¹) :=
        (((hx₁a.mul_left hya).mul_left hx₁a.inv_left).mul_left hya.inv_left).eq
      have hnc : x₁ * y * x₁⁻¹ * y⁻¹ * c = c * (x₁ * y * x₁⁻¹ * y⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.map_subtype_le _ hnθ)
      have hnN := hNK _ hna hnc
      have hn3 := not_three_dvd_orderOf_of_mem_theta hnθ
      have hx₁N := hzN (-i₁) k₁.2
      have hx₂N := hzN (-i₂) k₂.2
      have htN : t ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer htK
      have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
        mul_mem (mul_mem htN hx₂N) (inv_mem htN)
      have hX : thetaBarAct K ⟨x₁, hx₁N⟩ = MulAut.conj (π k₁) :=
        thetaBarAct_zpow_mul hKa (-i₁) k₁.2 hx₁N
      have hY : thetaBarAct K ⟨y, hyN⟩ = MulAut.conj (π t₁ * π k₂ * (π t₁)⁻¹) := by
        have e : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set G)) =
            ⟨t, htN⟩ * ⟨x₂, hx₂N⟩ * ⟨t, htN⟩⁻¹ := Subtype.ext rfl
        rw [e, map_mul, map_mul, map_inv, hπt, thetaBarAct_zpow_mul hKa (-i₂) k₂.2 hx₂N,
          map_mul, map_mul, map_inv]
      have eN : (⟨x₁ * y * x₁⁻¹ * y⁻¹, hnN⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨x₁, hx₁N⟩ * ⟨y, hyN⟩ * ⟨x₁, hx₁N⟩⁻¹ * ⟨y, hyN⟩⁻¹ := Subtype.ext rfl
      set ybar := π t₁ * π k₂ * (π t₁)⁻¹ with hybar
      have hn' : thetaBarAct K ⟨x₁ * y * x₁⁻¹ * y⁻¹, hnN⟩ =
          MulAut.conj (π k₁ * ybar * (π k₁)⁻¹ * ybar⁻¹) := by
        rw [eN, map_mul, map_mul, map_mul, map_inv, map_inv, hX, hY]
        simp only [hybar, map_mul, map_inv]
      have hk₁S : π k₁ ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) := hSbmem _ (hBS hk₁B)
      have hybS : ybar ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) := by
        rw [hybar, ← map_inv, ← map_mul, ← map_mul]
        exact hSbmem _ (ht₁k k₂ (hBS hk₂B))
      have hcS : π k₁ * ybar * (π k₁)⁻¹ * ybar⁻¹ ∈
          (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
        mul_mem (mul_mem (mul_mem hk₁S hybS) (inv_mem hk₁S)) (inv_mem hybS)
      have h1 := eq_one_of_thetaBarAct_eq_conj hZ hnN hn3 (hSb3 _ hcS) hn'
      have h2 := mul_inv_eq_one.mp h1
      calc π k₁ * ybar = π k₁ * ybar * (π k₁)⁻¹ * π k₁ := by group
        _ = ybar * π k₁ := by rw [h2]
    obtain ⟨k₂, hk₂B, hk₂⟩ : ∃ k₂ ∈ B, π t₁ * π k₂ * (π t₁)⁻¹ ∉ Bb := by
      by_contra hcon
      push Not at hcon
      apply htbB
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := hx
      exact hcon k hk
    set xb := π t₁ * π k₂ * (π t₁)⁻¹ with hxb
    have hxbS : xb ∈ (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) := by
      rw [hxb, ← map_inv, ← map_mul, ← map_mul]
      exact hSbmem _ (ht₁k k₂ (hBS hk₂B))
    have hsup : Bb ⊔ Subgroup.zpowers xb = (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :=
      eq_of_card_nine_lt hSb27 (sup_le hBbS (Subgroup.zpowers_le.mpr hxbS)) le_sup_left hBb9
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers xb)) hk₂
    have hBb9' : Nat.card Bb = 3 ^ 2 := by rw [hBb9]; norm_num
    have hBbab : CFSG.Assembly.IsElemAbelian 3 Bb :=
      ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hBb9', fun x hx => hSb3 x (hBbS hx)⟩
    have hcomm' : ∀ x ∈ Bb, ∀ y ∈ Subgroup.zpowers xb, x * y = y * x := by
      rintro _ ⟨k₁, hk₁B, rfl⟩ y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute (π k₁) xb from hcomm k₁ hk₁B k₂ hk₂B) m).eq
    have hab := Sec13.isElemAbelian_sup hBbab (Sec13.isElemAbelian_zpowers (hSb3 xb hxbS)) hcomm'
    rw [hsup] at hab
    have htop : Subgroup.center (Sb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = ⊤ := by
      have := hab.1
      refine eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => ?_
      exact mul_comm' y x
    have h3 := hHeis.1.2.2.2
    rw [htop, Subgroup.card_top, hSb27] at h3
    norm_num at h3

end CFSG.RankThree.PartTwo.Sec12.Res3Proof
