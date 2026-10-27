module

public import CFSG.Timmesfeld.Transvection.ResidueBenderBasic
public import CFSG.GH74.Uniqueness.Bender.Lemma32
import CFSG.Timmesfeld.Bridge.RootClosureThree
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
import CFSG.GroupTheory.QuasiDihedralFusion.Transport
import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r}

abbrev residueQuotient (Δ : Set (Subgroup H)) (P Q : Fin r → Subgroup H) (k : Fin r) :=
  ↥(residueGroup Δ P Q k) ⧸ Subgroup.center ↥(residueGroup Δ P Q k)

theorem isBenderGroup_residueQuotient [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) :
    CFSG.BenderSuzuki.IsBenderGroup (residueQuotient Δ P Q k) := by
  have hOT := isOddTransp_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  have hN := isNormalSet_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ
  have hgen := closure_residueElts_eq_top (Δ := Δ) (P := P) (Q := Q) (k := k)
  have hDD := exists_mul_mem_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hq
  have hdisc := disconnected_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  have hB := Bridge.OddTransp.oddTranspZStar (G := ↥(residueGroup Δ P Q k))
    (D := residueElts Δ P Q k) hOT hN hgen hDD hdisc
  have hZ := zStar_residueGroup_eq_center (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF
  exact Bridge.Asc72.isBenderGroup_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq hZ.symm) hB

@[expose] def residueMemberImage (X : Subgroup H) : Subgroup (residueQuotient Δ P Q k) :=
  (X.subgroupOf (residueGroup Δ P Q k)).map
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)))

theorem inf_center_eq_bot_of_mem_frameResidue (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {X : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) :
    X.subgroupOf (residueGroup Δ P Q k) ⊓
      Subgroup.center ↥(residueGroup Δ P Q k) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨hzX, hzC⟩ := hz
  by_contra hz1
  have hz1' : (z : H) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨Y, hY, hYX⟩ := exists_mem_frameResidue_ne hF X
  have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hYX.symm
  have hcomm : ∀ b ∈ Y, Commute (z : H) b := by
    intro b hb
    have hbL : b ∈ residueGroup Δ P Q k := frameResidue_le_residueGroup hY hb
    have hc := Subgroup.mem_center_iff.mp hzC (⟨b, hbL⟩ : ↥(residueGroup Δ P Q k))
    exact congrArg Subtype.val hc.symm
  exact (hopp.not_commute_of_mem hzX hz1') hcomm

theorem card_residueMemberImage {X : Subgroup H} (hXL : X ≤ residueGroup Δ P Q k)
    (hinf : X.subgroupOf (residueGroup Δ P Q k) ⊓
      Subgroup.center ↥(residueGroup Δ P Q k) = ⊥) :
    Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) = Nat.card X := by
  have hrel : (Subgroup.center ↥(residueGroup Δ P Q k)).relIndex
      (X.subgroupOf (residueGroup Δ P Q k)) = Nat.card X := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.center ↥(residueGroup Δ P Q k))
      (X.subgroupOf (residueGroup Δ P Q k)), inf_comm, hinf, Subgroup.relIndex_bot_left,
      card_subgroupOf_of_le hXL]
  have h := Subgroup.relIndex_ker
    (f := QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)))
    (K := X.subgroupOf (residueGroup Δ P Q k))
  rw [QuotientGroup.ker_mk'] at h
  change Nat.card ((X.subgroupOf (residueGroup Δ P Q k)).map
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)))) = Nat.card X
  rw [← h, hrel]


private theorem exists_residueElt_map_eq_of_orderOf_eq_two [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (residueQuotient Δ P Q k))
    {x : residueQuotient Δ P Q k} (hx : orderOf x = 2) :
    ∃ d ∈ residueElts Δ P Q k,
      (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) d = x := by
  classical
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  obtain ⟨a, haP, ha1⟩ := hΔ.root.exists_ne_one (hF.memP k)
  let d0 : ↥(residueGroup Δ P Q k) := residueElt hP haP ha1
  have hd0D : d0 ∈ residueElts Δ P Q k := residueElt_mem hP haP ha1
  have hinf := inf_center_eq_bot_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hP
  have hd0X : d0 ∈ (P k).subgroupOf (residueGroup Δ P Q k) := haP
  have hd0_not : d0 ∉ Subgroup.center ↥(residueGroup Δ P Q k) := by
    intro hc
    have hmem : d0 ∈ (P k).subgroupOf (residueGroup Δ P Q k) ⊓
        Subgroup.center ↥(residueGroup Δ P Q k) := ⟨hd0X, hc⟩
    rw [hinf] at hmem
    exact hd0D.1 (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
  let π := QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))
  have hd0sq : d0 * d0 = 1 := Subtype.ext (hΔ.root.mul_self (P k) (hF.memP k) (d0 : H) haP)
  have hd0bar2 : (π d0) * (π d0) = 1 := by
    rw [← map_mul, hd0sq, map_one]
  have hd0bar1 : π d0 ≠ 1 := by
    intro h
    exact hd0_not ((QuotientGroup.eq_one_iff _).mp h)
  have hd0bar_ord : orderOf (π d0) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hd0bar1
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB hd0bar_ord hx)
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(residueGroup Δ P Q k)) g
  refine ⟨g' * d0 * g'⁻¹, (isNormalSet_residueElts (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ) g' d0 hd0D, ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hg


theorem residueMemberImage_sq_eq_one (hΔ : IsTransvectionClass Δ) {X : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) {g : residueQuotient Δ P Q k}
    (hg : g ∈ residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) : g * g = 1 := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  have hx2 : x * x = 1 := Subtype.ext (hΔ.root.mul_self X hX.1 (x : H) hx)
  calc (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) x *
        (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) x
      = QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) (x * x) := by rw [map_mul]
    _ = 1 := by rw [hx2, map_one]

theorem isPGroup_residueMemberImage (hΔ : IsTransvectionClass Δ) {X : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) :
    IsPGroup 2 (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using residueMemberImage_sq_eq_one hΔ hX g.2

private theorem exists_benderSylowData_linear [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSL2Model n)
    (T : Sylow 2 (residueQuotient Δ P Q k)) :
    ∃ t, CFSG.GH74.Uniqueness.Bender.Lemma32 n 1 1
      (T : Subgroup (residueQuotient Δ P Q k)) t := by
  have hBT : CFSG.GH74.Uniqueness.Bender.BenderType (residueQuotient Δ P Q k) n 1 1 :=
    .linear n hn e
  obtain ⟨t, hc⟩ := hBT.exists_benderCore T
  exact ⟨t, hBT.lemma_3_2 T hc.sq_eq_one hc.not_mem⟩

private theorem exists_benderSylowData_unitary [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n)
    (T : Sylow 2 (residueQuotient Δ P Q k)) :
    ∃ t, CFSG.GH74.Uniqueness.Bender.Lemma32 n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1))
      (T : Subgroup (residueQuotient Δ P Q k)) t := by
  have hBT : CFSG.GH74.Uniqueness.Bender.BenderType (residueQuotient Δ P Q k) n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := .unitary n hn e
  obtain ⟨t, hc⟩ := hBT.exists_benderCore T
  exact ⟨t, hBT.lemma_3_2 T hc.sq_eq_one hc.not_mem⟩


private theorem eq_sylow_of_rootCenter_eq_of_psu3 [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n)
    {T T' : Sylow 2 (residueQuotient Δ P Q k)}
    (hcenter : CFSG.GH74.Uniqueness.Bender.rootCenter
        (T : Subgroup (residueQuotient Δ P Q k)) =
      CFSG.GH74.Uniqueness.Bender.rootCenter
        (T' : Subgroup (residueQuotient Δ P Q k))) : T = T' := by
  classical
  obtain ⟨t, hL⟩ := exists_benderSylowData_unitary (Δ := Δ) (P := P) (Q := Q) (k := k) hn e T
  have hcard : Nat.card (CFSG.GH74.Uniqueness.Bender.rootCenter
      (T : Subgroup (residueQuotient Δ P Q k))) = 2 ^ n := hL.card_center
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hne_bot : CFSG.GH74.Uniqueness.Bender.rootCenter
      (T : Subgroup (residueQuotient Δ P Q k)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨uT, hu1T⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne_bot
  let u : residueQuotient Δ P Q k := (uT : residueQuotient Δ P Q k)
  have hu1 : u ≠ 1 := fun h => hu1T (Subtype.ext h)
  have huT : u ∈ (T : Subgroup (residueQuotient Δ P Q k)) := uT.2.1
  have huT' : u ∈ (T' : Subgroup (residueQuotient Δ P Q k)) := by
    have hroot : u ∈ CFSG.GH74.Uniqueness.Bender.rootCenter
        (T' : Subgroup (residueQuotient Δ P Q k)) := by
      rw [← hcenter]
      exact uT.2
    exact (Subgroup.mem_inf.mp hroot).1
  by_contra hne
  have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
    CFSG.Models.benderPSU3Model_eq_psu3 n
  have e' : residueQuotient Δ P Q k ≃* CFSG.Open.PSU3 2 n :=
    e.trans (MulEquiv.subgroupCongr hmodel)
  have hB : CFSG.Open.fusionBenderBorel (residueQuotient Δ P Q k) (2 ^ n) 3 :=
    CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hn e'
  have hTI := CFSG.ComponentClassification.Asc76X.inf_eq_bot_of_fusionBenderBorel hB hne
  have hu_bot : u ∈ (⊥ : Subgroup (residueQuotient Δ P Q k)) := by
    rw [← hTI]
    exact ⟨huT, huT'⟩
  exact hu1 (Subgroup.mem_bot.mp hu_bot)


theorem map_eq_map_of_commute_of_mem_frameResidue [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {X Y : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) (hY : Y ∈ frameResidue Δ P Q k) (hXY : X ≠ Y)
    {xL yL : ↥(residueGroup Δ P Q k)}
    (hxX : (xL : H) ∈ X) (hx1 : (xL : H) ≠ 1)
    (hyY : (yL : H) ∈ Y) (hy1 : (yL : H) ≠ 1)
    (hcomm : Commute
      (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) xL)
      (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) yL)) :
    (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) xL) =
      (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) yL) := by
  let π := QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))
  have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hXY
  have hsqX : ∀ a ∈ X, a * a = 1 := fun a ha => hΔ.root.mul_self X hX.1 a ha
  have hoddH : Odd (orderOf ((xL : H) * (yL : H))) :=
    Opposite.odd_orderOf_mul (A := X) (B := Y) hsqX hopp hxX hx1 hyY hy1
  have hoddL : Odd (orderOf (xL * yL)) := by
    rw [← Subgroup.orderOf_coe]
    simpa using hoddH
  have hoddπ : Odd (orderOf (π xL * π yL)) := by
    have h1 : orderOf (π (xL * yL)) ∣ orderOf (xL * yL) := orderOf_map_dvd π (xL * yL)
    have h2 : Odd (orderOf (π (xL * yL))) := Odd.of_dvd_nat hoddL h1
    simpa [map_mul] using h2
  have hx2 : xL * xL = 1 := Subtype.ext (hΔ.root.mul_self X hX.1 (xL : H) hxX)
  have hy2 : yL * yL = 1 := Subtype.ext (hΔ.root.mul_self Y hY.1 (yL : H) hyY)
  have hxπ2 : (π xL) * (π xL) = 1 := by
    rw [← map_mul, hx2, map_one]
  have hyπ2 : (π yL) * (π yL) = 1 := by
    rw [← map_mul, hy2, map_one]
  have hsqπ : (π xL * π yL) * (π xL * π yL) = 1 := by
    calc (π xL * π yL) * (π xL * π yL) = π xL * (π yL * π xL) * π yL := by group
      _ = π xL * (π xL * π yL) * π yL := by rw [hcomm.eq]
      _ = (π xL * π xL) * (π yL * π yL) := by group
      _ = 1 := by rw [hxπ2, hyπ2, one_mul]
  have hord2 : orderOf (π xL * π yL) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
  have hord1 : orderOf (π xL * π yL) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · rw [h] at hoddπ
      obtain ⟨m, hm⟩ := hoddπ
      omega
  have hmul : (π xL) * (π yL) = 1 := orderOf_eq_one_iff.mp hord1
  calc π xL = π xL * (π yL * π yL) := by rw [hyπ2, mul_one]
    _ = (π xL * π yL) * π yL := by group
    _ = π yL := by rw [hmul, one_mul]

theorem residueMemberImage_le_rootCenter [Finite H] (hΔ : IsTransvectionClass Δ)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k)
    {T : Sylow 2 (residueQuotient Δ P Q k)} {n i e : ℕ}
    {t : residueQuotient Δ P Q k}
    (hL : CFSG.GH74.Uniqueness.Bender.Lemma32 n i e
      (T : Subgroup (residueQuotient Δ P Q k)) t)
    (hTle : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X ≤
      (T : Subgroup (residueQuotient Δ P Q k))) :
    residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X ≤
      CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup (residueQuotient Δ P Q k)) := by
  intro g hg
  rcases eq_or_ne g 1 with rfl | hg1
  · exact Subgroup.one_mem _
  · have hgT : g ∈ (T : Subgroup (residueQuotient Δ P Q k)) := hTle hg
    have hg2 : orderOf g = 2 := by
      exact orderOf_eq_prime (by
        rw [pow_two]
        exact residueMemberImage_sq_eq_one hΔ hX hg) hg1
    exact ((hL.involutions_iff g).mp ⟨Subgroup.le_normalizer hgT, hg2⟩).1


private theorem rootCenter_le_residueMemberImage_of_psu3 [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k)
    {T : Sylow 2 (residueQuotient Δ P Q k)} {t : residueQuotient Δ P Q k}
    (hL : CFSG.GH74.Uniqueness.Bender.Lemma32 n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1))
      (T : Subgroup (residueQuotient Δ P Q k)) t)
    (hXroot : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X ≤
      CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup (residueQuotient Δ P Q k)))
    (hcard : Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) =
      Nat.card X) :
    CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup (residueQuotient Δ P Q k)) ≤
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X := by
  classical
  let π := QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))
  let Qq := residueQuotient Δ P Q k
  have hB : CFSG.BenderSuzuki.IsBenderGroup Qq := .isPSU3 n hn e
  intro u hu
  rcases eq_or_ne u 1 with rfl | hu1
  · exact Subgroup.one_mem _
  · have hu2 : u * u = 1 := by
      have := hL.elemAbelian_center.2 u hu
      simpa [pow_two] using this
    have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
    obtain ⟨y, hyD, hπy⟩ := exists_residueElt_map_eq_of_orderOf_eq_two
      (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hB hu_ord
    obtain ⟨hy1, Y, hY, hyY⟩ := hyD
    by_cases hYX : Y = X
    · rw [hYX] at hyY
      rw [← hπy]
      exact Subgroup.mem_map_of_mem π (show y ∈ X.subgroupOf (residueGroup Δ P Q k) from hyY)
    · exfalso
      have hne : X ≠ Y := Ne.symm hYX
      obtain ⟨x, hxX, hx1⟩ := hΔ.root.exists_ne_one hX.1
      have hu_comm : ∀ v ∈ CFSG.GH74.Uniqueness.Bender.rootCenter
          (T : Subgroup Qq), Commute v u := by
        intro v hv
        exact Subgroup.mem_centralizer_iff.mp hu.2 v hv.1
      have hsub : (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X : Set Qq) ⊆
          ({1, u} : Set Qq) := by
        intro v hv
        obtain ⟨z, hzX, rfl⟩ := Subgroup.mem_map.mp hv
        by_cases hz1 : (z : ↥(residueGroup Δ P Q k)) = 1
        · left
          rw [hz1]
          simp
        · right
          have hzH1 : (z : H) ≠ 1 := fun h => hz1 (Subtype.ext h)
          have hzroot : π z ∈ CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup Qq) :=
            hXroot (Subgroup.mem_map_of_mem π hzX)
          have hcommzy : Commute
              (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) z)
              (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) y) := by
            rw [hπy]
            exact hu_comm (π z) hzroot
          have hmap := map_eq_map_of_commute_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q)
            (k := k) hΔ hML hF hX hY hne (xL := z) (yL := y) hzX hzH1 hyY hy1 hcommzy
          rw [hπy] at hmap
          exact hmap
      have hle2 : Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) ≤ 2 := by
        have hcoe : (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X : Set Qq).ncard =
            Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) :=
          Nat.card_coe_set_eq _
        rw [← hcoe]
        calc (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X : Set Qq).ncard
            ≤ ({1, u} : Set Qq).ncard := Set.ncard_le_ncard hsub
          _ ≤ 2 := by
            rcases eq_or_ne u 1 with rfl | hu1'
            · simp
            · have hpair := Set.ncard_pair (a := (1 : Qq)) (b := u) (Ne.symm hu1')
              rw [hpair]
      have hge : 4 ≤ Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) := by
        rw [hcard]
        exact hq X hX.1
      omega


private theorem residueMemberImage_eq_center_of_psu3 [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) :
    ∃ T : Sylow 2 (residueQuotient Δ P Q k),
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X =
        (Subgroup.center (T : Subgroup (residueQuotient Δ P Q k))).map
          (T : Subgroup (residueQuotient Δ P Q k)).subtype := by
  classical
  have hinf := inf_center_eq_bot_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hX
  have hcard : Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) =
      Nat.card X :=
    card_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
      (frameResidue_le_residueGroup hX) hinf
  obtain ⟨T, hTle⟩ := (isPGroup_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hX).exists_le_sylow
  obtain ⟨t, hL⟩ := exists_benderSylowData_unitary (Δ := Δ) (P := P) (Q := Q) (k := k) hn e T
  have hroot_le := residueMemberImage_le_rootCenter (Δ := Δ) (P := P) (Q := Q)
    (k := k) hΔ hX hL hTle
  have hroot_ge := rootCenter_le_residueMemberImage_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hq hn e hX hL hroot_le hcard
  refine ⟨T, ?_⟩
  rw [le_antisymm hroot_le hroot_ge, CFSG.GH74.Uniqueness.Bender.rootCenter_eq_map_center]

private theorem eq_of_map_eq_of_opposite [Finite H] (hΔ : IsTransvectionClass Δ)
    {X Y : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) (hY : Y ∈ frameResidue Δ P Q k)
    (hopp : Opposite X Y) {xL yL : ↥(residueGroup Δ P Q k)}
    (hxX : (xL : H) ∈ X) (hx1 : (xL : H) ≠ 1) (hyY : (yL : H) ∈ Y) (hy1 : (yL : H) ≠ 1)
    (hπ : (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) xL =
      (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) yL) : xL = yL := by
  let L := residueGroup Δ P Q k
  let π := QuotientGroup.mk' (Subgroup.center L)
  have hxL2 : xL * xL = 1 := Subtype.ext (hΔ.root.mul_self X hX.1 (xL : H) hxX)
  have hyL2 : yL * yL = 1 := Subtype.ext (hΔ.root.mul_self Y hY.1 (yL : H) hyY)
  have hz : xL * yL ∈ Subgroup.center L := by
    refine (QuotientGroup.eq_one_iff (xL * yL)).mp ?_
    change π (xL * yL) = 1
    rw [map_mul, ← hπ, ← map_mul, hxL2, map_one]
  have hcomm : Commute xL yL := by
    have hc := (Subgroup.mem_center_iff.mp hz) xL
    have hc' : yL = xL * yL * xL := by rw [← hc, ← mul_assoc, hxL2, one_mul]
    calc xL * yL = xL * yL * 1 := (mul_one _).symm
      _ = xL * yL * (xL * xL) := by rw [hxL2]
      _ = (xL * yL * xL) * xL := by group
      _ = yL * xL := by rw [← hc']
  have hz2 : (xL * yL) * (xL * yL) = 1 := by
    calc (xL * yL) * (xL * yL) = xL * (yL * xL) * yL := by group
      _ = xL * (xL * yL) * yL := by rw [← hcomm.eq]
      _ = (xL * xL) * (yL * yL) := by group
      _ = 1 := by rw [hxL2, hyL2, one_mul]
  have hodd : Odd (orderOf (xL * yL)) := by
    have hsqX : ∀ a ∈ X, a * a = 1 := fun a ha => hΔ.root.mul_self X hX.1 a ha
    have hoddH : Odd (orderOf ((xL : H) * (yL : H))) :=
      Opposite.odd_orderOf_mul (A := X) (B := Y) hsqX hopp hxX hx1 hyY hy1
    rw [← Subgroup.orderOf_coe]
    simpa using hoddH
  have hz1 : xL * yL = 1 := by
    have hdvd : orderOf (xL * yL) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · rw [h2] at hodd
      obtain ⟨m, hm⟩ := hodd
      omega
  calc xL = xL * (yL * yL) := by rw [hyL2, mul_one]
    _ = (xL * yL) * yL := by group
    _ = yL := by rw [hz1, one_mul]

theorem IsMaxFrame.eq_of_residueMemberImage_eq [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {X Y : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) (hY : Y ∈ frameResidue Δ P Q k)
    (h : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X =
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y) : X = Y := by
  classical
  by_contra hXY
  have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hXY
  let L := residueGroup Δ P Q k
  let π := QuotientGroup.mk' (Subgroup.center L)
  obtain ⟨x, hxX, hx1⟩ := hΔ.root.exists_ne_one hX.1
  let xL : ↥L := ⟨x, frameResidue_le_residueGroup hX hxX⟩
  have hxπ : π xL ∈ residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X :=
    Subgroup.mem_map_of_mem π (show xL ∈ X.subgroupOf L from hxX)
  rw [h] at hxπ
  obtain ⟨yL, hyY, hyπ⟩ := Subgroup.mem_map.mp hxπ
  have hxL_ne : xL ∉ Subgroup.center L := by
    intro hc
    have hmem : xL ∈ X.subgroupOf L ⊓ Subgroup.center L := ⟨hxX, hc⟩
    rw [inf_center_eq_bot_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
      hΔ hML hF hX, Subgroup.mem_bot] at hmem
    exact hx1 (congrArg Subtype.val hmem)
  have hyL1 : yL ≠ 1 := by
    intro hy
    refine hxL_ne ((QuotientGroup.eq_one_iff xL).mp ?_)
    change π xL = 1
    rw [← hyπ, hy, map_one]
  have hy1 : (yL : H) ≠ 1 := fun h' => hyL1 (Subtype.ext h')
  have hxLyL : xL = yL :=
    eq_of_map_eq_of_opposite hΔ hX hY hopp hxX hx1 hyY hy1 hyπ.symm
  have hxY : x ∈ Y := by
    have h' : (xL : H) = (yL : H) := congrArg Subtype.val hxLyL
    have hyY' : (yL : H) ∈ Y := hyY
    rw [← h'] at hyY'
    simpa using hyY'
  have hmem : x ∈ X ⊓ Y := ⟨hxX, hxY⟩
  rw [hopp.inf_eq_bot] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

private theorem exists_mem_frameResidue_image_eq_rootCenter_of_psu3 [Finite H]
    (hΔ : IsTransvectionClass Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n)
    (T : Sylow 2 (residueQuotient Δ P Q k)) :
    ∃ X ∈ frameResidue Δ P Q k,
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X =
        CFSG.GH74.Uniqueness.Bender.rootCenter
          (T : Subgroup (residueQuotient Δ P Q k)) := by
  classical
  let L := residueGroup Δ P Q k
  let Qq := residueQuotient Δ P Q k
  let π := QuotientGroup.mk' (Subgroup.center L)
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  obtain ⟨T₀, hT₀⟩ := residueMemberImage_eq_center_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hq hn e hP
  have hT₀root : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k) =
      CFSG.GH74.Uniqueness.Bender.rootCenter (T₀ : Subgroup Qq) :=
    hT₀.trans (CFSG.GH74.Uniqueness.Bender.rootCenter_eq_map_center _).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Qq T₀ T
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) g
  let A : Subgroup ↥L := (P k).subgroupOf L
  let X : Subgroup H := (conjSub A g').map L.subtype
  have hXeq : X = conjSub (P k) (g' : H) := by
    change (conjSub A g').map L.subtype = conjSub (P k) (g' : H)
    rw [← ModelRank.conjSub_map L.subtype A g',
      Subgroup.map_subgroupOf_eq_of_le (frameResidue_le_residueGroup hP)]
    rfl
  have hXmem : X ∈ frameResidue Δ P Q k := by
    rw [hXeq]
    exact conjSub_mem_frameResidue hΔ hP g'.2
  have hXsub : X.subgroupOf L = conjSub A g' := by
    change X.comap L.subtype = conjSub A g'
    rw [show X = (conjSub A g').map L.subtype from rfl,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hXimg : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X =
      conjSub (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k)) (π g') := by
    change (X.subgroupOf L).map π = conjSub (((P k).subgroupOf L).map π) (π g')
    rw [hXsub, ← ModelRank.conjSub_map π A g']
  have hTcoe : (T : Subgroup Qq) =
      (T₀ : Subgroup Qq).map (MulAut.conj (π g')).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hroot_conj : CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup Qq) =
      (CFSG.GH74.Uniqueness.Bender.rootCenter (T₀ : Subgroup Qq)).map
        (MulAut.conj (π g')).toMonoidHom := by
    rw [hTcoe]
    exact CFSG.QuasiDihedralFusion.centerOf_map (MulAut.conj (π g')) (T₀ : Subgroup Qq)
  refine ⟨X, hXmem, ?_⟩
  rw [hXimg, hT₀root]
  exact hroot_conj.symm


theorem inf_center_eq_bot_sup_of_mem_frameResidue [Finite H] (hΔ : IsTransvectionClass Δ)
    {A B : Subgroup H}
    (hA : A ∈ frameResidue Δ P Q k) (hB : B ∈ frameResidue Δ P Q k) (hopp : Opposite A B) :
    (A ⊔ B).subgroupOf (residueGroup Δ P Q k) ⊓
      Subgroup.center ↥(residueGroup Δ P Q k) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨hzS, hzC⟩ := hz
  let zS : ↥(A ⊔ B) := ⟨(z : H), hzS⟩
  have hSle : A ⊔ B ≤ residueGroup Δ P Q k :=
    sup_le (frameResidue_le_residueGroup hA) (frameResidue_le_residueGroup hB)
  have hzcenter : zS ∈ Subgroup.center ↥(A ⊔ B) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgL : (g : H) ∈ residueGroup Δ P Q k := hSle g.2
    have hc := Subgroup.mem_center_iff.mp hzC (⟨(g : H), hgL⟩ : ↥(residueGroup Δ P Q k))
    change (g : H) * (z : H) = (z : H) * (g : H)
    exact congrArg Subtype.val hc
  have hbot : Subgroup.center ↥(A ⊔ B) = ⊥ :=
    ElemAbRankOne.center_eq_bot (hopp.isElemAbRankOne hΔ.root hA.1)
  rw [hbot, Subgroup.mem_bot] at hzcenter
  have hz1 : z = 1 := by
    apply Subtype.ext
    have h := congrArg (fun w : ↥(A ⊔ B) => w.val) hzcenter
    simpa [zS] using h
  exact hz1


private theorem false_of_sz_case [Finite H] (hΔ : IsTransvectionClass Δ)
    (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {a : ℕ} (ha : 1 ≤ a)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.SzModel a) : False := by
  classical
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  have hQ : Q k ∈ frameResidue Δ P Q k := hF.toIsFrame.memQ_frameResidue k
  have hopp : Opposite (P k) (Q k) := hF.opposite k
  obtain ⟨m, hm2, hmcard, φ, -, -⟩ :=
    Opposite.exists_mulEquiv_SL2 (R := Δ) hΔ.root (hF.memP k) hopp (hq (P k) (hF.memP k))
  have hcardSL : Nat.card ↥(P k ⊔ Q k) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    calc Nat.card ↥(P k ⊔ Q k)
        = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) :=
          Nat.card_congr φ.toEquiv
      _ = 2 ^ m * ((2 ^ m) ^ 2 - 1) := Bridge.card_SL_two_galoisField_two m (by omega)
  have h3SL : 3 ∣ Nat.card ↥(P k ⊔ Q k) := by
    rw [hcardSL]
    refine dvd_mul_of_dvd_right ?_ _
    have h3 : 3 ∣ (2 ^ m) ^ 2 - 1 := by
      have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) m
      rw [← pow_mul, mul_comm, pow_mul] at this
      simpa using this
    exact h3
  have hSle : P k ⊔ Q k ≤ residueGroup Δ P Q k :=
    sup_le (frameResidue_le_residueGroup hP) (frameResidue_le_residueGroup hQ)
  have hinfS := inf_center_eq_bot_sup_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hP hQ hopp
  have hcardMap := card_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) hSle hinfS
  have h3img : 3 ∣ Nat.card
      (((P k ⊔ Q k).subgroupOf (residueGroup Δ P Q k)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)))) := by
    change 3 ∣ Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k ⊔ Q k))
    rw [hcardMap]
    exact h3SL
  have h3Q : 3 ∣ Nat.card (residueQuotient Δ P Q k) :=
    dvd_trans h3img (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_congr e.toEquiv] at h3Q
  exact CFSG.Timmesfeld.Bridge.RootClosure.not_three_dvd_card_szModel (n := a) ha h3Q


private theorem eq_sylow_of_mem_of_linear [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSL2Model n)
    {T : Sylow 2 (residueQuotient Δ P Q k)} {t : residueQuotient Δ P Q k}
    (hL : CFSG.GH74.Uniqueness.Bender.Lemma32 n 1 1
      (T : Subgroup (residueQuotient Δ P Q k)) t)
    {u : residueQuotient Δ P Q k} (huT : u ∈ (T : Subgroup (residueQuotient Δ P Q k)))
    (hu1 : u ≠ 1) {S : Sylow 2 (residueQuotient Δ P Q k)}
    (huS : u ∈ (S : Subgroup (residueQuotient Δ P Q k))) : S = T := by
  classical
  have hTcenter : CFSG.GH74.Uniqueness.Bender.rootCenter
      (T : Subgroup (residueQuotient Δ P Q k)) =
      (T : Subgroup (residueQuotient Δ P Q k)) := by
    apply Subgroup.eq_of_le_of_card_ge
      (H := CFSG.GH74.Uniqueness.Bender.rootCenter
        (T : Subgroup (residueQuotient Δ P Q k)))
      (K := (T : Subgroup (residueQuotient Δ P Q k)))
    · exact inf_le_left
    · rw [hL.card_center]
      have := hL.card_sylow
      simpa [pow_one] using this.le
  have huT' : u ∈ (T : Subgroup (residueQuotient Δ P Q k)) := huT
  rw [← hTcenter] at huT
  have hu2 : u * u = 1 := by
    have := hL.elemAbelian_center.2 u huT
    simpa [pow_two] using this
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
  have hBT : CFSG.GH74.Uniqueness.Bender.BenderType
      (residueQuotient Δ P Q k) n 1 1 := .linear n hn e
  obtain ⟨t', hc⟩ := hBT.exists_benderCore T
  obtain ⟨-, -, hcentcard, -, -, -, -⟩ := hBT.lemma_3_4_b T hc.sq_eq_one hc.not_mem
    (u := u) ⟨Subgroup.le_normalizer huT', hu_ord⟩
  have hcentcard' : Nat.card ↥(Subgroup.centralizer ({u} : Set (residueQuotient Δ P Q k))) =
      2 ^ n := by
    simpa using hcentcard
  have hTcard : Nat.card (T : Subgroup (residueQuotient Δ P Q k)) = 2 ^ n := by
    have := hL.card_sylow
    simpa [pow_one] using this
  have hcommT := Bridge.Asc72.IsBenderGroup.commute_of_psl2 hn e T
  have hTleC : (T : Subgroup (residueQuotient Δ P Q k)) ≤
      Subgroup.centralizer ({u} : Set (residueQuotient Δ P Q k)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcommT v hv u huT').symm
  have hTeqC : (T : Subgroup (residueQuotient Δ P Q k)) =
      Subgroup.centralizer ({u} : Set (residueQuotient Δ P Q k)) :=
    Subgroup.eq_of_le_of_card_ge hTleC (by rw [hcentcard', hTcard])
  have hScard : Nat.card (S : Subgroup (residueQuotient Δ P Q k)) =
      Nat.card (T : Subgroup (residueQuotient Δ P Q k)) :=
    Nat.card_congr (Sylow.equiv S T).toEquiv
  have hcommS := Bridge.Asc72.IsBenderGroup.commute_of_psl2 hn e S
  have hSleC : (S : Subgroup (residueQuotient Δ P Q k)) ≤
      Subgroup.centralizer ({u} : Set (residueQuotient Δ P Q k)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcommS v hv u huS).symm
  have hSeqC : (S : Subgroup (residueQuotient Δ P Q k)) =
      Subgroup.centralizer ({u} : Set (residueQuotient Δ P Q k)) :=
    Subgroup.eq_of_le_of_card_ge hSleC (by rw [hcentcard', hScard, hTcard])
  exact Sylow.ext_iff.2 (hSeqC.trans hTeqC.symm)

private theorem eq_of_le_sylow_of_mem_frameResidue_linear [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSL2Model n)
    {T : Sylow 2 (residueQuotient Δ P Q k)} {X Y : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) (hY : Y ∈ frameResidue Δ P Q k)
    (hTX : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X ≤
      (T : Subgroup (residueQuotient Δ P Q k)))
    (hTY : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y ≤
      (T : Subgroup (residueQuotient Δ P Q k))) : X = Y := by
  classical
  by_contra hXY
  let π := QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))
  have hcommT := Bridge.Asc72.IsBenderGroup.commute_of_psl2 hn e T
  obtain ⟨x, hxX, hx1⟩ := hΔ.root.exists_ne_one hX.1
  let xL : ↥(residueGroup Δ P Q k) := ⟨x, frameResidue_le_residueGroup hX hxX⟩
  have hxT : π xL ∈ (T : Subgroup (residueQuotient Δ P Q k)) :=
    hTX (Subgroup.mem_map_of_mem π (show xL ∈ X.subgroupOf (residueGroup Δ P Q k) from hxX))
  have hsub : (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y :
      Set (residueQuotient Δ P Q k)) ⊆ ({1, π xL} : Set (residueQuotient Δ P Q k)) := by
    intro v hv
    obtain ⟨y, hyY, rfl⟩ := Subgroup.mem_map.mp hv
    by_cases hy1 : (y : ↥(residueGroup Δ P Q k)) = 1
    · left
      rw [hy1]
      simp
    · right
      have hyH1 : (y : H) ≠ 1 := fun h => hy1 (Subtype.ext h)
      have hyT : π y ∈ (T : Subgroup (residueQuotient Δ P Q k)) :=
        hTY (Subgroup.mem_map_of_mem π hyY)
      have hcommxy : Commute (π xL) (π y) := hcommT _ hxT _ hyT
      have hmap := map_eq_map_of_commute_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q)
        (k := k) hΔ hML hF hX hY hXY (xL := xL) (yL := y) hxX hx1 hyY hyH1 hcommxy
      simpa [π, Set.mem_singleton_iff] using hmap.symm
  have hinfY := inf_center_eq_bot_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hY
  have hcardY : Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y) =
      Nat.card Y :=
    card_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
      (frameResidue_le_residueGroup hY) hinfY
  have hle2 : Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y) ≤ 2 := by
    have hcoe : (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y :
        Set (residueQuotient Δ P Q k)).ncard =
        Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y) :=
      Nat.card_coe_set_eq _
    rw [← hcoe]
    calc (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y :
          Set (residueQuotient Δ P Q k)).ncard
        ≤ ({1, π xL} : Set (residueQuotient Δ P Q k)).ncard := Set.ncard_le_ncard hsub
      _ ≤ 2 := by
        rcases eq_or_ne (π xL) 1 with h1 | h1
        · simp [h1]
        · have hpair := Set.ncard_pair (a := (1 : residueQuotient Δ P Q k)) (b := π xL)
            (Ne.symm h1)
          rw [hpair]
  have hge : 4 ≤ Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y) := by
    rw [hcardY]
    exact hq Y hY.1
  omega


private theorem card_eq_two_pow_of_linear [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSL2Model n)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k)
    {T : Sylow 2 (residueQuotient Δ P Q k)}
    (hTX : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X ≤
      (T : Subgroup (residueQuotient Δ P Q k))) : Nat.card X = 2 ^ n := by
  classical
  let π := QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))
  obtain ⟨t, hL⟩ := exists_benderSylowData_linear (Δ := Δ) (P := P) (Q := Q) (k := k) hn e T
  have hTcard : Nat.card (T : Subgroup (residueQuotient Δ P Q k)) = 2 ^ n := by
    have := hL.card_sylow
    simpa [pow_one] using this
  have hTcenter : CFSG.GH74.Uniqueness.Bender.rootCenter
      (T : Subgroup (residueQuotient Δ P Q k)) =
      (T : Subgroup (residueQuotient Δ P Q k)) := by
    apply Subgroup.eq_of_le_of_card_ge
      (H := CFSG.GH74.Uniqueness.Bender.rootCenter
        (T : Subgroup (residueQuotient Δ P Q k)))
      (K := (T : Subgroup (residueQuotient Δ P Q k)))
    · exact inf_le_left
    · rw [hL.card_center]
      simpa [pow_one] using hL.card_sylow.le
  have hB : CFSG.BenderSuzuki.IsBenderGroup (residueQuotient Δ P Q k) := .isPSL2 n hn e
  have hTle : (T : Subgroup (residueQuotient Δ P Q k)) ≤
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X := by
    intro u huT
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · have hu_root : u ∈ CFSG.GH74.Uniqueness.Bender.rootCenter
          (T : Subgroup (residueQuotient Δ P Q k)) := by
        rw [hTcenter]
        exact huT
      have hu2 : u * u = 1 := by
        have := hL.elemAbelian_center.2 u hu_root
        simpa [pow_two] using this
      have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
      obtain ⟨y, hyD, hπy⟩ := exists_residueElt_map_eq_of_orderOf_eq_two
        (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hB hu_ord
      obtain ⟨hy1, Y, hY, hyY⟩ := hyD
      obtain ⟨S, hSle⟩ :=
        (isPGroup_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hY).exists_le_sylow
      have huS : u ∈ (S : Subgroup (residueQuotient Δ P Q k)) := by
        rw [← hπy]
        exact hSle (Subgroup.mem_map_of_mem π
          (show y ∈ Y.subgroupOf (residueGroup Δ P Q k) from hyY))
      have hST : S = T := eq_sylow_of_mem_of_linear (Δ := Δ) (P := P) (Q := Q) (k := k)
        hn e hL huT hu1 huS
      have hYT : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) Y ≤
          (T : Subgroup (residueQuotient Δ P Q k)) := by
        rwa [hST] at hSle
      have hYX : Y = X := eq_of_le_sylow_of_mem_frameResidue_linear (Δ := Δ) (P := P) (Q := Q)
        (k := k) hΔ hML hF hq hn e hY hX hYT hTX
      rw [hYX] at hyY
      rw [← hπy]
      exact Subgroup.mem_map_of_mem π
        (show y ∈ X.subgroupOf (residueGroup Δ P Q k) from hyY)
  have hTeq : (T : Subgroup (residueQuotient Δ P Q k)) =
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X :=
    le_antisymm hTle hTX
  have hinfX := inf_center_eq_bot_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hX
  have hcardX := card_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
    (frameResidue_le_residueGroup hX) hinfX
  calc Nat.card X = Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) :=
        hcardX.symm
    _ = Nat.card (T : Subgroup (residueQuotient Δ P Q k)) := by rw [hTeq]
    _ = 2 ^ n := hTcard


private theorem residuePointMap_mem_linear [Finite H] (hΔ : IsTransvectionClass Δ)
    (hF : IsMaxFrame Δ P Q) :
    ∀ Pt : RankOne.Point ((P k).subgroupOf (P k ⊔ Q k)),
      Pt.val.map (P k ⊔ Q k).subtype ∈ frameResidue Δ P Q k := by
  classical
  intro Pt
  obtain ⟨g, hg⟩ := Pt.exists_eq
  have hcomp : ∀ g : ↥(P k ⊔ Q k),
      (P k ⊔ Q k).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : H)).toMonoidHom.comp (P k ⊔ Q k).subtype := by
    intro g
    ext x
    rfl
  have hFP : Pt.val.map (P k ⊔ Q k).subtype = conjSub (P k) (g : H) := by
    calc
      Pt.val.map (P k ⊔ Q k).subtype = ((P k).subgroupOf (P k ⊔ Q k)).map
          ((P k ⊔ Q k).subtype.comp (MulAut.conj g).toMonoidHom) := by
        rw [hg, Subgroup.map_map]
      _ = ((P k).subgroupOf (P k ⊔ Q k)).map
          ((MulAut.conj (g : H)).toMonoidHom.comp (P k ⊔ Q k).subtype) := by
        rw [hcomp g]
      _ = (((P k).subgroupOf (P k ⊔ Q k)).map (P k ⊔ Q k).subtype).map
          (MulAut.conj (g : H)) := by
        rw [Subgroup.map_map]
        rfl
      _ = (P k).map (MulAut.conj (g : H)) := by
        rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : P k ≤ P k ⊔ Q k)]
      _ = conjSub (P k) (g : H) := rfl
  rw [hFP]
  exact conjSub_mem_frameResidue hΔ (hF.toIsFrame.memP_frameResidue k)
    (sup_le (frameResidue_le_residueGroup (hF.toIsFrame.memP_frameResidue k))
      (frameResidue_le_residueGroup (hF.toIsFrame.memQ_frameResidue k)) g.2)

private theorem residuePointMap_injective_linear :
    Function.Injective (fun Pt : RankOne.Point ((P k).subgroupOf (P k ⊔ Q k)) =>
      Pt.val.map (P k ⊔ Q k).subtype) := by
  intro Pt Qt hPQ
  apply RankOne.Point.ext
  apply Subgroup.map_injective (f := (P k ⊔ Q k).subtype) (P k ⊔ Q k).subtype_injective
  exact hPQ

private theorem frameResidue_le_sup_of_linear [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSL2Model n) :
    ∀ X ∈ frameResidue Δ P Q k, X ≤ P k ⊔ Q k := by
  classical
  let S : Subgroup H := P k ⊔ Q k
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  have hSle : S ≤ residueGroup Δ P Q k :=
    sup_le (frameResidue_le_residueGroup hP)
      (frameResidue_le_residueGroup (hF.toIsFrame.memQ_frameResidue k))
  have hrank : IsElemAbRankOne ((P k).subgroupOf S) ((Q k).subgroupOf S) :=
    (hF.opposite k).isElemAbRankOne hΔ.root (hF.memP k)
  obtain ⟨T₀, hT₀⟩ :=
    (isPGroup_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hP).exists_le_sylow
  have hPk_card : Nat.card (P k) = 2 ^ n :=
    card_eq_two_pow_of_linear (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hq hn e hP hT₀
  have hpoint_card : Nat.card (RankOne.Point ((P k).subgroupOf S)) = 2 ^ n + 1 := by
    rw [hrank.card_point, card_subgroupOf_of_le (le_sup_left : P k ≤ S), hPk_card]
  let F : RankOne.Point ((P k).subgroupOf S) → Subgroup H := fun Pt => Pt.val.map S.subtype
  have hF_inj : Function.Injective F := residuePointMap_injective_linear
  have hF_mem : ∀ Pt : RankOne.Point ((P k).subgroupOf S), F Pt ∈ frameResidue Δ P Q k :=
    residuePointMap_mem_linear hΔ hF
  let G : RankOne.Point ((P k).subgroupOf S) → Sylow 2 (residueQuotient Δ P Q k) := fun Pt =>
    Classical.choose ((isPGroup_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
      hΔ (hF_mem Pt)).exists_le_sylow)
  have hG_le : ∀ Pt, residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (F Pt) ≤
      (G Pt : Subgroup (residueQuotient Δ P Q k)) := fun Pt =>
    Classical.choose_spec ((isPGroup_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
      hΔ (hF_mem Pt)).exists_le_sylow)
  have hG_inj : Function.Injective G := by
    intro Pt Qt hPQ
    apply hF_inj
    exact eq_of_le_sylow_of_mem_frameResidue_linear (Δ := Δ) (P := P) (Q := Q) (k := k)
      hΔ hML hF hq hn e (hF_mem Pt) (hF_mem Qt) (hPQ ▸ hG_le Pt) (hPQ ▸ hG_le Qt)
  have hSylow_card : Nat.card (Sylow 2 (residueQuotient Δ P Q k)) = 2 ^ n + 1 := by
    obtain ⟨t, hL⟩ := exists_benderSylowData_linear (Δ := Δ) (P := P) (Q := Q) (k := k) hn e T₀
    rw [Sylow.card_eq_index_normalizer]
    simpa [CFSG.GH74.Uniqueness.Bender.borel, pow_one] using hL.index_eq
  have hG_bij : Function.Bijective G :=
    (Nat.bijective_iff_injective_and_card G).mpr
      ⟨hG_inj, by rw [hpoint_card, hSylow_card]⟩
  intro X hX
  obtain ⟨T, hTX⟩ :=
    (isPGroup_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hX).exists_le_sylow
  obtain ⟨Pt, hPt⟩ := hG_bij.2 T
  have hFT : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (F Pt) ≤
      (T : Subgroup (residueQuotient Δ P Q k)) := by
    rw [← hPt]
    exact hG_le Pt
  have hXF : X = F Pt := eq_of_le_sylow_of_mem_frameResidue_linear (Δ := Δ) (P := P) (Q := Q)
    (k := k) hΔ hML hF hq hn e hX (hF_mem Pt) hTX hFT
  obtain ⟨g, hg⟩ := Pt.exists_eq
  have hF_eq : F Pt = conjSub (P k) (g : H) := by
    calc
      F Pt = ((P k).subgroupOf S).map
          (S.subtype.comp (MulAut.conj g).toMonoidHom) := by
        simp only [F, hg]
        rw [Subgroup.map_map]
      _ = ((P k).subgroupOf S).map
          ((MulAut.conj (g : H)).toMonoidHom.comp S.subtype) := by
        have hcomp : S.subtype.comp (MulAut.conj g).toMonoidHom =
            (MulAut.conj (g : H)).toMonoidHom.comp S.subtype := by
          ext x
          rfl
        rw [hcomp]
      _ = (((P k).subgroupOf S).map S.subtype).map
          (MulAut.conj (g : H)) := by
        rw [Subgroup.map_map]
        rfl
      _ = (P k).map (MulAut.conj (g : H)) := by
        rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : P k ≤ S)]
      _ = conjSub (P k) (g : H) := rfl
  rw [hXF, hF_eq]
  exact conjSub_le (le_sup_left : P k ≤ S) g.2

private theorem card_eq_two_pow_of_psu3 [Finite H] (hΔ : IsTransvectionClass Δ)
    (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) : Nat.card X = 2 ^ n := by
  obtain ⟨T, hT⟩ := residueMemberImage_eq_center_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hq hn e hX
  obtain ⟨t, hL⟩ := exists_benderSylowData_unitary (Δ := Δ) (P := P) (Q := Q) (k := k) hn e T
  have hinfX := inf_center_eq_bot_of_mem_frameResidue (Δ := Δ) (P := P) (Q := Q) (k := k)
    hΔ hML hF hX
  have hcardX := card_residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
    (frameResidue_le_residueGroup hX) hinfX
  calc Nat.card X = Nat.card (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X) :=
        hcardX.symm
    _ = Nat.card ((Subgroup.center (T : Subgroup (residueQuotient Δ P Q k))).map
          (T : Subgroup (residueQuotient Δ P Q k)).subtype) := by rw [hT]
    _ = Nat.card (Subgroup.center (T : Subgroup (residueQuotient Δ P Q k))) :=
        Subgroup.card_map_of_injective (T : Subgroup (residueQuotient Δ P Q k)).subtype_injective
    _ = Nat.card (CFSG.GH74.Uniqueness.Bender.rootCenter
          (T : Subgroup (residueQuotient Δ P Q k))) := by
        rw [CFSG.GH74.Uniqueness.Bender.rootCenter_eq_map_center]
        exact (Subgroup.card_map_of_injective
          (T : Subgroup (residueQuotient Δ P Q k)).subtype_injective).symm
    _ = 2 ^ n := hL.card_center

private theorem false_of_psl2_case [Finite H] (hΔ : IsTransvectionClass Δ) (hML : MeetsLines Δ)
    (hF : IsMaxFrame Δ P Q) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hns : ¬ IsSmallFrame Δ P Q k) {n : ℕ} (hn : 2 ≤ n)
    (e : residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSL2Model n) : False :=
  hns ((isSmallFrame_iff hF.toIsFrame).2
    (frameResidue_le_sup_of_linear (Δ := Δ) (P := P) (Q := Q) (k := k) hΔ hML hF hq hn e))


theorem IsMaxFrame.residueGroup_quotient_psu3 (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) :
    ∃ n : ℕ, 2 ≤ n ∧ (∀ A ∈ Δ, Nat.card A = 2 ^ n) ∧
      Nonempty (residueQuotient Δ P Q k ≃* CFSG.Theory.Comparator.PSU3Model n) := by
  haveI : Finite H := h.finite
  have hB := isBenderGroup_residueQuotient (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hML hF hq
  rcases hB with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · exact (false_of_psl2_case (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hML hF hq hns hn e).elim
  · exact (false_of_sz_case (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hF hq ha e).elim
  · refine ⟨n, hn, ?_, ⟨e⟩⟩
    intro A hA
    rw [h.cls.root.card_eq hA (hF.memP k)]
    exact card_eq_two_pow_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hML hF hq hn e
      (hF.toIsFrame.memP_frameResidue k)

theorem IsMaxFrame.map_mem_frameResidue_eq_center (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {X : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q k) :
    ∃ T : Sylow 2 (residueQuotient Δ P Q k),
      (X.subgroupOf (residueGroup Δ P Q k)).map
          (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))) =
        (Subgroup.center (T : Subgroup (residueQuotient Δ P Q k))).map
          (T : Subgroup (residueQuotient Δ P Q k)).subtype := by
  haveI : Finite H := h.finite
  have hB := isBenderGroup_residueQuotient (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hML hF hq
  rcases hB with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · exact (false_of_psl2_case (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hML hF hq hns hn e).elim
  · exact (false_of_sz_case (Δ := Δ) (P := P) (Q := Q) (k := k) h.cls hF hq ha e).elim
  · exact residueMemberImage_eq_center_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
      h.cls hML hF hq hn e hX


theorem IsMaxFrame.ncard_frameResidue_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) :
    (frameResidue Δ P Q k).ncard = (Nat.card (P k)) ^ 3 + 1 := by
  haveI : Finite H := h.finite
  obtain ⟨n, hn, hcardΔ, ⟨e⟩⟩ := hF.residueGroup_quotient_psu3 h hML hq hns
  let Qq := residueQuotient Δ P Q k
  have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
  obtain ⟨T₀, hT₀⟩ := residueMemberImage_eq_center_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
    h.cls hML hF hq hn e hP
  obtain ⟨t, hL⟩ := exists_benderSylowData_unitary (Δ := Δ) (P := P) (Q := Q) (k := k) hn e T₀
  have hSylow_card : Nat.card (Sylow 2 Qq) = (2 ^ n) ^ 3 + 1 := by
    rw [Sylow.card_eq_index_normalizer]
    simpa [CFSG.GH74.Uniqueness.Bender.borel] using hL.index_eq
  let f : {X // X ∈ frameResidue Δ P Q k} → Sylow 2 Qq := fun X =>
    Classical.choose (residueMemberImage_eq_center_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
      h.cls hML hF hq hn e X.2)
  have hf : ∀ X, residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X.1 =
      CFSG.GH74.Uniqueness.Bender.rootCenter (f X : Subgroup Qq) := fun X =>
    (Classical.choose_spec (residueMemberImage_eq_center_of_psu3 (Δ := Δ) (P := P) (Q := Q)
      (k := k) h.cls hML hF hq hn e X.2)).trans
      (CFSG.GH74.Uniqueness.Bender.rootCenter_eq_map_center _).symm
  have hf_inj : Function.Injective f := by
    intro X Y hXY
    apply Subtype.ext
    apply IsMaxFrame.eq_of_residueMemberImage_eq (Δ := Δ) (P := P) (Q := Q) (k := k)
      h.cls hML hF X.2 Y.2
    rw [hf X, hf Y, hXY]
  have hf_surj : Function.Surjective f := by
    intro T
    obtain ⟨X, hXmem, hXimg⟩ :=
      exists_mem_frameResidue_image_eq_rootCenter_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k)
        h.cls hML hF hq hn e T
    refine ⟨⟨X, hXmem⟩, ?_⟩
    apply eq_sylow_of_rootCenter_eq_of_psu3 (Δ := Δ) (P := P) (Q := Q) (k := k) hn e
    rw [← hf ⟨X, hXmem⟩, hXimg]
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  have hcardR : (frameResidue Δ P Q k).ncard = Nat.card (Sylow 2 Qq) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.ofBijective f hbij)
  have hqk : Nat.card (P k) = 2 ^ n := hcardΔ (P k) hP.1
  rw [hcardR, hSylow_card, hqk]


end CFSG.Timmesfeld.Transvection
