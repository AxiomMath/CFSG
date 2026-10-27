module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JA5Six
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Uniq
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Times
import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec4.Ronan148VL37
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_singleton_eq_of_zpowers_eq' {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, h,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

section Certificates

theorem not_case148Three_of_a5
    (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {J Yd : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hYdJ : Yd ≤ J) (hYdt : YdType148 d Yd)
    (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    letI := ker148_normal hY.2
    img148 A Y Yd = img148 A Y J →
    Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
    b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
    img148 A Y (deltaZero A (lB A) Y) =
      img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) →
    (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
      ¬ Case148Three A (lB A) (centPre148 A Y J)) := by
  intro heq hJ5 hbc hXeq
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  obtain ⟨φ⟩ := hJ5
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h60 : Nat.card (img148 A Y J) = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [h60]; norm_num
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hbJ := HJRes2.le_centralizer_of_theta hYdM heq hJθ hbA hbc.2
  have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hBJ : img148 A Y B ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hc.1]
    have hS' : ({b, d} : Set G) ⊆ (Y ⊔ A : Subgroup G) := by
      rintro g (rfl | rfl)
      · exact Subgroup.mem_sup_right hbA
      · exact Subgroup.mem_sup_right hdA
    refine img148_closure_le_centralizer hS' fun g hg => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hbJ hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hdJ hx)
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAp : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hjJ, hj1, hj3, hjC⟩ := exists_pow_eq_one_mem_centralizer hAp hAJα h3Jα
  have hjA : j ∈ img148 A Y A := hF3 j hjC hj3
  have hjZ : ∃ y ∈ img148 A Y J, j * y ≠ y * j := by
    by_contra hcon
    push Not at hcon
    apply hj1
    have hz : (⟨j, hjJ⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon g g.2).symm
    rw [hJZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hjB : j ∉ img148 A Y B := fun hjB' => by
    obtain ⟨y, hy, hjy⟩ := hjZ
    exact hjy (Subgroup.mem_centralizer_iff.mp (hBJ hjB') y hy).symm
  obtain ⟨hBA, -, hmax⟩ := img148_hyperplane_max (Y := Y) hA hB
  have hAeq : img148 A Y B ⊔ Subgroup.zpowers j = img148 A Y A := by
    rcases hmax _ le_sup_left (sup_le hBA (Subgroup.zpowers_le.mpr hjA)) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers j ≤ _) (Subgroup.mem_zpowers j)) hjB
    · exact h
  have hCB : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = img148 A Y B := by
    rcases hmax _ (le_inf hBA hBJ) inf_le_left with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hjy⟩ := hjZ
      have hjC' : j ∈ img148 A Y A ⊓
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [h]; exact hjA
      exact hjy (Subgroup.mem_centralizer_iff.mp hjC'.2 y hy).symm
  have hB9 : Nat.card (img148 A Y B) = 9 := by
    rw [card_img148_of_le hA.1.2 hB.1]
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZC : Zα ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((Zα : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  have hAZB : img148 A Y A ⊓ Zα ≤ img148 A Y B := fun x hx => hCB ▸ ⟨hx.1, hZC hx.2⟩
  have hjZα : ∀ z ∈ Zα, j * z = z * j := fun z hz =>
    Subgroup.mem_centralizer_iff.mp (hZC hz) j hjJ
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdαB : dα ∈ img148 A Y B :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA.1.2 hdA (Subgroup.one_mem A) (by rw [← hdαdef, h]; rfl)
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  intro h3
  obtain ⟨c₁, d₁, L₁, hc₁Ω, hL₁, hL₁J, hd₁A, hd₁1, hd₁c, hform, htype⟩ := h3
  have hdd : Subgroup.zpowers d = Subgroup.zpowers d₁ :=
    zpowers_eq_of_isLBConfig_of_theta h134 h48 hS hB hc hc₁Ω hL₁ hL₁J hd₁A hd₁1 hd₁c
  rw [← centralizer_singleton_eq_of_zpowers_eq' hdd] at hform
  have hkey : NoNormal3 ↥Zα → ∀ v ∈ Zα, dα * v = v * dα := by
    intro hNN
    set X₁ := deltaZero A (lB A) (centPre148 A Y J) with hX₁
    set O₁ := pPrimeCoreOf 3 X₁ with hO₁
    set D₁ := deltaZero A (lB A) (centPre148 A Y J ⊓ Subgroup.centralizer ({d} : Set G))
      with hD₁
    have hX₁M : X₁ ≤ Y ⊔ A := (deltaZero_le _).trans (centPre148_le.trans le_sup_left)
    have hO₁M : O₁ ≤ Y ⊔ A := (pPrimeCoreOf_le 3 _).trans hX₁M
    have hD₁X : D₁ ≤ X₁ := deltaZero_mono inf_le_left
    have hD₁M : D₁ ≤ Y ⊔ A := hD₁X.trans hX₁M
    have hsup : Zα = img148 A Y O₁ ⊔ img148 A Y D₁ := by
      have h1 := congrArg (img148 A Y) hform
      rwa [img148_sup hO₁M hD₁M] at h1
    have hOZ : img148 A Y O₁ ≤ Zα := img148_mono (pPrimeCoreOf_le 3 _)
    have hON : Zα ≤ Subgroup.normalizer (img148 A Y O₁ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
      img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 X₁)
    have hO3 : ¬ 3 ∣ Nat.card (img148 A Y O₁) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_img148
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)))
    have hO1 : img148 A Y O₁ = ⊥ := by
      have hNorm : ((img148 A Y O₁).subgroupOf Zα).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOZ).mpr hON
      have hc3 : ¬ 3 ∣ Nat.card ((img148 A Y O₁).subgroupOf Zα) := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOZ).toEquiv]
      have h0 := hNN _ hNorm hc3
      rw [Subgroup.subgroupOf_eq_bot] at h0
      have h1 := disjoint_iff.mp h0
      rwa [inf_eq_left.mpr hOZ] at h1
    rw [hO1, bot_sup_eq] at hsup
    intro v hv
    rw [hsup] at hv
    obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hv
    have hgd : g * d = d * g :=
      Subgroup.mem_centralizer_singleton_iff.mp ((deltaZero_le _ hgD).2)
    rw [hdαdef, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgd.symm
  have hnine : NoNine3 ↥Zα → Subgroup.center ↥Zα = ⊥ → (∀ v ∈ Zα, dα * v = v * dα) →
      False := by
    intro hN9 hZc hdZ
    refine false_of_noNine_of_inner (Jq := Subgroup.centralizer (Zα : Set _)) hAab hA3 hAp hF3
      hBA hB9 hdαB hdαA ?_ hdα1 hjA ?_ hAeq hAZB hdZ ?_ hAN hN9 hZc
    · exact Subgroup.mem_centralizer_iff.mpr fun v hv => (hdZ v hv).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun v hv => (hjZα v hv).symm
    · intro u hu v hv
      exact (Subgroup.mem_centralizer_iff.mp hu v hv).symm
  have h36 : 3 ^ 5 ∣ Nat.card Zα → (∀ v ∈ Zα, dα * v = v * dα) → False := by
    intro h5Z hdZ
    set Xα := img148 A Y (deltaZero A (lB A) Y) with hXα
    have hJZ1 : img148 A Y J ⊓ Zα = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxc : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZC hx.2) g g.2)
      rw [hJZ, Subgroup.mem_bot] at hxc
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxc
    have hJNZ : img148 A Y J ≤ Subgroup.normalizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro u hu
      refine Item148HJ.mem_normalizer_of_conj_mem fun v hv => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp (hZC hv) u hu
      rw [h1]
      simpa using hv
    have hcardX : Nat.card Xα = 60 * Nat.card Zα := by
      have key := Ronan148V.card_sup_mul_card_inf hJNZ
      rw [← hXeq, hJZ1, Subgroup.card_bot, mul_one, h60] at key
      exact key
    have h6X : 3 ^ 6 ∣ Nat.card Xα := by
      rw [hcardX]
      obtain ⟨k, hk⟩ := h5Z
      rw [hk]
      exact ⟨20 * k, by ring⟩
    have hXd : Xα ≤ Subgroup.centralizer {alpha148 A Y d hdA} := by
      rw [hXeq]
      refine sup_le hdJ fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hdZ x hx).symm
    have hAp' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
    have hAab' : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
      congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
    have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
    have hdec := HJRes2.deltaZero_eq_sup_of_le_centralizer hY.2 hAp' hAab' hdA hd3 hXd
    set O := pPrimeCoreOf 3 (deltaZero A (lB A) Y) with hO
    set D := deltaZero A (lB A) (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hD
    have hOY : O ≤ Y ⊔ A := ((pPrimeCoreOf_le 3 _).trans (deltaZero_le Y)).trans le_sup_left
    have hDY : D ≤ Y ⊔ A := ((deltaZero_le _).trans inf_le_left).trans le_sup_left
    have hXsup : Xα = img148 A Y O ⊔ img148 A Y D := by
      rw [hXα, hdec, img148_sup hOY hDY]
    have hDO : D ≤ Subgroup.normalizer (O : Set G) :=
      (deltaZero_mono inf_le_left).trans (le_normalizer_pPrimeCoreOf 3 _)
    have hdiv0 := card_sup_dvd_card_mul (img148_le_normalizer (A := A) (Y := Y) hDO)
    have hdiv : Nat.card ↥Xα ∣ Nat.card ↥(img148 A Y D) * Nat.card ↥(img148 A Y O) := by
      rw [hXsup, sup_comm (img148 A Y O) (img148 A Y D)]
      exact hdiv0
    have hO3 : ¬ 3 ∣ Nat.card (img148 A Y O) := fun h3 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
        (h3.trans (card_img148_dvd hOY))
    have h6D : 3 ^ 6 ∣ Nat.card D := by
      have h1 := h6X.trans hdiv
      rw [mul_comm] at h1
      exact (Ronan148V.pow_dvd_of_pow_dvd_mul_left hO3 h1).trans (card_img148_dvd hDY)
    have hDΔ : D ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
      (deltaZero_mono inf_le_right).trans (deltaZero_le_delta _)
    have hdΩ : Subgroup.zpowers d ∉ omegaA A :=
      Sec15.Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48
        (Item148HJ.sec14Std_of_isLBConfig hS hc) (Item148HJ.j2_of_isLBConfig hc) hdA hd1
        hc.2.2.2.2
    exact Ronan148V.not_pow_six_dvd_card_deltaQ hS (h143 G A c L hS) hdA hd1 hdΩ
      (h6D.trans (Subgroup.card_dvd_of_le hDΔ))
  rcases htype with hON | hcp | ha5 | h55 | h7 | hL37
  ·
    have hNN := noNormal3_congr e (noNormal3_of_isTripleCover_ON hON)
    refine h36 ?_ (hkey hNN)
    rw [← Nat.card_congr e.toEquiv]
    obtain ⟨hc3, ⟨χ⟩⟩ := hON
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _), hc3,
      Nat.card_congr χ.toEquiv, CFSG.Sporadic.ON.card_ON]
    norm_num
  ·
    have hNN := noNormal3_congr e (noNormal3_of_isCentralProductA6Covers hcp)
    refine h36 ?_ (hkey hNN)
    rw [← Nat.card_congr e.toEquiv, Ronan148V.card_of_isCentralProductA6Covers hcp]
    norm_num
  ·
    obtain ⟨U, V, hUn, hVn, hint, hUV, hU, hV⟩ := ha5
    have ha5' : IsA6CoverTimesA5 ↥Zα := by
      refine ⟨U.map e.toMonoidHom, V.map e.toMonoidHom, hUn.map _ e.surjective,
        hVn.map _ e.surjective, ?_, ?_,
        KFacts.KS14.isTripleCover_congr (U.equivMapOfInjective _ e.injective) hU, ?_⟩
      · rw [← Subgroup.map_inf_eq _ _ _ e.injective, hint, Subgroup.map_bot]
      · rw [← Subgroup.map_sup, hUV, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _
          e.surjective]
      · obtain ⟨ψ⟩ := hV
        exact ⟨(V.equivMapOfInjective _ e.injective).symm.trans ψ⟩
    exact false_of_isA6CoverTimesA5_of_le hAab hAp hF3 hBA hB9 hAeq hAZB hjZα hAN ha5'
  ·
    obtain ⟨χ⟩ := h55
    set f := (e.symm.trans χ).symm with hf
    have hNN := noNormal3_congr f noNormal3_alternating_five_sq
    have hZc : Subgroup.center ↥Zα = ⊥ := by
      have hmap := Subgroup.map_center_eq f
      rw [center_alternating_five_sq_eq_bot, Subgroup.map_bot] at hmap
      exact hmap.symm
    exact hnine (noNine_congr f noNine_alternating_five_sq) hZc (hkey hNN)
  ·
    obtain ⟨χ⟩ := h7
    set f := (e.symm.trans χ).symm with hf
    have hNN := noNormal3_congr f noNormal3_alternatingGroup_seven
    have hZc : Subgroup.center ↥Zα = ⊥ := by
      have hmap := Subgroup.map_center_eq f
      rw [center_alternatingGroup_seven_eq_bot, Subgroup.map_bot] at hmap
      exact hmap.symm
    exact hnine (noNine_congr f noNine_alternatingGroup_seven) hZc (hkey hNN)
  ·
    obtain ⟨hf7, ⟨χ⟩⟩ := hL37
    set f := (e.symm.trans χ).symm with hf
    have hNN := noNormal3_congr f noNormal3_projSL_three_seven
    have hN9 : NoNine3 ↥Zα := noNine_congr f Sec4.Ronan148V.noNine_projSL_three_seven
    have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
    have hZs : IsSimpleGroup ↥Zα := MulEquiv.isSimpleGroup f.symm
    have hZc : Subgroup.center ↥Zα = ⊥ := center_eq_bot_of_isSimpleGroup_of_nine_dvd hN9.1
    exact hnine hN9 hZc (hkey hNN)

@[expose] def Step148HJA5J2Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → ∀ hAJ : A ≤ Subgroup.normalizer (J : Set G),
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)) →
        b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        img148 A Y (deltaZero A (lB A) Y) =
          img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) →
        img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≠ ⊥ →
        Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
          CFSG.Blueprint.NativeSporadic.J2) →
        (omegaA A).ncard = 6

theorem step148HJA5Cent2_of_j2Six
    (h134 : Item134) (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14)
    (hR : Step148HJA5J2Six) : Step148HJA5Cent2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne
  exact ⟨not_case148Three_of_a5 h134 h48 h143 hS hY hB hc hJ hAJ hYdJ hYdt hdc heq hJ5 hbc hXeq,
    hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd
      hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXeq hZne⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
