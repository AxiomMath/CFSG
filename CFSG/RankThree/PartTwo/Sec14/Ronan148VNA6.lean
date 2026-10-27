module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJTypes
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VON
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VL37
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_centralNoncentral_of_inner {Q : Type} [Group Q] [Finite Q]
    {Aq Bq Jq Z : Subgroup Q} {dα j : Q} (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x)
    (hA3 : ∀ a ∈ Aq, a ^ 3 = 1) (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hBA : Bq ≤ Aq) (hB9 : Nat.card Bq = 9) (hdB : dα ∈ Bq) (hdA : dα ∈ Aq) (hd1 : dα ≠ 1)
    (hjJ : j ∈ Jq) (hAeq : Bq ⊔ Subgroup.zpowers j = Aq)
    (hAZB : Aq ⊓ Z ≤ Bq) (hdZ : ∀ v ∈ Z, dα * v = v * dα)
    (hJZ : ∀ u ∈ Jq, ∀ v ∈ Z, u * v = v * u)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Q)) (hZ : CentralNoncentral3 ↥Z) : dα ∈ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hdZα
  obtain ⟨h3, x, hx3, hxZ⟩ := hZ
  have h3c : 3 ∣ Nat.card ((Subgroup.center ↥Z).map Z.subtype) := by
    rwa [Subgroup.card_map_of_injective Z.subtype_injective]
  obtain ⟨k, hkZZ, hk1, hk3, hkA⟩ :=
    exists_pow_eq_one_mem_centralizer hAp (le_normalizer_map_center hAN) h3c
  have hkAq : k ∈ Aq := hF3 k hkA hk3
  have hkZ : k ∈ Z := Subgroup.map_subtype_le _ hkZZ
  have hkc : ∀ y ∈ Z, k * y = y * k := by
    obtain ⟨k', hk', rfl⟩ := hkZZ
    intro y hy
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hk') ⟨y, hy⟩)).symm
  have hkB : k ∈ Bq := hAZB ⟨hkAq, hkZ⟩
  have hkd : k ∉ Subgroup.zpowers dα := by
    intro hkd
    have hd3 : Nat.card (Subgroup.zpowers dα) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hA3 _ hdA) hd1
    have hkk : Subgroup.zpowers k = Subgroup.zpowers dα := zpowers_eq_of_card_three hd3 hkd hk1
    exact hdZα (Subgroup.zpowers_le.mpr hkZ (hkk ▸ Subgroup.mem_zpowers dα))
  have h9' := card_zpowers_sup_zpowers_eq_nine (hAab dα hdA k hkAq) (hA3 _ hdA) hd1 hk3 hkd
  have hBeq : Subgroup.zpowers dα ⊔ Subgroup.zpowers k = Bq :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hdB) (Subgroup.zpowers_le.mpr hkB)) (by rw [hB9, h9'])
  have hAZ : Aq ≤ Subgroup.centralizer (Z : Set Q) := by
    rw [← hAeq, ← hBeq]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hdZ y hy).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hkc y hy).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hJZ j hjJ y hy).symm
  have hx3' : (x : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  have hxA : (x : Q) ∈ Aq := by
    refine hF3 _ ?_ hx3'
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAZ ha) x x.2).symm
  apply hxZ
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hAZ hxA) g g.2)

section Certificates


@[expose] def Step148HJNormalInnerA6Cent2 : Prop :=
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
        Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
        (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
          Case148Three A (lB A) (centPre148 A Y J) ∧
            (Sec4.IsTripleCover
                  ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J)))
                  CFSG.Blueprint.NativeSporadic.ON ∨
                IsCentralProductA6Covers
                  ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) ∨
                IsA6CoverTimesA5
                  ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))))) →
        ∀ hdA : d ∈ A,
          alpha148 A Y d hdA ∉ img148 A Y (deltaZero A (lB A) (centPre148 A Y J))

theorem step148HJNormalInnerA6Cent_of_cent2
    (hON : ∀ (W : Type) [Group W], Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON →
      ∃ x : W, x ^ 3 = 1 ∧ x ∉ Subgroup.center W)
    (hL37 : ∀ _ : Fact (Nat.Prime 7),
      NoNine3 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))
    (hL37c : ∀ _ : Fact (Nat.Prime 7),
      Subgroup.center (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = ⊥)
    (hR : Step148HJNormalInnerA6Cent2) : Step148HJNormalInnerA6Cent := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hYB6 hdYB hbc hXJ h3'
  let := ker148_normal hY.2
  have hres := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
    hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hYB6 hdYB hbc hXJ
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hJp : Group.IsPerfect ↥(img148 A Y J) := by
    have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
    exact isPerfect_img148 hJM
  have hJc : IsComponent (img148 A Y J) := isComponent_img148_of_three_dvd hY.2 hJ h3J
  have hJcard : Nat.card (img148 A Y J) = 1080 := HJRes2.card_of_isTripleCover_six hJ6
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [hJcard]; norm_num
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAp0 : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
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
  obtain ⟨hBA, -, hmax⟩ := img148_hyperplane_max (Y := Y) hA hB
  obtain ⟨j, hjA, hjJ, hjnc⟩ := exists_noncentral_mem_of_tripleCover hJ6 hJp hA3 hF3 hAJα hBJ hBA
    hmax
  have hjB : j ∉ img148 A Y B := fun hjB' => by
    obtain ⟨y, hy, hjy⟩ := hjnc
    exact hjy (Subgroup.mem_centralizer_iff.mp (hBJ hjB') y hy).symm
  have hAeq : img148 A Y B ⊔ Subgroup.zpowers j = img148 A Y A := by
    rcases hmax _ le_sup_left (sup_le hBA (Subgroup.zpowers_le.mpr hjA)) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers j ≤ _) (Subgroup.mem_zpowers j)) hjB
    · exact h
  have hCB : img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = img148 A Y B := by
    rcases hmax _ (le_inf hBA hBJ) inf_le_left with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hjy⟩ := hjnc
      have hjC : j ∈ img148 A Y A ⊓
          Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rw [h]; exact hjA
      exact hjy (Subgroup.mem_centralizer_iff.mp hjC.2 y hy).symm
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZC : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hUV : ∀ u ∈ img148 A Y J, ∀ v ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)),
      u * v = v * u := fun u hu v hv => (Subgroup.mem_centralizer_iff.mp (hZC hv) u hu)
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYBJ hdYB, rfl⟩
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hd1
    exact alpha148_injective hA.1.2 hdA (Subgroup.one_mem A) (by rw [← hdαdef, h]; rfl)
  have hdZ : ∀ v ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)), dα * v = v * dα :=
    fun v hv => hUV dα hdJα v hv
  have hB9 : Nat.card (img148 A Y B) = 9 := by
    rw [card_img148_of_le hA.1.2 hB.1]
    have h2 := hB.2
    rw [hA.2] at h2
    omega
  have hdBα : dα ∈ img148 A Y B :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
  have hAZB : img148 A Y A ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      img148 A Y B := fun x hx => hCB ▸ ⟨hx.1, hZC hx.2⟩
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  intro htype3
  let := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ)
  have hcn : (Sec4.IsTripleCover
        ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J)))
        CFSG.Blueprint.NativeSporadic.ON ∨
      IsCentralProductA6Covers
        ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) ∨
      IsA6CoverTimesA5
        ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J)))) →
      CentralNoncentral3
        ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) → False :=
    fun hT hZ => hres ⟨h3', hT⟩ hdA (mem_of_centralNoncentral_of_inner hAab hA3 hAp0 hF3
      hBA hB9 hdBα hdαA hdα1 hjJ hAeq hAZB hdZ hUV hAN (centralNoncentral_congr e hZ))
  rcases htype3 with hON' | hcp | ha5 | hL37'
  · obtain ⟨x, hx3, hxZ⟩ := hON _ hON'
    exact hcn (Or.inl hON') ⟨by rw [hON'.1], x, hx3, hxZ⟩
  · exact hcn (Or.inr (Or.inl hcp)) (IsCentralProductA6Covers.central_noncentral hcp)
  · exact hcn (Or.inr (Or.inr ha5)) (IsA6CoverTimesA5.central_noncentral ha5)
  ·
    obtain ⟨hf7, ⟨χ⟩⟩ := hL37'
    have hZc : Subgroup.center ↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) = ⊥ := by
      have hmap := Subgroup.map_center_eq (e.symm.trans χ)
      rw [hL37c hf7] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ (e.symm.trans χ).injective).mp hmap
    exact false_of_noNine_of_inner hAab hA3 hAp0 hF3 hBA hB9 hdBα hdαA hdJα hdα1 hjA hjJ hAeq
      hAZB hdZ hUV hAN (noNine_congr (e.symm.trans χ).symm (hL37 hf7)) hZc

theorem step148HJNormalInnerA6Cent_of_cent2'
    (hR : Step148HJNormalInnerA6Cent2) :
    Step148HJNormalInnerA6Cent :=
  step148HJNormalInnerA6Cent_of_cent2
    (fun _ _ h => Sec4.Ronan148V.exists_noncentral_of_isTripleCover_ON h)
    (fun _ => Sec4.Ronan148V.noNine_projSL_three_seven)
    (fun _ => Sec4.Ronan148V.center_projSL_three_seven_eq_bot) hR

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
