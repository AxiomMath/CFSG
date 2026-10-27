module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJ
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJSix
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJNine
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import Certificates.Data.A5

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem center_alternatingGroup_five_eq_bot :
    Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 5)))
    with h | h
  · exact h
  · exfalso
    have hall : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by
      intro a b
      have : a ∈ Subgroup.center (alternatingGroup (Fin 5)) := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp this) b).symm
    have hne : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by decide
    obtain ⟨a, b, hab⟩ := hne
    exact hab (hall a b)

theorem center_alternating_five_sq_eq_bot :
    Subgroup.center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = ⊥ := by
  rw [Subgroup.center_prod, center_alternatingGroup_five_eq_bot, Subgroup.bot_prod_bot]

theorem center_alternatingGroup_seven_eq_bot :
    Subgroup.center (alternatingGroup (Fin 7)) = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7)))
    with h | h
  · exact h
  · exfalso
    set a : alternatingGroup (Fin 7) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    set b : alternatingGroup (Fin 7) :=
      ⟨Equiv.swap 1 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    have hab : a * b ≠ b * a := fun h' => by
      have h'' := congrArg Subtype.val h'
      revert h''
      decide
    have : a ∈ Subgroup.center (alternatingGroup (Fin 7)) := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this) b).symm

theorem exists_noncentral_mem_of_tripleCover {Q : Type} [Group Q] [Finite Q]
    {Aq Bq Jq : Subgroup Q} (hJ6 : Sec4.IsTripleCover ↥Jq (alternatingGroup (Fin 6)))
    (hJp : Group.IsPerfect ↥Jq) (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hAJ : Aq ≤ Subgroup.normalizer (Jq : Set Q))
    (hBJ : Bq ≤ Subgroup.centralizer (Jq : Set Q)) (hBA : Bq ≤ Aq)
    (hBmax : ∀ H : Subgroup Q, Bq ≤ H → H ≤ Aq → H = Bq ∨ H = Aq) :
    ∃ j ∈ Aq, j ∈ Jq ∧ ∃ y ∈ Jq, j * y ≠ y * j := by
  have hex : ∃ e ∈ Aq, ∃ y ∈ Jq, e * y ≠ y * e := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hJ6
    have hx3' : (x : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    have hxA : (x : Q) ∈ Aq := by
      refine hF3 _ ?_ hx3'
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcon a ha x x.2
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon x hxA g g.2).symm
  obtain ⟨e, heA, y0, hy0J, hey0⟩ := hex
  set σ := Jq.normalizerMonoidHom ⟨e, hAJ heA⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have h3 : (⟨e, hAJ heA⟩ : Subgroup.normalizer (Jq : Set Q)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA3 e heA)
    rw [h3, map_one]
  haveI := hJp
  obtain ⟨y, hy⟩ := Sec19.Item19Res4Proof.exists_eq_conj_of_isTripleA6 hJ6 σ hσ3
  have hact : ∀ x ∈ Jq, e * x * e⁻¹ = (y : Q) * x * (y : Q)⁻¹ := by
    intro x hx
    have h := congrArg (fun τ : MulAut ↥Jq => ((τ ⟨x, hx⟩ : ↥Jq) : Q)) hy
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hye : (y : Q) * e = e * y := by
    have h := hact y y.2
    have : e * (y : Q) * e⁻¹ = y := by rw [h]; group
    calc (y : Q) * e = e * (y : Q) * e⁻¹ * e := by rw [this]
      _ = e * y := by group
  have heB : e ∉ Bq := fun heB => hey0 (Subgroup.mem_centralizer_iff.mp (hBJ heB) y0 hy0J).symm
  have hAeq : Bq ⊔ Subgroup.zpowers e = Aq := by
    rcases hBmax _ le_sup_left (sup_le hBA (Subgroup.zpowers_le.mpr heA)) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers e ≤ _) (Subgroup.mem_zpowers e)) heB
    · exact h
  have hyA : (y : Q) ∈ Subgroup.centralizer (Aq : Set Q) := by
    have hle : Aq ≤ Subgroup.centralizer ({(y : Q)} : Set Q) := by
      rw [← hAeq]
      refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hBJ hb) y y.2).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hye.symm
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hy3 : y ^ 3 = 1 := by
    apply Sec19.Item19Res4Proof.pow_three_eq_one_of_isTripleA6 hJ6
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, ← hy, hσ3]
    have h2 := congrArg (fun τ : MulAut ↥Jq => τ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h2]
      _ = y ^ 3 * g := by group
  have hy3' : (y : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  refine ⟨y, hF3 _ hyA hy3', y.2, y0, hy0J, fun h => hey0 ?_⟩
  have h1 := hact y0 hy0J
  have h2 : (y : Q) * y0 * (y : Q)⁻¹ = y0 := by rw [h]; group
  calc e * y0 = e * y0 * e⁻¹ * e := by group
    _ = y0 * e := by rw [h1, h2]

theorem false_of_noNine_of_inner {Q : Type} [Group Q] [Finite Q] {Aq Bq Jq Z : Subgroup Q}
    {dα j : Q} (hAab : ∀ x ∈ Aq, ∀ y ∈ Aq, x * y = y * x) (hA3 : ∀ a ∈ Aq, a ^ 3 = 1)
    (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Q, w ∈ Subgroup.centralizer (Aq : Set Q) → w ^ 3 = 1 → w ∈ Aq)
    (hBA : Bq ≤ Aq) (hB9 : Nat.card Bq = 9) (hdB : dα ∈ Bq) (hdA : dα ∈ Aq) (hdJ : dα ∈ Jq)
    (hd1 : dα ≠ 1) (hjA : j ∈ Aq) (hjJ : j ∈ Jq) (hAeq : Bq ⊔ Subgroup.zpowers j = Aq)
    (hAZB : Aq ⊓ Z ≤ Bq) (hdZ : ∀ v ∈ Z, dα * v = v * dα)
    (hJZ : ∀ u ∈ Jq, ∀ v ∈ Z, u * v = v * u)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Q)) (hN9 : NoNine3 ↥Z)
    (hZc : Subgroup.center ↥Z = ⊥) : False := by
  obtain ⟨h9, hexp⟩ := noNine_subgroup hN9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdZα : dα ∉ Z := by
    intro hdz
    have : (⟨dα, hdz⟩ : ↥Z) ∈ Subgroup.center ↥Z := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hdZ g g.2).symm
    rw [hZc, Subgroup.mem_bot] at this
    exact hd1 (congrArg Subtype.val this)
  have hd3 : Nat.card (Subgroup.zpowers dα) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hA3 _ hdA) hd1
  obtain ⟨C, hC3, hCB, hdC, hAZC⟩ : ∃ C : Subgroup Q, Nat.card C = 3 ∧ C ≤ Bq ∧ dα ∉ C ∧
      Aq ⊓ Z ≤ C := by
    have hdiv : Nat.card ↥(Aq ⊓ Z) ∣ 3 ^ 2 := by
      have := Subgroup.card_dvd_of_le hAZB
      rw [hB9] at this
      simpa using this
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    ·
      rw [pow_zero] at hci
      have hnot : ¬ Bq ≤ Subgroup.zpowers dα := fun hle => by
        have := Subgroup.card_le_of_le hle
        rw [hB9, hd3] at this
        omega
      obtain ⟨b0, hb0B, hb0d⟩ := Set.not_subset.mp hnot
      have hb01 : b0 ≠ 1 := fun h1 => hb0d (h1 ▸ Subgroup.one_mem _)
      have hb03 : Nat.card (Subgroup.zpowers b0) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hA3 _ (hBA hb0B)) hb01
      refine ⟨Subgroup.zpowers b0, hb03, Subgroup.zpowers_le.mpr hb0B, fun hdb => ?_, ?_⟩
      · have heq := zpowers_eq_of_card_three hb03 hdb hd1
        exact hb0d (heq ▸ Subgroup.mem_zpowers b0)
      · rw [Subgroup.eq_bot_of_card_eq (Aq ⊓ Z) hci]
        exact bot_le
    · rw [pow_one] at hci
      exact ⟨_, hci, hAZB, fun hdz => hdZα hdz.2, le_rfl⟩
    · exfalso
      have heqB : Aq ⊓ Z = Bq :=
        Subgroup.eq_of_le_of_card_ge hAZB (by rw [hci, hB9]; norm_num)
      have hdAZ : dα ∈ Aq ⊓ Z := by rw [heqB]; exact hdB
      exact hdZα hdAZ.2
  have hCd : C ⊓ Subgroup.zpowers dα = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    rw [Subgroup.mem_bot] at hx1
    apply hdC
    have heq := zpowers_eq_of_card_three hd3 hx.2 hx1
    have : dα ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers dα
    exact Subgroup.zpowers_le.mpr hx.1 this
  have hCdB : C ⊔ Subgroup.zpowers dα = Bq := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hCB (Subgroup.zpowers_le.mpr hdB)) ?_
    rw [card_sup_eq_mul_of_commute (fun u hu v hv => hAab u (hBA (hCB hu)) v
      (hBA (Subgroup.zpowers_le.mpr hdB hv))) hCd, hC3, hd3, hB9]
  have hCE : C ⊔ (Aq ⊓ Jq) = Aq := by
    have h1 : Subgroup.zpowers dα ≤ Aq ⊓ Jq :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdA, hdJ⟩)
    have h2 : Subgroup.zpowers j ≤ Aq ⊓ Jq :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hjA, hjJ⟩)
    have hBle : Bq ≤ C ⊔ (Aq ⊓ Jq) := by
      rw [← hCdB]
      exact sup_le le_sup_left (h1.trans le_sup_right)
    refine le_antisymm (sup_le (hCB.trans hBA) inf_le_left) ?_
    calc Aq = Bq ⊔ Subgroup.zpowers j := hAeq.symm
      _ ≤ C ⊔ (Aq ⊓ Jq) := sup_le hBle (h2.trans le_sup_right)
  have hEZ : Aq ⊓ Jq ≤ Subgroup.centralizer (Z : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hJZ x hx.2 z hz).symm
  exact false_of_exp_three_of_le hAp hF3 hC3 hCE hEZ hAZC hAN h9 hexp

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem isComponent_img148_of_three_dvd (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (h3 : 3 ∣ Nat.card J) :
    IsComponent (img148 A Y J) := by
  obtain ⟨hJY, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  obtain ⟨hq, -⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3
  have hsub : ((img148 A Y J).subgroupOf (img148 A Y Y)).IsSubnormal :=
    Main148.isSubnormal_img148 hJY le_sup_left hJ'.2.1
  have hYsn : (img148 A Y Y).IsSubnormal := (Item148Res5.img148_normal hAY).isSubnormal
  exact ⟨hq, Subgroup.IsSubnormal.trans (img148_mono hJY) hsub hYsn⟩

end Quot

section Certificates


@[expose] def Step148HJNormalInnerA6Cent : Prop :=
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
          Case148Three A (lB A) (centPre148 A Y J) →
            ¬ (Sec4.IsTripleCover
                  ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J)))
                  CFSG.Blueprint.NativeSporadic.ON ∨
                IsCentralProductA6Covers
                  ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) ∨
                IsA6CoverTimesA5
                  ↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) ∨
                (∃ _ : Fact (Nat.Prime 7), Nonempty
                  (↥(img148 A (centPre148 A Y J) (deltaZero A (lB A) (centPre148 A Y J))) ≃*
                    CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))))

set_option maxHeartbeats 2000000 in
theorem step148HJNormalInnerA6_of_cent
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Step148HJNormalInnerA6Cent) :
    Step148HJNormalInnerA6 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hYB6 hdYB hbc hXJ
  let := ker148_normal hY.2
  have hres1 := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
    hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hYB6 hdYB hbc hXJ
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
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
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hjB : j ∉ img148 A Y B := fun hjB' => by
    obtain ⟨y, hy, hjy⟩ := hjnc
    exact hjy (Subgroup.mem_centralizer_iff.mp (hBJ hjB') y hy).symm
  have hAeq : img148 A Y B ⊔ Subgroup.zpowers j = img148 A Y A := by
    rcases hmax _ le_sup_left (sup_le hBA (Subgroup.zpowers_le.mpr hjA)) with h | h
    · exact absurd (h ▸ (le_sup_right : Subgroup.zpowers j ≤ _) (Subgroup.mem_zpowers j)) hjB
    · exact h
  have hCD : img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
      img148 A Y A ⊓ img148 A Y J = img148 A Y A := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    calc img148 A Y A = img148 A Y B ⊔ Subgroup.zpowers j := hAeq.symm
      _ ≤ _ := sup_le_sup (le_inf hBA hBJ)
          (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hjA, hjJ⟩))
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
  have hXle := img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hjJ hjA hjnc hCD
  have h3YB : 3 ∣ Nat.card YB := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
      HJRes2.card_of_isTripleCover_six hYB6]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hYBα : img148 A Y YB = img148 A Y J := by
    refine Subgroup.eq_of_le_of_card_ge (heq ▸ img148_mono hYBYd) ?_
    have h1 := card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      h3YB
    rw [HJRes2.card_of_isTripleCover_six hYB6] at h1
    rw [hJcard]
    exact h1
  have hJb : img148 A Y J ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (hYBC.trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)))
    exact Set.singleton_subset_iff.mpr hbB
  have hAV : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ img148 A Y J →
      j ∈ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro V hV hjV
    rw [← hAeq]
    refine sup_le (fun x hx => Subgroup.centralizer_le_normalizer _ ?_)
      (Subgroup.zpowers_le.mpr hjV)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hBJ hx) w (hV hw)
  have hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) :=
    le_of_forall_commutator_le_tripleCover hJ6 hJp hjJ hj3 hjnc fun V hV hV3 hjV =>
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hjA)).trans
        (commutator_le_img148_deltaZero_of_point h142 hS hY hc.2.1 V (hV.trans hJb) hV3
          (hAV V hV hjV))
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hXeq : img148 A Y (deltaZero A (lB A) Y) =
      img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :=
    le_antisymm hXle (sup_le hJX (hZle.trans inf_le_left))
  have hZC : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hZne : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≠ ⊥ := fun h0 =>
    hXJ (by rw [hXeq, h0, sup_bot_eq])
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
  have hXd : img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {dα} := by
    rw [hXeq]
    refine sup_le hdJ fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hdZ x hx).symm
  have hJZd : img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.zpowers dα := by
    intro x hx
    set d' : ↥(img148 A Y J) := ⟨dα, hdJα⟩ with hd'
    have hd'Z : d' ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hdJ g.2))
    have hd'1 : d' ≠ 1 := fun h => hdα1 (congrArg Subtype.val h)
    have hcen : Subgroup.zpowers d' = Subgroup.center ↥(img148 A Y J) :=
      zpowers_eq_of_card_three hJ6.1 hd'Z hd'1
    have hxZ : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hUV g g.2 x hx.2)
    rw [← hcen] at hxZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa [hd'] using congrArg Subtype.val hk⟩
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  set Xα := img148 A Y (deltaZero A (lB A) Y) with hXα
  have hZX : Zα ≤ Xα := hXeq ▸ le_sup_right
  have hJX' : img148 A Y J ≤ Xα := hXeq ▸ le_sup_left
  have hXN : ∀ {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}, (T = Zα ∨ T = img148 A Y J) →
      Xα ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro T hT
    rw [hXeq]
    rcases hT with rfl | rfl
    · refine sup_le (fun u hu => Subgroup.centralizer_le_normalizer _ ?_) Subgroup.le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hUV u hu v hv).symm
    · refine sup_le Subgroup.le_normalizer (fun v hv => Subgroup.centralizer_le_normalizer _ ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hUV u hu v hv
  have hcase3 : ∀ htype : Sec4.IsTripleCover ↥Xα CFSG.Blueprint.NativeSporadic.ON ∨
      IsCentralProductA6Covers ↥Xα ∨ IsA6CoverTimesA5 ↥Xα ∨
      Nonempty (↥Xα ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (↥Xα ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Xα ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))),
      Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y :=
    fun htype => Or.inr (Or.inl (HJRes2.case148Three_of_le_centralizer hS hY hc.2.1 hLb
      (Item148HJ.j2_of_isLBConfig hc) hdA hd1 hc.2.2.2.2 hXd htype))
  have hHJexcl : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ Zα →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      (↥V ≃* CFSG.Blueprint.NativeSporadic.J2) → False := by
    intro V hVZ hAV ψ
    have hVc : Subgroup.center ↥V = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨ψ⟩
    have hdV : dα ∉ V := by
      intro hdv
      have : (⟨dα, hdv⟩ : ↥V) ∈ Subgroup.center ↥V := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hdZ g (hVZ g.2)).symm
      rw [hVc, Subgroup.mem_bot] at this
      exact hdα1 (congrArg Subtype.val this)
    have hAVB : img148 A Y A ⊓ V ≤ img148 A Y B := fun x hx =>
      hCB ▸ ⟨hx.1, hZC (hVZ hx.2)⟩
    have hB9 : Nat.card (img148 A Y B) = 9 := by
      rw [card_img148_of_le hA.1.2 hB.1]
      have h2 := hB.2
      rw [hA.2] at h2
      omega
    obtain ⟨C, hC3, hAVC⟩ : ∃ C : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), Nat.card C = 3 ∧
        img148 A Y A ⊓ V ≤ C := by
      rcases card_le_of_le_isE27 hAE (inf_le_left : img148 A Y A ⊓ V ≤ img148 A Y A) with
        h | h | h | h
      · refine ⟨Subgroup.zpowers dα, ?_, ?_⟩
        · rw [Nat.card_zpowers]
          have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          exact orderOf_eq_prime (hA3 _ hdαA) hdα1
        · rw [Subgroup.eq_bot_of_card_eq _ h]
          exact bot_le
      · exact ⟨_, h, le_rfl⟩
      · exfalso
        have heqB : img148 A Y A ⊓ V = img148 A Y B :=
          Subgroup.eq_of_le_of_card_ge hAVB (by rw [h, hB9])
        have hdB' : dα ∈ img148 A Y B :=
          mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
        exact hdV (heqB ▸ hdB' : dα ∈ img148 A Y A ⊓ V).2
      · exfalso
        have := Subgroup.card_le_of_le hAVB
        rw [h, hB9] at this
        omega
    exact false_of_j2_of_le hAab hA3 hF3 hC3 hAVC hAV ψ
  have hNineExcl : NoNine3 ↥Zα → Subgroup.center ↥Zα = ⊥ → False := fun hN9 hZc =>
    false_of_noNine_of_inner hAab hA3 hAp0 hF3 hBA
      (by rw [card_img148_of_le hA.1.2 hB.1]; have h2 := hB.2; rw [hA.2] at h2; omega)
      (mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩) hdαA hdJα hdα1 hjA hjJ
      hAeq (fun x hx => hCB ▸ ⟨hx.1, hZC hx.2⟩) hdZ hUV hAN hN9 hZc
  rcases centPre148_type_of_hj h134 h48 hS hY ih hB hc hJY hAJ hJc h3Jα with
    h1 | hZ2 | hZ6 | hZ5 | h36
  · exact absurd h1 hZne
  ·
    obtain ⟨ψ⟩ := hZ2
    exact (hHJexcl _ le_rfl hAN ψ).elim
  ·
    have hdz : dα ∈ Zα := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hAp : IsPGroup 3 ↥(img148 A Y A) :=
        IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
      have h3c : 3 ∣ Nat.card ((Subgroup.center ↥Zα).map Zα.subtype) := by
        rw [Subgroup.card_map_of_injective Zα.subtype_injective, hZ6.1]
      obtain ⟨k, hkZZ, hk1, hk3, hkA⟩ :=
        exists_pow_eq_one_mem_centralizer hAp (le_normalizer_map_center hAN) h3c
      have hkAq : k ∈ img148 A Y A := hF3 k hkA hk3
      have hkZ : k ∈ Zα := Subgroup.map_subtype_le _ hkZZ
      have hkc : ∀ y ∈ Zα, k * y = y * k := by
        obtain ⟨k', hk', rfl⟩ := hkZZ
        intro y hy
        exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hk') ⟨y, hy⟩)).symm
      have hkB : k ∈ img148 A Y B := by
        rw [← hCB]
        exact ⟨hkAq, hZC hkZ⟩
      have hd3 : Nat.card (Subgroup.zpowers dα) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hA3 _ hdαA) hdα1
      by_cases hkd : k ∈ Subgroup.zpowers dα
      · have hkk : Subgroup.zpowers k = Subgroup.zpowers dα :=
          zpowers_eq_of_card_three hd3 hkd hk1
        have hdk : dα ∈ Subgroup.zpowers k := hkk ▸ Subgroup.mem_zpowers dα
        exact Subgroup.zpowers_le.mpr hkZ hdk
      · exfalso
        have hB9 : Nat.card (img148 A Y B) = 9 := by
          rw [card_img148_of_le hA.1.2 hB.1]
          have h2 := hB.2
          rw [hA.2] at h2
          omega
        have hdBα : dα ∈ img148 A Y B :=
          mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdB, rfl⟩
        have h9' := card_zpowers_sup_zpowers_eq_nine (hAab dα hdαA k hkAq) (hA3 _ hdαA) hdα1
          hk3 hkd
        have hBeq : Subgroup.zpowers dα ⊔ Subgroup.zpowers k = img148 A Y B :=
          Subgroup.eq_of_le_of_card_ge
            (sup_le (Subgroup.zpowers_le.mpr hdBα) (Subgroup.zpowers_le.mpr hkB))
            (by rw [hB9, h9'])
        have hAZ : img148 A Y A ≤ Subgroup.centralizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
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
            exact (hUV j hjJ y hy).symm
        obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hZ6
        have hx3' : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by
          simpa using congrArg Subtype.val hx3
        have hxA : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y A := by
          refine hF3 _ ?_ hx3'
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact (Subgroup.mem_centralizer_iff.mp (hAZ ha) x x.2).symm
        apply hxZ
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hAZ hxA) g g.2)
    refine hcase3 (Or.inr (Or.inl ?_))
    refine ⟨(img148 A Y J).subgroupOf Xα, Zα.subgroupOf Xα,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJX').mpr (hXN (Or.inr rfl)),
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr (hXN (Or.inl rfl)), ?_, ?_, ?_,
      KFacts.KS14.isTripleCover_congr (Subgroup.subgroupOfEquivOfLe hJX').symm hJ6,
      KFacts.KS14.isTripleCover_congr (Subgroup.subgroupOfEquivOfLe hZX).symm hZ6⟩
    · rw [← Subgroup.subgroupOf_sup hJX' hZX]
      exact Subgroup.subgroupOf_eq_top.mpr hXeq.le
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (hUV u (Subgroup.mem_subgroupOf.mp hu) v (Subgroup.mem_subgroupOf.mp hv)).symm
    · have hinf : img148 A Y J ⊓ Zα = Subgroup.zpowers dα :=
        le_antisymm hJZd (Subgroup.zpowers_le.mpr ⟨hdJα, hdz⟩)
      have h1 : Nat.card ↥((img148 A Y J).subgroupOf Xα ⊓ Zα.subgroupOf Xα) =
          Nat.card ↥(img148 A Y J ⊓ Zα) := by
        have hsub : (img148 A Y J).subgroupOf Xα ⊓ Zα.subgroupOf Xα =
            (img148 A Y J ⊓ Zα).subgroupOf Xα := by
          ext x
          simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
        rw [hsub]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hJX')).toEquiv
      rw [h1, hinf, Nat.card_zpowers]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (hA3 _ hdαA) hdα1
  ·
    obtain ⟨φZ⟩ := hZ5
    have hZc : Subgroup.center ↥Zα = ⊥ := by
      have hmap := Subgroup.map_center_eq φZ
      rw [center_alternatingGroup_five_eq_bot] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ φZ.injective).mp hmap
    have hint : img148 A Y J ⊓ Zα = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : ↥Zα) ∈ Subgroup.center ↥Zα := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hUV x hx.1 g g.2).symm
      rw [hZc, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    refine hcase3 (Or.inr (Or.inr (Or.inl ?_)))
    refine ⟨(img148 A Y J).subgroupOf Xα, Zα.subgroupOf Xα,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJX').mpr (hXN (Or.inr rfl)),
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr (hXN (Or.inl rfl)), ?_, ?_,
      KFacts.KS14.isTripleCover_congr (Subgroup.subgroupOfEquivOfLe hJX').symm hJ6,
      ⟨(Subgroup.subgroupOfEquivOfLe hZX).trans φZ⟩⟩
    · rw [eq_bot_iff]
      intro x hx
      have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J ⊓ Zα :=
        ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
      rw [hint, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
    · rw [← Subgroup.subgroupOf_sup hJX' hZX]
      exact Subgroup.subgroupOf_eq_top.mpr hXeq.le
  · obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
    rcases h36 with h3' | h6'
    ·
      exfalso
      have hno := hres1 h3'
      obtain ⟨-, -, -, -, -, -, -, -, -, -, htype3⟩ := h3'
      rcases htype3 with hON | hcp | ha5 | h55 | h7 | hL37
      · exact hno (Or.inl hON)
      · exact hno (Or.inr (Or.inl hcp))
      · exact hno (Or.inr (Or.inr (Or.inl ha5)))
      · obtain ⟨χ⟩ := h55
        have hZc : Subgroup.center ↥Zα = ⊥ := by
          have hmap := Subgroup.map_center_eq (e.symm.trans χ)
          rw [center_alternating_five_sq_eq_bot] at hmap
          exact (Subgroup.map_eq_bot_iff_of_injective _ (e.symm.trans χ).injective).mp hmap
        exact hNineExcl (noNine_congr (e.symm.trans χ).symm noNine_alternating_five_sq) hZc
      · obtain ⟨χ⟩ := h7
        have hZc : Subgroup.center ↥Zα = ⊥ := by
          have hmap := Subgroup.map_center_eq (e.symm.trans χ)
          rw [center_alternatingGroup_seven_eq_bot] at hmap
          exact (Subgroup.map_eq_bot_iff_of_injective _ (e.symm.trans χ).injective).mp hmap
        exact hNineExcl (noNine_congr (e.symm.trans χ).symm noNine_alternatingGroup_seven) hZc
      · exact hno (Or.inr (Or.inr (Or.inr hL37)))
    ·
      exfalso
      obtain ⟨⟨χ⟩, -, -⟩ := h6'
      obtain ⟨V, hVZ, ⟨ψV⟩, hVN⟩ := exists_j2_factor_le_normalizer (e.symm.trans χ)
      exact hHJexcl V hVZ (fun a ha => hVN a (hAN ha)) ψV

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
