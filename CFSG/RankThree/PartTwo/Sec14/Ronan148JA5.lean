module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JGen
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JA5Facts
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JFix
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JContrib
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JProd
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JTC
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Gen

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_le_img148_deltaZero_of_a5 (h142 : Concl142S14) {L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) (hY : Y ∈ scriptY A) {b : G} (hbΩ : Subgroup.zpowers b ∈ omegaA A)
    {J B : Subgroup G} (φ : ↥(img148 A Y J) ≃* alternatingGroup (Fin 5))
    (hJb : img148 A Y J ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)))
    (hBJ : img148 A Y B ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    {j : ↥(Y ⊔ A) ⧸ ker148 A Y} (hjJ : j ∈ img148 A Y J) (hj1 : j ≠ 1) (hj3 : j ^ 3 = 1)
    (hAeq : img148 A Y B ⊔ Subgroup.zpowers j = img148 A Y A) :
    img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
  set Jα := img148 A Y J with hJα
  set H : Subgroup ↥Jα := (img148 A Y (deltaZero A (lB A) Y)).subgroupOf Jα with hH
  set j' : ↥Jα := ⟨j, hjJ⟩ with hj'
  have hj'1 : j' ≠ 1 := fun h => hj1 (congrArg Subtype.val h)
  have hj'3 : j' ^ 3 = 1 := Subtype.ext (by simp [hj', hj3])
  have htop : H = ⊤ := by
    refine eq_top_of_forall_commutator_le_a5 φ hj'1 hj'3 fun V hV3 hjV => ?_
    set W : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) := V.map Jα.subtype with hW
    have hWJ : W ≤ Jα := Subgroup.map_subtype_le V
    have hW3 : ¬ 3 ∣ Nat.card W := by
      rwa [hW, Subgroup.card_map_of_injective Jα.subtype_injective]
    have hjW : j ∈ Subgroup.normalizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨j' * v * j'⁻¹, (Subgroup.mem_normalizer_iff.mp hjV v).mp hv, rfl⟩
      · rintro ⟨v, hv, hveq⟩
        have hxJ : x ∈ Jα := by
          have h1 : j⁻¹ * (j * x * j⁻¹) * j ∈ Jα :=
            Jα.mul_mem (Jα.mul_mem (Jα.inv_mem hjJ) (hveq ▸ v.2)) hjJ
          simpa [mul_assoc] using h1
        refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
        have h2 : j' * ⟨x, hxJ⟩ * j'⁻¹ = v := Subtype.ext hveq.symm
        exact (Subgroup.mem_normalizer_iff.mp hjV ⟨x, hxJ⟩).mpr (by rw [h2]; exact hv)
    have hBW : img148 A Y B ≤ Subgroup.normalizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp (hBJ hx) w (hWJ hw)
    have hAW : img148 A Y A ≤ Subgroup.normalizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [← hAeq]
      exact sup_le hBW (Subgroup.zpowers_le.mpr hjW)
    have hc := commutator_le_img148_deltaZero_of_point h142 hS hY hbΩ W (hWJ.trans hJb) hW3 hAW
    have hjA : Subgroup.zpowers j ≤ img148 A Y A := hAeq ▸ le_sup_right
    intro x hx
    have hxm : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ ⁅W, Subgroup.zpowers j⁆ := by
      have hmap : (⁅V, Subgroup.zpowers j'⁆).map Jα.subtype = ⁅W, Subgroup.zpowers j⁆ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        rfl
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    exact hc (Subgroup.commutator_mono le_rfl hjA hxm)
  intro x hx
  have : (⟨x, hx⟩ : ↥Jα) ∈ H := htop ▸ Subgroup.mem_top _
  exact this

end Gen

section Certificates


@[expose] def Step148HJA5Type : Prop :=
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
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
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
            alternatingGroup (Fin 5)) ∨
          Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J)))
            (alternatingGroup (Fin 6)) ∨
          (Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
              CFSG.Blueprint.NativeSporadic.J2) ∧ (omegaA A).ncard = 6)

theorem step148HJA5Inner2_of_type
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hT : Step148HJA5Type) :
    Step148HJA5Inner2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hYB5 hbc hXJ
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, hb1, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
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
  have hAp : IsPGroup 3 ↥(img148 A Y A) := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hjJ, hj1, hj3, hjC⟩ := exists_pow_eq_one_mem_centralizer hAp hAJα h3Jα
  have hjA : j ∈ img148 A Y A := mem_img148_of_commute hS.mem_partTwoF hY.2 hjC hj3
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
  have hCD : img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
      img148 A Y A ⊓ img148 A Y J = img148 A Y A := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    calc img148 A Y A = img148 A Y B ⊔ Subgroup.zpowers j := hAeq.symm
      _ ≤ _ := sup_le_sup (le_inf hBA hBJ) (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hjA, hjJ⟩))
  have hXle := img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hjJ hjA hjZ hCD
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
  have hYBα : img148 A Y YB = img148 A Y J := by
    refine Subgroup.eq_of_le_of_card_ge (heq ▸ img148_mono hYBYd) ?_
    obtain ⟨ψ⟩ := hYB5
    have h1 := card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      (three_dvd_card_of_ydType148 (d := b) (Or.inl ⟨ψ⟩))
    rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at h1
    rw [h60]
    exact h1
  have hJb : img148 A Y J ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (hYBC.trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)))
    exact Set.singleton_subset_iff.mpr hbB
  have hJX := img148_le_img148_deltaZero_of_a5 h142 hS hY hc.2.1 φ hJb hBJ hjJ hj1 hj3 hAeq
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
  have hint : img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZC hx.2) g g.2)
    rw [hJZ, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  have hne' : ∀ e ∈ img148 A Y A,
      e ∉ Subgroup.centralizer ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :
        Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      ∃ k ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)), e * k ≠ k * e := by
    intro e he heZ
    by_contra hcon
    push Not at hcon
    apply heZ
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcon k hk).symm
  have hXd : alpha148 A Y d hdA ∈ Subgroup.centralizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {alpha148 A Y d hdA} := by
    intro hdZ
    rw [hXeq]
    refine sup_le hdJ fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdZ x hx
  rcases hT G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
      hYBYd hYdJ hAYd hYdt hdc heq hη ⟨φ⟩ hYB5 hbc hXeq hZne with hZ5 | hZ6 | ⟨hZJ2, hΩ6⟩
  ·
    obtain ⟨φZ⟩ := hZ5
    have h3Z : 3 ∣ Nat.card (img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) := by
      rw [Nat.card_congr φZ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
      norm_num
    have hfix : ∀ e ∈ img148 A Y A,
        e ∉ Subgroup.centralizer ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :
          Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ∀ x ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)), x * e = e * x →
          Nat.Coprime (orderOf x) 3 → x = 1 := by
      intro e he heZ x hx hxe hx3
      have hx3' := pow_three_eq_one_of_commute_a5 φZ (hAN he) (hAE.1.2 e he) (hne' e he heZ)
        hx hxe
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hx3 (orderOf_dvd_of_pow_eq_one hx3'))
    have hdZ := alpha148_mem_centralizer_of_contrib h134 h48 hS hB hc hdA centPre148_le h3Z hfix
    have hiso := nonempty_mulEquiv_prod_of_commute_of_equiv hUV hint hXeq φ φZ
    exact Or.inr (Or.inl (HJRes2.case148Three_of_le_centralizer hS hY hc.2.1 hLb
      (Item148HJ.j2_of_isLBConfig hc) hdA hd1 hc.2.2.2.2 (hXd hdZ)
      (Or.inr (Or.inr (Or.inr (Or.inl hiso))))))
  ·
    set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
    set Xα := img148 A Y (deltaZero A (lB A) Y) with hXα
    have h3Z : 3 ∣ Nat.card Zα := by rw [HJRes2.card_of_isTripleCover_six hZ6]; norm_num
    have hfix : ∀ e ∈ img148 A Y A,
        e ∉ Subgroup.centralizer ((Zα : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ∀ x ∈ Zα, x * e = e * x → Nat.Coprime (orderOf x) 3 → x = 1 := fun e he heZ x hx hxe hx3 =>
      eq_one_of_commute_tripleCover hZ6 (hAN he) (hAE.1.2 e he) (hne' e he heZ) hx hxe hx3
    have hdZ := alpha148_mem_centralizer_of_contrib h134 h48 hS hB hc hdA centPre148_le h3Z hfix
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
    have htype : IsA6CoverTimesA5 ↥Xα := by
      refine ⟨Zα.subgroupOf Xα, (img148 A Y J).subgroupOf Xα,
        (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr (hXN (Or.inl rfl)),
        (Subgroup.normal_subgroupOf_iff_le_normalizer hJX').mpr (hXN (Or.inr rfl)), ?_, ?_,
        KFacts.KS14.isTripleCover_congr (Subgroup.subgroupOfEquivOfLe hZX).symm hZ6,
        ⟨(Subgroup.subgroupOfEquivOfLe hJX').trans φ⟩⟩
      · rw [eq_bot_iff]
        intro x hx
        have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J ⊓ Zα :=
          ⟨Subgroup.mem_subgroupOf.mp hx.2, Subgroup.mem_subgroupOf.mp hx.1⟩
        rw [hint, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (Subtype.ext h1)
      · rw [← Subgroup.subgroupOf_sup hZX hJX']
        exact Subgroup.subgroupOf_eq_top.mpr (hXeq.le.trans (sup_comm _ _).le)
    exact Or.inr (Or.inl (HJRes2.case148Three_of_le_centralizer hS hY hc.2.1 hLb
      (Item148HJ.j2_of_isLBConfig hc) hdA hd1 hc.2.2.2.2 (hXd hdZ)
      (Or.inr (Or.inr (Or.inl htype)))))
  ·
    obtain ⟨φZ⟩ := hZJ2
    exact Or.inr (Or.inr ⟨nonempty_mulEquiv_prod_of_commute_of_equiv hUV hint hXeq φ φZ,
      ⟨b, Lb, hc.2.1, hLb, Item148HJ.j2_of_isLBConfig hc⟩, hΩ6⟩)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
