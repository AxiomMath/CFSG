module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJTypes
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJA5Comp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelveImg
import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelveRes
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormal
import CFSG.RankThree.PartTwo.Sec14.Ronan148AFrame
import CFSG.RankThree.PartTwo.Sec14.Ronan148AInnerCenter
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148
  Ronan148M

variable {G : Type} [Group G] [Finite G]

theorem a5_structure148
    (h142 : Concl142S14)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    [(ker148 A Y).Normal] {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    {Yd : Subgroup G} (hYBYd : YB ≤ Yd) (hYdJ : Yd ≤ J)
    (hAYd : A ≤ Subgroup.normalizer (Yd : Set G)) (hYdt : YdType148 d Yd)
    (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y))
    (heq : img148 A Y Yd = img148 A Y J)
    (η : ↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J))
    (φ : ↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) :
    IsComponent (img148 A Y J) ∧
      (∃ j ∈ img148 A Y J, j ∈ img148 A Y A ∧ j ≠ 1) ∧
      img148 A Y (deltaZero A (lB A) Y) =
        img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ∧
      img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
      img148 A Y A ≤ Subgroup.normalizer
        ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
          Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  obtain ⟨hYB5, h2⟩ := HJRes2.a5_facts hbB hYB htype hYBYd (hAYd hbA) ⟨η.trans φ⟩
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have h60 : Nat.card (img148 A Y J) = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [h60]; norm_num
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 hYdt).trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hbJ := HJRes2.le_centralizer_of_theta hYdM heq hJθ hbA h2
  have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hBJ : img148 A Y B ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hc.1]
    have hS' : ({b, d} : Set G) ⊆ (Y ⊔ A : Subgroup G) := by
      rintro g (rfl | rfl)
      · exact Subgroup.mem_sup_right hbA
      · exact Subgroup.mem_sup_right hdA
    refine Ronan148J.img148_closure_le_centralizer hS' fun g hg => ?_
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
  obtain ⟨j, hjJ, hj1, hj3, hjC⟩ := Ronan148J.exists_pow_eq_one_mem_centralizer hAp hAJα h3Jα
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
  obtain ⟨hBA, -, hmax⟩ := Ronan148J.img148_hyperplane_max (Y := Y) hA hB
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
  have hXle := Ronan148J.img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hjJ hjA hjZ
    hCD
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
  have hYBα : img148 A Y YB = img148 A Y J := by
    refine Subgroup.eq_of_le_of_card_ge (heq ▸ img148_mono hYBYd) ?_
    obtain ⟨ψ⟩ := hYB5
    have h1 := Ronan148J.card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      (three_dvd_card_of_ydType148 (d := b) (Or.inl ⟨ψ⟩))
    rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at h1
    rw [h60]
    exact h1
  have hJb : img148 A Y J ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (hYBC.trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)))
    exact Set.singleton_subset_iff.mpr hbB
  have hJX := Ronan148J.img148_le_img148_deltaZero_of_a5 h142 hS hY hc.2.1 φ hJb hBJ hjJ hj1 hj3
    hAeq
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  refine ⟨hJc, ⟨j, hjJ, hjA, hj1⟩, le_antisymm hXle (sup_le hJX (hZle.trans inf_le_left)),
    hZle.trans inf_le_right, ?_⟩
  exact img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)

section Certificates

@[expose] def Step148NormalHJA5Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
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
        img148 A Y (deltaZero A (lB A) Y) =
          img148 A Y J ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) →
        (img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ ∨
          Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
            alternatingGroup (Fin 5))) →
        (omegaA A).ncard ≠ 12 →
        ∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K →
          Nonempty (↥K ≃* alternatingGroup (Fin 5)) →
          (∃ x ∈ img148 A Y Y, K = (img148 A Y J).map (MulAut.conj x).toMonoidHom ∨
            K = (img148 A Y (deltaZero A (lB A) (centPre148 A Y J))).map
              (MulAut.conj x).toMonoidHom) →
          K ≤ Subgroup.centralizer
            (img148 A Y (deltaZero A (lB A) Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          img148 A Y A ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          ∀ k₀ ∈ K, k₀ ∈ img148 A Y A → k₀ ≠ 1 →
          img148 A Y A ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
              Subgroup.zpowers k₀ = img148 A Y A →
          (∀ (a : G) (ha : a ∈ A), Subgroup.zpowers a ∈ omegaA A →
            alpha148 A Y a ha ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) →
          False

theorem step148NormalHJA5_of_two (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) (hTwo : Step148NormalHJA5Two) : Step148NormalHJA5 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ5
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  obtain ⟨η⟩ := hη
  obtain ⟨φ⟩ := hJ5
  obtain ⟨hJc, ⟨j, hjJ, hjA, hj1⟩, hXeq, hZC, hAN⟩ :=
    a5_structure148 h142 hS hY hB hYB htype hc hJ hAJ hYBYd hYdJ hAYd hYdt hdc heq η φ
  set Jα := img148 A Y J with hJα
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  set Aα := img148 A Y A with hAα
  have hAE := img148_isE27 (Y := Y) hA
  have hAα3 : ∀ a ∈ Aα, a ^ 3 = 1 := hAE.1.2
  have hAab : ∀ x ∈ Aα, ∀ y ∈ Aα, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup 3 ↥Aα := IsPGroup.of_card (n := 3) (by rw [hAE.2]; norm_num)
  have hF3 : ∀ w, w ∈ Subgroup.centralizer (Aα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
      w ∈ Aα := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hY.2 hw hw3
  have hAJα : Aα ≤ Subgroup.normalizer (Jα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hYn : (img148 A Y Y).Normal := Item148Res5.img148_normal hY.2
  have hHE : ∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K → K ≤ img148 A Y Y :=
    fun K hK => le_img148_of_isPerfect148 hA hY.2 hK.1.1
  have h60 : Nat.card ↥Jα = 60 := by
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have h3J' : 3 ∣ Nat.card ↥Jα := by rw [h60]; norm_num
  have hY₁ : centPre148 A Y J ∈ scriptY A := centPre148_mem_scriptY hY hAJ
  have hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y :=
    Ronan148J.pPrimeCoreOf_centPre148_eq_of_isComponent hY.2 hJY hJc h3J'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥Jα := isPerfect_img148 hJM
  have hJne : Jα ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h60
    norm_num at h60
  have hlt : Nat.card (centPre148 A Y J) < Nat.card Y :=
    card_centPre148_lt hJY (Ronan148M.exists_ne_comm_of_isPerfect hJp hJne)
  have h148₁ : Item148At A (lB A) (centPre148 A Y J) hY₁ := ih _ hY₁ hlt
  have hX1Y₁ : deltaZero A (lB A) (centPre148 A Y J) ≤ centPre148 A Y J :=
    sSup_le fun _ hQ => hQ.2
  have hCZ : img148 A Y Y ⊓ Subgroup.centralizer (Jα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
      Subgroup.normalizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    letI := ker148_normal hY₁.2
    have hN₁ := img148_le_normalizer_of_map_normal (A := A) hX1Y₁ h148₁.1
    have hY₁Z : img148 A Y (centPre148 A Y J) ≤ Subgroup.normalizer (Zα : Set _) := by
      rw [hZα, ← map_img148_compare148 hcore.le le_sup_left,
        ← map_img148_compare148 hcore.le (hX1Y₁.trans le_sup_left)]
      exact (Subgroup.map_mono hN₁).trans (Subgroup.le_normalizer_map _)
    rw [← Ronan148J.img148_centPre148_eq]
    exact hY₁Z
  have hZY : Zα ≤ img148 A Y Y := img148_mono ((deltaZero_le _).trans centPre148_le)
  have hZCY : Zα ≤ img148 A Y Y ⊓ Subgroup.centralizer (Jα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    le_inf hZY hZC
  have hZtype : Zα = ⊥ ∨ Nonempty (↥Zα ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover ↥Zα (alternatingGroup (Fin 6)) ∨
      Nonempty (↥Zα ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    by_cases hZ1 : Zα = ⊥
    · exact Or.inl hZ1
    right
    have hT : Ronan148J.Step148HJA5Type := Ronan148J.step148HJA5Type_of_cent h134 h48
      (Ronan148J.step148HJA5Cent_of_cent2 (Ronan148W.step148HJA5Cent2_of_twelve h134 h48 h143
        (step148HJA5J2Twelve_holds h134 h48)))
    obtain ⟨hYB5, h2⟩ := HJRes2.a5_facts hbB hYB htype hYBYd (hAYd hbA) ⟨η.trans φ⟩
    rcases hT G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
        hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ ⟨φ⟩ hYB5 ⟨hbA, h2⟩ hXeq hZ1 with h5 | h6 | ⟨h2', -⟩
    · exact Or.inl h5
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr h2')
  obtain ⟨j', hj'J, -, hj'3, hj'Z⟩ := exists_three_of_a5 φ
  have happ : (Zα = ⊥ ∨ Nonempty (↥Zα ≃* alternatingGroup (Fin 5))) →
      (Zα = ⊥ ∨ IsComponent Zα) →
      ∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K → K ≠ Jα → K ≠ Zα →
      ∀ x ∈ img148 A Y Y, ∀ W : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), (W = Jα ∨ W = Zα) →
        K = W.map (MulAut.conj x).toMonoidHom → False := by
    intro hZ15 hZcomp K hKc hKJ hKZ x hxY W hW hKW
    have hKJα : K ≤ Subgroup.centralizer (Jα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun _ hk =>
      Res2LBal.mem_centralizer_of_mem_of_ne hJc hKc hKJ.symm hk
    have hW5 : Nonempty (↥W ≃* alternatingGroup (Fin 5)) := by
      rcases hW with rfl | rfl
      · exact ⟨φ⟩
      · rcases hZ15 with hZ1 | hZ5
        · exfalso
          apply hKZ
          rw [hKW, hZ1, Subgroup.map_bot]
        · exact hZ5
    obtain ⟨φW⟩ := hW5
    obtain ⟨φK⟩ : Nonempty (↥K ≃* alternatingGroup (Fin 5)) := by
      rw [hKW]
      exact ⟨(W.equivMapOfInjective _ (MulAut.conj x).injective).symm.trans φW⟩
    have hKZα : K ≤ Subgroup.centralizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rcases hZcomp with hZ1 | hZc
      · intro k _
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [hZ1, SetLike.mem_coe, Subgroup.mem_bot] at hh
        rw [hh, one_mul, mul_one]
      · exact fun _ hk => Res2LBal.mem_centralizer_of_mem_of_ne hZc hKc hKZ.symm hk
    have hKX : K ≤ Subgroup.centralizer
        (img148 A Y (deltaZero A (lB A) Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro k hk
      rw [hXeq]
      exact mem_centralizer_sup (hKJα hk) (hKZα hk)
    have hAK := le_normalizer_of_a5_component148 hS hJc hKc hKJ hAJα hAα3 φ φK
    obtain ⟨k₀, hk₀K, hk₀A, hk₀1, hk₀3, hAeqK⟩ :=
      exists_inner_a5_of_normalizer hAab hAα3 hF3 hAK φK
    have hnoPt : ∀ (a : G) (ha : a ∈ A), Subgroup.zpowers a ∈ omegaA A →
        alpha148 A Y a ha ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro a ha haΩ haK
      have hKd : K ≤ Subgroup.centralizer {alpha148 A Y a ha} := fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp haK k hk)
      have hKa := le_img148_inf_centralizer hY.2 ha (hA.1.2 a ha) le_rfl (hHE K hKc) hKd
      have hKX' := le_img148_deltaZero_of_a5_point h142 hS hY haΩ φK hKa inf_le_right hk₀K hk₀1
        hk₀3 hAeqK
      obtain ⟨k, hkK, -, -, hkZ⟩ := exists_three_of_a5 φK
      exact hkZ (Subgroup.centralizer_le hKX' (hKX hkK))
    by_cases h12 : (omegaA A).ncard = 12
    ·
      obtain ⟨j₀, hj₀M, hj₀A, hj₀⟩ := mem_img148_iff.mp hjA
      have hα : alpha148 A Y j₀ hj₀A = j := (alpha148_eq_mk' hj₀A).trans hj₀
      have hj₀1 : j₀ ≠ 1 := by
        rintro rfl
        apply hj1
        rw [← hα]
        exact Ronan148V.alpha148_one'
      have hdJ := HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
      have hj₀d : Subgroup.zpowers j₀ ≠ Subgroup.zpowers d := by
        intro he
        have hjd : j ∈ Subgroup.zpowers (alpha148 A Y d hdA) := by
          rw [← hα]
          exact Ronan148V.alpha148_mem_of_mem_zpowers hA.1.2 hdA hj₀A
            (he ▸ Subgroup.mem_zpowers j₀) (Subgroup.mem_zpowers _)
        have hdC : alpha148 A Y d hdA ∈
            Subgroup.centralizer (Jα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact Subgroup.mem_centralizer_singleton_iff.mp (hdJ hg)
        exact not_mem_centralizer_of_a5 φ hjJ hj1 (Subgroup.zpowers_le.mpr hdC hjd)
      have hdΩ : Subgroup.zpowers d ∉ omegaA A :=
        Sec15.Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48
          (Item148HJ.sec14Std_of_isLBConfig hS hc) (Item148HJ.j2_of_isLBConfig hc) hdA hd1
          hc.2.2.2.2
      have hj₀Ω := zpowers_mem_omegaA_of_ncard_twelve hA h12 hdA hd1 hdΩ hj₀A hj₀1 hj₀d
      apply hnoPt j₀ hj₀A hj₀Ω
      rw [hα, Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hKJα hk) j hjJ).symm
    · have hKx : ∃ x ∈ img148 A Y Y, K = Jα.map (MulAut.conj x).toMonoidHom ∨
          K = Zα.map (MulAut.conj x).toMonoidHom := by
        refine ⟨x, hxY, ?_⟩
        rcases hW with rfl | rfl
        · exact Or.inl hKW
        · exact Or.inr hKW
      exact hTwo G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
        hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ ⟨φ⟩ hXeq hZ15 h12 K hKc ⟨φK⟩ hKx hKX
        hAK k₀ hk₀K hk₀A hk₀1 hAeqK hnoPt
  have hU6 : ∀ U : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), U ≤ Zα →
      Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)) → IsComponent Zα →
      ∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K → K ≠ Jα → K ≠ Zα →
      ∀ w ∈ K, w ^ 3 = 1 → w ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        False := by
    intro U hUZ hU hZc K hKc hKJ hKZ w hwK hw3 hwZ
    have hKJα : K ≤ Subgroup.centralizer (Jα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun _ hk =>
      Res2LBal.mem_centralizer_of_mem_of_ne hJc hKc hKJ.symm hk
    have hKU : K ≤ Subgroup.centralizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun _ hk =>
      Subgroup.centralizer_le hUZ (Res2LBal.mem_centralizer_of_mem_of_ne hZc hKc hKZ.symm hk)
    have hJU : Jα ≤ Subgroup.centralizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun g hg =>
      Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp (hZC (hUZ hu)) g hg).symm
    exact false_of_two_commuting_A6148 hS hU hJU hKU hKJα hj'J hwK hj'3 hw3 hj'Z hwZ
  have hfix : (Zα = ⊥ ∨ IsComponent Zα) →
      (∀ K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsComponent K → K ≠ Jα → K ≠ Zα →
        ∀ x ∈ img148 A Y Y, ∀ W : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), (W = Jα ∨ W = Zα) →
          K = W.map (MulAut.conj x).toMonoidHom → False) →
      ∀ x ∈ img148 A Y Y, (Jα ⊔ Zα).map (MulAut.conj x).toMonoidHom ≤ Jα ⊔ Zα := by
    intro hZcomp hthird x hxY
    have hW : ∀ W : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), (W = Jα ∨ W = Zα) →
        W.map (MulAut.conj x).toMonoidHom ≤ Jα ⊔ Zα := by
      intro W hW
      by_cases hW1 : W = ⊥
      · rw [hW1, Subgroup.map_bot]
        exact bot_le
      have hWc : IsComponent W := by
        rcases hW with rfl | rfl
        · exact hJc
        · exact hZcomp.resolve_left hW1
      have hKc : IsComponent (W.map (MulAut.conj x).toMonoidHom) :=
        Res2LBal.isComponent_conj hWc x
      by_cases hKJ : W.map (MulAut.conj x).toMonoidHom = Jα
      · rw [hKJ]
        exact le_sup_left
      by_cases hKZ : W.map (MulAut.conj x).toMonoidHom = Zα
      · rw [hKZ]
        exact le_sup_right
      exact (hthird _ hKc hKJ hKZ x hxY W hW rfl).elim
    rw [Subgroup.map_sup]
    exact sup_le (hW _ (Or.inl rfl)) (hW _ (Or.inr rfl))
  have hkey : ∀ x ∈ img148 A Y Y,
      (Jα ⊔ Zα).map (MulAut.conj x).toMonoidHom ≤ Jα ⊔ Zα := by
    rcases hZtype with hZ1 | hZ5 | hZ6 | hZ2
    · exact hfix (Or.inl hZ1) (happ (Or.inl hZ1) (Or.inl hZ1))
    · obtain ⟨φZ⟩ := hZ5
      have hZc : IsComponent Zα := isComponent_of_le_normalizer_inf_centralizer hYn hHE hJc
        (isTwelveType_of_mulEquiv_A5 φZ).1 hZCY hCZ
      exact hfix (Or.inr hZc) (happ (Or.inr ⟨φZ⟩) (Or.inr hZc))
    ·
      have hZp : Group.IsPerfect ↥Zα := isPerfect_of_le_commutator_of_isTripleCover hZ6 hAp hAN
        (img148_deltaZero_le_commutator centPre148_le)
      have hZc : IsComponent Zα := isComponent_of_le_normalizer_inf_centralizer hYn hHE hJc
        (isTwelveType_of_tripleCover_A6 hZ6 hZp).1 hZCY hCZ
      obtain ⟨u, huZα, hu3', huZ'⟩ := exists_noncentral_of_tripleCover_le hZ6
      refine hfix (Or.inr hZc) fun K hKc hKJ hKZ x _ W hW hKW => ?_
      obtain ⟨w, hwW, hw3, hwZ⟩ : ∃ w ∈ W, w ^ 3 = 1 ∧
          w ∉ Subgroup.centralizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rcases hW with rfl | rfl
        · exact ⟨j', hj'J, hj'3, hj'Z⟩
        · exact ⟨u, huZα, hu3', huZ'⟩
      refine hU6 Zα le_rfl hZ6 hZc K hKc hKJ hKZ (x * w * x⁻¹) ?_ ?_ ?_
      · rw [hKW]
        exact Res2LBal.conj_mem_map hwW x
      · rw [conj_pow, hw3, mul_one, mul_inv_cancel]
      · rw [hKW]
        exact conj_not_mem_centralizer_map hwZ x
    ·
      obtain ⟨φZ⟩ := hZ2
      obtain ⟨hZq, U, hUZ, hU6'⟩ := exists_tripleCover_A6_le_of_j2 φZ
      have hZc : IsComponent Zα :=
        isComponent_of_le_normalizer_inf_centralizer hYn hHE hJc hZq hZCY hCZ
      obtain ⟨u, huU, hu3', huZ⟩ := exists_noncentral_of_tripleCover_le hU6'
      have huZ' : u ∉ Subgroup.centralizer (Zα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun hC =>
        huZ (Subgroup.centralizer_le hUZ hC)
      refine hfix (Or.inr hZc) fun K hKc hKJ hKZ x _ W hW hKW => ?_
      obtain ⟨w, hwW, hw3, hwZ⟩ : ∃ w ∈ W, w ^ 3 = 1 ∧
          w ∉ Subgroup.centralizer (W : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
        rcases hW with rfl | rfl
        · exact ⟨j', hj'J, hj'3, hj'Z⟩
        · exact ⟨u, hUZ huU, hu3', huZ'⟩
      refine hU6 _ hUZ hU6' hZc K hKc hKJ hKZ (x * w * x⁻¹) ?_ ?_ ?_
      · rw [hKW]
        exact Res2LBal.conj_mem_map hwW x
      · rw [conj_pow, hw3, mul_one, mul_inv_cancel]
      · rw [hKW]
        exact conj_not_mem_centralizer_map hwZ x
  have hXY : deltaZero A (lB A) Y ≤ Y := sSup_le fun _ hQ => hQ.2
  have hX1 : deltaZero A (lB A) (centPre148 A Y J) ≤ Y ⊔ A :=
    ((deltaZero_le _).trans centPre148_le).trans le_sup_left
  have hXeq' : img148 A Y (deltaZero A (lB A) Y) =
      img148 A Y (J ⊔ deltaZero A (lB A) (centPre148 A Y J)) := by
    rw [img148_sup hJM hX1, hXeq]
  refine map_normal_of_img148_eq hXY hXeq' fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, img148_sup hJM hX1]
  set x := QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) with hx
  have hxY : x ∈ img148 A Y Y := mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_left hy, hy, rfl⟩
  refine le_antisymm (hkey x hxY) ?_
  have h2 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) (hkey x⁻¹ (inv_mem hxY))
  rwa [Res2LBal.map_conj_map_conj, mul_inv_cancel, Res2LBal.map_conj_one] at h2

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
