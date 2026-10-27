module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JA5Type
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JGen6
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJCent
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJExcl
import CFSG.RankThree.PartTwo.Sec14.Item148ProofNHJ
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofImgLe
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def KHJPerfectOver : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ z : X, z ≠ 1 → z ^ 3 = 1 → 27 ∣ Nat.card (Subgroup.centralizer ({z} : Set X)) →
    ∀ M : Subgroup X, Group.IsPerfect ↥M → Subgroup.centralizer ({z} : Set X) ≤ M →
      M = Subgroup.centralizer ({z} : Set X) ∨ M = ⊤

section Certificates


@[expose] def Step148HJHJCent : Prop :=
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
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) →
        d ∈ YB → b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        (img148 A Y (deltaZero A (lB A) Y) = img148 A Y J → ∀ a ∈ A,
          Subgroup.zpowers a ∈ omegaA A →
          (∃ La ∈ lA A a,
            Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2)) →
          a ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) →
        (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
          ¬ Case148Three A (lB A) (centPre148 A Y J) ∧
            ¬ Case148Six A (lB A) (centPre148 A Y J)) ∧
        (img148 A Y (deltaZero A (lB A) Y) = img148 A Y J →
          ∃ a ∈ A, Subgroup.zpowers a ∈ omegaA A ∧
            a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) ∧
        (img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) →
          Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
            alternatingGroup (Fin 5)) →
          (omegaA A).ncard = 6)

theorem centPre148_type_of_hj
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A (lB A) Y) {B Lb : Subgroup G}
    {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hJY : J ≤ Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    letI := ker148_normal hY.2
    IsComponent (img148 A Y J) → 3 ∣ Nat.card (img148 A Y J) →
    img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
        CFSG.Blueprint.NativeSporadic.J2) ∨
      Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J)))
        (alternatingGroup (Fin 6)) ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
        alternatingGroup (Fin 5)) ∨
      (letI := ker148_normal (le_normalizer_centPre148 (J := J) hY.2 hAJ);
        Case148Three A (lB A) (centPre148 A Y J) ∨ Case148Six A (lB A) (centPre148 A Y J)) := by
  intro hJc h3Jα
  let := ker148_normal hY.2
  have hne : img148 A Y J ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at h3Jα
    omega
  have hnc := exists_ne_comm_of_isPerfect hJc.1.1 hne
  obtain ⟨-, hcases⟩ := item148At_centPre148 (LB := lB A) hY ih hJY hAJ hnc
  obtain ⟨e⟩ := nonempty_img148_deltaZero_centPre148_equiv hY.2 hAJ hJY hJc h3Jα (lB A)
  have hpt := fun {c₁ : G} (hc₁ : Subgroup.zpowers c₁ ∈ omegaA A) {L₁ : Subgroup G}
      (hL₁ : L₁ ∈ lA A c₁) => j2_of_mem_lA_of_isLBConfig h134 h48 hS hB hc hc₁ hL₁
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6' | h7
  ·
    left
    have hcore := pPrimeCoreOf_centPre148_eq_of_isComponent hY.2 hJY hJc h3Jα
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_bot, mk'_ker148_eq_one_iff]
    have h := h1 hgD
    rwa [hcore] at h
  ·
    obtain ⟨c₁, hc₁, -, L₁, hL₁, hcase⟩ := h2
    obtain ⟨ψ⟩ := hpt hc₁ hL₁
    rcases hcase with hχ | ⟨hL, -⟩ | ⟨p, f, e', hp, -, -, hπ, -⟩ | ⟨-, hiv⟩
    ·
      obtain ⟨χ⟩ := hχ
      exact Or.inr (Or.inl ⟨e.symm.trans (χ.trans ψ)⟩)
    ·
      exfalso
      rcases hL with hμ | ⟨_, hμ⟩ | ⟨_, hμ⟩
      · obtain ⟨μ⟩ := hμ
        exact KFacts.KS14.ks17J2NotList.2.2.false (ψ.symm.trans μ)
      · obtain ⟨μ⟩ := hμ
        exact KFacts.KS14.not_isLThreeEpsAt_j2 5 2 (Or.inl ⟨ψ.symm.trans μ⟩)
      · obtain ⟨μ⟩ := hμ
        exact KFacts.KS14.not_isLThreeEpsAt_j2 5 1 (Or.inr ⟨by norm_num, ⟨ψ.symm.trans μ⟩⟩)
    ·
      exact absurd hπ (Sec15.Proof1514.not_isoLThreePi_of_j2 ψ)
    ·
      rcases hiv with h6c | hχ
      · exact Or.inr (Or.inr (Or.inl (KFacts.KS14.isTripleCover_congr e h6c)))
      · obtain ⟨χ⟩ := hχ
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans χ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
  ·
    exfalso
    obtain ⟨-, ⟨c₁, L₁, hc₁, hL₁, hμ⟩, -⟩ := h4
    obtain ⟨μ⟩ := hμ
    obtain ⟨ψ⟩ := hpt hc₁ hL₁
    exact KFacts.KS14.ks17J2NotList.2.1.false (ψ.symm.trans μ)
  ·
    exfalso
    obtain ⟨c₁, -, L₁, n, m, hc₁, hL₁, -, -, -, -, -, -, hε, -⟩ := h5
    obtain ⟨ψ⟩ := hpt hc₁ hL₁
    rcases hε with hμ | ⟨h2, hμ⟩
    · obtain ⟨μ⟩ := hμ
      exact KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (Or.inl ⟨ψ.symm.trans μ⟩)
    · obtain ⟨μ⟩ := hμ
      exact KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (Or.inr ⟨h2, ⟨ψ.symm.trans μ⟩⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6'))))
  ·
    exfalso
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, ha₁, -, hL₁, -, -, -, -,
      -, -, -, -, -, -, -, -, hπ₁, -⟩ := h7
    obtain ⟨ψ⟩ := hpt ha₁ hL₁
    exact Sec15.Proof1514.not_isoLThreePi_of_j2 ψ hπ₁

end Certificates

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_yd_facts_of_j2
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {d : G} (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    {Yd J : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (φ : ↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) (hdd : d ∈ Yd)
    (hd1 : alpha148 A Y d hdA ≠ 1) (hdα3 : alpha148 A Y d hdA ^ 3 = 1) :
    img148 A Y Yd = img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hdA} ∧
      Sec4.IsTripleCover ↥(img148 A Y Yd) (alternatingGroup (Fin 6)) ∧
      Group.IsPerfect ↥(img148 A Y Yd) ∧
      (∀ g ∈ img148 A Y Yd, (∀ h ∈ img148 A Y Yd, g * h = h * g) →
        g ∈ Subgroup.zpowers (alpha148 A Y d hdA)) ∧
      aschbacherSolvableCore 3 ↥(img148 A Y Yd) = ⊥ := by
  have h1080 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 1080 :=
    HJRes2.card_of_isTripleCover_six hA6
  have h3Yd : 3 ∣ Nat.card Yd := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥Yd), h1080]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨hYdle, -, -, -, ⟨η⟩⟩ := HJRes148.ydAlpha_facts hAY hdA hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have hq : Nat.card (↥(img148 A Y Yd) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y Yd)) = 1080 := by
    rw [← Nat.card_congr η.toEquiv, h1080]
  have hcard : Nat.card (img148 A Y Yd) =
      1080 * Nat.card (aschbacherSolvableCore 3 ↥(img148 A Y Yd)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (aschbacherSolvableCore 3 ↥(img148 A Y Yd)), hq]
  have h27 : 27 ∣ Nat.card ↥(img148 A Y J ⊓
      Subgroup.centralizer ({alpha148 A Y d hdA} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hYdle)
    rw [hcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hdJ : alpha148 A Y d hdA ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdd, rfl⟩
  obtain ⟨hC6, hCp, hC1080, hCZ⟩ := inf_centralizer_facts_of_j2 φ hdJ hd1 hdα3 h27
  have hYdeq : img148 A Y Yd = img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hdA} := by
    refine Subgroup.eq_of_le_of_card_ge hYdle ?_
    rw [hC1080, hcard]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hθ1 : aschbacherSolvableCore 3 ↥(img148 A Y Yd) = ⊥ := by
    have h1 : Nat.card (img148 A Y Yd) = 1080 := by rw [hYdeq]; exact hC1080
    rw [h1] at hcard
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  refine ⟨hYdeq, ?_, ?_, fun g hg hgc => hCZ g (hYdeq ▸ hg) fun h hh => hgc h (hYdeq ▸ hh), hθ1⟩
  · rw [hYdeq]; exact hC6
  · rw [hYdeq]; exact hCp

theorem exists_mul_of_mem_sup_of_commute {U V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hx : x ∈ U ⊔ V) :
    ∃ u ∈ U, ∃ v ∈ V, x = u * v := by
  rw [← commProdHom_range hUV] at hx
  obtain ⟨⟨u, v⟩, rfl⟩ := MonoidHom.mem_range.mp hx
  exact ⟨u, u.2, v, v.2, commProdHom_apply hUV _⟩

end Quot

section Certificates


set_option maxHeartbeats 2000000 in
theorem step148HJHJOuter2_of_cent
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8) (hK : KHJPerfectOver)
    (hR : Step148HJHJCent) : Step148HJHJOuter2 := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl
  let := ker148_normal hY.2
  obtain ⟨hres1, hres2, hres3⟩ := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc
    hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc hJ2 hexcl
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBM : YB ≤ Y ⊔ A := (hYBC.trans inf_le_left).trans le_sup_left
  obtain ⟨φ⟩ := hJ2
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJs : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup φ
  obtain ⟨hJc, hJZ⟩ := Item148Res5.isComponent_img148 hY.2 hJ hJs
  have hJcard : Nat.card (img148 A Y J) = 604800 := KFacts.KS14.card_eq_of_j2 ⟨φ⟩
  have h3Jα : 3 ∣ Nat.card (img148 A Y J) := by rw [hJcard]; norm_num
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
  have hJZ' : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.1⟩ : ↥(img148 A Y J)) ∈ Subgroup.center ↥(img148 A Y J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2)
    rw [hJZ, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  have hCD := sup_eq_of_forall_inner hAab hA3 hF3 hJZ' hAJα
    (fun a ha => exists_inner_of_j2 φ (hAJα ha) (hA3 a ha))
  set dα := alpha148 A Y d hdA with hdαdef
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hdα3 : dα ^ 3 = 1 := hA3 _ hdαA
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hdJα : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hdnc : ∃ y ∈ img148 A Y J, dα * y ≠ y * dα := by
    by_contra hcon
    push Not at hcon
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hdA fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcon x hx).symm
  have hdα1 : dα ≠ 1 := by
    intro h
    obtain ⟨y, -, hy⟩ := hdnc
    exact hy (by rw [h, one_mul, mul_one])
  have hXle := img148_deltaZero_le_sup_centPre148 (LB := lB A) hA hAJ hJc hdJα hdαA hdnc hCD
  obtain ⟨hYdeq, hYd6, hYdp, hYdZ, hYdθ⟩ :=
    img148_yd_facts_of_j2 hY.2 hdA hd3 hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hYdJα : img148 A Y Yd ≤ img148 A Y J := img148_mono hYdJ
  have hYdC : img148 A Y Yd ≤ Subgroup.centralizer {dα} := hYdeq ▸ inf_le_right
  have h3YB : 3 ∣ Nat.card YB := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
      HJRes2.card_of_isTripleCover_six hYB6]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hYBα : img148 A Y YB = img148 A Y Yd := by
    refine Subgroup.eq_of_le_of_card_ge (img148_mono hYBYd) ?_
    have h1 := card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      h3YB
    rw [HJRes2.card_of_isTripleCover_six hYB6] at h1
    rw [HJRes2.card_of_isTripleCover_six hYd6]
    exact h1
  have hYdb : img148 A Y Yd ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hYBα]
    refine img148_mono (hYBC.trans (inf_le_inf_left _ (Subgroup.centralizer_le ?_)))
    exact Set.singleton_subset_iff.mpr hbB
  have hAJYd : img148 A Y A ⊓ img148 A Y J ≤ img148 A Y Yd := by
    intro x hx
    rw [hYdeq]
    exact Subgroup.mem_inf.mpr ⟨hx.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx.1 dα hdαA)⟩
  obtain ⟨j, hjAJ, hjd⟩ : ∃ j ∈ img148 A Y A ⊓ img148 A Y J, j ∉ Subgroup.zpowers dα := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hYd6
    have hx3' : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    have hxJ : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J := hYdJα x.2
    have hxd : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) * dα = dα * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYdC x.2)
    have hAx : img148 A Y A ≤ Subgroup.centralizer {(x : ↥(Y ⊔ A) ⧸ ker148 A Y)} := by
      rw [← hCD]
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp ha.2 x hxJ).symm
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hcon a ha)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.zpow_left hxd.symm k).eq
    have hxA : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y A := by
      refine hF3 _ ?_ hx3'
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAx ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon _ ⟨hxA, hxJ⟩)
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgd : (g : ↥(Y ⊔ A) ⧸ ker148 A Y) * dα = dα * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYdC g.2)
    change (g : ↥(Y ⊔ A) ⧸ ker148 A Y) * x = x * g
    rw [← hk]
    exact (Commute.zpow_right hgd k).eq
  have hjA : j ∈ img148 A Y A := hjAJ.1
  have hj3 : j ^ 3 = 1 := hA3 j hjA
  have hjYd : j ∈ img148 A Y Yd := hAJYd hjAJ
  have hjnc : ∃ y ∈ img148 A Y Yd, j * y ≠ y * j := by
    by_contra hcon
    push Not at hcon
    exact hjd (hYdZ j hjYd hcon)
  have hdj : dα * j = j * dα := hAab dα hdαA j hjA
  have h9 : Nat.card ↥(Subgroup.zpowers dα ⊔ Subgroup.zpowers j) = 9 :=
    card_zpowers_sup_zpowers_eq_nine hdj hdα3 hdα1 hj3 hjd
  have hle9 : Nat.card ↥(img148 A Y A ⊓ img148 A Y J) ≤ 9 :=
    card_le_nine_of_le_tripleCover hYd6 hYdp hAJYd (fun a ha b hb => hAab a ha.1 b hb.1)
      (fun a ha => hA3 a ha.1)
  have hdjle : Subgroup.zpowers dα ⊔ Subgroup.zpowers j ≤ img148 A Y A ⊓ img148 A Y J :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hdαA, hdJα⟩) (Subgroup.zpowers_le.mpr hjAJ)
  have hAJeq : img148 A Y A ⊓ img148 A Y J = Subgroup.zpowers dα ⊔ Subgroup.zpowers j :=
    (Subgroup.eq_of_le_of_card_ge hdjle (by rw [h9]; exact hle9)).symm
  have hAV : ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ img148 A Y Yd →
      j ∈ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro V hV hjV
    rw [← hCD]
    refine sup_le (fun a ha => Subgroup.centralizer_le_normalizer _ ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp ha.2 v (hYdJα (hV hv))
    · rw [hAJeq]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_))
        (Subgroup.zpowers_le.mpr hjV)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYdC (hV hv))
  have hYdX : img148 A Y Yd ≤ img148 A Y (deltaZero A (lB A) Y) :=
    le_of_forall_commutator_le_tripleCover hYd6 hYdp hjYd hj3 hjnc fun V hV hV3 hjV =>
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hjA)).trans
        (commutator_le_img148_deltaZero_of_point h142 hS hY hc.2.1 V (hV.trans hYdb) hV3
          (hAV V hV hjV))
  have hZle := img148_deltaZero_centPre148_le (A := A) (Y := Y) (J := J) (LB := lB A)
  have hZX : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      img148 A Y (deltaZero A (lB A) Y) := hZle.trans inf_le_left
  have hZC : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hZle.trans inf_le_right
  have hUV : ∀ u ∈ img148 A Y J, ∀ v ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)),
      u * v = v * u := fun u hu v hv => (Subgroup.mem_centralizer_iff.mp (hZC hv) u hu)
  have hint : img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ hZC).trans hJZ'.le)
  have hAN : img148 A Y A ≤ Subgroup.normalizer
      ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) : Subgroup _) :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer (Sec14.le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2)
  set H := img148 A Y (deltaZero A (lB A) Y) ⊓ img148 A Y J with hHdef
  have hHJ : H ≤ img148 A Y J := inf_le_right
  have hYdH : img148 A Y Yd ≤ H := le_inf hYdX hYdJα
  have hXeqH : img148 A Y (deltaZero A (lB A) Y) =
      H ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hZX)
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_commute hUV (hXle hx)
    have huX : u ∈ img148 A Y (deltaZero A (lB A) Y) := by
      have := (img148 A Y (deltaZero A (lB A) Y)).mul_mem hx
        ((img148 A Y (deltaZero A (lB A) Y)).inv_mem (hZX hv))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem_sup ⟨huX, hu⟩ hv
  have hHH : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
  have hHp : Group.IsPerfect ↥H := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm hHH ?_
    have hHHJ : ⁅H, H⁆ ≤ img148 A Y J := hHH.trans hHJ
    have hXT : img148 A Y (deltaZero A (lB A) Y) ≤
        ⁅H, H⁆ ⊔ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
      refine img148_deltaZero_le_of_hyperplanes_of_le hA le_rfl fun E _ R hR hRE => ?_
      have hRY : R ≤ Y := hRE.trans inf_le_left
      have hRM : R ≤ Y ⊔ A := hRY.trans le_sup_left
      have hRX : img148 A Y R ≤ img148 A Y (deltaZero A (lB A) Y) :=
        img148_mono (le_deltaZero hR hRY)
      have hReq : img148 A Y R = ⁅img148 A Y R, img148 A Y A⁆ := by
        rw [← HJRes2.img148_commutator_eq hRM le_sup_right, ← hR.2]
      rw [hReq, Subgroup.commutator_le]
      intro q hq a ha
      obtain ⟨h, hh, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute (U := H)
        (V := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)))
        (fun u hu v hv => hUV u (hHJ hu) v hv) (by rw [← hXeqH]; exact hRX hq)
      obtain ⟨c', hc', u', hu', rfl⟩ := exists_mul_of_mem_sup_of_commute
        (U := img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
        (V := img148 A Y A ⊓ img148 A Y J)
        (fun u hu v hv => hAab u hu.1 v hv.1) (by rw [hCD]; exact ha)
      have hu'H : u' ∈ H := hYdH (hAJYd hu')
      set a' := c' * u' with ha'
      have hw : z * a' * z⁻¹ * a'⁻¹ ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := by
        have h1 : a' * z⁻¹ * a'⁻¹ ∈ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp
            (Subgroup.inv_mem _ hz)
        have h2 := Subgroup.mul_mem _ hz h1
        simpa [mul_assoc] using h2
      have hcu : c' * u' * h⁻¹ * u'⁻¹ * c'⁻¹ = u' * h⁻¹ * u'⁻¹ := by
        have hm : u' * h⁻¹ * u'⁻¹ ∈ img148 A Y J :=
          (img148 A Y J).mul_mem ((img148 A Y J).mul_mem (hHJ hu'H)
            ((img148 A Y J).inv_mem (hHJ hh))) ((img148 A Y J).inv_mem (hHJ hu'H))
        have hcm := Subgroup.mem_centralizer_iff.mp hc'.2 _ hm
        calc c' * u' * h⁻¹ * u'⁻¹ * c'⁻¹ = c' * (u' * h⁻¹ * u'⁻¹) * c'⁻¹ := by group
          _ = (u' * h⁻¹ * u'⁻¹) * c' * c'⁻¹ := by rw [← hcm]
          _ = u' * h⁻¹ * u'⁻¹ := by group
      have hwh : (z * a' * z⁻¹ * a'⁻¹) * h = h * (z * a' * z⁻¹ * a'⁻¹) :=
        (hUV h (hHJ hh) _ hw).symm
      have hkey : ⁅h * z, a'⁆ = (z * a' * z⁻¹ * a'⁻¹) * ⁅h, u'⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc h * z * a' * (h * z)⁻¹ * a'⁻¹
            = h * (z * a' * z⁻¹ * a'⁻¹) * (a' * h⁻¹ * a'⁻¹) := by group
          _ = (z * a' * z⁻¹ * a'⁻¹) * h * (a' * h⁻¹ * a'⁻¹) := by rw [← hwh]
          _ = (z * a' * z⁻¹ * a'⁻¹) * h * (u' * h⁻¹ * u'⁻¹) := by
              rw [ha', ← hcu]; group
          _ = (z * a' * z⁻¹ * a'⁻¹) * (h * u' * h⁻¹ * u'⁻¹) := by group
      rw [hkey]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw)
        (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hh hu'H))
    intro x hx
    obtain ⟨k, hk, z, hz, hkz⟩ := exists_mul_of_mem_sup_of_commute (U := ⁅H, H⁆)
      (V := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)))
      (fun u hu v hv => hUV u (hHHJ hu) v hv) (hXT hx.1)
    have hz1 : z = 1 := by
      have hzJ : z ∈ img148 A Y J := by
        have : z = k⁻¹ * x := by rw [hkz]; group
        rw [this]
        exact (img148 A Y J).mul_mem ((img148 A Y J).inv_mem (hHHJ hk)) hx.2
      have : z ∈ img148 A Y J ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) := ⟨hzJ, hz⟩
      rwa [hint, Subgroup.mem_bot] at this
    rw [hkz, hz1, mul_one]
    exact hk
  have hHcase : H = img148 A Y Yd ∨ H = img148 A Y J := by
    set z' : ↥(img148 A Y J) := ⟨dα, hdJα⟩ with hz'
    have hz'1 : z' ≠ 1 := fun h => hdα1 (congrArg Subtype.val h)
    have hz'3 : z' ^ 3 = 1 := Subtype.ext (by simpa [hz'] using hdα3)
    have hCmap : (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))).map
        (img148 A Y J).subtype = img148 A Y Yd := by
      rw [hYdeq]
      ext g
      constructor
      · rintro ⟨g', hg', rfl⟩
        have hg'' : g' * z' = z' * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'
        exact Subgroup.mem_inf.mpr ⟨g'.2,
          Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg'')⟩
      · intro hg
        obtain ⟨hgJ, hgc⟩ := Subgroup.mem_inf.mp hg
        have hgc' : g * dα = dα * g := Subgroup.mem_centralizer_singleton_iff.mp hgc
        refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hgc')
    have hC27 : 27 ∣ Nat.card (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))) := by
      have h1 : Nat.card ((Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))).map
          (img148 A Y J).subtype) =
          Nat.card (Subgroup.centralizer ({z'} : Set ↥(img148 A Y J))) :=
        Subgroup.card_map_of_injective (img148 A Y J).subtype_injective
      rw [hCmap, HJRes2.card_of_isTripleCover_six hYd6] at h1
      rw [← h1]
      norm_num
    haveI := hHp
    have hMp : Group.IsPerfect ↥(H.subgroupOf (img148 A Y J)) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hHJ).symm.toMonoidHom) (MulEquiv.surjective _)
    have hCM : Subgroup.centralizer ({z'} : Set ↥(img148 A Y J)) ≤
        H.subgroupOf (img148 A Y J) := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      exact hYdH (hCmap ▸ ⟨g, hg, rfl⟩)
    rcases hK _ ⟨φ⟩ z' hz'1 hz'3 hC27 _ hMp hCM with h | h
    · left
      rw [← hCmap, ← h, Subgroup.map_subgroupOf_eq_of_le hHJ]
    · right
      exact le_antisymm hHJ (Subgroup.subgroupOf_eq_top.mp h)
  have hC3 : Nat.card ↥(img148 A Y A ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 := by
    have hCJ : (img148 A Y A ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ⊓
          (img148 A Y A ⊓ img148 A Y J) = ⊥ := by
      rw [eq_bot_iff, ← hJZ']
      exact fun x hx => ⟨hx.2.2, hx.1.2⟩
    have h1 := card_sup_eq_mul_of_commute
      (U := img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
      (V := img148 A Y A ⊓ img148 A Y J) (fun u hu v hv => hAab u hu.1 v hv.1) hCJ
    rw [hCD, hAE.2, hAJeq, h9] at h1
    omega
  have hAZC : img148 A Y A ⊓ img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ≤
      img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun x hx => ⟨hx.1, hZC hx.2⟩
  have hEZ : img148 A Y A ⊓ img148 A Y J ≤
      Subgroup.centralizer ((img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) :
        Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hUV x hx.2 z hz).symm
  have hZtype : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) (centPre148 A Y J))) ≃*
        alternatingGroup (Fin 5)) := by
    rcases centPre148_type_of_hj h134 h48 hS hY ih hB hc hJY hAJ hJc h3Jα with
      h1 | hZ2 | hZ6 | hZ5 | h36
    · exact Or.inl h1
    · obtain ⟨ψ⟩ := hZ2
      exact (false_of_j2_of_le hAab hA3 hF3 hC3 hAZC hAN ψ).elim
    · exact (false_of_isTripleCover_of_le hAp hF3 hC3 hCD hEZ hAZC hAN hZ6).elim
    · exact Or.inr hZ5
    · rcases h36 with h3' | h6'
      · exact absurd h3' hres1.1
      · exact absurd h6' hres1.2
  have hbYd := HJRes2.le_centralizer_of_theta hYdM rfl hYdθ hbA hbc.2
  have hXH : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) = ⊥ →
      img148 A Y (deltaZero A (lB A) Y) = H := fun h0 => by rw [hXeqH, h0, sup_bot_eq]
  rcases hHcase with hHYd | hHJα <;> rcases hZtype with hZ1 | hZ5
  ·
    have hXYd : img148 A Y (deltaZero A (lB A) Y) = img148 A Y Yd := (hXH hZ1).trans hHYd
    refine Or.inl (HJRes2.case148Two_of_le_centralizer_b hS hY hB hc
      (fun hb => by rw [hXYd]; exact hbYd) (Or.inl (by rw [hXYd]; exact hYd6)))
  ·
    obtain ⟨φZ⟩ := hZ5
    set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
    set Xα := img148 A Y (deltaZero A (lB A) Y) with hXα
    have hXeq : Xα = img148 A Y Yd ⊔ Zα := by rw [hXeqH, hHYd]
    have h3Z : 3 ∣ Nat.card Zα := by
      rw [Nat.card_congr φZ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
      norm_num
    have hne' : ∀ e ∈ img148 A Y A,
        e ∉ Subgroup.centralizer ((Zα : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ∃ k ∈ Zα, e * k ≠ k * e := by
      intro e he heZ
      by_contra hcon
      push Not at hcon
      apply heZ
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcon k hk).symm
    have hfix : ∀ e ∈ img148 A Y A,
        e ∉ Subgroup.centralizer ((Zα : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
        ∀ x ∈ Zα, x * e = e * x → Nat.Coprime (orderOf x) 3 → x = 1 := by
      intro e he heZ x hx hxe hx3
      have hx3' := pow_three_eq_one_of_commute_a5 φZ (hAN he) (hA3 e he) (hne' e he heZ)
        hx hxe
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hx3 (orderOf_dvd_of_pow_eq_one hx3'))
    have hdZ := alpha148_mem_centralizer_of_contrib h134 h48 hS hB hc hdA centPre148_le h3Z hfix
    have hXd : Xα ≤ Subgroup.centralizer {dα} := by
      rw [hXeq]
      refine sup_le hYdC fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hdZ x hx
    have hYdZ' : ∀ u ∈ img148 A Y Yd, ∀ v ∈ Zα, u * v = v * u :=
      fun u hu v hv => hUV u (hYdJα hu) v hv
    have hint' : img148 A Y Yd ⊓ Zα = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ hYdJα).trans hint.le)
    have hZX' : Zα ≤ Xα := hXeq ▸ le_sup_right
    have hYdX' : img148 A Y Yd ≤ Xα := hXeq ▸ le_sup_left
    have hXN : ∀ {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}, (T = Zα ∨ T = img148 A Y Yd) →
        Xα ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      intro T hT
      rw [hXeq]
      rcases hT with rfl | rfl
      · refine sup_le (fun u hu => Subgroup.centralizer_le_normalizer _ ?_)
          Subgroup.le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hYdZ' u hu v hv).symm
      · refine sup_le Subgroup.le_normalizer (fun v hv => Subgroup.centralizer_le_normalizer _ ?_)
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact hYdZ' u hu v hv
    have htype : IsA6CoverTimesA5 ↥Xα := by
      refine ⟨(img148 A Y Yd).subgroupOf Xα, Zα.subgroupOf Xα,
        (Subgroup.normal_subgroupOf_iff_le_normalizer hYdX').mpr (hXN (Or.inr rfl)),
        (Subgroup.normal_subgroupOf_iff_le_normalizer hZX').mpr (hXN (Or.inl rfl)), ?_, ?_,
        KFacts.KS14.isTripleCover_congr (Subgroup.subgroupOfEquivOfLe hYdX').symm hYd6,
        ⟨(Subgroup.subgroupOfEquivOfLe hZX').trans φZ⟩⟩
      · rw [eq_bot_iff]
        intro x hx
        have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y Yd ⊓ Zα :=
          ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
        rw [hint', Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (Subtype.ext h1)
      · rw [← Subgroup.subgroupOf_sup hYdX' hZX']
        exact Subgroup.subgroupOf_eq_top.mpr hXeq.le
    exact Or.inr (Or.inl (HJRes2.case148Three_of_le_centralizer hS hY hc.2.1 hLb
      (Item148HJ.j2_of_isLBConfig hc) hdA hd1 hc.2.2.2.2 hXd
      (Or.inr (Or.inr (Or.inl htype)))))
  ·
    exfalso
    have hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J := (hXH hZ1).trans hHJα
    obtain ⟨a, ha, haΩ, hac⟩ := hres2 hXJ
    have hall := allPointsHJ_of_isLBConfig h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
      hS hc hB
    obtain ⟨La, hLa, hLa2⟩ := hall a haΩ
    exact hexcl hXJ a ha haΩ ⟨La, hLa, hLa2⟩ hac
  ·
    obtain ⟨φZ⟩ := hZ5
    have hJX : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := hHJα ▸ inf_le_left
    have hXeq : img148 A Y (deltaZero A (lB A) Y) =
        img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ⊔ img148 A Y J := by
      rw [hXeqH, hHJα]
      exact sup_comm _ _
    have hint' : img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) ⊓ img148 A Y J = ⊥ := by
      rw [inf_comm]; exact hint
    exact Or.inr (Or.inr ⟨nonempty_mulEquiv_prod_of_commute_of_equiv
      (fun u hu v hv => (hUV v hv u hu).symm) hint' hXeq φZ φ,
      ⟨b, Lb, hc.2.1, hLb, Item148HJ.j2_of_isLBConfig hc⟩, hres3 hJX ⟨φZ⟩⟩)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
