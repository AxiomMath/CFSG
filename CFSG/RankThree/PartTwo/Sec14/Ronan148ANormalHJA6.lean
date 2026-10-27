module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJInner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148VA6Z
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormal
import CFSG.RankThree.PartTwo.Sec14.Ronan148AFrame

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148
  Ronan148M
open Equiv

variable {G : Type} [Group G] [Finite G]

theorem exists_component_part148 {A Y : Subgroup G} [(ker148 A Y).Normal]
    {J Z : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hZ : Nonempty (↥Z ≃* alternatingGroup (Fin 5)) ∨
      (Sec4.IsTripleCover ↥Z (alternatingGroup (Fin 6)) ∧ (Subgroup.center ↥Z).map Z.subtype ≤ J)) :
    ∃ D : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), IsQuasisimple ↥D ∧ D ≤ Z ∧ J ⊔ Z = J ⊔ D ∧
      Subgroup.normalizer (Z : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
        Subgroup.normalizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
      ∃ u ∈ D, u ^ 3 = 1 ∧ u ∉ Subgroup.centralizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  rcases hZ with hψ | ⟨hT, hZJ⟩
  ·
    obtain ⟨ψ⟩ := hψ
    have hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hZs : IsSimpleGroup ↥Z := MulEquiv.isSimpleGroup ψ
    set σ : alternatingGroup (Fin 5) := ⟨swap 0 1 * swap 0 2,
      Perm.mem_alternatingGroup.mpr (by decide)⟩ with hσ
    set τ : alternatingGroup (Fin 5) := ⟨swap 0 3 * swap 0 4,
      Perm.mem_alternatingGroup.mpr (by decide)⟩ with hτ
    have hστ : σ * τ ≠ τ * σ := fun h0 => by
      have := congrArg Subtype.val h0
      revert this
      decide
    have hnc : ∃ a b : ↥Z, a * b ≠ b * a := ⟨ψ.symm σ, ψ.symm τ, fun h0 => hστ (by
      have := congrArg ψ h0
      simpa using this)⟩
    obtain ⟨hq, hZc⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
    refine ⟨Z, hq, le_rfl, rfl, le_rfl, (ψ.symm σ : ↥(Y ⊔ A) ⧸ ker148 A Y), (ψ.symm σ).2, ?_, ?_⟩
    · have h3 : σ ^ 3 = 1 := Subtype.ext (by decide)
      have := congrArg (fun w : ↥Z => (w : ↥(Y ⊔ A) ⧸ ker148 A Y)) (map_pow ψ.symm σ 3)
      simp only [h3, map_one] at this
      simpa using this.symm
    · intro hC
      have hcen : ψ.symm σ ∈ Subgroup.center ↥Z := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC g g.2)
      rw [hZc, Subgroup.mem_bot] at hcen
      have h1 : σ = 1 := by simpa using congrArg ψ hcen
      have := congrArg Subtype.val h1
      revert this
      decide
  ·
    obtain ⟨hq, hsup, u, hu, hu3, huC⟩ := quasisimple_commutator_of_isTripleCover_A6 hT
    set D := (commutator ↥Z).map Z.subtype with hD
    have hinj : Function.Injective Z.subtype := Z.subtype_injective
    have hDeq : D = ⁅Z, Z⁆ := by
      rw [hD, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hDZ : D ≤ Z := Subgroup.map_subtype_le _
    refine ⟨D, ?_, hDZ, ?_, ?_, (u : ↥(Y ⊔ A) ⧸ ker148 A Y), ⟨u, hu, rfl⟩,
      by simpa using congrArg Subtype.val hu3, ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((commutator ↥Z).equivMapOfInjective Z.subtype hinj) hq
    · refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left (hDZ.trans le_sup_right))
      intro z hz
      have hz' : (⟨z, hz⟩ : ↥Z) ∈ (commutator ↥Z ⊔ Subgroup.center ↥Z : Subgroup ↥Z) := by
        rw [hsup]
        exact Subgroup.mem_top _
      rw [← SetLike.mem_coe, Subgroup.mul_normal] at hz'
      obtain ⟨k, hk, w, hw, hkw⟩ := hz'
      have hzkw : z = (k : ↥(Y ⊔ A) ⧸ ker148 A Y) * (w : ↥(Y ⊔ A) ⧸ ker148 A Y) := by
        have := congrArg Subtype.val hkw
        simpa using this.symm
      rw [hzkw]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨k, hk, rfl⟩)
        (Subgroup.mem_sup_left (hZJ ⟨w, hw, rfl⟩))
    · intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
      rw [hDeq, Subgroup.map_commutator, hg]
    · intro hC
      apply huC
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC _ ⟨k, hk, rfl⟩)

section Certificates

@[expose] def Step148NormalHJA6One : Prop :=
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
        Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
        img148 A Y (deltaZero A (lB A) Y) = img148 A Y J →
        ∀ (y : G) (hy : y ∈ Y),
          QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) ∈
            Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))

set_option maxHeartbeats 1000000 in
theorem step148NormalHJA6_of_one
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) (hOne : Step148NormalHJA6One) : Step148NormalHJA6 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨η⟩ := hη
  have hYd6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr η.symm hJ6
  obtain ⟨hYB6, hdYB, hbc⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hYd6
  obtain ⟨hXeq, hZt⟩ := Ronan148V.a6InnerStructure_holds h142 h134 h48 h143 G A c L hS Y hY hs ih B
    hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ hJ6
    hYB6 hdYB hbc hdA
  have hXY : deltaZero A (lB A) Y ≤ Y := sSup_le fun _ hQ => hQ.2
  set Zα := img148 A Y (deltaZero A (lB A) (centPre148 A Y J)) with hZα
  rcases hZt with hZ1 | hZt
  ·
    have hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J := by
      rw [hXeq, hZ1, sup_bot_eq]
    exact map_normal_of_img148_eq hXY hXJ (hOne G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB
      htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq ⟨η⟩ hJ6 hXJ)
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hdJ : alpha148 A Y d hdA ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  obtain ⟨D, hDq, hDZ, hJZD, hND, u, hu, hu3, huC⟩ := exists_component_part148
    (J := img148 A Y J) (Z := Zα) (by
      rcases hZt with hZ5 | ⟨hT, hcen⟩
      · exact Or.inl hZ5
      · refine Or.inr ⟨hT, ?_⟩
        rw [hcen, Subgroup.zpowers_le]
        exact hdJ)
  have hJcard : Nat.card ↥(img148 A Y J) = 1080 :=
    Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hJ6
  have h3J' : 3 ∣ Nat.card ↥(img148 A Y J) := by rw [hJcard]; norm_num
  have h3J : 3 ∣ Nat.card J := h3J'.trans (card_img148_dvd hJM)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  have hY₁ : centPre148 A Y J ∈ scriptY A := centPre148_mem_scriptY hY hAJ
  have hcore : pPrimeCoreOf 3 (centPre148 A Y J) = pPrimeCoreOf 3 Y :=
    Ronan148J.pPrimeCoreOf_centPre148_eq_of_isComponent hY.2 hJY hJc h3J'
  have : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hJne : img148 A Y J ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hJcard
    norm_num at hJcard
  have hlt : Nat.card (centPre148 A Y J) < Nat.card Y :=
    card_centPre148_lt hJY (Ronan148M.exists_ne_comm_of_isPerfect hJp hJne)
  have h148₁ : Item148At A (lB A) (centPre148 A Y J) hY₁ := ih _ hY₁ hlt
  letI := ker148_normal hY₁.2
  have hX1Y₁ : deltaZero A (lB A) (centPre148 A Y J) ≤ centPre148 A Y J :=
    sSup_le fun _ hQ => hQ.2
  have hN₁ := img148_le_normalizer_of_map_normal (A := A) hX1Y₁ h148₁.1
  have hY₁Z : img148 A Y (centPre148 A Y J) ≤ Subgroup.normalizer (Zα : Set _) := by
    rw [hZα, ← map_img148_compare148 hcore.le le_sup_left,
      ← map_img148_compare148 hcore.le (hX1Y₁.trans le_sup_left)]
    exact (Subgroup.map_mono hN₁).trans (Subgroup.le_normalizer_map _)
  have hY₁eq := Ronan148J.img148_centPre148_eq (A := A) (Y := Y) (J := J)
  have hZY₁ : Zα ≤ img148 A Y (centPre148 A Y J) := img148_mono hX1Y₁
  have hDC : D ≤ img148 A Y Y ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    hY₁eq ▸ hDZ.trans hZY₁
  have hDc : IsComponent D := isComponent_of_le_centralizer_A6148 hS hY.2 hJc hJ6 hDq hDC
    (hY₁eq ▸ hY₁Z.trans hND)
  have hDJ : D ≠ img148 A Y J := by
    intro hDJ
    apply huC
    rw [hDJ]
    exact (hDC (hDJ ▸ hu)).2
  have hXeq' : img148 A Y (deltaZero A (lB A) Y) =
      img148 A Y (J ⊔ deltaZero A (lB A) (centPre148 A Y J)) := by
    rw [img148_sup hJM ((hX1Y₁.trans centPre148_le).trans le_sup_left), hXeq]
  refine map_normal_of_img148_eq hXY hXeq' fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    img148_sup hJM ((hX1Y₁.trans centPre148_le).trans le_sup_left), ← hZα, hJZD]
  exact map_conj_sup_eq_of_two_components_A6148 hS hJc hJ6 hDc hDJ hu hu3 huC _

theorem step148NormalHJA6E_of_one
    (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) (hOne : Step148NormalHJA6One) : Step148NormalHJA6E :=
  fun G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 _ _ _ _ =>
    step148NormalHJA6_of_one h142 h134 h48 h143 hOne G A c L hS Y hY hs ih hcases h1 B hB hnot YB
      hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
