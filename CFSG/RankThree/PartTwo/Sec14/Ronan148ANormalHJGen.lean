module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJA5Two
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJA6Two
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148 Ronan148M

variable {G : Type} [Group G] [Finite G]

theorem deltaZero_eq_of_le148 {A : Subgroup G} {LB : Subgroup G → Subgroup G} {U Y : Subgroup G}
    (hUY : U ≤ Y) (hXU : deltaZero A LB Y ≤ U) : deltaZero A LB U = deltaZero A LB Y :=
  le_antisymm (Sec14.deltaZero_mono hUY)
    (sSup_le fun _ hQ => le_deltaZero hQ.1 ((le_deltaZero hQ.1 hQ.2).trans hXU))

section Certificates


theorem img148_le_normalizer_of_member148 {A Y : Subgroup G} (hY : Y ∈ scriptY A)
    [(ker148 A Y).Normal] (ih : Ind148 A (lB A) Y) {U : Subgroup G} (hUY : U ≤ Y) (hUne : U ≠ Y)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hXU : deltaZero A (lB A) Y ≤ U) :
    deltaZero A (lB A) U = deltaZero A (lB A) Y ∧
      img148 A Y U ≤ Subgroup.normalizer ((img148 A Y (deltaZero A (lB A) Y) ⊔
        img148 A Y (pPrimeCoreOf 3 U) : Subgroup _) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
      img148 A Y U ≤
        Subgroup.normalizer (img148 A Y (pPrimeCoreOf 3 U) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
      ¬ 3 ∣ Nat.card (img148 A Y (pPrimeCoreOf 3 U)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : U ∈ scriptY A := ⟨fun h => hY.1 (top_le_iff.mp (h ▸ hUY)), hAU⟩
  have hlt : Nat.card U < Nat.card Y := Subgroup.card_lt_of_lt (lt_of_le_of_ne hUY hUne)
  have hΔ := deltaZero_eq_of_le148 (A := A) (LB := lB A) hUY hXU
  have hUM : U ≤ Y ⊔ A := hUY.trans le_sup_left
  have hNU := (map_mk_normal_iff (deltaZero_le U)).mp (ih U hU hlt).1
  refine ⟨hΔ, ?_, img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 U),
    Item148PtRes.not_three_dvd_card_img148
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 U))⟩
  have h1 := img148_le_normalizer (A := A) (Y := Y) hNU
  rwa [img148_sup ((deltaZero_le U).trans hUM) ((pPrimeCoreOf_le 3 U).trans hUM), hΔ] at h1

theorem false_of_conj_le_member148 {A Y : Subgroup G} (hY : Y ∈ scriptY A) [(ker148 A Y).Normal]
    (ih : Ind148 A (lB A) Y) {U : Subgroup G} (hUY : U ≤ Y) (hUne : U ≠ Y)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hXU : deltaZero A (lB A) Y ≤ U)
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hxU : x ∈ img148 A Y U)
    {K : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hK : IsComponent K) (h3K : 3 ∣ Nat.card K)
    (hKx : K ≤ (img148 A Y (deltaZero A (lB A) Y)).map (MulAut.conj x).toMonoidHom)
    (hKC : K ≤ Subgroup.centralizer
      (img148 A Y (deltaZero A (lB A) Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) : False := by
  set X := img148 A Y (deltaZero A (lB A) Y) with hXdef
  set O := img148 A Y (pPrimeCoreOf 3 U) with hOdef
  obtain ⟨-, hN, hON, hO3⟩ := img148_le_normalizer_of_member148 hY ih hUY hUne hAU hXU
  have hxN := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hxU)
  have hKXO : K ≤ X ⊔ O := by
    rw [← hxN]
    exact hKx.trans (Subgroup.map_mono le_sup_left)
  have hXU' : X ≤ img148 A Y U := img148_mono hXU
  have hKU : K ≤ img148 A Y U := by
    intro k hk
    obtain ⟨w, hw, rfl⟩ := hKx hk
    exact (img148 A Y U).mul_mem ((img148 A Y U).mul_mem hxU (hXU' hw))
      ((img148 A Y U).inv_mem hxU)
  have hOU : O ≤ img148 A Y U := img148_mono (pPrimeCoreOf_le 3 U)
  have hOn : (O.subgroupOf (img148 A Y U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOU).mpr hON
  have hKO : K ≤ Subgroup.centralizer (O : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rcases CFSG.LocalCores.component_normal_subgroup
        (CFSG.LocalCores.component_overgroup hK hKU) hOn with h | h
    · exfalso
      have hKO' : K ≤ O := CFSG.LocalCores.le_of_subgroupOf_le hKU h
      exact hO3 (h3K.trans (Subgroup.card_dvd_of_le hKO'))
    · have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hKU h
      rw [inf_eq_left.mpr hOU] at h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hKK : K ≤ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := fun k hk =>
    Subgroup.centralizer_le hKXO (mem_centralizer_sup (hKC hk) (hKO hk))
  have hcomm : IsMulCommutative ↥K := Subgroup.le_centralizer_iff_isMulCommutative.mp hKK
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isMulCommutative ↥K hcomm

@[expose] def Step148NormalHJA5Three : Prop :=
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
          ∀ x ∈ img148 A Y Y, (K = (img148 A Y J).map (MulAut.conj x).toMonoidHom ∨
            K = (img148 A Y (deltaZero A (lB A) (centPre148 A Y J))).map
              (MulAut.conj x).toMonoidHom) →
          (∀ U : Subgroup G, U ≤ Y → A ≤ Subgroup.normalizer (U : Set G) →
            deltaZero A (lB A) Y ≤ U → x ∈ img148 A Y U → U = Y) →
          K ≤ Subgroup.centralizer
            (img148 A Y (deltaZero A (lB A) Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          img148 A Y A ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          ∀ k₀ ∈ K, k₀ ∈ img148 A Y A → k₀ ≠ 1 →
          img148 A Y A ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
              Subgroup.zpowers k₀ = img148 A Y A →
          (∀ (a : G) (ha : a ∈ A), Subgroup.zpowers a ∈ omegaA A →
            alpha148 A Y a ha ∉ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) →
          False

theorem step148NormalHJA5Two_of_three (hThree : Step148NormalHJA5Three) :
    Step148NormalHJA5Two := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hXeq hZ15 h12 K hKc hK5 hKx hKX hAK k₀ hk₀K hk₀A
    hk₀1 hAeqK hnoPt
  let := ker148_normal hY.2
  obtain ⟨x, hxY, hKx⟩ := hKx
  by_cases hgen : ∀ U : Subgroup G, U ≤ Y → A ≤ Subgroup.normalizer (U : Set G) →
      deltaZero A (lB A) Y ≤ U → x ∈ img148 A Y U → U = Y
  · exact hThree G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
      hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ5 hXeq hZ15 h12 K hKc hK5 x hxY hKx hgen
      hKX hAK k₀ hk₀K hk₀A hk₀1 hAeqK hnoPt
  push Not at hgen
  obtain ⟨U, hUY, hAU, hXU, hxU, hUne⟩ := hgen
  obtain ⟨φK⟩ := hK5
  have h3K : 3 ∣ Nat.card K := by
    rw [Nat.card_congr φK.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num
  have hKle : K ≤ (img148 A Y (deltaZero A (lB A) Y)).map (MulAut.conj x).toMonoidHom := by
    rcases hKx with rfl | rfl
    · exact Subgroup.map_mono (le_sup_left.trans hXeq.symm.le)
    · exact Subgroup.map_mono (le_sup_right.trans hXeq.symm.le)
  exact false_of_conj_le_member148 hY ih hUY hUne hAU hXU hxU hKc h3K hKle hKX

@[expose] def Step148NormalHJA6One3 : Prop :=
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
        (omegaA A).ncard ≠ 12 →
        ∀ (y : G) (hy : y ∈ Y),
          (∀ U : Subgroup G, U ≤ Y → A ≤ Subgroup.normalizer (U : Set G) →
            deltaZero A (lB A) Y ≤ U → y ∈ U → U = Y) →
          QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) ∈
            Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))

theorem step148NormalHJA6One2_of_three (hThree : Step148NormalHJA6One3) :
    Step148NormalHJA6One2 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ h12 y hy
  let := ker148_normal hY.2
  by_cases hgen : ∀ U : Subgroup G, U ≤ Y → A ≤ Subgroup.normalizer (U : Set G) →
      deltaZero A (lB A) Y ≤ U → y ∈ U → U = Y
  · exact hThree G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
      hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ h12 y hy hgen
  push Not at hgen
  obtain ⟨U, hUY, hAU, hXU, hyU, hUne⟩ := hgen
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hJcard : Nat.card ↥(img148 A Y J) = 1080 :=
    Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hJ6
  have h3J' : 3 ∣ Nat.card ↥(img148 A Y J) := by rw [hJcard]; norm_num
  have h3J : 3 ∣ Nat.card J := h3J'.trans (card_img148_dvd hJM)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  by_contra hN
  set x := QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) with hx
  have hne : (img148 A Y J).map (MulAut.conj x).toMonoidHom ≠ img148 A Y J := by
    intro heq'
    apply hN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq'
  have hKc : IsComponent ((img148 A Y J).map (MulAut.conj x).toMonoidHom) :=
    Res2LBal.isComponent_conj hJc x
  have h3K : 3 ∣ Nat.card ↥((img148 A Y J).map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact h3J'
  have hxU : x ∈ img148 A Y U := mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_left hy, hyU, rfl⟩
  refine false_of_conj_le_member148 hY ih hUY hUne hAU hXU hxU hKc h3K (by rw [hXJ]) ?_
  rw [hXJ]
  exact fun _ hk => Res2LBal.mem_centralizer_of_mem_of_ne hJc hKc hne.symm hk

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
