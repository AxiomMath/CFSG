module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4GenLift
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4GenPerm
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.LiebeckY4.Gen
open scoped commutatorElement

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

private theorem type_facts {Yt : Type*} [Group Yt] [Finite Yt]
    (htype : Sec4.IsTripleCover Yt (alternatingGroup (Fin 6)) ∨
      Nonempty (Yt ≃* alternatingGroup (Fin 5))) :
    (∀ z ∈ Subgroup.center Yt, z ^ 3 = 1) ∧ 3 ∣ Nat.card Yt := by
  rcases htype with ⟨hc3, -⟩ | he
  · refine ⟨fun z hz => ?_, hc3 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center Yt)⟩
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center Yt) hz
    rw [hc3] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  · obtain ⟨e⟩ := he
    obtain ⟨-, hc5, -⟩ := Item148HJ.alternatingGroup_five_facts
    have hmap := Subgroup.map_center_eq e
    rw [hc5] at hmap
    have hcb : Subgroup.center Yt = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [hcb, Subgroup.mem_bot] at hz
      rw [hz, one_pow]
    · rw [Nat.card_congr e.toEquiv, card_alt_five]
      norm_num

theorem step148HJYBGen_holds :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → ∀ M ∈ scriptY A, ¬ Group.IsSolvable ↥M →
      ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) M B →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      ∀ YB ∈ thetaComponentsIn (M ⊓ Subgroup.centralizer (B : Set G)),
        (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
        deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G)) ≤
          pPrimeCoreOf 3 (M ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
        YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
          ¬ IsMulCommutative ↥(((deltaZero A (lB A) YB).subgroupOf M).map
              (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) ∧
            ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (deltaZero A (lB A) YB)) := by
  intro G _ _ A c L h M hM hMs B hB hnot b d Lb hc YB hYB htype hle hYBle
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (B : Set G) with hCdef
  set N := pPrimeCoreOf 3 C with hNdef
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  have hJC : J ≤ C := Item148HJ.residual_le_centralizer hc
  have hJN : C ≤ Subgroup.normalizer (J : Set G) :=
    Item148HJ.centralizer_le_normalizer_residual h hc
  have hlB : lB A B = J := Item148HJ.lB_eq_residual h hB hc
  obtain ⟨_, _, hq, hZ, _, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  obtain ⟨a₀, ha₀, ha₀d, ha₀B⟩ := Item148HJ.exists_mem_not_mem_zpowers h hB hc
  have ha₀J : a₀ ∈ J := Item148HJ.inf_le_residual h hB hc ha₀
  obtain ⟨j₀, hj₀J, hj₀⟩ := Item148HJ.exists_commutator_not_mem h hB hc ha₀ ha₀d
  have hD := h.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hB.1 hy) x hx
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 C
  have hJNθ : ∀ x ∈ J, x ∈ N → x ∈ inSubgroup (aschbacherSolvableCore 3) Lb := by
    intro x hxJ hxN
    have hMn : (N.subgroupOf J).Normal :=
      Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
        (Late.le_normalizer_inf (hJC.trans hCN) Subgroup.le_normalizer)
    have hM3 : ¬ 3 ∣ Nat.card (N.subgroupOf J) := fun h3 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 (h3.trans (by
        rw [← Subgroup.card_map_of_injective J.subtype_injective, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left))
    exact (Item148HJ.mem_ker_resProj ⟨x, hxJ⟩).mp
      (Item148HJ.le_ker_of_normal _ hq hZ hMn hM3 (Subgroup.mem_subgroupOf.mpr hxN))
  have hθN : ∀ x ∈ J, x ∈ inSubgroup (aschbacherSolvableCore 3) Lb → x ∈ N := by
    intro x hxJ hxθ
    have hS := Item148HJ.sec14Std_of_isLBConfig h hc
    have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
    have hCLb : C ≤ Subgroup.normalizer (Lb : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)).trans
        (centralizer_le_normalizer_of_j2 hS (Item148HJ.j2_of_isLBConfig hc))
    have hθn : C ≤ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore 3) Lb : Subgroup G) : Set G) :=
      hCLb.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        Lb _ (solvable_prime_complement_core_characterization Nat.prime_three).2.1)
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
    have hle : inSubgroup (aschbacherSolvableCore 3) Lb ⊓ C ≤ N :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hθn Subgroup.le_normalizer)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hθ3 (h3.trans (by
          refine (Subgroup.card_dvd_of_le inf_le_left).trans ?_
          rw [inSubgroup, Subgroup.card_map_of_injective Lb.subtype_injective])))
    exact hle ⟨hxθ, hJC hxJ⟩
  set N₀ := CFSG.pPrimeCore 3 ↥C with hN₀def
  set π := QuotientGroup.mk' N₀ with hπdef
  set JH := J.subgroupOf C with hJHdef
  set 𝔍 := JH.map π with h𝔍def
  have hNsub : N.subgroupOf C = N₀ := by
    rw [hNdef, pPrimeCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hsup : (N ⊔ J).subgroupOf C = N₀ ⊔ JH := by
    rw [Subgroup.subgroupOf_sup (pPrimeCoreOf_le 3 C) hJC, hNsub]
  set ψ₁ : ↥J →* (↥C ⧸ N₀) := π.comp (Subgroup.inclusion hJC) with hψ₁
  have hψ₁r : ψ₁.range = 𝔍 := by rw [hψ₁, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ψ₁.ker = (Item148HJ.resProj Lb d).ker := by
    ext j
    rw [MonoidHom.mem_ker, Item148HJ.mem_ker_resProj, hψ₁, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hj
      exact hJNθ j j.2 ⟨_, hj, rfl⟩
    · intro hj
      obtain ⟨n, hn, hnj⟩ := hθN j j.2 hj
      have : n = Subgroup.inclusion hJC j := Subtype.ext hnj
      exact this ▸ hn
  let e𝔍 : ↥𝔍 ≃* ↥(Item148HJ.resProj Lb d).range :=
    (MulEquiv.subgroupCongr hψ₁r.symm).trans (Item148HJ.rangeEquivOfKerEq ψ₁ _ hker)
  have h𝔍tc : Sec4.IsTripleCover ↥𝔍 (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr e𝔍.symm htc
  have h𝔍p : Group.IsPerfect ↥𝔍 :=
    Group.IsPerfect.ofSurjective (f := e𝔍.symm.toMonoidHom) e𝔍.symm.surjective
  set a₀C : ↥C := ⟨a₀, hAC ha₀.1⟩ with ha₀C
  set x := π a₀C with hxdef
  have hx𝔍 : x ∈ 𝔍 := ⟨a₀C, Subgroup.mem_subgroupOf.mpr ha₀J, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← map_pow]
    have : a₀C ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 a₀ ha₀.1)
    rw [this, map_one]
  have hcommJ : ∀ u ∈ J, ∀ v ∈ J, ⁅u, v⁆ ∈ J := fun u hu v hv =>
    Subgroup.commutator_mem_commutator hu hv |> (Subgroup.commutator_le_self J)
  have hxZ : ∃ y ∈ 𝔍, x * y ≠ y * x := by
    refine ⟨π ⟨j₀, hJC hj₀J⟩, ⟨_, Subgroup.mem_subgroupOf.mpr hj₀J, rfl⟩, fun hxy => hj₀ ?_⟩
    have hcm : π ⁅(⟨j₀, hJC hj₀J⟩ : ↥C), a₀C⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hxy.symm
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcm
    exact hJNθ _ (hcommJ _ hj₀J _ ha₀J) ⟨_, hcm, rfl⟩
  have hYBM : YB ≤ M ⊓ C := le_of_mem_thetaComponentsIn hYB
  have hYBC : YB ≤ C := hYBM.trans inf_le_right
  have hYBJ : YB ≤ N ⊔ J := hlB ▸ hYBle
  obtain ⟨hcen3, h3Y⟩ := type_facts htype
  have hAMC : A ≤ Subgroup.normalizer ((M ⊓ C : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hM.2 (hAC.trans Subgroup.le_normalizer)
  have hnot' : ¬ deltaZero A (lB A) (M ⊓ C) ≤ pPrimeCoreOf 3 (M ⊓ C) := hnot
  have hAYB : A ≤ Subgroup.normalizer (YB : Set G) :=
    normalizes_of_le_sup hAMC hYB hcen3 h3Y hle hnot'
  have hconj : ∀ (g : ↥C) {X : Subgroup G}, (g : G) ∈ Subgroup.normalizer (X : Set G) →
      g ∈ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro g X hX
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hX y
  set P : Subgroup (↥C ⧸ N₀) := (YB.subgroupOf C).map π with hPdef
  have hP𝔍 : P ≤ 𝔍 := by
    have h1 : YB.subgroupOf C ≤ N₀ ⊔ JH := hsup ▸ Subgroup.comap_mono hYBJ
    calc P ≤ (N₀ ⊔ JH).map π := Subgroup.map_mono h1
      _ = 𝔍 := by
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),
          bot_sup_eq]
  have hPperf : Group.IsPerfect ↥P := by
    have hYBp : Group.IsPerfect ↥YB := isPerfect_of_mem_thetaComponentsIn hYB
    have : Group.IsPerfect ↥(YB.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYBC).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hYBC).symm.surjective
    exact Group.IsPerfect.map (H := YB.subgroupOf C) π
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hYBN : YB ≤ N := by
      intro y hy
      have hy' : π ⟨y, hYBC hy⟩ ∈ P := ⟨⟨y, hYBC hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        ← hNsub, Subgroup.mem_subgroupOf] at hy'
      exact hy'
    have h3YB : 3 ∣ Nat.card YB := h3Y.trans (Subgroup.card_quotient_dvd_card _)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3
      (h3YB.trans (Subgroup.card_dvd_of_le hYBN))
  have hxP : x ∈ Subgroup.normalizer (P : Set (↥C ⧸ N₀)) :=
    Subgroup.le_normalizer_map π ⟨a₀C, hconj a₀C (hAYB ha₀.1), rfl⟩
  obtain ⟨V₁, V₂, hV₁P, hV₂P, hV₁3, hV₂3, hxV₁, hxV₂, hnn, hf₁, hf₂⟩ :=
    exists_two_invariant_in h𝔍tc hx𝔍 hx3 hxZ hP𝔍 hPperf hPne hxP
  have hker' : ∀ c' : ↥C, π c' = 1 → (c' : G) ∈ N := by
    intro c' hc'
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hNsub,
      Subgroup.mem_subgroupOf] at hc'
    exact hc'
  have hπB : ∀ b' c' : ↥C, (b' : G) ∈ B → π b' * π c' = π c' * π b' := by
    intro b' c' hb'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c'.2 b' hb')
  obtain ⟨Q₁, hQ₁, hQ₁YB, hVQ₁⟩ := exists_scriptQZero_lift h hB hCdef hYBC hAYB hYBle π hker'
    hπB a₀C ha₀.1 ha₀B V₁ hV₁P hV₁3 hxV₁ hf₁
  obtain ⟨Q₂, hQ₂, hQ₂YB, hVQ₂⟩ := exists_scriptQZero_lift h hB hCdef hYBC hAYB hYBle π hker'
    hπB a₀C ha₀.1 ha₀B V₂ hV₂P hV₂3 hxV₂ hf₂
  set K := deltaZero A (lB A) YB with hKdef
  have hKYB : K ≤ YB := deltaZero_le YB
  have hKC : K ≤ C := hKYB.trans hYBC
  have hKM : K ≤ M := hKYB.trans (hYBM.trans inf_le_left)
  set T : Subgroup (↥C ⧸ N₀) := (K.subgroupOf C).map π with hTdef
  have hTP : T ≤ P := Subgroup.map_mono (Subgroup.subgroupOf_mono C hKYB)
  have hT𝔍 : T ≤ 𝔍 := hTP.trans hP𝔍
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
  have hxT : x ∈ Subgroup.normalizer (T : Set (↥C ⧸ N₀)) :=
    Subgroup.le_normalizer_map π ⟨a₀C, hconj a₀C (hAK ha₀.1), rfl⟩
  have hVQT : ∀ Q ∈ scriptQZero A (lB A), Q ≤ YB → (Q.subgroupOf C).map π ≤ T :=
    fun Q hQ hQY => Subgroup.map_mono (Subgroup.subgroupOf_mono C (le_deltaZero hQ hQY))
  have hV₁T : V₁ ≤ T := hVQ₁.trans (hVQT Q₁ hQ₁ hQ₁YB)
  have hV₂T : V₂ ≤ T := hVQ₂.trans (hVQT Q₂ hQ₂ hQ₂YB)
  rcases Item148HJ.triple_cover_dichotomy_in h𝔍tc h𝔍p hx𝔍 hx3 hxZ hT𝔍 hxT with hα | ⟨hβ, hU⟩
  · exact absurd (hV₂T.trans (hα V₁ hV₁T hV₁3 hxV₁)) hnn
  have hTT : T ≤ inSubgroup perfectResidual T := by
    set W : Subgroup G := ((inSubgroup perfectResidual T).comap π).map C.subtype with hW
    have hKW : K ≤ W := by
      refine sSup_le fun Q hQ => ?_
      have hQC : Q ≤ C := hQ.2.trans hYBC
      have hQ3 : ¬ 3 ∣ Nat.card ((Q.subgroupOf C).map π) := by
        intro h3
        have hQ3' : ¬ 3 ∣ Nat.card Q :=
          (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.1.2.1
        apply hQ3'
        refine h3.trans ((Subgroup.card_map_dvd _ π).trans ?_)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv]
      have hQT := hU _ (hVQT Q hQ.1 hQ.2) hQ3
      intro q hq
      exact ⟨⟨q, hQC hq⟩, hQT ⟨⟨q, hQC hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩, rfl⟩
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨w, hw, hwk⟩ := hKW (Subgroup.mem_subgroupOf.mp hk)
    have : w = k := Subtype.ext hwk
    exact this ▸ hw
  have hTeq : T = inSubgroup perfectResidual T := le_antisymm hTT (Subgroup.map_subtype_le _)
  have hTper : Group.IsPerfect ↥T := by
    have := Item148HJ.isPerfect_inSubgroup_perfectResidual T
    exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hTeq.symm).toMonoidHom)
      (MulEquiv.subgroupCongr hTeq.symm).surjective
  obtain ⟨hT3, hT3top⟩ : 3 ∣ Nat.card T ∧ oPrimeResidual 3 ↥T = ⊤ := by
    rcases hβ with he | h𝔍eq
    · obtain ⟨e⟩ := he
      let e' : ↥T ≃* alternatingGroup (Fin 5) := (MulEquiv.subgroupCongr hTeq).trans e
      refine ⟨?_, Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e' ?_⟩
      · rw [Nat.card_congr e'.toEquiv, card_alt_five]
        norm_num
      · have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
        exact Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup
          (by rw [card_alt_five]; norm_num)
    · have hT𝔍eq : T = 𝔍 := hTeq.trans h𝔍eq
      let e' : ↥T ≃* ↥𝔍 := MulEquiv.subgroupCongr hT𝔍eq
      refine ⟨?_, Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e' ?_⟩
      · rw [Nat.card_congr e'.toEquiv]
        have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥𝔍)
        rwa [h𝔍tc.1] at this
      · exact Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isTripleCover h𝔍tc
          Sec17.Proof171Steps.oPrimeResidual_alternatingGroup_six
  refine ⟨fun hcomm => ?_, fun hsol => ?_⟩
  ·
    set OM := pPrimeCoreOf 3 M with hOM
    have hU3 : ¬ 3 ∣ Nat.card (((OM ⊓ C).subgroupOf C).map π) := by
      intro h3
      have h1 := h3.trans (Subgroup.card_map_dvd _ π)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : OM ⊓ C ≤ C)).toEquiv]
        at h1
      have h2 : Nat.card (OM ⊓ C : Subgroup G) ∣ Nat.card OM :=
        Subgroup.card_dvd_of_le inf_le_left
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)
        (h1.trans h2)
    have hTU : T ≤ ((OM ⊓ C).subgroupOf C).map π := by
      calc T = ⁅T, T⁆ := (Subgroup.isPerfect_iff.mp hTper).symm
        _ ≤ ((OM ⊓ C).subgroupOf C).map π := by
          rw [Subgroup.commutator_le]
          rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
          have hk₁K : (k₁ : G) ∈ K := Subgroup.mem_subgroupOf.mp hk₁
          have hk₂K : (k₂ : G) ∈ K := Subgroup.mem_subgroupOf.mp hk₂
          set m₁ : ↥M := ⟨k₁, hKM hk₁K⟩ with hm₁
          set m₂ : ↥M := ⟨k₂, hKM hk₂K⟩ with hm₂
          set fM := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M) with hfM
          have hx₁ : fM m₁ ∈ (K.subgroupOf M).map fM :=
            ⟨m₁, Subgroup.mem_subgroupOf.mpr hk₁K, rfl⟩
          have hx₂ : fM m₂ ∈ (K.subgroupOf M).map fM :=
            ⟨m₂, Subgroup.mem_subgroupOf.mpr hk₂K, rfl⟩
          have hc := hcomm.is_comm.comm (⟨fM m₁, hx₁⟩ : ↥((K.subgroupOf M).map fM)) ⟨fM m₂, hx₂⟩
          have hc' : fM m₁ * fM m₂ = fM m₂ * fM m₁ := congrArg Subtype.val hc
          have h1 : fM ⁅m₁, m₂⁆ = 1 := by
            rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
            exact hc'
          rw [hfM, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
          have hmem : (⁅k₁, k₂⁆ : ↥C) ∈ (OM ⊓ C).subgroupOf C :=
            Subgroup.mem_subgroupOf.mpr ⟨⟨⁅m₁, m₂⁆, h1, rfl⟩, (⁅k₁, k₂⁆ : ↥C).2⟩
          rw [← map_commutatorElement]
          exact Subgroup.mem_map_of_mem π hmem
    exact hU3 (hT3.trans (Subgroup.card_dvd_of_le hTU))
  ·
    let fK : ↥K →* ↥C ⧸ N₀ := π.comp (Subgroup.inclusion hKC)
    have hfKr : fK.range = T := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have hKb3 : oPrimeResidual 3 ↥fK.range = ⊤ :=
      Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv (MulEquiv.subgroupCongr hfKr) hT3top
    have hKbp : Group.IsPerfect ↥fK.range := by
      have := hTper
      exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hfKr.symm).toMonoidHom)
        (MulEquiv.subgroupCongr hfKr.symm).surjective
    have hTne : T ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hT3
      omega
    have : Nontrivial ↥fK.range := (Subgroup.nontrivial_iff_ne_bot _).mpr (hfKr ▸ hTne)
    have hO : Group.IsSolvable ↥(oPrimeResidual 3 ↥K) := by
      have : Group.IsSolvable ↥((oPrimeResidual 3 ↥K).map K.subtype) := hsol
      exact Group.isSolvable_of_isSolvable_injective
        (f := ((oPrimeResidual 3 ↥K).equivMapOfInjective K.subtype
          K.subtype_injective).toMonoidHom) (MulEquiv.injective _)
    have hmap := Sec17.Proof171Steps.map_oPrimeResidual_three fK.rangeRestrict
      fK.rangeRestrict_surjective
    rw [hKb3] at hmap
    have hsurj : Function.Surjective (fK.rangeRestrict.comp (oPrimeResidual 3 ↥K).subtype) := by
      intro z
      have hz : z ∈ (oPrimeResidual 3 ↥K).map fK.rangeRestrict := hmap ▸ Subgroup.mem_top z
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨⟨w, hw⟩, rfl⟩
    have hRs : Group.IsSolvable ↥fK.range := by
      have := hO
      exact Group.isSolvable_of_surjective hsurj
    have := hKbp
    exact Group.IsPerfect.not_isSolvable _ hRs

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
