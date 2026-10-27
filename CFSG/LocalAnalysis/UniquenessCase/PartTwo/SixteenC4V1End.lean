module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Parity
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1_enh_actTil_eq_one_of_centralizes (S : s16c4v1_Sit D V L hV)
    {k : G} (hk : k ∈ Subgroup.centralizer (V : Set G)) (hkM : k ∈ D.M) :
    actTil (v1Sub D.M ⊥ V hV L) V hV ⟨k, s16c4v1_mem_stabTil S hkM⟩ = 1 := by
  rw [actTil_eq_one_iff]
  intro v hv
  have hcomm : k * v = v * k := (Subgroup.mem_centralizer_iff.1 hk v hv).symm
  rw [show k * v * k⁻¹ * v⁻¹ = 1 by rw [hcomm]; group]
  exact (v1Sub D.M ⊥ V hV L).one_mem

theorem s16c4v1_frattini_three (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) :
    ∃ X : Subgroup G, X ≤ D.M ∧
      X ≤ Subgroup.normalizer ((D.T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
      IsPGroup 3 X ∧ ¬ IsCyclic X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let V1 : Subgroup G := v1Sub D.M ⊥ V hV L
  let Cv : Subgroup G := Subgroup.centralizer (V : Set G)
  let Q : Subgroup G := D.T ⊓ Cv
  let K : Subgroup G := D.M ⊓ Cv
  let N : Subgroup G := D.M ⊓ Subgroup.normalizer (Q : Set G)
  have hKnormal : D.M ≤ Subgroup.normalizer (K : Set G) := by
    intro m hm
    have hmV : m ∈ Subgroup.normalizer (V : Set G) :=
      S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer hm
    have hle : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Cv : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf
        (Subgroup.centralizer_le_normalizer (V : Set G))
    have hmC : m ∈ Subgroup.normalizer (Cv : Set G) := hle hmV
    have hmDM : m ∈ Subgroup.normalizer (D.M : Set G) := Subgroup.le_normalizer (H := D.M) hm
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := D.M) (K := Cv) ⟨hmDM, hmC⟩
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K := by
    have h := D.sylowM.inf_of_le_normalizer (N := K) inf_le_left hKnormal
    have heq : D.T ⊓ K = Q := by
      show D.T ⊓ (D.M ⊓ Cv) = D.T ⊓ Cv
      rw [← inf_assoc, inf_eq_left.mpr D.sylowM.le]
    rwa [heq] at h
  have hherm : herm S.F.σ (Pi.single (0 : Fin 4) (1 : S.F.K))
      (Pi.single (0 : Fin 4) (1 : S.F.K)) ≠ 0 := by
    rw [herm_single_right, Pi.single_eq_same, map_one, one_mul]
    exact one_ne_zero
  obtain ⟨E₀, hEab, hEcard, -⟩ :=
    s16c4v1_stab_nonsing (K := S.F.K) (σ := S.F.σ) S.F.card_K S.F.isUnitary hherm
  have hE₀p : IsPGroup 3 E₀ := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hEab.2 x x.2)⟩
  have hE₀c : ¬ IsCyclic E₀ :=
    CFSG.AGLEmbedding.BlockCyc.not_isCyclic_of_isElemAbelian_sq hEab hEcard
  let πR : ↥(SUid S.F.σ 4) →* MulAut (Vtil V1 V hV) :=
    (Subgroup.subtype (lBar V1 V hV L)).comp
      (S.F.π : ↥(SUid S.F.σ 4) →* ↥(lBar V1 V hV L))
  have hπRinj : Function.Injective πR := by
    intro a b hab
    have h1 : (S.F.π a : ↥(lBar V1 V hV L)) = S.F.π b :=
      Subgroup.subtype_injective _ hab
    exact S.F.π.injective h1
  let E : Subgroup (MulAut (Vtil V1 V hV)) := E₀.map πR
  have hEp : IsPGroup 3 E := hE₀p.map πR
  have hEnc : ¬ IsCyclic E := SpLift.not_isCyclic_map πR hπRinj hE₀c
  have hElBar : E ≤ lBar V1 V hV L := by
    rintro φ ⟨γ, -, rfl⟩
    exact (S.F.π γ).2
  have hbar_le : barSub V1 V hV D.M ≤ barSub V1 V hV N := by
    intro φ hφ
    obtain ⟨m, hmM, hmeq⟩ := (mem_barSub V1 V hV D.M φ).1 hφ
    obtain ⟨k, hk, hkn⟩ := uc22r8100b_frattini hQ (hKnormal hmM)
    let ks : ↥(stabTil V1 V) := ⟨k, s16c4v1_mem_stabTil S hk.1⟩
    have hks1 : actTil V1 V hV ks = 1 :=
      s16c4v1_enh_actTil_eq_one_of_centralizes S hk.2 hk.1
    have hmem : actTil V1 V hV (ks⁻¹ * m) ∈ barSub V1 V hV N := by
      have hgN : (ks⁻¹ * m : G) ∈ N := by
        refine ⟨?_, ?_⟩
        · show k⁻¹ * (m : G) ∈ D.M
          exact D.M.mul_mem (D.M.inv_mem hk.1) hmM
        · show k⁻¹ * (m : G) ∈ Subgroup.normalizer (Q : Set G)
          exact hkn
      exact actTil_mem_barSub V1 V hV hgN (ks⁻¹ * m).2
    have hmul : actTil V1 V hV m = actTil V1 V hV (ks⁻¹ * m) := by
      have h1 : ks * (ks⁻¹ * m) = m := by group
      calc actTil V1 V hV m = actTil V1 V hV (ks * (ks⁻¹ * m)) := by rw [h1]
        _ = actTil V1 V hV ks * actTil V1 V hV (ks⁻¹ * m) := map_mul _ _ _
        _ = actTil V1 V hV (ks⁻¹ * m) := by rw [hks1, one_mul]
    rw [← hmeq, hmul]
    exact hmem
  have hEbar : E ≤ barSub V1 V hV N :=
    (hElBar.trans (barSub_mono V1 V hV S.sect.setting.hyp151.le)).trans hbar_le
  let C : Subgroup G := preBarSub N V1 V hV E
  have hCs : C ≤ stabTil V1 V := fun c hc => ((mem_preBarSub N V1 V hV E).1 hc).2.choose
  let hAct : ↥C →* MulAut (Vtil V1 V hV) := (actTil V1 V hV).comp (Subgroup.inclusion hCs)
  have hActE : ∀ c : ↥C, hAct c ∈ E := by
    intro c
    obtain ⟨-, h, hE'⟩ := (mem_preBarSub N V1 V hV E).1 c.2
    change actTil V1 V hV (Subgroup.inclusion hCs c) ∈ E
    have hsub : (Subgroup.inclusion hCs c : ↥(stabTil V1 V)) = ⟨(c : G), h⟩ := by
      apply Subtype.ext
      exact Subgroup.coe_inclusion hCs c
    rw [hsub]
    exact hE'
  let f : ↥C →* ↥E := hAct.codRestrict E hActE
  have hf : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨m, hmN, hmφ⟩ := (mem_barSub V1 V hV N φ).1 (hEbar hφ)
    have hmC : (m : G) ∈ C := by
      refine (mem_preBarSub N V1 V hV E).2 ⟨hmN, m.2, ?_⟩
      change actTil V1 V hV m ∈ E
      rw [hmφ]
      exact hφ
    refine ⟨⟨(m : G), hmC⟩, Subtype.ext ?_⟩
    have hsub : (Subgroup.inclusion hCs ⟨(m : G), hmC⟩ : ↥(stabTil V1 V)) = m := by
      apply Subtype.ext
      exact Subgroup.coe_inclusion hCs _
    change actTil V1 V hV (Subgroup.inclusion hCs ⟨(m : G), hmC⟩) = φ
    rw [hsub, hmφ]
  have htop : (⊤ : Subgroup ↥E) ≃* ↥E := Subgroup.topEquiv
  obtain ⟨X, -, hXp, hXc⟩ :=
    SpLift.exists_noncyclic_pSubgroup_le f hf (p := 3) (K := ⊤) (E := ⊤)
      (by rw [Subgroup.index_top]; norm_num)
      (hEp.of_equiv htop.symm)
      (fun hc => hEnc ((MulEquiv.isCyclic htop).mp hc))
  let X' : Subgroup G := X.map C.subtype
  have hX'N : X' ≤ N := by
    rintro _ ⟨x, -, rfl⟩
    exact ((mem_preBarSub N V1 V hV E).1 x.2).1
  refine ⟨X', hX'N.trans inf_le_left, hX'N.trans inf_le_right, hXp.map C.subtype, ?_⟩
  exact SpLift.not_isCyclic_map C.subtype (Subgroup.subtype_injective C) hXc

theorem s16c4v1_wClos_normalized (hV : IsElemAbelian 2 V) {T : Subgroup G}
    (hcomm : ∀ g : G, conjSubgroup V g ≤ T → ⁅V, conjSubgroup V g⁆ = ⊥) {n : G}
    (hn : n ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) :
    n ∈ Subgroup.normalizer ((E3.wClos V 0 T : Subgroup G) : Set G) := by
  have heq : E3.wClos V 0 T = E3.wClos V 0 (T ⊓ Subgroup.centralizer (V : Set G)) := by
    refine le_antisymm (E3.wClos_le_of_forall fun A hA => ?_) (E3.wClos_mono inf_le_left)
    obtain ⟨hAT, g, hAg, hmQ⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isElemAbelian_conjSubgroup hV g).isPGroup hAg).1 hmQ
    have hVA : ⁅V, conjSubgroup V g⁆ = ⊥ := hcomm g (hAeq ▸ hAT)
    refine E3.le_wClos ⟨fun a ha => ⟨hAT ha, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩,
      g, hAg, hmQ⟩
    have ha' : a ∈ conjSubgroup V g := hAeq ▸ ha
    have hc := Subgroup.commutator_mem_commutator hv ha'
    rw [hVA, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      at hc
    exact hc
  rw [heq]
  exact E3.normalizer_le_normalizer_wClos _ hn

theorem s16c4v1_normalizer_wClos_le (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    (hcomm : ∀ g : G, conjSubgroup V g ≤ D.T → ⁅V, conjSubgroup V g⁆ = ⊥) :
    Subgroup.normalizer ((E3.wClos V 0 D.T : Subgroup G) : Set G) ≤ D.M := by
  obtain ⟨X, hXM, hXQ, hX3, hXc⟩ := s16c4v1_frattini_three S hstd
  have h3 : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  have hyp125 := S.sect.setting.hyp16.hyp125
  have hVT : V ≤ D.T := TwelveTwentyTwo.le_T_of_hyp125 hyp125
  have hWT : E3.wClos V 0 D.T ≤ D.T := E3.wClos_le_of_forall fun B hB => hB.1
  have hc1 : conjSubgroup V 1 = V := by
    ext x
    simp [mem_conjSubgroup_iff]
  have hVW : V ≤ E3.wClos V 0 D.T := by
    refine E3.le_wClos (E3.mem_gammaSet_iff.mpr ⟨hVT, 1, ?_, ?_⟩)
    · rw [hc1]
    · rw [hc1]
      exact E3.mQuot_self V
  have hWne : E3.wClos V 0 D.T ≠ ⊥ := fun h =>
    hyp125.pairFacts.ne_bot (le_bot_iff.mp (h ▸ hVW))
  exact normalizer_le_of_noncyclic D hstd.r61 h3 hXM hX3 hXc hWne
    (D.sylowM.isPGroup.to_le hWT) fun n hn => s16c4v1_wClos_normalized hV hcomm (hXQ hn)

theorem s16c4v1_centralizer_cClos_le (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) :
    Subgroup.centralizer ((E3.cClos V 1 D.T : Subgroup G) : Set G) ≤ D.M := by
  have hyp125 := S.sect.setting.hyp16.hyp125
  have hVT : V ≤ D.T := TwelveTwentyTwo.le_T_of_hyp125 hyp125
  have h1T : v1Sub D.M ⊥ V hV L ≤ D.T := (s16c4v1_v1_le S).trans hVT
  have hTn : D.T ≤ Subgroup.normalizer ((v1Sub D.M ⊥ V hV L : Subgroup G) : Set G) :=
    fun t ht => s15_Infra_le_normalizer_v1Sub hyp125 hV (D.sylowM.le ht)
  obtain ⟨z, hz1, hz, hzc⟩ := CFSG.Quasithin.Vol2.Ch11.SecD.exists_mem_centralizer_ne_one
    D.sylowM.isPGroup h1T hTn S.ne_bot
  have hzW : z ∈ E3.cClos V 1 D.T :=
    ⟨h1T hz1, Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (E3.wClos_le 1 D.T)) hzc⟩
  have hnb : ¬ s16c4v1_Bad D z := fun hbad =>
    (s16c4v1_bad_sing S hstd (s16c4v1_v1_le S hz1) hz hbad).1
      ((s16c4v1_vec_eq_zero_iff S (s16c4v1_v1_le S hz1)).2 hz1)
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzW)).trans (not_not.1 hnb)

theorem s16c4v1_ending (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    (hcomm : ∀ g : G, conjSubgroup V g ≤ D.T → ⁅V, conjSubgroup V g⁆ = ⊥) : False := by
  have hyp125 := S.sect.setting.hyp16.hyp125
  have h3 : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  have h1219 : D.sig = D.sig1 := hstd.h1219 ⊥ V hyp125
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hstd.sigmaStd h1219 h3
  have hmb : MBarGT D.M ⊥ V (D.k + 0) := by
    rw [hk]
    exact Sixteen24.mBarGT_one_of_case4 D hstd.r1217 S.sect S.case4
  rcases twelve_ten_two D hstd.dataExt hstd.r61 hstd.r126 hstd.w3_111 hyp125 rfl hmb with h | h
  · exact h (s16c4v1_normalizer_wClos_le S hstd hcomm)
  · rw [hk] at h
    exact h (s16c4v1_centralizer_cClos_le S hstd)

theorem s16c4v1_scalar_false (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) : False := by
  refine s16c4v1_ending S hstd fun g hgT => ?_
  by_contra hne
  exact s16c4v1_lemma13 S hstd hz ⟨hgT.trans D.sylowM.le, hne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
