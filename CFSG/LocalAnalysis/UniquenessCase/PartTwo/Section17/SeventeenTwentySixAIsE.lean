module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveAction
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem4
public import CFSG.LocalAnalysis.WeakClosure81.NineSixNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.RankThreeUC
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem config17_26a_II_not_map_le_centralizer
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V) (hJ2 : IsSpor (Bar2 L) .J2)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAO : ¬ A ≤ pCoreOf 2 (L ⊔ D.T)) :
    ¬ (A.subgroupOf (L ⊔ D.T)).map (gap17_25_action c.hyp125 c) ≤
      Subgroup.centralizer
        (((barSub V₀ V c.hyp125.isElemAbelian L).subgroupOf
            (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))) :
          Set ↥(barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))) := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hAT : A ≤ L ⊔ D.T := hA.1.trans le_sup_right
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
  intro hle
  apply hAO
  set H : Subgroup G := L ⊔ D.T with hHdef
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV H with hYdef
  set K : Subgroup ↥Y := (barSub V₀ V hV L).subgroupOf Y with hKdef
  set f : ↥H →* ↥Y := gap17_25_action c.hyp125 c with hfdef
  have hcomap : A ≤ ((Subgroup.centralizer (K : Set ↥Y)).comap f).map H.subtype := by
    intro a ha
    refine Subgroup.mem_map.mpr ⟨⟨a, hAT ha⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.mpr
      (hle (Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr ha)))
  have hKn : K.Normal := gap17_25_barSub_normal c hMnorm
  have hcn : ((Subgroup.centralizer (K : Set ↥Y)).comap f).Normal :=
    Subgroup.Normal.comap
      (@Subgroup.normal_centralizer ↥Y (inferInstance : Group ↥Y) K hKn) f
  intro a ha
  exact Subgroup.map_mono (CFSG.LieType.BorelTits.le_pCore 2 hcn
    (gap17_25_comap_centralizer_isPGroup c h20 hC117 hJ2)) (hcomap ha)

theorem config17_26a_II_card_map_le_two {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAk : ((gap17_25_action c.hyp125 c).ker.map (L ⊔ D.T).subtype).relIndex A ≤ 2) :
    Nat.card ↥((A.subgroupOf (L ⊔ D.T)).map (gap17_25_action c.hyp125 c)) ≤ 2 := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hAT : A ≤ L ⊔ D.T := hA.1.trans le_sup_right
  set H : Subgroup G := L ⊔ D.T with hHdef
  set f : ↥H →* ↥(barSub V₀ V hV H) := gap17_25_action c.hyp125 c with hfdef
  have hmap : (A.subgroupOf H).map H.subtype = A :=
    Subgroup.map_subgroupOf_eq_of_le hAT
  have hrel : (f.ker.map H.subtype).relIndex A = f.ker.relIndex (A.subgroupOf H) := by
    have h := Subgroup.relIndex_map_map_of_injective (f := H.subtype)
      f.ker (A.subgroupOf H) H.subtype_injective
    rwa [hmap] at h
  rw [← Subgroup.relIndex_ker (A.subgroupOf H) f, ← hrel]
  exact hAk

theorem config17_26a_II_isE
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V) (hJ2 : IsSpor (Bar2 L) .J2)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAO : ¬ A ≤ pCoreOf 2 (L ⊔ D.T))
    (hAk : ((gap17_25_action c.hyp125 c).ker.map (L ⊔ D.T).subtype).relIndex A ≤ 2) :
    E1.IsE 1 (L ⊔ D.T) D.T A (L ⊔ D.T) := by
  classical
  have hV := c.hyp125.isElemAbelian
  have hAT : A ≤ L ⊔ D.T := hA.1.trans le_sup_right
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hL1 : barSub V₀ V hV L ≠ ⊥ := gap17_25_barSub_L_ne_bot c h20 hC117
  set H : Subgroup G := L ⊔ D.T with hHdef
  set Y : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV H with hYdef
  set K : Subgroup ↥Y := (barSub V₀ V hV L).subgroupOf Y with hKdef
  set f : ↥H →* ↥Y := gap17_25_action c.hyp125 c with hfdef
  have hT : IsSylowIn 2 D.T H :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort.isSylowIn_of_le D le_sup_right
  have hker : IsPGroup 2 ↥f.ker :=
    gap17_25_action_ker_isPGroup c.hyp125 c hMnorm hsimple hL1
  have hKn : K.Normal := gap17_25_barSub_normal c hMnorm
  have hKspor : IsSpor ↥K .J2 := gap17_25_barSub_isSpor c hJ2 hL1
  obtain ⟨eK⟩ := hKspor
  have hsimpleK : IsSimpleGroup ↥K :=
    (MulEquiv.isSimpleGroup_congr eK).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcardK : Nat.card ↥K = 604800 :=
    (Nat.card_congr eK.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hcenterK : Subgroup.center ↥K = ⊥ :=
    CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_card_not_prime (W := ↥K) (by
      rw [hcardK]
      norm_num)
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥K = ⊤ :=
      Subgroup.center_eq_top_iff.mpr ⟨⟨fun a b => h a b⟩⟩
    have hle : (⊤ : Subgroup ↥K) ≤ ⊥ := by
      rw [← htop, hcenterK]
    have hsub : Subsingleton ↥K := ⟨fun a b => by
      rw [Subgroup.mem_bot.mp (hle (Subgroup.mem_top a)),
        Subgroup.mem_bot.mp (hle (Subgroup.mem_top b))]⟩
    have hcard1 : Nat.card ↥K = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    omega
  have htwo : ∀ y : ↥Y, ∃ k : ℕ, y ^ 2 ^ k ∈ K := by
    obtain ⟨n, hn⟩ := exists_index_barSub_pow_two c.hyp125 c hMnorm
    have hnK : K.index = 2 ^ n := by simpa only [K, Y] using hn
    intro y
    exact ⟨n, by simpa [hnK] using @Subgroup.pow_index_mem ↥Y _ K hKn y⟩
  have hYfin : Finite ↥Y := Subtype.finite
  exact @CFSG.Quasithin.Vol2.Ch11.SecU1.isE_one_self_of_almostSimple_image G
    (inferInstance : Group G) (inferInstance : Finite G) ↥Y
    (inferInstance : Group ↥Y) hYfin H D.T A hT hA.1 f
    (gap17_25_action_surjective c) hker K hKn hsimpleK hnab htwo
    (config17_26a_II_not_map_le_centralizer c h20 hC117 hJ2 hA hAO)
    (config17_26a_II_card_map_le_two c hA hAk)

theorem config17_26a_II_center_ne_bot
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V) (hK2 : K_J2_centralizer_shape)
    (hJ2 : IsSpor (Bar2 L) .J2) (hm : 4 < mSub V₀)
    (h2grp : IsPGroup 2 ↥(H17_25_one D V₀ V L c.hyp125.isElemAbelian ⊓
      centralizer (E3.cClos V₀ 2 D.T : Set G)))
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hE : E1.IsE 1 (L ⊔ D.T) D.T A (L ⊔ D.T)) :
    A ⊓ centerOf (E3.wClos A 2 (pCoreOf 2 (L ⊔ D.T))) ≠ ⊥ := by
  classical
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    have hzero : mSub (⊥ : Subgroup G) = 0 := CFSG.Quasithin.rk_bot
    rw [hbot, hzero] at hm
    omega
  have hTI0 : CFSG.CGT.Timmesfeld75.IsTI V₀ := by
    rcases c.hyp125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.2.2.2.1
  have hV0el : IsElemAbelian 2 V₀ := c.hyp125.pairFacts.elemAbelian₀
  obtain ⟨hAT, g, hAg, hmq⟩ := hA
  have hconjel : IsElemAbelian 2 (conjSubgroup V₀ g) := isElemAbelian_conjSubgroup' hV0el g
  have hAeq : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hconjel)
      hAg).mp hmq
  subst hAeq
  have hATI : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V₀ g) := isTI_conj hTI0 g
  have hcard : Nat.card ↥(conjSubgroup V₀ g) = Nat.card ↥V₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hrk : rk ↥(conjSubgroup V₀ g) = mSub V₀ := by
    unfold mSub rk
    rw [hcard]
  refine E3.e3_17_two_core (H := L ⊔ D.T) (S := D.T) (i := 0) (j := 1) (k := 2) hconjel
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort.isSylowIn_of_le D le_sup_right)
    (by norm_num) (lt_rParam_of_isTI hATI (by omega)) (by omega) hAT le_rfl
    (by rw [E3.mQuot_self]) hE ?_
  intro hbot
  rw [E3.cClos_conjV] at hbot
  have hres : twoResidual (L ⊔ D.T) ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  set H₁ : Subgroup G := H17_25_one D V₀ V L c.hyp125.isElemAbelian with hH₁def
  have hshape := gap17_25_H1_shape_of D V₀ V h20 hC117 hK2 L c hJ2
  have h3bar : 3 ∣ Nat.card (Bar2 H₁) := by
    rcases hshape with h | h
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
  have hcardH : Nat.card ↥H₁ = Nat.card (Bar2 H₁) * Nat.card (CFSG.pCore 2 ↥H₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H₁)
  have h3 : 3 ∣ Nat.card ↥H₁ := by
    rw [hcardH]
    exact dvd_mul_of_dvd_left h3bar _
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' ↥H₁
    (inferInstance : Group ↥H₁) (inferInstance : Finite ↥H₁) 3 ⟨Nat.prime_three⟩ h3
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hH1le : H₁ ≤ L ⊔ D.T := inf_le_left
  have hxres : (x : G) ∈ twoResidual (L ⊔ D.T) :=
    CFSG.Quasithin.F6.mem_twoResidual_of_odd (hH1le x.2) (by rw [hxo]; decide)
  have hxC : (x : G) ∈ H₁ ⊓ centralizer (E3.cClos V₀ 2 D.T : Set G) := ⟨x.2, hres hxres⟩
  obtain ⟨k, hk⟩ := h2grp ⟨(x : G), hxC⟩
  have hk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : 3 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one hk'
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
