module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.LocalAnalysis.WeakClosure81.SixSix
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenConj
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveEighteen

private theorem conjSubgroup_inv_le_iff (B M : Subgroup G) (g : G) :
    conjSubgroup B g⁻¹ ≤ M ↔ B ≤ conjSubgroup M g :=
  (E3.le_conjSubgroup_iff_inv_le g).symm

theorem six_nine_one_core_of_isE_gen {M V₀ V H S A K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hMnorm : normalizer (V : Set G) = M) (hN₀ : normalizer (V₀ : Set G) = M)
    (hTI : ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀)
    (hS : IsSylowIn 2 S H) {i n k : ℕ} (hink : i + n ≤ k)
    (hA : A ∈ E3.gammaSet V i S) (hAV : A ≤ V) (hK : E1.IsE n H S A K)
    (hkV : k < rk ↥V) (hr : (k : ℕ∞) < E3.rParam V)
    (hmbar : k < mBar M V₀ V hV)
    (hne : ⁅twoResidual K, E3.cClos V k S⁆ ≠ ⊥) :
    V₀ ≠ ⊥ ∧ ∃ g ∈ K, InCalO1 k M V₀ V g := by
  obtain ⟨hAS, x, hAx, hmx⟩ := hA
  have hAi : E3.mQuot V A ≤ i := (E3.mQuot_conj_eq hV hAV hAx).trans_le hmx.le
  have hAab : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAV hV
  have hAK : A ≤ K := (E3.card_le_of_isE hS hAS hAab hK).1
  have hijk : i + n ≤ k := hink
  set Q := E3.cClos V k (pCoreOf 2 K) with hQ
  set W := E3.wClos V k (pCoreOf 2 K) with hW
  set B := A ⊓ pCoreOf 2 K with hB
  have hBW : B ≤ W := E3.e3_17_B_le hV hS hijk hkV hAS hAV hAi hK
  have hmB : E3.mQuot V B ≤ k := by
    have h := E3.e3_17_mQuot hV hS hAS hAV hAi hK
    rw [hB]
    omega
  have hcentle : Subgroup.centralizer (W : Set G) ≤ M := by
    rw [← hMnorm]
    exact E3.e3_17_cent_le hV hS hijk hr hkV hAS hAV hAi hK
  have hQM : Q ≤ M := (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans hcentle
  have hQW : Q ≤ centralizer (B : Set G) :=
    (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans (Subgroup.centralizer_le hBW)
  have hQ2 : IsPGroup 2 Q := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left
  have hcomm := E3.e3_17_comm_ne hV hS hijk hr hkV hAS hAV hAi hK hne
  have hEne : ⁅A, Q⁆ ≠ ⊥ := hcomm.2
  have hQct : Q ≤ F11.CTilde M V₀ V :=
    le_cTilde_of_lt_mBar hV hV₀ hM hM₀ hmbar (inf_le_left.trans hAV : B ≤ V) hQM hQ2 hQW hmB
  have hE_le_V₀ : ⁅A, Q⁆ ≤ V₀ := by
    refine Subgroup.commutator_le.2 ?_
    intro a ha q hq
    have hmem : q * a * q⁻¹ * a⁻¹ ∈ V₀ :=
      centralizesMod_of_mem_cTilde hV hM hM₀ (hQct hq) a (hAV ha)
    have e : ⁅a, q⁆ = (q * a * q⁻¹ * a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V₀.inv_mem hmem
  have hV₀ne : V₀ ≠ ⊥ := by
    intro h
    rw [h] at hE_le_V₀
    exact hEne (le_bot_iff.1 hE_le_V₀)
  obtain ⟨⟨t, htE⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htV₀ : t ∈ V₀ := hE_le_V₀ htE
  have hCGE : centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) ≤ M := by
    refine (Subgroup.centralizer_le (Set.singleton_subset_iff.2 htE)).trans ?_
    rw [← hN₀]
    intro c hc
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    apply hTI c
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨t, ?_⟩, fun h => ht1' (congrArg Subtype.val h)⟩
    refine Subgroup.mem_inf.2 ⟨htV₀, ?_⟩
    rw [mem_conjSubgroup_iff]
    have hcx : t * c = c * t := (Subgroup.mem_centralizer_iff.1 hc) t (Set.mem_singleton t)
    rw [← hcx]
    simpa using htV₀
  have hA2 : IsPGroup 2 A := (B2F.isPGroup_of_isElemAbelian hV).to_le hAV
  have hAne : ¬ A ≤ pCoreOf 2 K := by
    intro hAle
    have hAB : B = A := inf_eq_left.2 hAle
    have hAW : A ≤ W := hAB ▸ hBW
    have hQA : Q ≤ centralizer (A : Set G) :=
      (inf_le_right : Q ≤ Subgroup.centralizer (W : Set G)).trans (Subgroup.centralizer_le hAW)
    apply hEne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hQA
  obtain ⟨g, hgK, hgnon2⟩ := exists_not_isPGroup_sup_conj_of_not_le_pCore hAK hA2 hAne
  have hWnorm : K ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := k) (pCoreOf 2 K))
  have hQnorm : K ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_cClos (V := V) (i := k) (pCoreOf 2 K))
  have hQg : conjSubgroup Q g = Q := conjSubgroup_eq_iff_mem_normalizer.2 (hQnorm hgK)
  have hQg_inv : conjSubgroup Q g⁻¹ = Q :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hQnorm (K.inv_mem hgK))
  have hWg : conjSubgroup W g = W := conjSubgroup_eq_iff_mem_normalizer.2 (hWnorm hgK)
  have hWg_inv : conjSubgroup W g⁻¹ = W :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hWnorm (K.inv_mem hgK))
  have hE_le_Q : ⁅A, Q⁆ ≤ Q := by
    refine Subgroup.commutator_le.2 ?_
    intro a ha q hq
    have haN : a ∈ Subgroup.normalizer (Q : Set G) := hQnorm (hAK ha)
    have h1 : a * q * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 haN q).1 hq
    have e : ⁅a, q⁆ = (a * q * a⁻¹) * q⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have hEg_le_M : conjSubgroup (⁅A, Q⁆) g ≤ M :=
    ((E3.conjSubgroup_mono_left g hE_le_Q).trans (le_of_eq hQg)).trans hQM
  have hEginv_le_M : conjSubgroup (⁅A, Q⁆) g⁻¹ ≤ M :=
    ((E3.conjSubgroup_mono_left g⁻¹ hE_le_Q).trans (le_of_eq hQg_inv)).trans hQM
  have hBg_le_W : conjSubgroup B g ≤ W :=
    (E3.conjSubgroup_mono_left g hBW).trans (le_of_eq hWg)
  have hBginv_le_W : conjSubgroup B g⁻¹ ≤ W :=
    (E3.conjSubgroup_mono_left g⁻¹ hBW).trans (le_of_eq hWg_inv)
  have heC_of_Q : ∀ {e : G}, e ∈ Q → e ∈ centralizer (W : Set G) := by
    intro e he
    exact (Subgroup.mem_inf.1 (hQ ▸ he)).2
  have hBg_le_CGE : conjSubgroup B g ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1
      (heC_of_Q (hE_le_Q he)) b (hBg_le_W hb))).symm
  have hBginv_le_CGE : conjSubgroup B g⁻¹ ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1
      (heC_of_Q (hE_le_Q he)) b (hBginv_le_W hb))).symm
  have hBg_le_M : conjSubgroup B g ≤ M := hBg_le_CGE.trans hCGE
  have hBginv_le_M : conjSubgroup B g⁻¹ ≤ M := hBginv_le_CGE.trans hCGE
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hnotVg : ¬ conjSubgroup V g ≤ M :=
    not_conjSubgroup_le_normalizer_of_not_isPGroup hV2 hAV hM hgnon2
  have hnotVMg : ¬ V ≤ conjSubgroup M g :=
    not_le_conjSubgroup_of_not_isPGroup hV2 hAV hMnorm hgnon2
  have hOFirst : OFirst k M V₀ V g := by
    refine ⟨hnotVg, ?_, ?_⟩
    · have hB_le : B ≤ V ⊓ conjSubgroup M g :=
        le_inf (inf_le_left.trans hAV) ((conjSubgroup_inv_le_iff B M g).1 hBginv_le_M)
      exact (le_of_eq (mQuot_inf_left V (conjSubgroup M g)).symm).trans
        ((E3.mQuot_mono hB_le).trans hmB)
    · intro _
      refine Subgroup.ne_bot_iff_exists_ne_one.2
        ⟨⟨t, Subgroup.mem_inf.2 ⟨htV₀,
          ((conjSubgroup_inv_le_iff (⁅A, Q⁆) M g).1 hEginv_le_M) htE⟩⟩,
          fun h => ht1' (congrArg Subtype.val h)⟩
  have hODual : ODual k M V₀ V g := by
    refine ⟨hnotVMg, ?_, ?_⟩
    · have hBg_le : conjSubgroup B g ≤ conjSubgroup V g ⊓ M :=
        le_inf (E3.conjSubgroup_mono_left g (inf_le_left.trans hAV)) hBg_le_M
      have h1 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M) ≤ E3.mQuot V B :=
        (E3.mQuot_mono hBg_le).trans_eq (E3.mQuot_conjSubgroup V B g)
      exact (le_of_eq (mQuot_inf_left (conjSubgroup V g) M).symm).trans (h1.trans hmB)
    · intro _
      refine Subgroup.ne_bot_iff_exists_ne_one.2
        ⟨⟨(g : G)⁻¹ * t * (g : G), ?_⟩, ?_⟩
      · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [mem_conjSubgroup_iff, show g * ((g : G)⁻¹ * t * (g : G)) * g⁻¹ = t by group]
          exact htV₀
        · exact hEg_le_M (mem_conjSubgroup_iff.2 (by
            rw [show g * ((g : G)⁻¹ * t * (g : G)) * g⁻¹ = t by group]
            exact htE))
      · intro heq
        apply ht1'
        have hval : (g : G)⁻¹ * t * (g : G) = 1 := congrArg Subtype.val heq
        calc t = (g : G) * ((g : G)⁻¹ * t * (g : G)) * (g : G)⁻¹ := by group
          _ = (g : G) * 1 * (g : G)⁻¹ := by rw [hval]
          _ = 1 := by group
  exact ⟨hV₀ne, g, hgK, (six_six hV hV₀ hM hM₀ hmbar g).1 ⟨hOFirst, hODual⟩⟩

theorem exists_inCalO1_of_commutator_ne_bot_gen {M V₀ V H S A K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hMnorm : normalizer (V : Set G) = M) (hN₀ : normalizer (V₀ : Set G) = M)
    (hTI : ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀)
    (hS : IsSylowIn 2 S H) {i n k : ℕ} (hink : i + n ≤ k)
    (hA : A ∈ E3.gammaSet V i S) (hK : E1.IsE n H S A K)
    (hkV : k < rk ↥V) (hr : (k : ℕ∞) < E3.rParam V)
    (hmbar : k < mBar M V₀ V hV)
    (hne : ⁅twoResidual K, E3.cClos V k S⁆ ≠ ⊥) :
    V₀ ≠ ⊥ ∧ ∃ g : G, InCalO1 k M V₀ V g := by
  obtain ⟨-, x, hAx, -⟩ := id hA
  have hVx : IsElemAbelian 2 (conjSubgroup V x) := E3.isElemAbelian_conjSubgroup hV x
  have hV₀x : conjSubgroup V₀ x ≤ conjSubgroup V x := E3.conjSubgroup_mono_left x hV₀
  have hNx : normalizer (conjSubgroup V x : Set G) = conjSubgroup M x := by
    rw [← E3.conjSubgroup_normalizer, hMnorm]
  have hN₀x : normalizer (conjSubgroup V₀ x : Set G) = conjSubgroup M x := by
    rw [← E3.conjSubgroup_normalizer, hN₀]
  have key := six_nine_one_core_of_isE_gen (M := conjSubgroup M x) (V₀ := conjSubgroup V₀ x)
    (V := conjSubgroup V x) hVx hV₀x hNx.ge hN₀x.ge hNx hN₀x (isTI_form_conj hTI x) hS hink
    (by rwa [E3.gammaSet_conjV]) hAx hK (by rwa [E3.rk_conjSubgroup]) (by rwa [E3.rParam_conj])
    (by rw [mBar_conj M V₀ V hV hV₀ hM hM₀ x]; exact hmbar) (by rwa [E3.cClos_conjV])
  obtain ⟨hV₀ne, g', -, hg'⟩ := key
  refine ⟨fun h => hV₀ne (by rw [h, E3.conjSubgroup_bot]), x * g' * x⁻¹, ?_⟩
  have hO : InCalO k M V₀ V (x * g' * x⁻¹) := by
    refine (inCalO_conj x (x * g' * x⁻¹)).1 ?_
    rw [show x⁻¹ * (x * g' * x⁻¹) * x = g' by group]
    exact hg'.1
  exact (six_six hV hV₀ hM hM₀ hmbar _).1 hO

end TwelveEighteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
