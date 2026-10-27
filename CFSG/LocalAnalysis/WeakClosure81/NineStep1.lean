module

public import CFSG.LocalAnalysis.WeakClosure81.NineLemmaD
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwoUncond
public import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.MS93.PUEquiv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.LieType.BorelTits Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

theorem nineE_le_pCoreOf (V K : Subgroup G) : nineE V K ≤ pCoreOf 2 K :=
  (A4.omegaOneCenterOf_le (E3.wClos V 1 (pCoreOf 2 K))).trans (E3.wClos_le 1 (pCoreOf 2 K))

theorem isElemAbelian_nineE (V K : Subgroup G) : IsElemAbelian 2 (nineE V K) :=
  B2F.isElemAbelian_omegaOneCenterOf (E3.wClos V 1 (pCoreOf 2 K))

theorem nineE_subgroupOf_normal (V K : Subgroup G) : ((nineE V K).subgroupOf K).Normal := by
  have hEK : nineE V K ≤ K := (nineE_le_pCoreOf V K).trans (pCoreOf_le 2 K)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr ?_
  intro k hk
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hR : conjSubgroup (pCoreOf 2 K) k = pCoreOf 2 K :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (le_normalizer_pCoreOf 2 K hk)
  have hW : conjSubgroup (E3.wClos V 1 (pCoreOf 2 K)) k =
      E3.wClos V 1 (pCoreOf 2 K) := by
    rw [← E3.wClos_conj (V := V) (i := 1) (X := pCoreOf 2 K) k, hR]
  have hmap : conjSubgroup (omegaOneCenterOf (E3.wClos V 1 (pCoreOf 2 K))) k =
      omegaOneCenterOf (conjSubgroup (E3.wClos V 1 (pCoreOf 2 K)) k) := by
    have h := CFSG.Quasithin.MS93.PU.omegaOneCenterOf_map
      (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective
      (E3.wClos V 1 (pCoreOf 2 K))
    exact h.symm
  unfold nineE
  exact hmap.trans (congrArg omegaOneCenterOf hW)

theorem conjSubgroup_mem_omegaIn {V K U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) {k : G} (hk : k ∈ K) :
    conjSubgroup U k ∈ omegaIn V K (nineE V K) := by
  have hEK : nineE V K ≤ K := (nineE_le_pCoreOf V K).trans (pCoreOf_le 2 K)
  refine ⟨conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hU.1 hk, ?_⟩
  have hKfix : conjSubgroup K k = K :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hk)
  exact (E3.conjSubgroup_mono_left k hU.2).trans hKfix.le

theorem commutator_eq_bot_of_mem_omegaSet (hV : Hyp7 V) (hm : 2 < rk ↥V) {U B : Subgroup G}
    (hU : U ∈ omegaSet V K (nineE V K)) (hB : IsGConj V B) (hBR : B ≤ pCoreOf 2 K) :
    ⁅U, B⁆ = ⊥ := by
  rw [mem_omegaSet] at hU
  obtain ⟨g, rfl, hEU, -⟩ := hU
  obtain ⟨b, rfl⟩ := hB
  have hk1 : 1 < rk ↥V := by omega
  have hBW : conjSubgroup V b ≤ E3.wClos V 1 (pCoreOf 2 K) :=
    E3.le_wClos_of_mQuot_le (X := pCoreOf 2 K) (B := conjSubgroup V b) hV.1 b
      hBR le_rfl (by simp [E3.mQuot_self]) hk1
  have hEcent : nineE V K ≤
      Subgroup.centralizer (E3.wClos V 1 (pCoreOf 2 K) : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  obtain ⟨x, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEU
  have hxE : (x : G) ∈ nineE V K := (Subgroup.mem_inf.mp x.2).1
  have hxU : (x : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.mp x.2).2
  have hx1 : (x : G) ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hBcent : conjSubgroup V b ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp (hEcent hxE) y (hBW hy)).symm
  have hBnorm : conjSubgroup V b ≤
      Subgroup.normalizer (conjSubgroup V g : Set G) :=
    hBcent.trans (centralizer_le_normalizer_conj hV.2.2 g hxU hx1)
  have hBne : conjSubgroup V b ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (conjSubgroup V b) = Nat.card V := E3.card_conjSubgroup V b
    rw [hbot, card_bot] at hcard
    exact absurd hV.2.1 (by rw [← hcard]; omega)
  have hNne : conjSubgroup V b ⊓ Subgroup.normalizer (conjSubgroup V g : Set G) ≠ ⊥ := by
    rwa [inf_eq_left.mpr hBnorm]
  rcases two_conj_eq_or_comm hV.1 hV.2.2
      (W := conjSubgroup V b) (W' := conjSubgroup V g) ⟨b, rfl⟩ ⟨g, rfl⟩ hNne with
    hcomm | ⟨y, hy, hUy⟩
  · refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hcomm v hv u hu
  · have hyNU : y ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
      (sup_le hBnorm Subgroup.le_normalizer) hy
    have h1 : y ∈ conjSubgroup (Subgroup.normalizer (conjSubgroup V b : Set G)) y := by
      rw [conjSubgroup_normalizer, ← hUy]
      exact hyNU
    have hyNB : y ∈ Subgroup.normalizer (conjSubgroup V b : Set G) := by
      rw [mem_conjSubgroup_iff] at h1
      simpa [mul_assoc] using h1
    have hUB : conjSubgroup V g = conjSubgroup V b := by
      rw [hUy]
      exact conjSubgroup_eq_iff_mem_normalizer.mpr hyNB
    rw [hUB]
    exact Subgroup.commutator_self_eq_bot_iff.mpr (isElemAbelian_conjSubgroup' hV.1 b).1

theorem commutator_twoResidual_eq_bot_of_mem_omegaIn (hV : Hyp7 V) (hm : 2 < rk ↥V)
    (h : TwoPTwoIrred K S X p) {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K))
    {B : Subgroup G} (hB : IsGConj V B) (hBR : B ≤ pCoreOf 2 K) : ⁅B, twoResidual K⁆ = ⊥ := by
  let N : Subgroup G := ⨆ W ∈ omegaIn V K (nineE V K), W
  have hNK : N ≤ K := iSup₂_le fun W hW => hW.2
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) := by
    intro k hk
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hle : conjSubgroup N k ≤ N := by
      have hmap : conjSubgroup N k =
          ⨆ W ∈ omegaIn V K (nineE V K), conjSubgroup W k := by
        dsimp only [N]
        simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
      rw [hmap]
      refine iSup_le fun W => iSup_le fun hW => ?_
      exact le_iSup₂_of_le (conjSubgroup W k) (conjSubgroup_mem_omegaIn hW hk) le_rfl
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (E3.card_conjSubgroup N k).symm)
  have hNnormal : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hNnorm
  have hNnot : ¬ N ≤ nineFrattiniR K X := by
    obtain ⟨g, hUg, -, hUnotR⟩ := mem_omegaSet.mp hU.1
    have hUAb : IsElemAbelian 2 U := by
      rw [hUg]
      exact isElemAbelian_conjSubgroup' hV.1 g
    have hU2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian hUAb
    have hUleN : U ≤ N := le_iSup₂_of_le U hU le_rfl
    intro hle
    exact TwoPTwo.not_le_frattiniR_of_isPGroup h.toTwoPTwo hU.2 hU2 hUnotR (hUleN.trans hle)
  have hres : twoResidual K ≤ N :=
    TwoPTwoIrred.twoResidual_le_of_not_le_frattiniR h hNK hNnormal hNnot
  have hWcent : ∀ W ∈ omegaIn V K (nineE V K), W ≤ Subgroup.centralizer (B : Set G) := by
    intro W hW
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_mem_omegaSet hV hm hW.1 hB hBR)
  have hNB : N ≤ Subgroup.centralizer (B : Set G) := by
    show (⨆ W ∈ omegaIn V K (nineE V K), W) ≤ Subgroup.centralizer (B : Set G)
    exact iSup₂_le hWcent
  have hcommNB : ⁅N, B⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hNB
  rw [Subgroup.commutator_comm B (twoResidual K)]
  exact le_bot_iff.mp ((Subgroup.commutator_mono hres le_rfl).trans (le_of_eq hcommNB))

private theorem nineStep1_wClos_zero_eq_iSup {V X : Subgroup G} (hV : IsElemAbelian 2 V) :
    E3.wClos V 0 X = ⨆ (g : G) (_ : conjSubgroup V g ≤ X), conjSubgroup V g := by
  refine le_antisymm ?_ ?_
  · rw [E3.wClos]
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAX, g, hAg, hm⟩ := hA
    have hAV : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g)
        hAg).1 hm
    rw [hAV]
    exact le_iSup₂_of_le g (hAV ▸ hAX) le_rfl
  · refine iSup₂_le fun g hg => ?_
    rw [E3.wClos]
    exact le_iSup₂_of_le (conjSubgroup V g) ⟨hg, g, le_rfl, E3.mQuot_self _⟩ le_rfl

theorem le_normalizer_wClos_zero_of_forall_le (hV : IsElemAbelian 2 V) (h : TwoPTwo K S X p)
    (hall : ∀ B : Subgroup G, IsGConj V B → B ≤ S → B ≤ pCoreOf 2 K) :
    K ≤ normalizer (E3.wClos V 0 S : Set G) := by
  have hSR : pCoreOf 2 K ≤ S := TwoPTwo.pCoreOf_le_sylowTwo h
  have hS := nineStep1_wClos_zero_eq_iSup (V := V) (X := S) hV
  have hR := nineStep1_wClos_zero_eq_iSup (V := V) (X := pCoreOf 2 K) hV
  have hEq : E3.wClos V 0 S = E3.wClos V 0 (pCoreOf 2 K) := by
    rw [hS, hR]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun g hg => ?_
      exact le_iSup₂_of_le g (hall (conjSubgroup V g) ⟨g, rfl⟩ hg) le_rfl
    · refine iSup₂_le fun g hg => ?_
      exact le_iSup₂_of_le g (hg.trans hSR) le_rfl
  rw [hEq]
  exact (le_normalizer_pCoreOf 2 K).trans
    (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) (pCoreOf 2 K))

theorem exists_conj_not_mem_omegaSet (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : TwoPTwoIrred K S X p)
    (hW : ¬ K ≤ normalizer (E3.wClos V 0 S : Set G)) (h3 : ¬ NineOneThree V K) :
    ∃ A : Subgroup G, IsGConj V A ∧ A ≤ S ∧ A ∉ omegaSet V K (nineE V K) ∧
      ¬ A ≤ pCoreOf 2 K := by
  by_contra hcon
  have hnone : ∀ A : Subgroup G, IsGConj V A → A ≤ S →
      A ∈ omegaSet V K (nineE V K) ∨ A ≤ pCoreOf 2 K := by
    intro A hA hAS
    by_cases hAω : A ∈ omegaSet V K (nineE V K)
    · exact Or.inl hAω
    · refine Or.inr ?_
      by_contra hAR
      exact hcon ⟨A, hA, hAS, hAω, hAR⟩
  by_cases hΩ : omegaIn V K (nineE V K) = ∅
  · apply hW
    refine le_normalizer_wClos_zero_of_forall_le hV.1 h.toTwoPTwo ?_
    intro B hB hBS
    rcases hnone B hB hBS with hBω | hBR
    · exfalso
      rw [Set.eq_empty_iff_forall_notMem] at hΩ
      exact hΩ B ⟨hBω, hBS.trans h.sylowTwo.le⟩
    · exact hBR
  · apply h3
    obtain ⟨U, hU⟩ := Set.nonempty_iff_ne_empty.mpr hΩ
    unfold NineOneThree
    refine ⟨?_, ?_⟩
    · intro B hB hBK
      obtain ⟨g, rfl⟩ := hB
      have hB2 : IsPGroup 2 (conjSubgroup V g) :=
        E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV.1) g
      obtain ⟨k, hk, hBk⟩ := E3.exists_le_conj_of_isSylowIn h.sylowTwo hBK hB2
      have hAS : conjSubgroup (conjSubgroup V g) k⁻¹ ≤ S :=
        (E3.conjSubgroup_le_iff_le_inv (A := conjSubgroup V g) (B := S) k⁻¹).mpr
          (by simpa using hBk)
      have hAconj : IsGConj V (conjSubgroup (conjSubgroup V g) k⁻¹) :=
        ⟨g * k⁻¹, by rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]⟩
      have hBinv : conjSubgroup (conjSubgroup (conjSubgroup V g) k⁻¹) k =
          conjSubgroup V g := by
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]
        simp [CFSG.Quasithin.conjSubgroup_one]
      rcases hnone (conjSubgroup (conjSubgroup V g) k⁻¹) hAconj hAS with hAω | hAR
      · left
        have hEω : conjSubgroup (conjSubgroup (conjSubgroup V g) k⁻¹) k ∈
            omegaSet V K (nineE V K) :=
          conjSubgroup_mem_omegaSet ((nineE_le_pCoreOf V K).trans (pCoreOf_le 2 K))
            (nineE_subgroupOf_normal V K) hAω hk
        exact ⟨by rwa [hBinv] at hEω, hBK⟩
      · right
        have hRfix : conjSubgroup (pCoreOf 2 K) k = pCoreOf 2 K :=
          conjSubgroup_eq_iff_mem_normalizer.mpr (le_normalizer_pCoreOf 2 K hk)
        calc conjSubgroup V g = conjSubgroup (conjSubgroup (conjSubgroup V g) k⁻¹) k :=
              hBinv.symm
          _ ≤ conjSubgroup (pCoreOf 2 K) k := E3.conjSubgroup_mono_left k hAR
          _ = pCoreOf 2 K := hRfix
    · intro B hB hBR
      exact commutator_twoResidual_eq_bot_of_mem_omegaIn hV hm h hU hB hBR

end CFSG.LocalAnalysis.WeakClosure81
