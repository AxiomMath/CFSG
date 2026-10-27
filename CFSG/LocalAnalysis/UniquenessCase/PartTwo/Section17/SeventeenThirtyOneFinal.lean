module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOneFull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOneTitsPerm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoCartan
public import CFSG.GroupTheory.PerfectLiftPCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LargeReeParabolicHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
  (center_eq_bot_of_simple_of_two_le_pRank)

variable {G : Type} [Group G] [Finite G]

theorem inFSq_of_isL2_or_isSz_of_normal_sup {H K T : Subgroup G} {m : ℕ}
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hTsyl : IsSylowIn 2 T H)
    (hsup : K ⊔ T = H) (hperf : ⁅K, K⁆ = K) (hshape : IsL2 (Bar2 K) m ∨ IsSz (Bar2 K) m)
    (hKc : Inputs1719.K_L2SzAutRank) : InFSq m H := by
  classical
  have hsimpleK : IsSimpleGroup (Bar2 K) := S19.isSimpleGroup_of_isL2_or_isSz hshape
  obtain ⟨⟨e⟩, hCnormal, hsimpleC, hncC, -, hcent, hquot⟩ :=
    S18.fstar_imageBar2_of_normal hKH hKn hTsyl hsup hperf hsimpleK
  have hnabC : ∃ a b : ↥(S18.imageBar2 H K), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hncC ⟨⟨fun a b => h a b⟩⟩
  have hshapeC : IsL2 ↥(S18.imageBar2 H K) m ∨ IsSz ↥(S18.imageBar2 H K) m :=
    hshape.imp (LieModel.of_mulEquiv e) (LieModel.of_mulEquiv e)
  have hm : CFSG.Open.pRank 2 (⊤ : Subgroup (Bar2 H)) ≤ m :=
    hKc (Bar2 H) (S18.imageBar2 H K) m hsimpleC hncC hcent hquot hshapeC
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := Bar2 H)
  have hS : IsSylowIn 2 (S : Subgroup (Bar2 H)) ⊤ := isSylowIn_top S
  have hsupC : (S18.imageBar2 H K) ⊔ (S : Subgroup (Bar2 H)) = ⊤ := by
    have : (S18.imageBar2 H K).Normal := hCnormal
    rw [sup_comm]
    exact CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top (N := S18.imageBar2 H K) hquot S
  have hInF : InFGroup m (Bar2 H) :=
    inFGroup_of_twoRank_le hCnormal hsimpleC hnabC hcent ⟨_, hS, hsupC⟩ hm
  exact inF_top_of_inFGroup m hInF

theorem fixV_barSub_eq_bot_of_normal_gen
    {D : Data G} (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) (h869 : F08.R869 D) (h127 : R127 D) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal)
    (hshape : (∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      CFSG.Quasithin.IsTits (Bar2 L) ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :
    fixV (barSub V₀ V hV.isElemAbelian L) = ⊥ := by
  have hnt : ¬ F08.Thin8 L := by
    apply not_thin_of_exceptional k_exceptionalNotThin
    rcases hshape with h2 | hT | h3
    · exact Or.inl h2
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hT⟩))))
    · exact Or.inr (Or.inr h3)
  set A := pCoreOf 2 D.M with hA
  set K := L ⊔ A with hK
  have hLK : L ≤ K := le_sup_left
  have hAK : A ≤ K := le_sup_right
  have hKM : K ≤ D.M := sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hLKstab : L ≤ stabTil V₀ V :=
    hL.1.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hAKstab : A ≤ stabTil V₀ V :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M).trans
      (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hbar : barSub V₀ V hV.isElemAbelian K = barSub V₀ V hV.isElemAbelian L := by
    have hsup : barSub V₀ V hV.isElemAbelian (L ⊔ A) =
        barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian A := by
      unfold barSub
      rw [Subgroup.subgroupOf_sup hLKstab hAKstab, Subgroup.map_sup]
    rw [show K = L ⊔ A from rfl, hsup, barSub_pCoreOf_eq_bot_of_hyp125 hV, sup_bot_eq]
  have hKnormal : (K.subgroupOf D.M).Normal := by
    have hNL : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have hNA : D.M ≤ Subgroup.normalizer (A : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 fun x hx => ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup L A ⟨hNL hx, hNA hx⟩
  have hcomp : F12.IsComponentModO2 D.M K := isComponentModO2_sup_pCoreOf hL hN
  have hU : UniqueMax D.M (K ⊔ D.T) := by
    have hNcal : calNOf L = {D.M} := h869 L (Or.inl hL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
    have hUL : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le hNcal
    exact UC22.uc22p22u_uniqueMax_mono D (hLK.trans le_sup_left)
      (sup_le hKM D.sylowM.le) hUL
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_not_thin hV (ElevenNine.c117_of_hyp11 D h869 (hV.hyp11 h127)) hL hnt
  have hKH : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M K) ≠ ⊥ := by
    rw [uc22p2214_conjClosure_eq_of_normal hKM hKnormal, hbar]
    exact hL1
  have h26 := twelve_twentySix D h640 hFF hV hcomp hU hKH
  rcases h26 with hfix | ⟨-, hclass, -⟩
  · rwa [uc22p2214_conjClosure_eq_of_normal hKM hKnormal, hbar] at hfix
  · obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv hL hN
    rcases hshape with ⟨n, h2⟩ | hT | ⟨n, h3⟩
    · exact absurd hclass (not_classicalEvenAltG2Der_of_is2F4
        (CFSG.Quasithin.Is2F4.of_mulEquiv e.symm h2))
    · exact absurd hclass (not_classicalEvenAltG2Der_of_isTits
        (CFSG.Quasithin.IsTits.of_mulEquiv e.symm hT))
    · exact absurd hclass (not_classicalEvenAltG2Der_of_is3D4
        (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h3))

theorem exists_delta_2F4 {D : Data G}
    (hKc : Inputs1719.K_L2SzAutRank) (hP : Inputs1719.K_2F4ParabolicGen)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hUL : UniqueMax D.M L) {n : ℕ}
    (h2F4 : CFSG.Quasithin.Is2F4 n (Bar2 L)) :
    ∃ Δ : Finset (Subgroup G), (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧
      UniqueMax D.M (⨆ H ∈ Δ, H) ∧ ∃ ι : Subgroup G → ℕ, (∀ H ∈ Δ, InFSq (ι H) H) ∧
        Δ.sum ι ≤ 2 * n := by
  classical
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  have hTLsylOf : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    D.sylowM.inf_of_le_normalizer hL.1.le hMN
  have hTLsyl : IsSylowIn 2 (D.T ⊓ L) L := by
    have h := hTLsylOf
    rwa [CFSG.ABGLocalTools.isSylowOf_iff] at h
  set S : Subgroup (Bar2 L) := ((D.T ⊓ L).subgroupOf L).map π with hSdef
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTLsyl
  obtain ⟨Y₁, Y₂, hperf₁, hperf₂, hSz, hL2, hgen, hinv⟩ := hP (Bar2 L) n h2F4 S hS
  have hSα : ∀ (t : G) (ht : t ∈ D.T),
      S.map (CFSG.pCoreQuotMulAut ↥L
        (Subgroup.normalizerMonoidHom L ⟨t, hMN (D.sylowM.le ht)⟩)).toMonoidHom = S :=
    map_pCoreQuotMulAut_sylow hMN
  have hYT₁ : ∀ (t : G) (ht : t ∈ D.T),
      ((Y₁.comap π).map L.subtype).map (MulAut.conj t).toMonoidHom =
        (Y₁.comap π).map L.subtype := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (S18.mem_normalizer_barPreimage (hMN (D.sylowM.le ht)) (hinv _ (hSα t ht)).1)
  have hYT₂ : ∀ (t : G) (ht : t ∈ D.T),
      ((Y₂.comap π).map L.subtype).map (MulAut.conj t).toMonoidHom =
        (Y₂.comap π).map L.subtype := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (S18.mem_normalizer_barPreimage (hMN (D.sylowM.le ht)) (hinv _ (hSα t ht)).2)
  obtain ⟨K₁, hK₁L, hK₁perf, hTK₁, ⟨e₁⟩, himg₁⟩ :=
    CFSG.GroupTheory.exists_perfect_lift_quotient_pCore Y₁ hperf₁ hYT₁
  obtain ⟨K₂, hK₂L, hK₂perf, hTK₂, ⟨e₂⟩, himg₂⟩ :=
    CFSG.GroupTheory.exists_perfect_lift_quotient_pCore Y₂ hperf₂ hYT₂
  have hmapK : ((K₁ ⊔ K₂ ⊔ (D.T ⊓ L)).subgroupOf L).map π = ⊤ := by
    rw [Subgroup.subgroupOf_sup (sup_le hK₁L hK₂L) inf_le_right, Subgroup.map_sup,
      Subgroup.subgroupOf_sup hK₁L hK₂L, Subgroup.map_sup, himg₁, himg₂, ← hSdef]
    exact hgen
  have hLK : L ≤ K₁ ⊔ K₂ ⊔ (D.T ⊓ L) :=
    (Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top
      (sup_le (sup_le hK₁L hK₂L) inf_le_right) hmapK).trans
      (sup_le le_rfl ((CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTLsyl).trans le_sup_right))
  have hLle : L ≤ (K₁ ⊔ D.T) ⊔ (K₂ ⊔ D.T) := by
    refine hLK.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact (le_sup_left : K₁ ≤ K₁ ⊔ D.T).trans le_sup_left
    · exact (le_sup_left : K₂ ≤ K₂ ⊔ D.T).trans le_sup_right
    · exact ((inf_le_left : D.T ⊓ L ≤ D.T).trans le_sup_right).trans le_sup_left
  have hleM : (K₁ ⊔ D.T) ⊔ (K₂ ⊔ D.T) ≤ D.M := by
    refine sup_le (sup_le (hK₁L.trans hL.1.le) D.sylowM.le)
      (sup_le (hK₂L.trans hL.1.le) D.sylowM.le)
  have hInF₁ : InFSq n (K₁ ⊔ D.T) := by
    have hK'n : (K₁.subgroupOf (K₁ ⊔ D.T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTK₁)
    exact inFSq_of_isL2_or_isSz_of_normal_sup le_sup_left hK'n
      (TwelveShort.isSylowIn_of_le D le_sup_right) rfl hK₁perf
      (Or.inr (LieModel.of_mulEquiv e₁.symm hSz)) hKc
  have hInF₂ : InFSq n (K₂ ⊔ D.T) := by
    have hK'n : (K₂.subgroupOf (K₂ ⊔ D.T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTK₂)
    exact inFSq_of_isL2_or_isSz_of_normal_sup le_sup_left hK'n
      (TwelveShort.isSylowIn_of_le D le_sup_right) rfl hK₂perf
      (Or.inl (LieModel.of_mulEquiv e₂.symm hL2)) hKc
  refine ⟨{K₁ ⊔ D.T, K₂ ⊔ D.T}, ?_, ?_, (fun _ => n), ?_, ?_⟩
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact ⟨le_sup_right, (sup_le (hK₁L.trans hL.1.le) D.sylowM.le)⟩
    · exact ⟨le_sup_right, (sup_le (hK₂L.trans hL.1.le) D.sylowM.le)⟩
  · have hsupΔ : (⨆ H ∈ ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)), H) =
        (K₁ ⊔ D.T) ⊔ (K₂ ⊔ D.T) := by
      rw [← Finset.sup_eq_iSup]
      simp [Finset.sup_insert, Finset.sup_singleton]
    rw [hsupΔ]
    exact UC22.uc22p22u_uniqueMax_mono D hLle hleM hUL
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact hInF₁
    · exact hInF₂
  · have h1 : ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)).sum (fun _ => n) =
        ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)).card * n := by
      rw [Finset.sum_const, smul_eq_mul]
    have h2 : ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)).card ≤ 2 := by
      have h := Finset.card_insert_le (K₁ ⊔ D.T) ({K₂ ⊔ D.T} : Finset (Subgroup G))
      simp only [Finset.card_singleton] at h
      omega
    rw [h1]
    exact Nat.mul_le_mul_right n h2

theorem exists_delta_Tits {D : Data G}
    (hTi : Inputs1719.K_TitsParabolicGen)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hUL : UniqueMax D.M L) (hTits : LieModel (Bar2 L) .Tits 0 2 1) :
    ∃ Δ : Finset (Subgroup G), (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧
      UniqueMax D.M (⨆ H ∈ Δ, H) ∧ ∃ ι : Subgroup G → ℕ, (∀ H ∈ Δ, InFSq (ι H) H) ∧
        Δ.sum ι ≤ 2 := by
  classical
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  have hTLsylOf : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    D.sylowM.inf_of_le_normalizer hL.1.le hMN
  have hTLsyl : IsSylowIn 2 (D.T ⊓ L) L := by
    have h := hTLsylOf
    rwa [CFSG.ABGLocalTools.isSylowOf_iff] at h
  set S : Subgroup (Bar2 L) := ((D.T ⊓ L).subgroupOf L).map π with hSdef
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTLsyl
  obtain ⟨P₁, P₂, hS₁, hS₂, hcard₁, hcard₂, hsup, hinv⟩ := hTi (Bar2 L) hTits S hS
  have hSα := map_pCoreQuotMulAut_sylow hMN
  have hp₁ : S.relIndex P₁ = 3 := by
    have h := Subgroup.relIndex_mul_card S P₁
    rw [inf_eq_left.mpr hS₁, hcard₁] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hp₂ : S.relIndex P₂ = 5 := by
    have h := Subgroup.relIndex_mul_card S P₂
    rw [inf_eq_left.mpr hS₂, hcard₂] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hcomap : S.comap π = (D.T ⊓ L).subgroupOf L := by
    rw [hSdef]
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
      have hmem : x * y⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
      rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 L] at hmem
      have hmem' : x * y⁻¹ ∈ (D.T ⊓ L).subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr
          (CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTLsyl (Subgroup.mem_subgroupOf.mp hmem))
      have hxeq : x = (x * y⁻¹) * y := by group
      rw [hxeq]
      exact Subgroup.mul_mem _ hmem' hy
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  set K₁ : Subgroup G := (P₁.comap π).map L.subtype with hK₁
  set K₂ : Subgroup G := (P₂.comap π).map L.subtype with hK₂
  have hK₁L : K₁ ≤ L := Subgroup.map_subtype_le _
  have hK₂L : K₂ ≤ L := Subgroup.map_subtype_le _
  have hK₁sub : K₁.subgroupOf L = P₁.comap π := by
    rw [hK₁, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hK₂sub : K₂.subgroupOf L = P₂.comap π := by
    rw [hK₂, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hidx₁ : (D.T ⊓ L).relIndex K₁ = 3 := by
    have h1 : ((D.T ⊓ L).subgroupOf L).relIndex (P₁.comap π) = 3 := by
      rw [← hcomap, Subgroup.relIndex_comap S π (P₁.comap π),
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) P₁, hp₁]
    rw [← Subgroup.relIndex_subgroupOf (H := D.T ⊓ L) (K := K₁) (L := L) hK₁L, hK₁sub]
    exact h1
  have hidx₂ : (D.T ⊓ L).relIndex K₂ = 5 := by
    have h1 : ((D.T ⊓ L).subgroupOf L).relIndex (P₂.comap π) = 5 := by
      rw [← hcomap, Subgroup.relIndex_comap S π (P₂.comap π),
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) P₂, hp₂]
    rw [← Subgroup.relIndex_subgroupOf (H := D.T ⊓ L) (K := K₂) (L := L) hK₂L, hK₂sub]
    exact h1
  have hTLle₁ : D.T ⊓ L ≤ K₁ := by
    intro x hx
    have hx' : x ∈ D.T ∧ x ∈ L := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx'.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hmem : π ⟨x, hx'.2⟩ ∈ ((D.T ⊓ L).subgroupOf L).map π :=
      Subgroup.mem_map.mpr ⟨⟨x, hx'.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [← hSdef] at hmem
    exact hS₁ hmem
  have hTLle₂ : D.T ⊓ L ≤ K₂ := by
    intro x hx
    have hx' : x ∈ D.T ∧ x ∈ L := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx'.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hmem : π ⟨x, hx'.2⟩ ∈ ((D.T ⊓ L).subgroupOf L).map π :=
      Subgroup.mem_map.mpr ⟨⟨x, hx'.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [← hSdef] at hmem
    exact hS₂ hmem
  have hTK₁ : D.T ≤ Subgroup.normalizer (K₁ : Set G) := fun t ht =>
    S18.mem_normalizer_barPreimage (hMN (D.sylowM.le ht)) (hinv _ (hSα t ht)).1
  have hTK₂ : D.T ≤ Subgroup.normalizer (K₂ : Set G) := fun t ht =>
    S18.mem_normalizer_barPreimage (hMN (D.sylowM.le ht)) (hinv _ (hSα t ht)).2
  have hcardK₁ : Nat.card ↥K₁ = 3 * Nat.card ↥(D.T ⊓ L) := by
    have h := Subgroup.relIndex_mul_card (D.T ⊓ L) K₁
    rw [inf_eq_left.mpr hTLle₁, hidx₁] at h
    exact h.symm
  have hcardK₂ : Nat.card ↥K₂ = 5 * Nat.card ↥(D.T ⊓ L) := by
    have h := Subgroup.relIndex_mul_card (D.T ⊓ L) K₂
    rw [inf_eq_left.mpr hTLle₂, hidx₂] at h
    exact h.symm
  have hinf₁ : D.T ⊓ K₁ = D.T ⊓ L := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hK₁L (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hTLle₁ hx⟩
  have hinf₂ : D.T ⊓ K₂ = D.T ⊓ L := by
    refine le_antisymm ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hK₂L (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hTLle₂ hx⟩
  have hH₁card : Nat.card ↥(K₁ ⊔ D.T) = 3 * Nat.card ↥D.T := by
    have h := Subgroup.relIndex_mul_card D.T (K₁ ⊔ D.T)
    rw [inf_eq_left.mpr le_sup_right, sup_comm K₁ D.T,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hTK₁).1, hinf₁, hidx₁] at h
    rw [sup_comm K₁ D.T]
    exact h.symm
  have hH₂card : Nat.card ↥(K₂ ⊔ D.T) = 5 * Nat.card ↥D.T := by
    have h := Subgroup.relIndex_mul_card D.T (K₂ ⊔ D.T)
    rw [inf_eq_left.mpr le_sup_right, sup_comm K₂ D.T,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hTK₂).1, hinf₂, hidx₂] at h
    rw [sup_comm K₂ D.T]
    exact h.symm
  have h3dvd : 3 ∣ Nat.card ↥K₁ := by
    rw [hcardK₁]; exact dvd_mul_right 3 _
  have h5dvd : 5 ∣ Nat.card ↥K₂ := by
    rw [hcardK₂]; exact dvd_mul_right 5 _
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  let A₁ : Subgroup G := Subgroup.zpowers (y₁ : G)
  let A₂ : Subgroup G := Subgroup.zpowers (y₂ : G)
  have hA₁K : A₁ ≤ K₁ := Subgroup.zpowers_le.mpr y₁.2
  have hA₂K : A₂ ≤ K₂ := Subgroup.zpowers_le.mpr y₂.2
  have hA₁card : Nat.card ↥A₁ = 3 := by
    rw [show Nat.card ↥A₁ = orderOf (y₁ : G) from Nat.card_zpowers _, Subgroup.orderOf_coe, hy₁]
  have hA₂card : Nat.card ↥A₂ = 5 := by
    rw [show Nat.card ↥A₂ = orderOf (y₂ : G) from Nat.card_zpowers _, Subgroup.orderOf_coe, hy₂]
  have hA₁inf : A₁ ⊓ D.T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hA₁card]
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
  have hA₂inf : A₂ ⊓ D.T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hA₂card]
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)
  have hH₁perm : Permutes A₁ D.T := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hA₁inf ?_
    have hle : A₁ ⊔ D.T ≤ K₁ ⊔ D.T := sup_le (hA₁K.trans le_sup_left) le_sup_right
    calc Nat.card ↥(A₁ ⊔ D.T) ≤ Nat.card ↥(K₁ ⊔ D.T) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
      _ = 3 * Nat.card ↥D.T := hH₁card
      _ = Nat.card ↥A₁ * Nat.card ↥D.T := by rw [hA₁card]
  have hH₂perm : Permutes A₂ D.T := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hA₂inf ?_
    have hle : A₂ ⊔ D.T ≤ K₂ ⊔ D.T := sup_le (hA₂K.trans le_sup_left) le_sup_right
    calc Nat.card ↥(A₂ ⊔ D.T) ≤ Nat.card ↥(K₂ ⊔ D.T) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
      _ = 5 * Nat.card ↥D.T := hH₂card
      _ = Nat.card ↥A₂ * Nat.card ↥D.T := by rw [hA₂card]
  have hInF₁ : InFSq 1 (K₁ ⊔ D.T) := by
    have hle : A₁ ⊔ D.T ≤ K₁ ⊔ D.T := sup_le (hA₁K.trans le_sup_left) le_sup_right
    have hcardsup : Nat.card ↥(A₁ ⊔ D.T) = Nat.card ↥(K₁ ⊔ D.T) := by
      rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hH₁perm hA₁inf,
        hA₁card, hH₁card]
    have heq : A₁ ⊔ D.T = K₁ ⊔ D.T :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardsup.symm)
    rw [← heq]
    exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group A₁ D.T 3
      Nat.prime_three (by norm_num) hA₁card D.sylowM.isPGroup hH₁perm
  have hInF₂ : InFSq 1 (K₂ ⊔ D.T) := by
    have hle : A₂ ⊔ D.T ≤ K₂ ⊔ D.T := sup_le (hA₂K.trans le_sup_left) le_sup_right
    have hcardsup : Nat.card ↥(A₂ ⊔ D.T) = Nat.card ↥(K₂ ⊔ D.T) := by
      rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hH₂perm hA₂inf,
        hA₂card, hH₂card]
    have heq : A₂ ⊔ D.T = K₂ ⊔ D.T :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardsup.symm)
    rw [← heq]
    exact CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_prime_mul_two_group A₂ D.T 5
      Nat.prime_five (by norm_num) hA₂card D.sylowM.isPGroup hH₂perm
  have hmapK : ((K₁ ⊔ K₂).subgroupOf L).map π = ⊤ := by
    rw [Subgroup.subgroupOf_sup hK₁L hK₂L, Subgroup.map_sup, hK₁sub, hK₂sub,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) P₁,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) P₂, hsup]
  have hLK : L ≤ K₁ ⊔ K₂ :=
    (Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top (sup_le hK₁L hK₂L) hmapK).trans
      (sup_le le_rfl
        (((CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTLsyl).trans hTLle₁).trans le_sup_left))
  have hLle : L ≤ (K₁ ⊔ D.T) ⊔ (K₂ ⊔ D.T) := by
    refine hLK.trans (sup_le ?_ ?_)
    · exact (le_sup_left : K₁ ≤ K₁ ⊔ D.T).trans le_sup_left
    · exact (le_sup_left : K₂ ≤ K₂ ⊔ D.T).trans le_sup_right
  have hleM : (K₁ ⊔ D.T) ⊔ (K₂ ⊔ D.T) ≤ D.M := by
    refine sup_le (sup_le (hK₁L.trans hL.1.le) D.sylowM.le)
      (sup_le (hK₂L.trans hL.1.le) D.sylowM.le)
  refine ⟨{K₁ ⊔ D.T, K₂ ⊔ D.T}, ?_, ?_, (fun _ => 1), ?_, ?_⟩
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact ⟨le_sup_right, sup_le (hK₁L.trans hL.1.le) D.sylowM.le⟩
    · exact ⟨le_sup_right, sup_le (hK₂L.trans hL.1.le) D.sylowM.le⟩
  · have hsupΔ : (⨆ H ∈ ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)), H) =
        (K₁ ⊔ D.T) ⊔ (K₂ ⊔ D.T) := by
      rw [← Finset.sup_eq_iSup]
      simp [Finset.sup_insert, Finset.sup_singleton]
    rw [hsupΔ]
    exact UC22.uc22p22u_uniqueMax_mono D hLle hleM hUL
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact hInF₁
    · exact hInF₂
  · have h1 : ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)).sum (fun _ => 1) =
        ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : ({K₁ ⊔ D.T, K₂ ⊔ D.T} : Finset (Subgroup G)).card ≤ 2 := by
      have h := Finset.card_insert_le (K₁ ⊔ D.T) ({K₂ ⊔ D.T} : Finset (Subgroup G))
      simp only [Finset.card_singleton] at h
      omega
    rw [h1]
    exact h2

theorem seventeen_thirtyone_normal_ne_bot
    (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h126 : R126 D) (h869 : F08.R869 D)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (hMc2F4 : W4McClurg2F4)
    (hMcTits : W4McClurgTits) (h2F4 : Inputs1719.W4Lem4_17TwoF4N)
    (hKc : Inputs1719.K_L2SzAutRank) (hP : Inputs1719.K_2F4ParabolicGen)
    (hTi : Inputs1719.K_TitsParabolicGen)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥)
    (L : Subgroup G) (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) :
    (∀ n : ℕ, ¬ CFSG.Quasithin.Is2F4 n (Bar2 L)) ∧ ¬ LieModel (Bar2 L) .Tits 0 2 1 := by
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  have hLMbar : barSub V₀ V hV.isElemAbelian L ≤ Mbar D.M V₀ V hV.isElemAbelian :=
    barSub_mono V₀ V hV.isElemAbelian hL.1.le
  have hNormBar : ((barSub V₀ V hV.isElemAbelian L).subgroupOf
      (Mbar D.M V₀ V hV.isElemAbelian)).Normal :=
    barSub_subgroupOf_mbar_normal hV.isElemAbelian hL.1.le hMN
  have hpow : ∀ w : Vtil V₀ V hV.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian
  have hC117 := ElevenNine.c117_of_hyp11 D h869 (hV.hyp11 h127)
  have hk := TwelveSeven.k_le_two D
  constructor
  · intro n h2F4Shape
    have hshape : ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
        CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :=
      Or.inl ⟨n, h2F4Shape⟩
    have hnt := not_thin_of_exceptional k_exceptionalNotThin hshape
    have hL1 := barSub_ne_bot_of_not_thin hV hC117 hL hnt
    have hshapeBar := is2F4_barSub_of_is2F4 hV hL hL1 h2F4Shape
    have hfix := fixV_barSub_eq_bot_of_normal_gen h640 hFF h869 h127 hV hL hN
      (Or.inl ⟨n, h2F4Shape⟩)
    have hm : 4 * n + 2 < mBar D.M V₀ V hV.isElemAbelian :=
      hMc2F4 (W := Vtil V₀ V hV.isElemAbelian) hpow
        (Y := Mbar D.M V₀ V hV.isElemAbelian) (L := barSub V₀ V hV.isElemAbelian L) (n := n)
        hLMbar hNormBar hshapeBar hfix
    have hsimple : IsSimpleGroup (Bar2 L) :=
      (CFSG.LieType.Simplicity.fam_2f4_simplicity (Bar2 L) 2 n h2F4Shape).2
    have hb := bBar_le_two_mul_of_is2F4 hV h2F4 hL hN hL1 hfix hsimple h2F4Shape
    have hb' : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 * n := by
      rwa [uc22p2214_conjClosure_eq_of_normal hL.1.le hN]
    have hUL : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le
      (h869 L (Or.inl hL) L le_rfl (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt)
    obtain ⟨Δ, hΔ, hΔU, ι, hι, hsum⟩ := exists_delta_2F4 hKc hP hL hN hUL h2F4Shape
    have h2 := twelve_twentyThree_two D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV₀
      hL.1 hL.2.2 hL1 hΔ hΔU ι hι
    omega
  · intro hTits
    have hshape : ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
        CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :=
      Or.inr (Or.inl hTits)
    have hnt := not_thin_of_exceptional k_exceptionalNotThin hshape
    have hL1 := barSub_ne_bot_of_not_thin hV hC117 hL hnt
    have hRT : CFSG.Quasithin.IsTits (Bar2 L) :=
      (CFSG.Blueprint.LieModel.reeTitsModel hTits (by decide)).2
    have hshapeBar := isTits_barSub_of_isTits hV hL hL1 hRT
    have hfix := fixV_barSub_eq_bot_of_normal_gen h640 hFF h869 h127 hV hL hN
      (Or.inr (Or.inl hRT))
    have hm : 6 < mBar D.M V₀ V hV.isElemAbelian :=
      hMcTits (W := Vtil V₀ V hV.isElemAbelian) hpow
        (Y := Mbar D.M V₀ V hV.isElemAbelian) (L := barSub V₀ V hV.isElemAbelian L)
        hLMbar hNormBar hshapeBar hfix
    have hsimple : IsSimpleGroup (Bar2 L) :=
      (CFSG.LieType.Simplicity.fam_tits_simplicity (Bar2 L) 2 1 hRT).2
    have hb := bBar_le_two_of_isTits hV hL hN hL1 hfix hsimple hRT
    have hb' : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 := by
      rwa [uc22p2214_conjClosure_eq_of_normal hL.1.le hN]
    have hUL : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le
      (h869 L (Or.inl hL) L le_rfl (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt)
    obtain ⟨Δ, hΔ, hΔU, ι, hι, hsum⟩ := exists_delta_Tits hTi hL hN hUL hTits
    have h2 := twelve_twentyThree_two D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV₀
      hL.1 hL.2.2 hL1 hΔ hΔU ι hι
    omega

theorem false_of_not_normal_2F4
    (D : Data G) (hSg : UC6S846.SigmaStd D)
    (hP : Inputs1719.K_2F4Parabolic) (hTi : Inputs1719.K_TitsParabolic)
    (hK3 : Inputs1719.K_BorelTorusAbelian) (hK4 : Inputs1719.K_CartanRank)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h1 : R17_1At D V₀ V hV)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ D.M ≤ normalizer (L : Set G)) {n : ℕ}
    (h2F4 : CFSG.Quasithin.Is2F4 n (Bar2 L)) : False := by
  classical
  obtain ⟨-, h3⟩ := odd_and_three_le_of_is2F4 h2F4
  have hk1 : D.k = 1 := k_eq_one_of_not_normal hSg hP hTi hL hnN (Or.inl ⟨n, h2F4⟩)
  have hnn : ¬ (L.subgroupOf D.M).Normal := fun hN =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN)
  have h2n : 7 ≤ 2 ^ n - 1 := by
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 * m := ⟨2 ^ (n - 1), by rw [← pow_succ']; congr 1; omega⟩
    omega
  have hLie : LieModel (Bar2 L) .twistedF4 0 2 n := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h2F4⟩))
  have hadm := hLie.admissible
  have hsimple : IsSimpleGroup (Bar2 L) :=
    (CFSG.LieType.Simplicity.fam_2f4_simplicity (Bar2 L) 2 n h2F4).2
  have hZbot : Subgroup.center (Bar2 L) = ⊥ :=
    @center_eq_bot_of_simple_of_two_le_pRank _ _ _ hsimple 3 Nat.prime_three
      (two_le_pRank_three_bar2_of_exceptional hP hTi (Or.inl ⟨n, h2F4⟩))
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZbot
  have hLieInf : LieModel (BarInf L) .twistedF4 0 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLie
  have hchev : CIsChevOver (BarInf L) n := ⟨.twistedF4, 0, hadm, hLieInf⟩
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.PermSylowTwo.exists_isSylowTwoOf_top (Bar2 L)
  obtain ⟨e'⟩ := uc22p21k_quotCenter_equiv hZbot
  have hLieQ : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .twistedF4 0 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e'.symm hLie
  have hoddc : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    rw [hZbot, Subgroup.card_bot]
    exact odd_one
  have hrank2 : 2 ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) :=
    hK4 (Bar2 L) .twistedF4 0 n hadm hLieQ hL.2.2 hoddc S hS r hr hr2 hrdvd
      (fun h => nomatch h) (fun h => nomatch h)
  have hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    rw [hZbot, Subgroup.card_bot]
    exact hr.not_dvd_one
  obtain ⟨C, hC⟩ := exists_cIsCartanOf hL
  have hCr : 2 ≤ CFSG.Open.pRank r C :=
    cartanRank_le_pRank_cartan hK4 hL hC hadm hLieInf hr hr2 hrdvd
      (fun h => nomatch h) (fun h => nomatch h)
  have hLr : 2 ≤ CFSG.Open.pRank r L := hCr.trans (CFSG.SectionRank.pRank_mono hr.one_lt hC.1)
  obtain ⟨E₀, hE₀L, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank hr.one_lt L
  have h4 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.calCRankTwice D.M L hL hnN r hr hr2 hZ
    E₀ hE₀L hE₀el (CFSG.Open.pRank r L) hE₀card
  have hrsig : r ∈ D.sig := hSg.four_mem r hr hr2 (by omega)
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hrsig
  obtain ⟨E, hEB, hEel, hperm, hErank⟩ :=
    exists_permuting_elemAbelian_noncyclic_of_calC (D := D) (L := L)
      (X := UC22.conjClosure D.M L) (n := n) (r := r) hL rfl hchev hK3 hnn hZ S hS
      (by omega) hr hr2
  have hEM : E ≤ D.M :=
    (hEB.trans inf_le_left).trans (TwelveTwentyThree.conjClosure_le hL.1.le)
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hin : F11.InP11 D E := inP11_of_strongly hr hr2 hsp hEM hEel.isPGroup hEel.2 hEnc hperm
  have hk2 : D.k = 2 := (h1.2 ⟨E, hin⟩).2.1
  omega

theorem seventeen_thirtyone
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h869 : F08.R869 D) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hMc2F4 : W4McClurg2F4) (hMcTits : W4McClurgTits) (h2F4 : Inputs1719.W4Lem4_17TwoF4N)
    (hK4 : Inputs1719.K_CartanRank)
    (hSg : UC6S846.SigmaStd D)
    (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) (h1 : R17_1At D V₀ V hV) :
    R17_31At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  have hPGen : Inputs1719.K_2F4ParabolicGen := Inputs1719.k_2F4ParabolicGen_holds
  have hTiGen : Inputs1719.K_TitsParabolicGen := Inputs1719.k_TitsParabolicGen_holds
  have hP : Inputs1719.K_2F4Parabolic := Inputs1719.k_2F4Parabolic_holds
  have hTi : Inputs1719.K_TitsParabolic := Inputs1719.k_TitsParabolic_holds
  intro L hL
  by_cases hN : (L.subgroupOf D.M).Normal
  · by_cases hV₀ : V₀ = ⊥
    · subst hV₀
      exact seventeen_thirtyone_normal_v0eq1 D hx h61 h126 h111 h869 h127 h640 hFF hMc2F4
        hMcTits h2F4 hV L hL hN
    · exact seventeen_thirtyone_normal_ne_bot D hx h61 h127 h1114 h162 hTor h1482 h126
        h869 h640 hFF hMc2F4 hMcTits h2F4 Inputs1719.k_L2SzAutRank_holds hPGen hTiGen hV hV₀ L
        hL hN
  · have hnN : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
      hN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
    refine ⟨fun n h2F4 => false_of_not_normal_2F4 D hSg hP hTi hK3 hK4 hV h1 hL hnN h2F4,
      fun hTits => ?_⟩
    obtain ⟨E, hEX, hEel, hperm, hrank⟩ := gap17_31_TitsPerm_holds hTiGen D L hL hnN hTits
    exact false_of_permuting_elemAbelian_rank_two_of_k_one h1
      (k_eq_one_of_not_normal hSg hP hTi hL hnN (Or.inr hTits))
      (hEX.trans (TwelveTwentyThree.conjClosure_le hL.1.le)) hEel hperm hrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
