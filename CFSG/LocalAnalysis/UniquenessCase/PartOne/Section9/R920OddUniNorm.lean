module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddInv
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddPair
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def tbar9 (L Y H : Subgroup G) : Subgroup (F09.Lbar9 Y H) :=
  (F09.img9 H (L ⊓ F09.L9 Y H)).subgroupOf (F09.img9 H (F09.L9 Y H))

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem inf_M_le_normalizer_L (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) : H ⊓ D.M ≤ normalizer (L : Set G) := by
  intro g hg
  obtain ⟨hgH, hgM⟩ := Subgroup.mem_inf.1 hg
  by_contra hgL
  have hne : L.map (MulAut.conj g).toMonoidHom ≠ L := fun h =>
    hgL (UC6S846.mem_normalizer_iff_map_conj.2 h)
  have hL'C : L.map (MulAut.conj g).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M (MulAut.conj g)
      (UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hgM)) S.L_mem
  obtain ⟨-, -, hrk⟩ := hyp.2.1
  obtain ⟨x, hxX, hx⟩ :=
    exists_orderOf_eq_of_dvd_card_bar2 Nat.prime_three S.three_dvd_card_bar2_opp
  have hxK : x ∈ F09.L9 Y H := F09.opp_le_L9 Y H hxX
  have hxM : x ∈ D.M := S.opp_le_M hxX
  have hy : orderOf (g * x * g⁻¹) = 3 := by
    rw [← hx]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  have hyK : g * x * g⁻¹ ∈ F09.L9 Y H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_L9 Y H hgH) x).1 hxK
  have h2 : 2 ≤ CFSG.Open.pRank 3 (F09.L9 Y H ⊓ D.M) :=
    two_le_pRank_of_pair Nat.prime_three (by norm_num) S.L_mem hL'C hne.symm
      (center_eq_bot_of_isL2Odd S.L_mem.2.2 S.shape_L) inf_le_right (S.opp_le_L hxX)
      (Subgroup.mem_map.2 ⟨x, S.opp_le_L hxX, rfl⟩) (Subgroup.mem_inf.2 ⟨hxK, hxM⟩)
      (Subgroup.mem_inf.2 ⟨hyK, D.M.mul_mem (D.M.mul_mem hgM hxM) (D.M.inv_mem hgM)⟩) hx hy
  have h1 : CFSG.Open.pRank 3 (F09.L9 Y H ⊓ D.M) ≤ CFSG.Open.pRank 3 (F09.L9 Y H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) inf_le_left
  have h3 : CFSG.Open.pRank 3 (F09.L9 Y H) = 1 := hrk
  omega

theorem nonempty_bar2_L_equiv_inf_L9 (S : Slice D L D₃ Y H q) :
    Nonempty (Bar2 L ≃* Bar2 (L ⊓ F09.L9 Y H)) := by
  have hXT : Opp 3 Y ≤ L ⊓ F09.L9 Y H := le_inf S.opp_le_L (F09.opp_le_L9 Y H)
  have hXN : Opp 3 Y ≤ normalizer (pCoreOf 2 L : Set G) :=
    S.opp_le_L.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hT : L ⊓ F09.L9 Y H = Opp 3 Y ⊔ pCoreOf 2 (L ⊓ F09.L9 Y H) := by
    refine le_antisymm (fun t ht => ?_) (sup_le hXT (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
    have ht' : t ∈ (Opp 3 Y : Set G) * (pCoreOf 2 L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN, ← S.L_eq_opp_sup]
      exact ht.1
    obtain ⟨a, ha, b, hb, rfl⟩ := ht'
    have hbT : b ∈ L ⊓ F09.L9 Y H := by
      rw [← inv_mul_cancel_left a b]
      exact (L ⊓ F09.L9 Y H).mul_mem ((L ⊓ F09.L9 Y H).inv_mem (hXT ha)) ht
    exact Subgroup.mul_mem_sup ha
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 inf_le_left ⟨hbT, hb⟩)
  obtain ⟨e₁⟩ := S.nonempty_bar2_L_opp_equiv
  obtain ⟨e₂⟩ :=
    CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv hXT hT
  exact ⟨e₁.trans e₂.symm⟩

theorem inf_L9_inf_I9_le_pCoreOf (S : Slice D L D₃ Y H q) :
    (L ⊓ F09.L9 Y H) ⊓ F09.I9 H ≤ pCoreOf 2 (L ⊓ F09.L9 Y H) := by
  set T := L ⊓ F09.L9 Y H
  have hTH : T ≤ H := inf_le_right.trans (L9_le_of_le S.Y_le_H)
  have hHI : H ≤ normalizer (F09.I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  set N : Subgroup ↥T := (F09.I9 H).subgroupOf T with hN
  haveI : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (hTH.trans hHI)
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have h2 : Nat.card N ∣ Nat.card (F09.I9 H) := by
      rw [← Subgroup.card_map_of_injective T.subtype_injective, hN,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcop : Nat.Coprime 3 (Nat.card (F09.I9 H)) :=
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H
    exact fun h3 => absurd (Nat.Coprime.coprime_dvd_right (h3.trans h2) hcop) (by decide)
  obtain ⟨e⟩ := S.nonempty_bar2_L_equiv_inf_L9
  obtain ⟨e'⟩ := S.nonempty_bar2_L_opp_equiv
  have h3 : 3 ∣ Nat.card (Bar2 T) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv]
    exact S.three_dvd_card_bar2_opp
  have hle := le_pCore_two_of_normal
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide)
      (CFSG.Blueprint.LieModel.of_mulEquiv e S.shape_L)) h3 hN3
  intro x hx
  exact (CFSG.mem_openPCoreOf_iff (⟨x, hx.1⟩ : ↥T)).2 (hle (Subgroup.mem_subgroupOf.2 hx.2))

theorem isL2Odd_bar2_tbar9 (S : Slice D L D₃ Y H q) : IsL2Odd (Bar2 (tbar9 L Y H)) q := by
  have hTH : L ⊓ F09.L9 Y H ≤ H := inf_le_right.trans (L9_le_of_le S.Y_le_H)
  have hle : F09.img9 H (L ⊓ F09.L9 Y H) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono (Subgroup.comap_mono inf_le_right)
  have hker : IsPGroup 2 (toImg9 hTH).ker := by
    have hO : IsPGroup 2 ↥(pCoreOf 2 (L ⊓ F09.L9 Y H)) := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      exact CFSG.pCore_isPGroup.map _
    intro g
    have hg : ((g : ↥(L ⊓ F09.L9 Y H)) : G) ∈ pCoreOf 2 (L ⊓ F09.L9 Y H) :=
      S.inf_L9_inf_I9_le_pCoreOf ⟨(g : ↥(L ⊓ F09.L9 Y H)).2, (mem_ker_toImg9 hTH).1 g.2⟩
    obtain ⟨k, hk⟩ := hO ⟨_, hg⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (toImg9 hTH)
    (toImg9_surjective hTH) hker
  obtain ⟨e₀⟩ := S.nonempty_bar2_L_equiv_inf_L9
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (e.trans (UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hle)).symm)
    (CFSG.Blueprint.LieModel.of_mulEquiv e₀ S.shape_L)

theorem wbar9_le_normalizer_tbar9 (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) :
    wbar9 D Y H ≤ normalizer (tbar9 L Y H : Set (F09.Lbar9 Y H)) := by
  intro w hw
  rw [wbar9, Subgroup.mem_subgroupOf] at hw
  obtain ⟨g, hg, hgw⟩ := Subgroup.mem_map.1 hw
  have hgT : (g : G) ∈ normalizer ((L ⊓ F09.L9 Y H : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨S.inf_M_le_normalizer_L hyp (Subgroup.mem_subgroupOf.1 hg), le_normalizer_L9 Y H g.2⟩
  have hg' : g ∈ normalizer (((L ⊓ F09.L9 Y H).subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    Subgroup.le_normalizer_comap H.subtype hgT
  have hN : (w : F09.Hbar9 H) ∈
      normalizer (F09.img9 H (L ⊓ F09.L9 Y H) : Set (F09.Hbar9 H)) := by
    rw [← hgw]
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))
      (Subgroup.mem_map_of_mem _ hg')
  rw [Subgroup.mem_normalizer_iff]
  intro t
  simp only [tbar9, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 hN (t : F09.Hbar9 H)

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
