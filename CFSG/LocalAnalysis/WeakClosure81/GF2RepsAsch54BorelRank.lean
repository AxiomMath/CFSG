module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem not_isCalL0_of_isCompositionFactor_of_normal_isPGroup_odd_index
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧
        ∃ a b : L, a * b ≠ b * a)
    {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y) [A.Normal]
    (hA2 : IsPGroup 2 A) (hodd : Odd A.index) {L : Type} [Group L]
    (hcf : E1.IsCompositionFactor Y L) (hcal : IsCalL0 L) : False := by
  obtain ⟨hLfin, hrank, a, b, hab⟩ := hL0 L hcal
  rcases isCompositionFactor_of_normal A hcf with hA | hQ
  · have hAsolv : Group.IsSolvable ↥A :=
      @IsNilpotent.to_isSolvable ↥A _ hA2.isNilpotent
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      (X := ↥A) (L := L) hAsolv hA a b)
  · have hoddQ : Odd (Nat.card (Y ⧸ A)) := by
      rw [← Subgroup.index_eq_card]
      exact hodd
    have hoddL : Odd (Nat.card L) :=
      Odd.of_dvd_nat hoddQ (isCompositionFactor_natCard_dvd hQ)
    have hnotdvd : ¬ 2 ∣ Nat.card L := by
      intro hdvd
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd)) hoddL
    have hrank0 : CFSG.Open.pRank 2 (⊤ : Subgroup L) = 0 :=
      @CFSG.pRank_eq_zero_of_not_dvd_card L _ hLfin 2 Nat.prime_two hnotdvd
    omega

theorem pRank_perfectCore_lGen_of_pRank_normalizer
    (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a)
    {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} (hK : CFSG.Open.IsKGroup Q)
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hT : IsSylowIn 2 T ⊤) {p : ℕ} (hp : p.Prime)
    (hpL : 3 < CFSG.Open.pRank p (⊤ : Subgroup ↥L))
    (hpN : ∀ S : Sylow 2 ↥L,
      1 < CFSG.Open.pRank p (Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L))) :
    3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
      1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T) := by
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal (hT : IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hSylL : IsSylowIn 2 (T ⊓ L) L := hTL
  let S : Sylow 2 ↥L := CFSG.Quasithin.A4.toSylow hTL
  have hScoe : (S : Subgroup ↥L) = (T ⊓ L).subgroupOf L :=
    CFSG.Quasithin.A4.toSylow_coe hTL
  set H : Subgroup Q :=
    Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) with hHdef
  have hTH : T ≤ H := by
    rw [hHdef]
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer ht, by
        rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
        exact Subgroup.mem_top t⟩)
  have hHlt : H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hHtop => ?_
    rw [hHdef] at hHtop
    have hSsubn : ((T ⊓ L).subgroupOf L).Normal := by
      refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
      rw [hHtop]
      exact le_top
    rcases @CFSG.eq_bot_or_eq_top_of_normal ↥L _ hLs ((T ⊓ L).subgroupOf L) hSsubn
      with hbot | htop
    · have hSbot : (S : Subgroup ↥L) = ⊥ := by rw [hScoe, hbot]
      have hnotdvd : ¬ 2 ∣ Nat.card L := by
        have h := S.not_dvd_index
        rwa [hSbot, Subgroup.index_bot] at h
      have hoddL : Odd (Nat.card L) :=
        Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
      have hfinL : Finite L := inferInstance
      exact (Nat.not_odd_iff_even.mpr
        (@CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even L _ hfinL
          hLs hLnab).1) hoddL
    · have hLp : IsPGroup 2 ↥L := by
        have htopP : IsPGroup 2 (⊤ : Subgroup ↥L) := by
          rw [← htop]
          exact CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le inf_le_right hSylL.isPGroup
        exact htopP.of_equiv Subgroup.topEquiv
      have hLsolv : Group.IsSolvable ↥L :=
        @IsNilpotent.to_isSolvable ↥L _ hLp.isNilpotent
      obtain ⟨a, b, hab⟩ := hLnab
      exact hab (@CFSG.LocalAnalysis.ComponentInitial.solvable_simple_abelian ↥L _ hLs
        hLsolv a b)
  have hKL : CFSG.Open.IsKGroup ↥L := hK.of_injective L.subtype L.subtype_injective
  have hcat := hKL.isCatalogGroup_of_surjective ⊤ hLnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    @isSolvable_quotient_of_outSolvable Q _ L hLn (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
        (hS _ hLs hLnab hcat))
  have hSH : T ⊓ L ≤ H := inf_le_left.trans hTH
  have hSleLH : T ⊓ L ≤ L ⊓ H := le_inf inf_le_right hSH
  have hB2 : IsPGroup 2 ((T ⊓ L).subgroupOf (L ⊓ H)) :=
    CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le hSleLH hSylL.isPGroup
  have hLHnorm : L ⊓ H ≤ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
    inf_le_right.trans hHdef.le
  have hBnormal : ((T ⊓ L).subgroupOf (L ⊓ H)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLHnorm
  have hSylLH : IsSylowIn 2 (T ⊓ L) (L ⊓ H) :=
    isSylowIn_of_le_of_le hSylL hSleLH inf_le_left
  have hBidx : ((T ⊓ L).subgroupOf (L ⊓ H)).index = (T ⊓ L).relIndex (L ⊓ H) := by
    rw [← Subgroup.relIndex_top_right ((T ⊓ L).subgroupOf (L ⊓ H))]
    have h := Subgroup.relIndex_subgroupOf (H := T ⊓ L) (K := L ⊓ H) (L := L ⊓ H)
      le_rfl
    simpa [Subgroup.subgroupOf_self] using h
  have hBodd : Odd ((T ⊓ L).subgroupOf (L ⊓ H)).index := by
    rw [hBidx]
    exact Nat.not_even_iff_odd.mp fun he =>
      hSylLH.not_dvd_relIndex (even_iff_two_dvd.mp he)
  have hXeq : L.subgroupOf H = (L ⊓ H).subgroupOf H := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
  let eX : ↥(L.subgroupOf H) ≃* ↥(L ⊓ H) :=
    (MulEquiv.subgroupCongr hXeq).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have hnoH : ¬ HasCompFactor H IsCalL0 := by
    rintro ⟨F, hgrpF, hcf, hcal⟩
    obtain ⟨hFfin, -, a, b, hab⟩ := @hL0 F hgrpF hcal
    have hcfL : @E1.IsCompositionFactor ↥(L.subgroupOf H) _ F hgrpF :=
      @isCompositionFactor_subgroupOf_of_isSolvable_quot Q _ _ L hLn hq H F hgrpF hcf
        ⟨a, b, hab⟩
    have hcfY : @E1.IsCompositionFactor ↥(L ⊓ H) _ F hgrpF :=
      (@CFSG.Quasithin.H13.L829N.isCompositionFactor_congr ↥(L.subgroupOf H)
        ↥(L ⊓ H) _ _ eX F hgrpF).mp hcfL
    exact @not_isCalL0_of_isCompositionFactor_of_normal_isPGroup_odd_index hL0
      ↥(L ⊓ H) _ _ ((T ⊓ L).subgroupOf (L ⊓ H)) hBnormal hB2 hBodd F hgrpF hcfY hcal
  have hHmem : H ∈ calLT IsCalL0 ⊤ T := ⟨hTH, hHlt, hnoH⟩
  have hHle : H ≤ lGen IsCalL0 ⊤ T := le_iSup₂_of_le H hHmem le_rfl
  have hNmap : (Subgroup.normalizer (S : Set ↥L)).map L.subtype ≤ H := by
    have hSset : (S : Set ↥L) =
        (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      congrArg (fun K : Subgroup ↥L => (K : Set ↥L)) hScoe
    rw [hSset]
    rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer L (T ⊓ L)
      inf_le_right]
    change ((L ⊓ H).subgroupOf L).map L.subtype ≤ H
    have hmap : ((L ⊓ H).subgroupOf L).map L.subtype = L ⊓ H := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
    rw [hmap]
    exact inf_le_right
  have hpHgt1 : 1 < CFSG.Open.pRank p H := by
    have hmapRank : CFSG.Open.pRank p (Subgroup.normalizer (S : Set ↥L)) ≤
        CFSG.Open.pRank p H :=
      (CFSG.SectionRank.pRank_le_map (p := p) hp.one_lt L.subtype
        L.subtype_injective _).trans
        (CFSG.SectionRank.pRank_mono hp.one_lt hNmap)
    exact lt_of_lt_of_le (hpN S) hmapRank
  have hlgenRank : 1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T) :=
    lt_of_lt_of_le hpHgt1 (CFSG.SectionRank.pRank_mono hp.one_lt hHle)
  have hLperf : ⁅L, L⁆ = L := by
    have hperfL : Group.IsPerfect ↥L :=
      @CFSG.Semidihedral.CoreFreeDihedral.isPerfect_of_simple_nonabelian ↥L _ hLs hLnab
    have hmap := congrArg (Subgroup.map L.subtype) hperfL.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype] at hmap
    exact hmap
  have hLlePerf : L ≤ perfectCore (⊤ : Subgroup Q) :=
    le_perfectCore_of_perfect le_top hLperf
  have hperfRank : 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) := by
    have htopLe : CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ CFSG.Open.pRank p L := by
      have hmapL : (⊤ : Subgroup ↥L).map L.subtype = L := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      have h := CFSG.SectionRank.pRank_le_map (p := p) hp.one_lt
        L.subtype L.subtype_injective (⊤ : Subgroup ↥L)
      rwa [hmapL] at h
    exact lt_of_lt_of_le hpL (htopLe.trans (CFSG.SectionRank.pRank_mono
      hp.one_lt hLlePerf))
  exact ⟨hperfRank, hlgenRank⟩

theorem asch54Case_of_pRank_normalizer (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a)
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      3 < CFSG.Open.pRank p (⊤ : Subgroup X) ∧
      ∀ S : Sylow 2 X, 1 < CFSG.Open.pRank p (Subgroup.normalizer ((S : Subgroup X) : Set X))) :
    Asch54Case P := by
  intro Q _ _ L T hK hLn hLs hLnab hC hPL _ hT _
  obtain ⟨p, hp, hp2, hpL, hpN⟩ := hP ↥L hPL
  exact Or.inr ⟨p, hp, hp2,
    pRank_perfectCore_lGen_of_pRank_normalizer hS hL0 hK hLn hLs hLnab hC hT hp hpL hpN⟩

end CFSG.LocalAnalysis.WeakClosure81
