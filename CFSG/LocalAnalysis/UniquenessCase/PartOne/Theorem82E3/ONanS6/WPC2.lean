module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

noncomputable abbrev Lz (c : Ctx82E3 D) (x : G) : Subgroup G :=
  inSubgroup perfectResidual (c.L ⊓ Subgroup.centralizer ({x} : Set G))

theorem isHatON_lbar_of_onan'
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩

theorem zSub_image_le_center
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ((zSub P c.L).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) ≤ Subgroup.center c.Lbar := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = (Q.subgroupOf c.L).map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hHat := isHatON_lbar_of_onan' c hON
  have hcen := (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S).2.2.2
  rintro w ⟨z, hz, rfl⟩
  have hzZ : (z : G) ∈ zSub P c.L := Subgroup.mem_subgroupOf.mp hz
  have hzQ : (z : G) ∈ Q := hzZ.1
  have hzcent := hzZ.2
  have hzY : z ∈ Q.subgroupOf c.L := by
    rw [Subgroup.mem_subgroupOf]; exact hzQ
  have hzS : π z ∈ (S : Subgroup c.Lbar) := by
    rw [hScoe]
    exact Subgroup.mem_map_of_mem π hzY
  refine hcen (π z) hzS ?_
  intro s hs
  rw [hScoe] at hs
  obtain ⟨q, hqY, rfl⟩ := Subgroup.mem_map.mp hs
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hqY
  exact Subgroup.mem_centralizer_iff.mp hzcent (q : G) hqQ

theorem zSub_commutator_le_pCoreOf
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ zSub P c.L) :
    ∀ k ∈ c.L, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := by
  classical
  intro k hk
  have hxL : x ∈ c.L := (Subgroup.mem_inf.mp hx).1.2
  let xL : ↥c.L := ⟨x, hxL⟩
  let kL : ↥c.L := ⟨k, hk⟩
  have hxcen : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) xL ∈
      Subgroup.center c.Lbar :=
    zSub_image_le_center c hON hP ⟨xL, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hcomm : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) xL *
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) kL =
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) kL *
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) xL :=
    (Subgroup.mem_center_iff.mp hxcen _).symm
  have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
      (xL * kL * xL⁻¹ * kL⁻¹) = 1 := by
    rw [show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (xL * kL * xL⁻¹ * kL⁻¹) =
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) xL *
          QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) kL *
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) xL)⁻¹ *
          (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) kL)⁻¹ by
      simp only [map_mul, map_inv]]
    rw [hcomm]
    group
  have hmem : (xL * kL * xL⁻¹ * kL⁻¹ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L :=
    (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨_, hmem, rfl⟩

noncomputable abbrev Cbar (c : Ctx82E3 D) : Subgroup G :=
  (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map D.M.subtype

theorem card_zSub_of_onan'
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card (zSub P c.L) = 3 := by
  simpa [zSub] using Ctx82E3.card_inf_centralizer_of_onan c hON hP

theorem Lz_sup_pCore_eq
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    c.L = Lz c x ⊔ CFSG.Open.pCoreOf 2 c.L := by
  have hxL : x ∈ c.L := (Subgroup.mem_inf.mp hx).1.2
  have hxM : x ∈ D.M := c.hyp81.1 hxL
  have hx3 : x ^ 3 = 1 := hA.2 x (hZA hx)
  have hq : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native c.Lbar).mp hON.1
  have hK : c.L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn D.M :=
    CFSG.RankThree.PartTwo.Sec18.mem_oTwoComponentsIn_of_quasisimple c.hyp81.1
      ((CFSG.Open.IsSubnormal.iff_subgroupOf c.hyp81.1).mp c.hyp81.2.1)
      c.hyp81.2.2.1 (by simpa [Ctx82E3.Lbar] using hq)
  have hKsn : x ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hxM
  have hcc := zSub_commutator_le_pCoreOf c hON hP hx
  exact (CFSG.RankThree.PartTwo.Sec18.Item18ResProof.mem_thetaComponentsAt_perfectResidual
    (K := c.L) (X := D.M) (c := x) hK hC hKsn hx3 hcc).2.2

theorem Lz_image_eq_top
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    ((Lz c x).subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) = ⊤ := by
  have hsup := Lz_sup_pCore_eq c hON hP hA hZA hx hx1 hC
  have hLzL : Lz c x ≤ c.L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hOL : CFSG.Open.pCoreOf 2 c.L ≤ c.L :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 c.L
  refine eq_top_iff.mpr ?_
  rintro q -
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) q
  have hlG : (l : G) ∈ Lz c x ⊔ CFSG.Open.pCoreOf 2 c.L := by
    rw [← hsup]
    exact l.2
  have hl : (l : ↥c.L) ∈ (Lz c x).subgroupOf c.L ⊔
      ((CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L) := by
    rw [← Subgroup.subgroupOf_sup hLzL hOL]
    exact Subgroup.mem_subgroupOf.mpr hlG
  have hOeq : (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L = CFSG.Open.pCore 2 ↥c.L := by
    ext u
    simp [CFSG.Open.pCoreOf, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hOsub : ((CFSG.Open.pCoreOf 2 c.L).subgroupOf c.L).Normal := by
    rw [hOeq]
    exact CFSG.pCore_normal
  letI := hOsub
  rw [Subgroup.mem_sup_of_normal_right] at hl
  obtain ⟨lz, hlz, o, ho, hlo⟩ := hl
  refine Subgroup.mem_map.mpr ⟨lz, hlz, ?_⟩
  have ho' : o ∈ CFSG.Open.pCore 2 ↥c.L := by
    rw [← hOeq]
    exact ho
  have ho1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) o = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ho'
  calc QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) lz =
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) lz *
        QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) o := by
        rw [ho1, mul_one]
    _ = QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (lz * o) := (map_mul _ _ _).symm
    _ = QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) l := by rw [hlo]

theorem Lz_mem_thetaComponentsAt
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    Lz c x ∈ thetaComponentsAt 3 x := by
  have hxL : x ∈ c.L := (Subgroup.mem_inf.mp hx).1.2
  have hxM : x ∈ D.M := c.hyp81.1 hxL
  have hx3 : x ^ 3 = 1 := hA.2 x (hZA hx)
  have hq : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native c.Lbar).mp hON.1
  have hK : c.L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn D.M :=
    CFSG.RankThree.PartTwo.Sec18.mem_oTwoComponentsIn_of_quasisimple c.hyp81.1
      ((CFSG.Open.IsSubnormal.iff_subgroupOf c.hyp81.1).mp c.hyp81.2.1)
      c.hyp81.2.2.1 (by simpa [Ctx82E3.Lbar] using hq)
  have hKsn : x ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hxM
  have hcc := zSub_commutator_le_pCoreOf c hON hP hx
  exact (CFSG.RankThree.PartTwo.Sec18.Item18ResProof.mem_thetaComponentsAt_perfectResidual
    (K := c.L) (X := D.M) (c := x) hK hC hKsn hx3 hcc).1

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
