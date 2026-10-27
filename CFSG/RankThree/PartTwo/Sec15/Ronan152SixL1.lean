module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Ctx
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25F
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.GH74.GLS.LU.Local.FiveSL2

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups

namespace Ronan152Six

open Proof152Gen Ronan152SL25

section SLTwoFive

variable {X₀ : Type} [Group X₀] [Finite X₀]

theorem le_theta_of_quot_sl25 (hXs : IsSimpleGroup (X₀ ⧸ aschbacherSolvableCore 3 X₀))
    {R : Subgroup X₀} [R.Normal] (e : X₀ ⧸ R ≃* SL(2, ZMod 5)) :
    R ≤ aschbacherSolvableCore 3 X₀ := by
  have hθ := solvable_prime_complement_core_characterization (H := X₀) Nat.prime_three
  set θ := aschbacherSolvableCore 3 X₀ with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hSLp : ⁅(⊤ : Subgroup (X₀ ⧸ R)), ⊤⁆ = ⊤ :=
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_perfect e.symm
  have hSL120 : Nat.card (X₀ ⧸ R) = 120 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm
  have hSLnt : Nontrivial (X₀ ⧸ R) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hSL120]
    norm_num
  have hSLns : ¬ Group.IsSolvable (X₀ ⧸ R) := by
    intro hs
    have : Group.IsPerfect (X₀ ⧸ R) := ⟨hSLp⟩
    exact Group.IsPerfect.not_isSolvable (X₀ ⧸ R) hs
  have hRn : (R.map π).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective θ)
  rcases hRn.eq_bot_or_eq_top with hbot | htop
  · rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · exfalso
    have hsup : R ⊔ θ = ⊤ := by
      have h1 := Subgroup.comap_map_eq π R
      rw [htop, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' R).comp θ.subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
      have hx : x ∈ R ⊔ θ := hsup ▸ Subgroup.mem_top x
      rw [Subgroup.mem_sup_of_normal_left] at hx
      obtain ⟨n, hn, t, ht, rfl⟩ := hx
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have : Group.IsSolvable θ := hθ.1
    exact hSLns (Group.isSolvable_of_surjective hsurj)

theorem dvd_card_of_cover_sl25 (hXs : IsSimpleGroup (X₀ ⧸ aschbacherSolvableCore 3 X₀))
    (hX60 : Nat.card (X₀ ⧸ aschbacherSolvableCore 3 X₀) = 60)
    {R : Subgroup X₀} [R.Normal] (e : X₀ ⧸ R ≃* SL(2, ZMod 5)) {D : Subgroup X₀}
    (hD : D.map (QuotientGroup.mk' (aschbacherSolvableCore 3 X₀)) = ⊤) :
    120 ∣ Nat.card D := by
  set θ := aschbacherSolvableCore 3 X₀ with hθdef
  have hRθ : R ≤ θ := le_theta_of_quot_sl25 hXs e
  have hSL120 : Nat.card (X₀ ⧸ R) = 120 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm
  set H := D.map (QuotientGroup.mk' R) with hH
  set ψ : X₀ ⧸ R →* X₀ ⧸ θ := QuotientGroup.map R θ (MonoidHom.id X₀) (by
    intro x hx
    exact hRθ hx) with hψ
  have hψH : H.map ψ = ⊤ := by
    rw [hH, Subgroup.map_map]
    have : ψ.comp (QuotientGroup.mk' R) = QuotientGroup.mk' θ := by
      ext x
      rfl
    rw [this, hD]
  have h60 : 60 ∣ Nat.card H := by
    have h := Subgroup.card_map_dvd H ψ
    rw [hψH, Subgroup.card_top, hX60] at h
    exact h
  have h120 : Nat.card H ∣ 120 := hSL120 ▸ Subgroup.card_subgroup_dvd_card H
  have hHcard : Nat.card H = 120 := by
    obtain ⟨k, hk⟩ := h60
    have hk' : 60 * k ∣ 60 * 2 := by rw [← hk]; exact h120
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hk'
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h1 | h2
    · exfalso
      have hH60 : Nat.card H = 60 := by rw [hk, h1]
      have hidx : H.index = 2 := by
        have h := Subgroup.card_mul_index H
        rw [hH60, hSL120] at h
        omega
      have hHn : H.Normal := Subgroup.normal_of_index_eq_two hidx
      rcases CFSG.GH74.GLS.LU.Local.Five.sl2_five_normal_cases e.symm H with h0 | hZ | htop
      · rw [h0, Subgroup.card_bot] at hH60
        omega
      · rw [hZ, CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm] at hH60
        omega
      · rw [htop, Subgroup.card_top, hSL120] at hH60
        omega
    · rw [hk, h2]
  have h := Subgroup.card_map_dvd D (QuotientGroup.mk' R)
  rw [← hH, hHcard] at h
  exact h

end SLTwoFive

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_pCoreOf_centralizer (h142 : Item142AllS14) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {M X : Subgroup G} (hctx : Ctx152J A (lB A) M X) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d)
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {c, d} : Set G)) :
    ∃ z ∈ CFSG.Open.pCoreOf 2 L,
      z ∈ Subgroup.centralizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) ∧ z ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
  have hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp).1
  have hd3 : d ^ 3 = 1 := (Late.isE27_of_mem_partTwoE hS13.mem_partTwoE).1.2 d hdA
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := hdc
  have hdXL : d ∈ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hctx.norm_x hS13.le_normalizer hdA
  have hdsc : d ∈ Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) := by
    rw [hcent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdC : d ∈ Sec4.thetaQuotCentralizer X :=
    Proof152F.mem_thetaQuotCentralizer_of_mem hctx.norm_x hdsc
  have hW : ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ :=
    map_inf_eq_top_of_centJ h142 h hctx hdA hJ hcent
  have hW' := map_inf_centralizer_eq_top inf_le_left hdXL hd3 hdC hW
  obtain ⟨D, hDW, hDp, hDtop⟩ := exists_isPerfect_cover hXp hW'
  have hDX : D ≤ X := hDW.trans (inf_le_left.trans inf_le_left)
  have hDL : D ≤ L := hDW.trans (inf_le_left.trans inf_le_right)
  have hDd : D ≤ Subgroup.centralizer ({d} : Set G) := hDW.trans inf_le_right
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set z : ↥L ⧸ θ := ρ ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θ)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥L ⧸ θ), z ∈ (S' : Subgroup (↥L ⧸ θ)) ∧
      (S' : Subgroup (↥L ⧸ θ)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    refine ⟨S3.mapSurjective (QuotientGroup.mk'_surjective θ), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  have hDz : (D.subgroupOf L).map ρ ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyd : (y : G) * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hDd (Subgroup.mem_subgroupOf.mp hy))
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyd
  have hθL2 : IsPGroup 2 θ := isPGroup_theta_of_j2 h hJ
  have hF60 := card_map_eq_sixty hXs hX60 hJ hθL2 hDX hDL hDtop hDp hz1 hzc hDz
  have hD120 : 120 ∣ Nat.card D := by
    have hD' : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ :=
      hDtop
    have hcard : Nat.card (D.subgroupOf X) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv
    rcases hctx.sl25 with he | he
    · obtain ⟨e⟩ := he
      exact hcard ▸ dvd_card_of_cover_sl25 hXs hX60 e hD'
    · obtain ⟨e⟩ := he
      exact hcard ▸ dvd_card_of_cover_sl25 hXs hX60 e hD'
  set fL : ↥D →* ↥L ⧸ θ := ρ.comp (Subgroup.inclusion hDL) with hfL
  have hfLr : fL.range = (D.subgroupOf L).map ρ := by
    rw [hfL, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr y.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker : fL.ker ≠ ⊥ := by
    intro hbot
    have h1 := Subgroup.card_mul_index fL.ker
    rw [Subgroup.index_ker, hfLr, hF60, hbot, Subgroup.card_bot, one_mul] at h1
    rw [← h1] at hD120
    norm_num at hD120
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hxθ : Subgroup.inclusion hDL x ∈ θ := by
    have h1 : fL x = 1 := hx
    rw [hfL, MonoidHom.comp_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hθO : θ ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, hθL2⟩
  refine ⟨(x : G), ⟨Subgroup.inclusion hDL x, hθO hxθ, rfl⟩, ?_, ?_⟩
  ·
    have hxc : (x : G) ∈ Subgroup.centralizer ({c} : Set G) := hS13.le_centralizer (hDL x.2)
    have hxd : (x : G) ∈ Subgroup.centralizer ({d} : Set G) := hDd x.2
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : Subgroup.closure {c, d} ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxd).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  · exact fun h1 => hx1' (Subtype.ext h1)

theorem pCoreOf_inf_centralizer_ne_bot (h142 : Item142AllS14) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {M X : Subgroup G} (hctx : Ctx152J A (lB A) M X) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d)
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {c, d} : Set G)) :
    CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) ≠ ⊥ := by
  obtain ⟨z, hzO, hzC, hz1⟩ :=
    exists_mem_pCoreOf_centralizer h142 h hJ hctx hdA hd1 hdc hcent
  intro hbot
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzC d
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))).symm
  have : z ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) := ⟨hzO, hzd⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hz1 this

end Config

end Ronan152Six

end CFSG.RankThree.PartTwo.Sec15
