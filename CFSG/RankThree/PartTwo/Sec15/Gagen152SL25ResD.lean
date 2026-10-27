module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResCtx
import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofP
import CFSG.GH74.GLS.LU.Local.FiveSL2

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G]

theorem not_le_of_quotient_card_eq_sixty {D : Type*} [Group D] [Finite D]
    {K K' : Subgroup D} [K.Normal] [K'.Normal] (hK : K ≤ K')
    (h60 : Nat.card (D ⧸ K) = 60) (h120 : Nat.card (D ⧸ K') = 120) : False := by
  set π : D ⧸ K →* D ⧸ K' := QuotientGroup.map K K' (MonoidHom.id D) (fun x hx => hK hx)
    with hπ
  have hcomp : π.comp (QuotientGroup.mk' K) = QuotientGroup.mk' K' := by
    ext x
    rfl
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K' y
    exact ⟨QuotientGroup.mk' K x, by rw [← hcomp]; rfl⟩
  have hdvd : Nat.card (D ⧸ K') ∣ Nat.card (D ⧸ K) := by
    have h := Subgroup.card_map_dvd (⊤ : Subgroup (D ⧸ K)) π
    rwa [Subgroup.map_top_of_surjective π hsurj, Subgroup.card_top, Subgroup.card_top] at h
  rw [h60, h120] at hdvd
  norm_num at hdvd

theorem card_map_eq_one_twenty_of_cover {X : Type} [Group X] [Finite X]
    {K θ : Subgroup X} [K.Normal] [θ.Normal] (hKθ : K ≤ θ)
    (e : X ⧸ K ≃* SL(2, ZMod 5)) (hθ60 : Nat.card (X ⧸ θ) = 60) {D : Subgroup X}
    (hD : D.map (QuotientGroup.mk' θ) = ⊤) :
    Nat.card (D.map (QuotientGroup.mk' K)) = 120 := by
  set H : Subgroup (X ⧸ K) := D.map (QuotientGroup.mk' K) with hH
  set ψ : X ⧸ K →* X ⧸ θ := QuotientGroup.map K θ (MonoidHom.id X) (fun x hx => hKθ hx)
    with hψ
  have hψH : H.map ψ = ⊤ := by
    rw [hH, Subgroup.map_map]
    have hcomp : ψ.comp (QuotientGroup.mk' K) = QuotientGroup.mk' θ := by
      ext x
      rfl
    rw [hcomp, hD]
  have h60 : 60 ∣ Nat.card H := by
    have h := Subgroup.card_map_dvd H ψ
    rwa [hψH, Subgroup.card_top, hθ60] at h
  have hX120 : Nat.card (X ⧸ K) = 120 :=
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm
  have h120 : Nat.card H ∣ 120 := hX120 ▸ Subgroup.card_subgroup_dvd_card H
  obtain ⟨k, hk⟩ := h60
  have hk' : 60 * k ∣ 60 * 2 := by rw [← hk]; exact h120
  have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hk'
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h1 | h2
  · exfalso
    have hH60 : Nat.card H = 60 := by rw [hk, h1]
    have hidx : H.index = 2 := by
      have h := Subgroup.card_mul_index H
      rw [hH60, hX120] at h
      omega
    haveI hHn : H.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases CFSG.GH74.GLS.LU.Local.Five.sl2_five_normal_cases e.symm H with h0 | hZ | htop
    · rw [h0, Subgroup.card_bot] at hH60
      omega
    · rw [hZ, CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm] at hH60
      omega
    · rw [htop, Subgroup.card_top, hX120] at hH60
      omega
  · rw [hk, h2]

variable {A : Subgroup G} {c : G} {L M X B : Subgroup G} {b d : G} {Lb : Subgroup G} {p : ℕ}
  {P : Subgroup G} {e : G}

theorem ResCtx.exists_cover
    (h142 : Item142AllS14) (h : ResCtx A c L M X B b d Lb p P e) :
    ∃ D : Subgroup G, D ≤ X ⊓ Lb ⊓ Subgroup.centralizer ({d} : Set G) ∧ Group.IsPerfect D ∧
      (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ ∧
      ∃ z ∈ D, z ∈ inSubgroup (aschbacherSolvableCore 3) Lb ∧ z ∉ oTwoOddIn X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.sec15R.toSec14Std.isE27
  obtain ⟨hbΩ, hLb, hJ, hθL2, hbA, hb1, hdA, hd1, hdc, hdb⟩ :=
    Ronan152SL25.lbConfig_facts hA h.hyp h.config
  have hSb : Sec14Std G A b Lb :=
    { h.sec15R.toSec14Std with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  have hcent' : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {b, d} : Set G) := by
    rw [h.cent, h.config.1]
  obtain ⟨hXs, hX60⟩ := Ronan152SL25.isSimpleGroup_theta_quotJ h.ctx
  have hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (isQuasisimple_theta_of_mem_thetaComponentsIn h.ctx.mem_comp).1
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := hdc
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hdXL : d ∈ Subgroup.normalizer (((X ⊓ Lb) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf h.ctx.norm_x hSb.toSec13Data.le_normalizer hdA
  have hdsc : d ∈ Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) := by
    rw [hcent']
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdC : d ∈ Sec4.thetaQuotCentralizer X :=
    Proof152F.mem_thetaQuotCentralizer_of_mem h.ctx.norm_x hdsc
  have hW : ((X ⊓ Lb).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ :=
    Ronan152SL25.map_inf_eq_top_of_centJ h142 hSb h.ctx hdA hJ hcent'
  have hW' := Proof152Gen.map_inf_centralizer_eq_top (inf_le_left : X ⊓ Lb ≤ X)
    hdXL hd3 hdC hW
  obtain ⟨D, hDW, hDp, hDtop⟩ := Proof152Gen.exists_isPerfect_cover hXp hW'
  have hDX : D ≤ X := hDW.trans (inf_le_left.trans inf_le_left)
  have hDLb : D ≤ Lb := hDW.trans (inf_le_left.trans inf_le_right)
  have hDd : D ≤ Subgroup.centralizer ({d} : Set G) := hDW.trans inf_le_right
  set θL := aschbacherSolvableCore 3 ↥Lb with hθL
  set ρ : ↥Lb →* ↥Lb ⧸ θL := QuotientGroup.mk' θL with hρ
  set z : ↥Lb ⧸ θL := ρ ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥Lb) ∈ θL := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θL) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    have h3 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, hmem⟩ : θL)
    rw [hord] at h3
    exact (solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three).2.2.1 h3
  have hzc : ∃ S' : Sylow 3 (↥Lb ⧸ θL), z ∈ (S' : Subgroup (↥Lb ⧸ θL)) ∧
      (S' : Subgroup (↥Lb ⧸ θL)) ≤ Subgroup.centralizer ({z} : Set (↥Lb ⧸ θL)) := by
    refine ⟨S3.mapSurjective (QuotientGroup.mk'_surjective θL), ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact ⟨⟨d, hdL⟩, hdS3, rfl⟩
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨s, hs, rfl⟩
      have hs' := hS3d hs
      rw [Subgroup.mem_centralizer_singleton_iff] at hs' ⊢
      rw [hz, ← map_mul, ← map_mul, hs']
  have hDz : (D.subgroupOf Lb).map ρ ≤
      Subgroup.centralizer ({z} : Set (↥Lb ⧸ θL)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyd : (y : G) * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hDd (Subgroup.mem_subgroupOf.mp hy))
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyd
  have hF60 : Nat.card ((D.subgroupOf Lb).map ρ) = 60 :=
    Proof152Gen.card_map_eq_sixty hXs hX60 hJ hθL2 hDX hDLb hDtop hDp hz1 hzc hDz
  have h2 : 2 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [hX60]
    norm_num
  have hKθ : (oTwoOddIn X).subgroupOf X ≤ aschbacherSolvableCore 3 ↥X := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := Proof152F.oTwoOddIn_le_theta hXs h2 (Subgroup.mem_subgroupOf.mp hy)
    have hyt : y' = y := Subtype.ext hyy'
    simpa [hyt] using hy'
  have hKeq : (oTwoOddIn X).subgroupOf X =
      (CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
    rw [oTwoOddIn, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self (by simp)
  haveI hKn : ((oTwoOddIn X).subgroupOf X).Normal := by
    rw [hKeq]
    exact Subgroup.Normal.comap (CFSG.oddCore_normal _) _
  have hNle : CFSG.pCore 2 ↥X ≤ (oTwoOddIn X).subgroupOf X := by
    rw [hKeq]
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  have hKmapped : ((oTwoOddIn X).subgroupOf X).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) = CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [hKeq]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  obtain ⟨⟨eSL⟩, -⟩ := Proof152ConfA.sl25_data h.ctx.sl25
  let eX : ↥X ⧸ (oTwoOddIn X).subgroupOf X ≃* SL(2, ZMod 5) :=
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 ↥X)
      ((oTwoOddIn X).subgroupOf X) hNle).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hKmapped).trans eSL)
  have hX120 : Nat.card (↥X ⧸ (oTwoOddIn X).subgroupOf X) = 120 :=
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_card eX.symm
  have hH120 : Nat.card ((D.subgroupOf X).map
      (QuotientGroup.mk' ((oTwoOddIn X).subgroupOf X))) = 120 :=
    card_map_eq_one_twenty_of_cover hKθ eX hX60 hDtop
  set fL : ↥D →* ↥Lb ⧸ θL := ρ.comp (Subgroup.inclusion hDLb) with hfL
  set gX : ↥D →* ↥X ⧸ (oTwoOddIn X).subgroupOf X :=
    (QuotientGroup.mk' ((oTwoOddIn X).subgroupOf X)).comp (Subgroup.inclusion hDX) with hgX
  have hincl : ∀ {K : Subgroup G} (hDK : D ≤ K),
      (Subgroup.inclusion hDK).range = D.subgroupOf K := by
    intro K hDK
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr y.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hfLr : fL.range = (D.subgroupOf Lb).map ρ := by
    rw [hfL, MonoidHom.range_comp, hincl hDLb]
  have hgXr : gX.range = (D.subgroupOf X).map
      (QuotientGroup.mk' ((oTwoOddIn X).subgroupOf X)) := by
    rw [hgX, MonoidHom.range_comp, hincl hDX]
  have hDquot60 : Nat.card (↥D ⧸ fL.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange fL).toEquiv, hfLr, hF60]
  have htop : (D.subgroupOf X).map
      (QuotientGroup.mk' ((oTwoOddIn X).subgroupOf X)) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hH120]; exact hX120.symm)
  have hsurj : Function.Surjective gX := by
    rw [← MonoidHom.range_eq_top, hgXr]
    exact htop
  have hDquot120 : Nat.card (↥D ⧸ gX.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective gX hsurj).toEquiv, hX120]
  have hnotle : ¬ fL.ker ≤ gX.ker := fun hle =>
    not_le_of_quotient_card_eq_sixty hle hDquot60 hDquot120
  obtain ⟨x, hxK, hxK'⟩ := Set.not_subset.mp
    (show ¬ (fL.ker : Set ↥D) ⊆ (gX.ker : Set ↥D) from hnotle)
  have hxθL : Subgroup.inclusion hDLb x ∈ θL := by
    have h1 : fL x = 1 := hxK
    rw [hfL, MonoidHom.comp_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hxR : ((x : ↥D) : G) ∉ oTwoOddIn X := by
    intro hxR
    apply hxK'
    have hmem : (⟨(x : G), hDX x.2⟩ : ↥X) ∈ (oTwoOddIn X).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hxR
    have h1 : gX x = 1 := by
      rw [hgX, MonoidHom.comp_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    exact h1
  exact ⟨D, hDW, hDp, hDtop, (x : G), x.2,
    ⟨Subgroup.inclusion hDLb x, hxθL, rfl⟩, hxR⟩

end Gagen152SL25Res

end CFSG.RankThree.PartTwo.Sec15
