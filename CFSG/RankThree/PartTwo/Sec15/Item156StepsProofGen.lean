module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofCover
public import CFSG.RankThree.PartTwo.Sec15.KS152Named
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Named
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
public import CFSG.RankThree.PartTwo.Sec15.Item156Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen

namespace Proof156

variable {G : Type} [Group G] [Finite G]

theorem facts_of_data156 {A Y L₀ X₁ : Subgroup G} {c₀ d : G}
    (D : Data156 A (lB A) Y c₀ L₀ d X₁) (hA : Late.IsE27 A) :
    A ≤ Subgroup.normalizer (X₁ : Set G) ∧ X₁ = delta A (lB A) X₁ ∧
      inSubgroup (aschbacherSolvableCore 3) X₁ = CFSG.Open.pCoreOf 2 X₁ ∧
      IsQuasisimple (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) ∧
      (Nonempty (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁ ≃* alternatingGroup (Fin 5)) ∨
        Sec4.IsTripleCover (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) (alternatingGroup (Fin 6))) ∧
      3 ∣ Nat.card ((↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) ⧸
        Subgroup.center (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁)) ∧
      Late.sectionCentralizer A X₁ (inSubgroup (aschbacherSolvableCore 3) X₁) =
        (Subgroup.closure {c₀, d} : Set G) ∧
      c₀ ∈ Sec4.thetaQuotCentralizer X₁ ∧ d ∈ Sec4.thetaQuotCentralizer X₁ ∧
      ¬ A ≤ Sec4.thetaQuotCentralizer X₁ := by
  have hX4 : X₁ ∈ scriptY4 A (lB A) := D.mem_x.1
  have hAX : A ≤ Subgroup.normalizer (X₁ : Set G) := hX4.1.2
  have hq2 : IsQuasisimple (↥X₁ ⧸ CFSG.pCore 2 ↥X₁) := hX4.2.2.2
  have hθO := inSubgroup_theta_eq_pCoreOf_of_type hq2 D.type_x
  have hXq := isQuasisimple_theta_of_type hq2 D.type_x
  have htype := type_theta_of_type hq2 D.type_x
  have hcent : Late.sectionCentralizer A X₁ (inSubgroup (aschbacherSolvableCore 3) X₁) =
      (Subgroup.closure {c₀, d} : Set G) := by
    rw [hθO]
    exact D.cent
  have hc₀A : c₀ ∈ A := Subgroup.zpowers_le.mp D.omega.1
  have hcsc : c₀ ∈ Late.sectionCentralizer A X₁ (inSubgroup (aschbacherSolvableCore 3) X₁) := by
    rw [hcent]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hdsc : d ∈ Late.sectionCentralizer A X₁ (inSubgroup (aschbacherSolvableCore 3) X₁) := by
    rw [hcent]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact ⟨hAX, hX4.2.2.1, hθO, hXq, htype, three_dvd_card_quot_center_of_type hXq htype, hcent,
    mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX hcsc,
    mem_thetaQuotCentralizer_of_mem_sectionCentralizer hAX hdsc,
    not_le_thetaQuotCentralizer_of_subset_closure hA hc₀A D.mem_d hcent.le⟩

theorem cover_of_data156 {A L₀ : Subgroup G} {c₀ : G} (h₀ : Sec14Std G A c₀ L₀)
    (h142 : Item142 A (lB A) c₀ L₀ h₀.toSec13Data.isElemAbelian.1 h₀.toSec13Data.mem_A)
    {Y X₁ : Subgroup G} {d : G} (D : Data156 A (lB A) Y c₀ L₀ d X₁) :
    X₁ ≤ (X₁ ⊓ L₀) ⊔ inSubgroup (aschbacherSolvableCore 3) X₁ := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h₀.toSec13Data.mem_partTwoE
  obtain ⟨hAX, hXΔ, -, hXq, -, hX3, -, hcC, -, hAnc⟩ := facts_of_data156 D hA
  exact le_inf_sup_theta_of_item142 h₀ D.hj h142 hAX hXΔ hXq hX3 hcC hAnc

theorem three_dvd_card_inf_of_data156 {A L₀ : Subgroup G} {c₀ : G} (h₀ : Sec14Std G A c₀ L₀)
    (h142 : Item142 A (lB A) c₀ L₀ h₀.toSec13Data.isElemAbelian.1 h₀.toSec13Data.mem_A)
    {Y X₁ : Subgroup G} {d : G} (D : Data156 A (lB A) Y c₀ L₀ d X₁) :
    3 ∣ Nat.card ↥(L₀ ⊓ Y) := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h₀.toSec13Data.mem_partTwoE
  obtain ⟨-, -, -, -, htype, -⟩ := facts_of_data156 D hA
  have hcov := cover_of_data156 h₀ h142 D
  have htop := map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  have h1 : Nat.card (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) ∣ Nat.card ↥(X₁ ⊓ L₀) := by
    have h := Subgroup.card_map_dvd ((X₁ ⊓ L₀).subgroupOf X₁)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X₁))
    rw [htop, Subgroup.card_top,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X₁ ⊓ L₀ ≤ X₁)).toEquiv] at h
    exact h
  have h3 : 3 ∣ Nat.card (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) := by
    rcases card_of_type htype with h | h <;> rw [h] <;> norm_num
  have hle : X₁ ⊓ L₀ ≤ L₀ ⊓ Y := le_inf inf_le_right (inf_le_left.trans D.le_x)
  exact (h3.trans h1).trans (Subgroup.card_dvd_of_le hle)

theorem card_dvd_card_map_of_cover {X L D : Subgroup G}
    (hXq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hZ3 : IsPGroup 3 (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)))
    (hθL2 : IsPGroup 2 (aschbacherSolvableCore 3 ↥L)) (hDX : D ≤ X) (hDL : D ≤ L)
    (hDtop : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) ∣
      Nat.card ((D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let θX := aschbacherSolvableCore 3 ↥X
  let θL := aschbacherSolvableCore 3 ↥L
  let fX : ↥D →* ↥X ⧸ θX := (QuotientGroup.mk' θX).comp (Subgroup.inclusion hDX)
  let fL : ↥D →* ↥L ⧸ θL := (QuotientGroup.mk' θL).comp (Subgroup.inclusion hDL)
  have hincl : ∀ {K : Subgroup G} (hDK : D ≤ K),
      (Subgroup.inclusion hDK).range = D.subgroupOf K := by
    intro K hDK
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr y.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hfXr : fX.range = (D.subgroupOf X).map (QuotientGroup.mk' θX) := by
    rw [MonoidHom.range_comp, hincl hDX]
  have hfLr : fL.range = (D.subgroupOf L).map (QuotientGroup.mk' θL) := by
    rw [MonoidHom.range_comp, hincl hDL]
  have hcardX : Nat.card fX.ker * Nat.card (↥X ⧸ θX) = Nat.card D := by
    have h := Subgroup.card_mul_index fX.ker
    rw [Subgroup.index_ker, hfXr, hDtop, Subgroup.card_top] at h
    exact h
  have hcardL : Nat.card fL.ker *
      Nat.card ((D.subgroupOf L).map (QuotientGroup.mk' θL)) = Nat.card D := by
    have h := Subgroup.card_mul_index fL.ker
    rw [Subgroup.index_ker, hfLr] at h
    exact h
  have hkerL : fL.ker.map (Subgroup.inclusion hDL) ≤ θL := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hker2 : IsPGroup 2 fL.ker :=
    ((hθL2.to_le hkerL).of_equiv
      (fL.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hDL)).symm)
  have hfXs : Function.Surjective fX := by
    rw [← MonoidHom.range_eq_top, hfXr, hDtop]
  have hle : fL.ker ≤ fX.ker := by
    have hn : (fL.ker.map fX).Normal := (fL.normal_ker).map fX hfXs
    have h2 : IsPGroup 2 (fL.ker.map fX) := hker2.map fX
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hn with ht | hc
    · exfalso
      rw [ht] at h2
      have hp : IsPGroup 2 (↥X ⧸ θX) := h2.of_equiv Subgroup.topEquiv
      obtain ⟨hperf, hs, -⟩ := hXq
      have : Nontrivial (↥X ⧸ θX) := by
        have := hs.toNontrivial
        obtain ⟨x, hx⟩ := exists_ne (1 : (↥X ⧸ θX) ⧸ Subgroup.center (↥X ⧸ θX))
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨⟨y, 1, fun h => hx (by rw [h]; rfl)⟩⟩
      have : Group.IsPerfect (↥X ⧸ θX) := hperf
      exact Group.IsPerfect.not_isNilpotent (↥X ⧸ θX) hp.isNilpotent
    · have h3 : IsPGroup 3 (fL.ker.map fX) := hZ3.to_le hc
      have h1 : fL.ker.map fX = ⊥ := by
        obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h2
        obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp h3
        rw [ha] at hb
        rcases a with _ | a
        · exact Subgroup.eq_bot_of_card_eq _ (by rw [ha, pow_zero])
        · exfalso
          have h23 : 2 ∣ 3 ^ b := hb ▸ dvd_pow_self 2 (Nat.succ_ne_zero a)
          exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h23) (by norm_num)
      exact (Subgroup.map_eq_bot_iff _).mp h1
  have hm := Subgroup.relIndex_mul_card fL.ker fX.ker
  rw [inf_eq_left.mpr hle] at hm
  have hpos : 0 < Nat.card fL.ker := Nat.card_pos
  refine ⟨fL.ker.relIndex fX.ker, ?_⟩
  have h : Nat.card fL.ker * Nat.card ((D.subgroupOf L).map (QuotientGroup.mk' θL)) =
      Nat.card fL.ker * (Nat.card (↥X ⧸ θX) * fL.ker.relIndex fX.ker) := by
    rw [hcardL, ← hcardX, ← hm]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos h

theorem exists_sixty_of_cover
    {X L D : Subgroup G}
    (hXq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (htype : Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hθL2 : IsPGroup 2 (aschbacherSolvableCore 3 ↥L)) (hDX : D ≤ X) (hDL : D ≤ L)
    (hDtop : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤)
    (hDp : Group.IsPerfect D) {z : ↥L ⧸ aschbacherSolvableCore 3 ↥L} (hz1 : z ≠ 1)
    (hzc : ∃ S' : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L), z ∈ (S' : Subgroup _) ∧
      (S' : Subgroup _) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hDz : (D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
      Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    ∃ F : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      F ≤ (D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ∧
      Group.IsPerfect F ∧ Nat.card F = 60 ∧
      F ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have hFp : Group.IsPerfect ((D.subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) := by
    have : Group.IsPerfect (D.subgroupOf L) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hDL).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.map _
  rcases htype with he | h6
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X) := e.isSimpleGroup
    have hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
    exact ⟨_, le_rfl, hFp, card_map_eq_sixty hXs hX60 hJ hθL2 hDX hDL hDtop hDp hz1 hzc hDz, hDz⟩
  · have hdvd := card_dvd_card_map_of_cover hXq (isPGroup_center_of_type hXq (Or.inr h6)) hθL2
      hDX hDL hDtop
    rw [card_of_isTripleCover h6, card_alternatingGroup_six] at hdvd
    obtain ⟨hZc, hZ3, hZn, ⟨eA⟩⟩ :=
      KFacts.KS14.j2_centralizer_quotient Sec4.Sporadic.rank3II_4_15 hJ hz1 hzc
    set C := Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) with hC
    set Z := (Subgroup.zpowers z).subgroupOf C with hZ
    have hC1080 : Nat.card C = 1080 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [Nat.card_congr eA.toEquiv, KFacts.KS14.card_alternatingGroup_six, hZ3] at h
      exact h
    have hFle : Nat.card ((D.subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) ≤ 1080 :=
      hC1080 ▸ Subgroup.card_le_of_le hDz
    have hpos : 0 < Nat.card ((D.subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) := Nat.card_pos
    have hF1080 : Nat.card ((D.subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 1080 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk] at hFle hpos ⊢
      have hk1 : k = 1 := by
        rcases k with _ | _ | k
        · omega
        · rfl
        · omega
      rw [hk1, mul_one]
    have hFC : (D.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) = C :=
      Subgroup.eq_of_le_of_card_ge hDz (by rw [hC1080, hF1080])
    obtain ⟨F₀, hF₀p, hF₀60⟩ := exists_isPerfect_card_sixty_of_quotient_six Z hZc hZ3 eA
    refine ⟨F₀.map C.subtype, ?_, isPerfect_map_subtype hF₀p, ?_, Subgroup.map_subtype_le F₀⟩
    · rw [hFC]
      exact Subgroup.map_subtype_le F₀
    · rw [Subgroup.card_map_of_injective C.subtype_injective, hF₀60]

end Proof156

open Proof156

variable {G : Type} [Group G] [Finite G]

theorem step156Meet_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h142 : Item142AllS14) : Step156Meet A (lB A) := by
  intro Y _ _ c₀ L₀ d X₁ D _ _
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  exact three_dvd_card_inf_of_data156 h₀ (h142 G A c₀ L₀ h₀) D

theorem ks156HJGen_of
    (h142 : Item142AllS14) : KS156HJGen := by
  intro G _ _ A c L h Y _ _ d X₁ D _ S _ _ hSH
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  have hJ := D.hj
  set U := S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) with hU
  set J := U ⊔ X₁ with hJdef
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤ J :=
    (theta_le_of_mem_scriptQPiStar h hJ hSH).trans le_sup_left
  obtain ⟨hQ2, hQ64⟩ := sixtyFour_dvd_card_map_inf ks152J2InvolNine_holds h hJ hSH
  obtain ⟨hAX, -, -, hXq, htype, -, -, -, hdC, -⟩ := facts_of_data156 D hA
  have hcov := cover_of_data156 h (h142 G A c L h) D
  have hd3 : d ^ 3 = 1 := hA.1.2 d D.mem_d
  obtain ⟨hdL, S3, hdS3, hS3d⟩ := D.central_d
  have hdXL : d ∈ Subgroup.normalizer ((X₁ ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAX hS13.le_normalizer D.mem_d
  have hW : ((X₁ ⊓ L).subgroupOf X₁).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X₁)) = ⊤ :=
    map_subgroupOf_eq_top_of_le_sup inf_le_left hcov
  have hW' := map_inf_centralizer_eq_top inf_le_left hdXL hd3 hdC hW
  obtain ⟨D', hD'W, hD'p, hD'top⟩ := exists_isPerfect_cover hXq.1 hW'
  have hD'X : D' ≤ X₁ := hD'W.trans (inf_le_left.trans inf_le_left)
  have hD'L : D' ≤ L := hD'W.trans (inf_le_left.trans inf_le_right)
  have hD'd : D' ≤ Subgroup.centralizer ({d} : Set G) := hD'W.trans inf_le_right
  set z : ↥L ⧸ θ := ρ ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro hz1
    have hmem : (⟨d, hdL⟩ : ↥L) ∈ θ := (QuotientGroup.eq_one_iff _).mp hz1
    have hord : orderOf (⟨⟨d, hdL⟩, hmem⟩ : θ) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 D.ne_d
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
  have hD'z : (D'.subgroupOf L).map ρ ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ θ)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyd : (y : G) * d = d * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hD'd (Subgroup.mem_subgroupOf.mp hy))
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyd
  obtain ⟨F₀, hF₀D, hF₀p, hF₀60, hF₀z⟩ := exists_sixty_of_cover hXq htype hJ
    (isPGroup_theta_of_j2 h hJ) hD'X hD'L hD'top hD'p hz1 hzc hD'z
  have htop := ks152J2Gen_holds (↥L ⧸ θ) hJ z hz1 hzc _ F₀ hQ2 hQ64 hF₀z hF₀p hF₀60
  have hJbar : (J.subgroupOf L).map ρ = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine sup_le (Subgroup.map_mono fun x hx => ?_)
      (hF₀D.trans (Subgroup.map_mono fun x hx => ?_))
    · exact Subgroup.mem_subgroupOf.mpr
        ((le_sup_left : U ≤ J) (Subgroup.mem_subgroupOf.mp hx).1)
    · exact Subgroup.mem_subgroupOf.mpr
        ((le_sup_right : X₁ ≤ J) (hD'X (Subgroup.mem_subgroupOf.mp hx)))
  have hLJ : L ≤ J := by
    intro l hl
    obtain ⟨j, hj, hjl⟩ : ρ ⟨l, hl⟩ ∈ (J.subgroupOf L).map ρ := hJbar ▸ Subgroup.mem_top _
    have hjθ : j⁻¹ * ⟨l, hl⟩ ∈ θ := by
      rw [← QuotientGroup.eq]
      exact hjl
    have h1 : ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ J := hθL ⟨_, hjθ, rfl⟩
    have h2 : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have h3 : l = (j : G) * ((j⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h3]
    exact J.mul_mem h2 h1
  exact hLJ.trans (sup_le_sup inf_le_left D.le_x)

end CFSG.RankThree.PartTwo.Sec15
