module

public import CFSG.LocalAnalysis.StandardType.GGSporKB7bCover
public import CFSG.LocalAnalysis.StandardType.GGSporKB7bStd
public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Monster.GMS.BabyTwoAAutBridge
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.Existence.MilestoneInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

private theorem gkB_exists_babyInv_centralizer_le
    {e : NativeSporadic.B} (he : orderOf e = 7) :
    ∃ α' : NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 α' ∧
      Subgroup.centralizer ({e} : Set NativeSporadic.B) ≤
        Subgroup.centralizer ({α'} : Set NativeSporadic.B) := by
  have P := bSevenElem_parts
  have hα : CFSG.Monster.GMS.BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bSeven_isConj hxS he)
  refine ⟨c * alphaB * c⁻¹, hα.of_isConj (isConj_iff.2 ⟨c, rfl⟩), ?_⟩
  have hle := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.centralizer_xSeven_le
  intro g hg
  have hg' : g * e = e * g := (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 hg
  have hmem : c⁻¹ * g * c ∈ Subgroup.centralizer ({xSeven} : Set NativeSporadic.B) := by
    refine (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
    have hx' : xSeven = c⁻¹ * e * c := by
      rw [← hc]
      group
    rw [hx']
    calc c⁻¹ * g * c * (c⁻¹ * e * c) = c⁻¹ * (g * e) * c := by group
      _ = c⁻¹ * (e * g) * c := by rw [hg']
      _ = c⁻¹ * e * c * (c⁻¹ * g * c) := by group
  have hα' : c⁻¹ * g * c * alphaB = alphaB * (c⁻¹ * g * c) :=
    (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 (hle hmem)
  refine (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
  calc g * (c * alphaB * c⁻¹) = c * (c⁻¹ * g * c * alphaB) * c⁻¹ := by group
    _ = c * (alphaB * (c⁻¹ * g * c)) * c⁻¹ := by rw [hα']
    _ = c * alphaB * c⁻¹ * g := by group

private theorem gkB_card_centralizer_map_equiv {G : Type*} [Group G] {α : G} {E : Subgroup G}
    {L : Type*} [Group L] (f : ↥(Subgroup.centralizer ({α} : Set G)) →* L)
    (ψ : ↥(Subgroup.centralizer ({α} : Set G)) ≃* L) (hf : ∀ x, f x = ψ x)
    (hEle : E ≤ Subgroup.centralizer ({α} : Set G))
    (hC : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer ({α} : Set G)) :
    Nat.card ↥(Subgroup.centralizer (E : Set G)) =
      Nat.card ↥(Subgroup.centralizer
        (((E.subgroupOf (Subgroup.centralizer ({α} : Set G))).map f) : Set L)) := by
  let C : Subgroup G := Subgroup.centralizer ({α} : Set G)
  change Nat.card ↥(Subgroup.centralizer (E : Set G)) =
    Nat.card ↥(Subgroup.centralizer (((E.subgroupOf C).map f) : Set L))
  refine Nat.card_congr
    { toFun := fun g => ⟨f ⟨g.1, hC g.2⟩, ?_⟩
      invFun := fun h => ⟨(ψ.symm h.1).1, ?_⟩
      left_inv := fun g => ?_
      right_inv := fun h => ?_ }
  · rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxE : (x : G) ∈ E := (Subgroup.mem_subgroupOf).1 hx
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext ((Subgroup.mem_centralizer_iff).1 g.2 (x : G) hxE))
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heC : e ∈ C := hEle he
    have hmem : (⟨e, heC⟩ : ↥C) ∈ E.subgroupOf C := (Subgroup.mem_subgroupOf).2 he
    have hcomm := (Subgroup.mem_centralizer_iff).1 h.2 (f ⟨e, heC⟩)
      (Subgroup.mem_map.mpr ⟨⟨e, heC⟩, hmem, rfl⟩)
    have hsym : ψ.symm (f ⟨e, heC⟩) = (⟨e, heC⟩ : ↥C) := by
      rw [hf ⟨e, heC⟩, MulEquiv.symm_apply_apply]
    have h2 : (⟨e, heC⟩ : ↥C) * ψ.symm h.1 = ψ.symm h.1 * ⟨e, heC⟩ := by
      simpa only [map_mul, hsym] using congrArg ψ.symm hcomm
    exact congrArg Subtype.val h2
  · apply Subtype.ext
    dsimp only
    rw [hf ⟨g.1, hC g.2⟩, MulEquiv.symm_apply_apply]
  · apply Subtype.ext
    dsimp only
    rw [hf]
    exact (congrArg ψ (Subtype.ext rfl)).trans (MulEquiv.apply_symm_apply ψ h.1)

theorem bSevenCentAbelian_native
    [Finite NativeSporadic.B] :
    BSevenCentAbelian NativeSporadic.B := by
  intro E hE h49 a ha b hb
  obtain hbot | ⟨e, heE, he_ne⟩ := Subgroup.bot_or_exists_ne_one E
  · rw [hbot, Subgroup.card_bot] at h49
    norm_num at h49
  have he7 : orderOf e = 7 := orderOf_eq_prime (hE.2 e heE) he_ne
  have hEcent : E ≤ Subgroup.centralizer (E : Set NativeSporadic.B) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1
  obtain ⟨α', hα', hleα⟩ := gkB_exists_babyInv_centralizer_le he7
  have hsub : ({e} : Set NativeSporadic.B) ⊆ (E : Set NativeSporadic.B) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact heE
  have hcle_e : Subgroup.centralizer (E : Set NativeSporadic.B) ≤
      Subgroup.centralizer ({e} : Set NativeSporadic.B) := Subgroup.centralizer_le hsub
  have hcle : Subgroup.centralizer (E : Set NativeSporadic.B) ≤
      Subgroup.centralizer ({α'} : Set NativeSporadic.B) := le_trans hcle_e hleα
  have hEle : E ≤ Subgroup.centralizer ({α'} : Set NativeSporadic.B) := le_trans hEcent hcle
  obtain ⟨ψ⟩ := CFSG.Monster.GMS.nonempty_centralizer_mulEquiv_Eam
    CFSG.Monster.Existence.babyTableIII hα'
  haveI : Finite ↥CFSG.Monster.B.TwoA.Amalgam.Eam := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨hidx, -, -, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : Subgroup.zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  let ψhom : ↥(Subgroup.centralizer ({α'} : Set NativeSporadic.B)) →*
      ↥CFSG.Monster.B.TwoA.Amalgam.Eam :=
    { toFun := ψ, map_one' := map_one ψ, map_mul' := map_mul ψ }
  let EY : Subgroup ↥CFSG.Monster.B.TwoA.Amalgam.Eam :=
    (E.subgroupOf (Subgroup.centralizer ({α'} : Set NativeSporadic.B))).map ψhom
  have hcard : Nat.card ↥(Subgroup.centralizer (E : Set NativeSporadic.B)) =
      Nat.card ↥(Subgroup.centralizer (EY : Set ↥CFSG.Monster.B.TwoA.Amalgam.Eam)) :=
    gkB_card_centralizer_map_equiv ψhom ψ (fun _ => rfl) hEle hcle
  have hEY : Nat.card EY = 49 := by
    dsimp only [EY]
    rw [Subgroup.card_map_of_injective (f := ψhom) (fun _ _ h => ψ.injective h)]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv, h49]
  have hdvd : Nat.card ↥(Subgroup.centralizer (E : Set NativeSporadic.B)) ∣ 196 := by
    rw [hcard]
    exact gk7b_card_centralizer_dvd_of_cover hidx hZY hZ2 φ
      gk7b_stdGroup_card_centralizer_eq hEY
  let E' : Subgroup ↥(Subgroup.centralizer (E : Set NativeSporadic.B)) :=
    E.subgroupOf (Subgroup.centralizer (E : Set NativeSporadic.B))
  have hE'center : E' ≤ Subgroup.center ↥(Subgroup.centralizer (E : Set NativeSporadic.B)) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hxE : (x : NativeSporadic.B) ∈ E := by
      dsimp only [E'] at hx
      exact (Subgroup.mem_subgroupOf).1 hx
    exact ((Subgroup.mem_centralizer_iff).1 g.2 (x : NativeSporadic.B) hxE).symm
  have hcardE' : Nat.card E' = 49 := by
    dsimp only [E']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEcent).toEquiv, h49]
  have hodd : Odd (Nat.card E') := by
    rw [hcardE']
    norm_num
  have hidxE : E'.index * 49 = Nat.card ↥(Subgroup.centralizer (E : Set NativeSporadic.B)) := by
    rw [← hcardE']
    exact Subgroup.index_mul_card E'
  have h4 : E'.index ∣ 4 := by
    have h : E'.index * 49 ∣ 196 := by rw [hidxE]; exact hdvd
    rw [show (196 : ℕ) = 4 * 49 by norm_num] at h
    exact (mul_dvd_mul_iff_right (by norm_num : (49 : ℕ) ≠ 0)).1 h
  have hcomm := gk7b_mul_comm_of_le_center hE'center hodd h4
    (⟨a, ha⟩ : ↥(Subgroup.centralizer (E : Set NativeSporadic.B))) ⟨b, hb⟩
  simpa using congrArg Subtype.val hcomm

theorem ggSporK_bSevenCentAbelian_B
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BSevenCentAbelian (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  exact @bSevenCentAbelian_of_mulEquiv NativeSporadic.B
    (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ e' bSevenCentAbelian_native

end CFSG.StandardType.SporadicShape
