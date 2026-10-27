module

public import CFSG.LocalAnalysis.StandardType.GGSporKB7cCover
public import CFSG.LocalAnalysis.StandardType.GGSporKB7cStd
public import CFSG.LocalAnalysis.StandardType.GGSporKB7cCore
public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Monster.GMS.BabyTwoAAutBridge
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.Existence.MilestoneInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint

private theorem gk7c_card_centralizer_eq_of_le
    {G Y : Type*} [Group G] [Group Y] {α x : G}
    (ψ : ↥(Subgroup.centralizer ({α} : Set G)) ≃* Y)
    (hle : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({α} : Set G)) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer
        ({ψ ⟨x, hle ((Subgroup.mem_centralizer_singleton_iff (G := G)).2 rfl)⟩} : Set Y)) := by
  set y : Y := ψ ⟨x, hle ((Subgroup.mem_centralizer_singleton_iff (G := G)).2 rfl)⟩ with hy
  refine Nat.card_congr
    { toFun := fun g => ⟨ψ ⟨g, hle g.2⟩, ?_⟩
      invFun := fun h => ⟨((ψ.symm h : ↥(Subgroup.centralizer ({α} : Set G))) : G), ?_⟩
      left_inv := fun g => by simp
      right_inv := fun h => by simp }
  · have hg : (g : G) * x = x * g :=
      (Subgroup.mem_centralizer_singleton_iff (G := G)).1 g.2
    refine (Subgroup.mem_centralizer_singleton_iff (G := Y)).2 ?_
    rw [hy, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (by simpa using hg))
  · have hh : (h : Y) * y = y * (h : Y) :=
      (Subgroup.mem_centralizer_singleton_iff (G := Y)).1 h.2
    refine (Subgroup.mem_centralizer_singleton_iff (G := G)).2 ?_
    have he : ψ.symm (h : Y) *
          ⟨x, hle ((Subgroup.mem_centralizer_singleton_iff (G := G)).2 rfl)⟩ =
        ⟨x, hle ((Subgroup.mem_centralizer_singleton_iff (G := G)).2 rfl)⟩ *
          ψ.symm (h : Y) := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hy]
      exact hh
    have he' := congrArg Subtype.val he
    simpa only [Subgroup.coe_mul] using he'

theorem bSevenSpread_native
    [Finite NativeSporadic.B] (hB7a : BSevenComp NativeSporadic.B) :
    BSevenSpread NativeSporadic.B := by
  intro E hE h49 hex
  obtain ⟨t, ht1, hall⟩ := hex
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsMulCommutative ↥E := hE.1
  have h7 : ∀ e ∈ E, e ≠ 1 → orderOf e = 7 :=
    fun e he he1 => orderOf_eq_prime (hE.2 e he) he1
  have hexists : ∃ e ∈ E, e ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one E with hbot | h
    · exfalso
      rw [Subgroup.eq_bot_iff_card] at hbot
      omega
    · exact h
  obtain ⟨e0, he0E, he0ne1⟩ := hexists
  have he07 : orderOf e0 = 7 := h7 e0 he0E he0ne1
  obtain ⟨J0, hJ0, -, hJ0card, hJ0core⟩ := hB7a e0 he07
  have htJ0 : t ∈ J0 ⊓ Subgroup.centralizer (J0 : Set NativeSporadic.B) :=
    hall e0 he0E he0ne1 J0 hJ0
  have hle0 : Subgroup.centralizer ({e0} : Set NativeSporadic.B) ≤
      Subgroup.centralizer ({t} : Set NativeSporadic.B) :=
    gk7c_centralizer_le_of_core hJ0.1 hJ0card hJ0core htJ0 ht1
  have hα : CFSG.Monster.GMS.BabyInv 0 t :=
    gk7c_babyInv_of_core he07 hJ0.1 hJ0card hJ0core htJ0 ht1
  have hE_Ce0 : E ≤ Subgroup.centralizer ({e0} : Set NativeSporadic.B) := by
    intro e he
    exact (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2
      (Subgroup.mul_comm_of_mem_isMulCommutative E he he0E)
  have hE_Ct : E ≤ Subgroup.centralizer ({t} : Set NativeSporadic.B) := hE_Ce0.trans hle0
  obtain ⟨ψ⟩ := CFSG.Monster.GMS.nonempty_centralizer_mulEquiv_Eam
    CFSG.Monster.Existence.babyTableIII hα
  haveI : Finite ↥CFSG.Monster.B.TwoA.Amalgam.Eam := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨hidx, -, -, hcen', hZ2, ⟨φ⟩, -⟩ :=
    CFSG.Monster.B.TwoA.Amalgam.short_F4_derived_standard_perfect_cover
  have hZY : Subgroup.zpowers CFSG.Monster.B.TwoA.Amalgam.cE' ≤
      commutator ↥CFSG.Monster.B.TwoA.Amalgam.Eam := by
    rw [← hcen']
    exact Subgroup.map_subtype_le _
  let ψhom : ↥(Subgroup.centralizer ({t} : Set NativeSporadic.B)) →*
      ↥CFSG.Monster.B.TwoA.Amalgam.Eam :=
    { toFun := fun g => ψ g
      map_one' := map_one ψ
      map_mul' := fun a b => map_mul ψ a b }
  have hEY : Nat.card ((E.subgroupOf (Subgroup.centralizer ({t} : Set NativeSporadic.B))).map
      ψhom) = 49 := by
    rw [Subgroup.card_map_of_injective (f := ψhom) (fun a b h => ψ.injective h),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_Ct).toEquiv, h49]
  obtain ⟨y, hyEY, hy1, hyndvd⟩ :=
    gk7c_exists_not_dvd_nine_of_cover hidx hZY hZ2 φ
      gk7c_stdGroup_exists_not_dvd_nine hEY
  rw [Subgroup.mem_map] at hyEY
  obtain ⟨⟨e, heCt⟩, heE, hyeq⟩ := hyEY
  have heE' : e ∈ E := (Subgroup.mem_comap).1 heE
  have he1 : e ≠ 1 := by
    intro h
    apply hy1
    have hsub : (⟨e, heCt⟩ : ↥(Subgroup.centralizer ({t} : Set NativeSporadic.B))) = 1 :=
      Subtype.ext h
    rw [← hyeq, hsub, map_one]
  have he7 : orderOf e = 7 := h7 e heE' he1
  have hle_e : Subgroup.centralizer ({e} : Set NativeSporadic.B) ≤
      Subgroup.centralizer ({t} : Set NativeSporadic.B) := by
    obtain ⟨Je, hJe, -, hJecard, hJecore⟩ := hB7a e he7
    have htJe : t ∈ Je ⊓ Subgroup.centralizer (Je : Set NativeSporadic.B) :=
      hall e heE' he1 Je hJe
    exact gk7c_centralizer_le_of_core hJe.1 hJecard hJecore htJe ht1
  have h9 : 9 ∣ Nat.card (Subgroup.centralizer ({e} : Set NativeSporadic.B)) :=
    gk7c_nine_dvd_card_centralizer he7
  apply hyndvd
  have hcard := gk7c_card_centralizer_eq_of_le ψ hle_e
  have hxα : e ∈ Subgroup.centralizer ({t} : Set NativeSporadic.B) :=
    hle_e ((Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 rfl)
  have hsub : (⟨e, hxα⟩ : ↥(Subgroup.centralizer ({t} : Set NativeSporadic.B))) = ⟨e, heCt⟩ :=
    Subtype.ext rfl
  have hψeq : ψ ⟨e, hxα⟩ = y := by
    rw [hsub]
    exact hyeq
  rw [← hψeq, ← hcard]
  exact h9

theorem ggSporK_bSevenSpread_B
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group]
    (hB7a : BSevenComp (TauCeti.CFSGIndex.sporadic .B).Group) :
    BSevenSpread (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  have hB7a' : BSevenComp NativeSporadic.B :=
    @bSevenComp_of_mulEquiv (TauCeti.CFSGIndex.sporadic .B).Group NativeSporadic.B
      _ _ _ _ e'.symm hB7a
  exact @bSevenSpread_of_mulEquiv NativeSporadic.B (TauCeti.CFSGIndex.sporadic .B).Group
    _ _ _ _ e' (bSevenSpread_native hB7a')

end CFSG.StandardType.SporadicShape
