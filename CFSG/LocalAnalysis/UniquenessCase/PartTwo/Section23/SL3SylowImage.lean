module

public import CFSG.GroupTheory.BinaryNaturalSLThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveRoot
public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem phiT_apply_mkTil_of_mem_centralizer (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {t : ↥D.T}
    (hcent : (t : G) ∈ Subgroup.centralizer (D.Z : Set G)) (v : IntMod c.V hV)
    (hvZ : v.val ∈ D.Z) :
    (c.phiT hV t) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV v := by
  rw [Ctx23L.phiT]
  change actTil (⊥ : Subgroup G) c.V hV ⟨(t : G), c.T_le_stabTil t.2⟩
    (mkTil (⊥ : Subgroup G) c.V hV v) = _
  rw [actTil_mk]
  congr 1
  apply IntMod.val_injective
  rw [actStab_apply_val]
  have hcomm : (t : G) * v.val * (t : G)⁻¹ = v.val := by
    have hc := (Subgroup.mem_centralizer_iff.mp hcent) v.val hvZ
    calc (t : G) * v.val * (t : G)⁻¹ = v.val * (t : G) * (t : G)⁻¹ := by rw [hc]
      _ = v.val := by group
  rw [hcomm]

private theorem phiL_apply_mkTil_of_mem_centralizer (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {x : ↥c.L}
    (hcent : (x : G) ∈ Subgroup.centralizer (D.Z : Set G)) (v : IntMod c.V hV)
    (hvZ : v.val ∈ D.Z) :
    ((c.phiL hV x : ↥(c.H hV)) : MulAut (c.W hV))
        (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV v := by
  unfold Ctx23L.phiL
  change actTil (⊥ : Subgroup G) c.V hV ⟨(x : G), c.L_le_stabTil x.2⟩
    (mkTil (⊥ : Subgroup G) c.V hV v) = _
  rw [actTil_mk]
  congr 1
  apply IntMod.val_injective
  rw [actStab_apply_val]
  have hcomm : (x : G) * v.val * (x : G)⁻¹ = v.val := by
    have hc := (Subgroup.mem_centralizer_iff.mp hcent) v.val hvZ
    calc (x : G) * v.val * (x : G)⁻¹ = v.val * (x : G) * (x : G)⁻¹ := by rw [hc]
      _ = v.val := by group
  rw [hcomm]

private theorem Ztil_fixed_sylowStar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ∀ s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)), ∀ y ∈ c.Ztil hV,
      (s : MulAut (c.W hV)) y = y := by
  intro s hs y hy
  rw [c.sylowStar_coe] at hs
  obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
  have hxT : (x : G) ∈ D.T := Subgroup.mem_subgroupOf.1 hx
  have hcent : (x : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T hxT
  change y ∈ imgTil (⊥ : Subgroup G) c.V hV D.Z at hy
  rw [mem_imgTil] at hy
  obtain ⟨v, hvZ, rfl⟩ := hy
  rw [← hxs]
  exact phiL_apply_mkTil_of_mem_centralizer c hV hcent v hvZ

private theorem Ztil_fixed_phiT (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (t : ↥D.T) : ∀ y ∈ c.Ztil hV, c.phiT hV t y = y := by
  intro y hy
  have hcent : (t : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T t.2
  change y ∈ imgTil (⊥ : Subgroup G) c.V hV D.Z at hy
  rw [mem_imgTil] at hy
  obtain ⟨v, hvZ, rfl⟩ := hy
  exact phiT_apply_mkTil_of_mem_centralizer c hV hcent v hvZ

private theorem phiT_mem_H_of_sl3 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (t : ↥D.T) : c.phiT hV t ∈ c.H hV := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZel : IsElemAbelian 2 D.Z :=
    CFSG.CGT.PushingUpLit.CGT6.isElemAbelian_omegaOneCenterIn D.T
  have hZcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZel
  have hY : Nat.card (c.Ztil hV) = 2 ^ CFSG.Open.pRank 2 D.Z := by
    rw [c.card_Ztil hV, hZcard]
  refine CFSG.Quasithin.BinaryNaturalSL.mem_of_normalizes_three hnat hm (c.sylowStar hV)
    (Ztil_fixed_sylowStar c hV) hY ?_ ?_ (Ztil_fixed_phiT c hV t)
  · intro h hh
    exact (Subgroup.mem_normalizer_iff.mp
      (c.Tstar_le_normalizer hV ⟨t, rfl⟩) h).1 hh
  · obtain ⟨k, hk⟩ := (c.isPGroup_Tstar hV).exists_orderOf_eq_pow
      ⟨c.phiT hV t, ⟨t, rfl⟩⟩
    refine ⟨k, ?_⟩
    have h := pow_orderOf_eq_one (⟨c.phiT hV t, ⟨t, rfl⟩⟩ : ↥(c.Tstar hV))
    rw [hk] at h
    exact congrArg Subtype.val h

private theorem Tstar_le_H (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    c.Tstar hV ≤ c.H hV := by
  rintro φ ⟨t, rfl⟩
  exact phiT_mem_H_of_sl3 c hV hm hnat t

theorem phiT_mem_sylowStar_of_sl3 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z))
    (t : ↥D.T) :
    ∃ s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)), (s : MulAut (c.W hV)) = c.phiT hV t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTstar_le_H : c.Tstar hV ≤ c.H hV := Tstar_le_H c hV hm hnat
  let TstarH : Subgroup ↥(c.H hV) := (c.Tstar hV).subgroupOf (c.H hV)
  have hTstarH : IsPGroup 2 TstarH := (c.isPGroup_Tstar hV).comap_subtype
  have hsle : (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ TstarH := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := c.H hV)]
    rw [Subgroup.map_subgroupOf_eq_of_le hTstar_le_H]
    exact c.sylowStar_le_Tstar hV
  have hnorm : (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Subgroup.normalizer TstarH :=
    hsle.trans (Subgroup.le_normalizer (H := TstarH))
  let Q : Subgroup ↥(c.H hV) :=
    (TstarH : Subgroup ↥(c.H hV)) ⊔ (c.sylowStar hV : Subgroup ↥(c.H hV))
  have hsup : IsPGroup 2 Q :=
    IsPGroup.to_sup_of_normal_left' hTstarH (c.sylowStar hV).isPGroup' hnorm
  have heq : Q = (c.sylowStar hV : Subgroup ↥(c.H hV)) :=
    (c.sylowStar hV).is_maximal' hsup le_sup_right
  let sH : ↥(c.H hV) := ⟨c.phiT hV t, phiT_mem_H_of_sl3 c hV hm hnat t⟩
  have hmemTstarH : sH ∈ TstarH := Subgroup.mem_subgroupOf.mpr ⟨t, rfl⟩
  have hmemS : sH ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)) := by
    rw [← heq]
    exact Subgroup.mem_sup_left hmemTstarH
  exact ⟨sH, hmemS, rfl⟩

private theorem phiT_eq_phiL_of_mem (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (y : ↥c.L) (hyT : (y : G) ∈ D.T) :
    c.phiT hV ⟨(y : G), hyT⟩ = (c.phiL hV y : MulAut (c.W hV)) := by
  unfold Ctx23L.phiT Ctx23L.phiL
  change actTil (⊥ : Subgroup G) c.V hV ⟨(y : G), c.T_le_stabTil hyT⟩ =
    actTil (⊥ : Subgroup G) c.V hV ⟨(y : G), c.L_le_stabTil y.2⟩
  rw [show (⟨(y : G), c.T_le_stabTil hyT⟩ : stabTil (⊥ : Subgroup G) c.V) =
      ⟨(y : G), c.L_le_stabTil y.2⟩ from Subtype.ext rfl]

private theorem centralizes_of_phiT_eq_one (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (u : ↥D.T) (hu : c.phiT hV u = 1) :
    (u : G) ∈ Subgroup.centralizer (c.V : Set G) := by
  have hact : actTil (⊥ : Subgroup G) c.V hV ⟨(u : G), c.T_le_stabTil u.2⟩ = 1 := by
    have h := hu
    rw [Ctx23L.phiT, MonoidHom.comp_apply] at h
    convert h using 2
    exact Subtype.ext rfl
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := (actTil_eq_one_iff (⊥ : Subgroup G) c.V hV
    ⟨(u : G), c.T_le_stabTil u.2⟩).mp hact v hv
  rw [Subgroup.mem_bot] at h
  have h2 : (u : G) * v = v * (u : G) := by
    have h3 : (u : G) * v * (u : G)⁻¹ = v := by
      have := congrArg (· * v) h
      simpa [mul_assoc] using this
    calc (u : G) * v = ((u : G) * v * (u : G)⁻¹) * (u : G) := by group
      _ = v * (u : G) := by rw [h3]
  exact h2.symm

private theorem exists_mem_T_inf_L_of_phiT_mem_sylow (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {t : ↥D.T} {s : ↥(c.H hV)}
    (hsS : s ∈ (c.sylowStar hV : Subgroup ↥(c.H hV)))
    (hs_eq : (s : MulAut (c.W hV)) = c.phiT hV t) :
    ∃ y ∈ D.T ⊓ c.L, (y : G)⁻¹ * (t : G) ∈ Subgroup.centralizer (c.V : Set G) := by
  rw [c.sylowStar_coe] at hsS
  obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp hsS
  have hyT : (y : G) ∈ D.T := Subgroup.mem_subgroupOf.1 hy
  have hyL : (y : G) ∈ c.L := y.2
  refine ⟨(y : G), Subgroup.mem_inf.mpr ⟨hyT, hyL⟩, ?_⟩
  have hphiT_y : c.phiT hV ⟨(y : G), hyT⟩ = (c.phiL hV y : MulAut (c.W hV)) :=
    phiT_eq_phiL_of_mem c hV y hyT
  have hphiT_t : c.phiT hV t = (c.phiL hV y : MulAut (c.W hV)) :=
    hs_eq.symm.trans (congrArg Subtype.val hys).symm
  have hphiT_u : c.phiT hV (⟨(y : G), hyT⟩⁻¹ * t) = 1 := by
    rw [map_mul, map_inv, hphiT_y, hphiT_t, inv_mul_cancel]
  exact centralizes_of_phiT_eq_one c hV _ hphiT_u

theorem exists_mem_T_inf_L_mul_inv_mem_centralizer_of_sl3 (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hm : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    ∀ t ∈ D.T, ∃ y ∈ D.T ⊓ c.L, y⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G) := by
  intro t ht
  obtain ⟨s, hsS, hs_eq⟩ := c.phiT_mem_sylowStar_of_sl3 hV hm hnat ⟨t, ht⟩
  exact exists_mem_T_inf_L_of_phiT_mem_sylow c hV hsS hs_eq

theorem T_eq_sup_inf_centralizer_of_sl3 (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hm : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z)) :
    D.T = (D.T ⊓ c.L) ⊔ (D.T ⊓ Subgroup.centralizer (c.V : Set G)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨y, hy, hz⟩ :=
      c.exists_mem_T_inf_L_mul_inv_mem_centralizer_of_sl3 hV hm hnat t ht
    have hyT : (y : G) ∈ D.T := (Subgroup.mem_inf.mp hy).1
    have hzT : (y : G)⁻¹ * t ∈ D.T := D.T.mul_mem (D.T.inv_mem hyT) ht
    have hz' : (y : G)⁻¹ * t ∈ D.T ⊓ Subgroup.centralizer (c.V : Set G) :=
      Subgroup.mem_inf.mpr ⟨hzT, hz⟩
    have ht_eq : t = y * ((y : G)⁻¹ * t) := by group
    rw [ht_eq]
    exact Subgroup.mul_mem_sup hy hz'
  · exact sup_le inf_le_left inf_le_left

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
