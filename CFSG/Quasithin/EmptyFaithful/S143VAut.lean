module

public import CFSG.Quasithin.EmptyFaithful.S143VTh
public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section

variable (h : Hyp1281Two G T M L) (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T)
  (D : HatModel T M)

include h hZU in
theorem qtilde_isPlusType (hd : Module.finrank (ZMod 2) D.V = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (G11.P4InspOrth.p4insporth_quad (f := D.B) (q := qhat D) (fun x y => qhat_add h hZU D x y))) :
    IsPlusType (qtilde h hZU D) := by
  obtain ⟨W', hW'dim, hW'sing⟩ := hplus
  have hrk : Module.finrank (ZMod 2) W' = 2 := by omega
  let Wm : Subgroup (Multiplicative D.V) := AddSubgroup.toSubgroup W'.toAddSubgroup
  let W : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    Wm.map (theta h hZU D).symm.toMonoidHom
  refine ⟨W, ?_, ?_⟩
  · have h1 : Nat.card W = Nat.card Wm :=
      Subgroup.card_map_of_injective (theta h hZU D).symm.injective
    have h2 : Nat.card Wm = Nat.card W' :=
      Nat.card_congr
        { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
          invFun := fun y => ⟨Multiplicative.ofAdd y.1, y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [h1, h2, natCard_eq_two_pow_finrank, hrk]
    norm_num
  · rintro w ⟨y, hy, rfl⟩
    show qtilde h hZU D ((theta h hZU D).symm y) = 0
    unfold qtilde
    rw [MulEquiv.apply_symm_apply]
    exact hW'sing (Multiplicative.toAdd y) hy

include h hZU in
theorem autOn_tilde_eq (hd : Module.finrank (ZMod 2) D.V = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (G11.P4InspOrth.p4insporth_quad (f := D.B) (q := qhat D) (fun x y => qhat_add h hZU D x y)))
    (hcard : Nat.card (D.img (mcOf T)) = 72) :
    autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) = orthogonalGroupOf (qtilde h hZU D) := by
  rw [← S143.range_actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
    mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22]
  have hle : (S143.actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)
      mcOf_le_normalizer_Z h.g1_le_normalizer_uOfL22).range ≤
      orthogonalGroupOf (qtilde h hZU D) := by
    rintro _ ⟨x, rfl⟩
    exact actTilde_mem_orthogonalGroupOf h hZU D x
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun a b => (tilde_isMulCommutative h hZU D).is_comm.comm a b }
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType
    (W := ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (q := qtilde h hZU D)
    (tilde_mul_self h hZU D) (card_tilde h hZU D hd) (qtilde_isQuadraticFormOn h hZU D)
    (qtilde_isNondeg h hZU D) (qtilde_isPlusType h hZU D hd hplus)
  have hcardO : Nat.card ↥(orthogonalGroupOf (qtilde h hZU D)) = 72 := hS.card_X
  have hcr := (card_range_actTilde h hZU D).trans hcard
  have : Finite ↥(orthogonalGroupOf (qtilde h hZU D)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardO]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardO, hcr])

end

omit [Finite G] in
theorem wOf_eq_wOfU (T M : Subgroup G) : S143.wOf T M = Hyp1281Two.wOfU T M := rfl

omit [Finite G] in
theorem conjSubgroup_eq_rconj (X : Subgroup G) (g : G) : conjSubgroup X g = rconj X g := rfl

section Concl

theorem concl14315_of_data (h : Hyp1281Two G T M (yOfL22 T M))
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (hZU : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T) (D : HatModel T M)
    (hd : Module.finrank (ZMod 2) D.V = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (G11.P4InspOrth.p4insporth_quad (f := D.B) (q := qhat D) (fun x y => qhat_add h hZU D x y)))
    (hcard : Nat.card (D.img (mcOf T)) = 72) (hq8 : IsQ8Sq ↥(uOfL22 T M)) : S143.Concl14315 T M where
  q8sq := hq8
  orth := ⟨qtilde h hZU D, qtilde_isQuadraticFormOn h hZU D, qtilde_isNondeg h hZU D,
    qtilde_isPlusType h hZU D hd hplus, card_tilde h hZU D hd,
    fun x hx u hu hxu => qtilde_compat h hZU D x hx u hu hxu, autOn_tilde_eq h hZU D hd hplus hcard⟩
  eSing := fun g hgL hgH e he => by
    have hg : GoodElt128 T (yOfL22 T M) g :=
      ⟨hgL, fun hn => hgH (by rwa [h.normalizer_Z_eq_centralizer] at hn)⟩
    rw [wOf_eq_wOfU, conjSubgroup_eq_rconj, h.wOfU_inf_rconj_eq hU hg] at he
    exact (h.isElemAbelian_inf_rconj hU hg).2 e he

end Concl

end S143V

end CFSG.Quasithin
