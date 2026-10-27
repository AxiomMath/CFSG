module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

abbrev W (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) : Type :=
  Vtil (⊥ : Subgroup G) c.V hV

noncomputable abbrev H (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup (MulAut (c.W hV)) :=
  barSub (⊥ : Subgroup G) c.V hV c.L

theorem L_le_stabTil (c : Ctx23L D Ch) :
    c.L ≤ stabTil (⊥ : Subgroup G) c.V := by
  refine le_stabTil ?_ ?_
  · exact (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (sup_le_normalizer_V D Ch c)
  · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top

theorem T_le_stabTil (c : Ctx23L D Ch) :
    D.T ≤ stabTil (⊥ : Subgroup G) c.V := by
  refine le_stabTil ?_ ?_
  · exact le_sup_right.trans (sup_le_normalizer_V D Ch c)
  · rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top

@[expose] noncomputable def phiL (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ↥c.L →* ↥(c.H hV) :=
  ((actTil (⊥ : Subgroup G) c.V hV).comp (Subgroup.inclusion c.L_le_stabTil)).codRestrict
    (c.H hV) fun x =>
      (mem_barSub (⊥ : Subgroup G) c.V hV c.L _).2 ⟨⟨x, c.L_le_stabTil x.2⟩, x.2, rfl⟩

theorem phiL_surjective (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Function.Surjective (c.phiL hV) := by
  intro φ
  obtain ⟨g, hgL, hgφ⟩ := (mem_barSub (⊥ : Subgroup G) c.V hV c.L φ).1 φ.2
  refine ⟨⟨(g : G), hgL⟩, Subtype.ext ?_⟩
  change actTil (⊥ : Subgroup G) c.V hV
      (⟨(g : G), c.L_le_stabTil hgL⟩ : stabTil (⊥ : Subgroup G) c.V) = (φ : MulAut (c.W hV))
  rw [show (⟨(g : G), c.L_le_stabTil hgL⟩ : stabTil (⊥ : Subgroup G) c.V) = g from
    Subtype.ext rfl]
  exact hgφ

theorem phiL_eq_one_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (x : ↥c.L) :
    c.phiL hV x = 1 ↔ (x : G) ∈ Subgroup.centralizer (c.V : Set G) := by
  constructor
  · intro h
    have h' : actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ = 1 :=
      congrArg Subtype.val h
    rw [actTil_eq_one_iff] at h'
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' := h' v hv
    rw [Subgroup.mem_bot] at hv'
    have h2 : (x : G) * v * (x : G)⁻¹ = v := mul_inv_eq_one.mp hv'
    have h3 := congrArg (· * (x : G)) h2
    simpa [mul_assoc] using h3.symm
  · intro h
    apply Subtype.ext
    change actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ = 1
    rw [actTil_eq_one_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hc := (Subgroup.mem_centralizer_iff.mp h) v hv
    rw [← hc]
    group

@[expose] noncomputable def phiT (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ↥D.T →* MulAut (c.W hV) :=
  (actTil (⊥ : Subgroup G) c.V hV).comp (Subgroup.inclusion c.T_le_stabTil)

@[expose] noncomputable def Tstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup (MulAut (c.W hV)) :=
  (c.phiT hV).range

theorem conj_mem (c : Ctx23L D Ch) (t : ↥D.T) (x : ↥c.L) :
    (t : G) * (x : G) * (t : G)⁻¹ ∈ c.L :=
  (Subgroup.mem_normalizer_iff.mp (c.hL.1.1 t.2) (x : G)).1 x.2

theorem phiT_conj_phiL (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (t : ↥D.T) (x : ↥c.L) :
    MulAut.conj (c.phiT hV t) (c.phiL hV x : MulAut (c.W hV)) =
      c.phiL hV ⟨(t : G) * (x : G) * (t : G)⁻¹, c.conj_mem t x⟩ := by
  rw [MulAut.conj_apply]
  change actTil (⊥ : Subgroup G) c.V hV ⟨t, c.T_le_stabTil t.2⟩ *
      actTil (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ *
      (actTil (⊥ : Subgroup G) c.V hV ⟨t, c.T_le_stabTil t.2⟩)⁻¹ =
    actTil (⊥ : Subgroup G) c.V hV
      ⟨(t : G) * (x : G) * (t : G)⁻¹, c.L_le_stabTil (c.conj_mem t x)⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem Tstar_le_normalizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    c.Tstar hV ≤ Subgroup.normalizer (c.H hV : Set (MulAut (c.W hV))) := by
  intro φ hφ
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨x, hx⟩ := c.phiL_surjective hV ⟨h, hh⟩
    have hx' : (c.phiL hV x : MulAut (c.W hV)) = h := congrArg Subtype.val hx
    rw [← hx', ← MulAut.conj_apply, c.phiT_conj_phiL hV t x]
    exact (c.phiL hV _).2
  · intro hh
    obtain ⟨x, hx⟩ := c.phiL_surjective hV ⟨(c.phiT hV t) * h * (c.phiT hV t)⁻¹, hh⟩
    have hmid : (c.phiT hV t) * h * (c.phiT hV t)⁻¹ = (c.phiL hV x : MulAut (c.W hV)) :=
      (congrArg Subtype.val hx).symm
    have hφinv : (c.phiT hV t)⁻¹ = c.phiT hV t⁻¹ := by rw [← map_inv]
    have hh' : h = (c.phiT hV t)⁻¹ * (c.phiT hV t * h * (c.phiT hV t)⁻¹) *
        (c.phiT hV t) := by group
    rw [hh']
    have hfinal : (c.phiT hV t)⁻¹ * (c.phiT hV t * h * (c.phiT hV t)⁻¹) *
        (c.phiT hV t) =
        (c.phiL hV ⟨(t⁻¹ : G) * (x : G) * (t⁻¹ : G)⁻¹, c.conj_mem t⁻¹ x⟩ :
          MulAut (c.W hV)) := by
      calc (c.phiT hV t)⁻¹ * (c.phiT hV t * h * (c.phiT hV t)⁻¹) * (c.phiT hV t)
          = MulAut.conj (c.phiT hV t⁻¹) (c.phiL hV x : MulAut (c.W hV)) := by
            rw [hmid, hφinv, MulAut.conj_apply]
            congr 1
            rw [map_inv, inv_inv]
        _ = (c.phiL hV ⟨(t⁻¹ : G) * (x : G) * (t⁻¹ : G)⁻¹, c.conj_mem t⁻¹ x⟩ :
            MulAut (c.W hV)) := c.phiT_conj_phiL hV t⁻¹ x
    rw [hfinal]
    exact (c.phiL hV _).2

theorem isPGroup_Tstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    IsPGroup 2 ↥(c.Tstar hV) := by
  have hT : IsPGroup 2 ↥D.T := D.sylowG.isPGroup
  have hTtop : IsPGroup 2 (⊤ : Subgroup ↥D.T) := by
    intro x
    obtain ⟨n, hn⟩ := hT x.1
    exact ⟨n, Subtype.ext hn⟩
  rw [Ctx23L.Tstar, MonoidHom.range_eq_map]
  exact hTtop.map (c.phiT hV)

theorem isSylowIn_T_inf_L (c : Ctx23L D Ch) :
    CFSG.Quasithin.IsSylowIn 2 (D.T ⊓ c.L) c.L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTG : CFSG.Quasithin.IsSylowIn 2 D.T ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowG
  have hTLT : CFSG.Quasithin.IsSylowIn 2 D.T (c.L ⊔ D.T) :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_of_le_of_le hTG le_sup_right le_top
  have hLnorm : (c.L.subgroupOf (c.L ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer c.hL.1.1)
  exact hTLT.inf_normal le_sup_left hLnorm

private theorem card_map_T_inf_L (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Nat.card ((D.T.subgroupOf c.L).map (c.phiL hV)) =
      2 ^ (Nat.card ↥(c.H hV)).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SL : Sylow 2 ↥c.L := (isSylowIn_T_inf_L c).toSylow
  let Q : Sylow 2 ↥(c.H hV) := SL.mapSurjective (c.phiL_surjective hV)
  have hP : ((D.T.subgroupOf c.L) : Subgroup ↥c.L).map (c.phiL hV) =
      (Q : Subgroup ↥(c.H hV)) := by
    rw [Sylow.coe_mapSurjective]
    congr 1
    rw [CFSG.Quasithin.IsSylowIn.coe_toSylow]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hP]
  exact Sylow.card_eq_multiplicity Q

noncomputable def sylowStar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Sylow 2 ↥(c.H hV) :=
  Sylow.ofCard ((D.T.subgroupOf c.L).map (c.phiL hV)) (c.card_map_T_inf_L hV)

@[simp] theorem sylowStar_coe (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    (c.sylowStar hV : Subgroup ↥(c.H hV)) = (D.T.subgroupOf c.L).map (c.phiL hV) :=
  Sylow.coe_ofCard _ _

theorem sylowStar_le_Tstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ((c.sylowStar hV : Subgroup ↥(c.H hV)).map (c.H hV).subtype) ≤ c.Tstar hV := by
  intro φ hφ
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hφ
  rw [Ctx23L.sylowStar_coe] at hh
  obtain ⟨x, hxT, hx⟩ := Subgroup.mem_map.1 hh
  rw [Ctx23L.Tstar, MonoidHom.mem_range]
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hxT⟩, ?_⟩
  rw [← hx]
  change actTil (⊥ : Subgroup G) c.V hV ⟨(x : G), c.T_le_stabTil (Subgroup.mem_subgroupOf.1 hxT)⟩ =
    actTil (⊥ : Subgroup G) c.V hV ⟨(x : G), c.L_le_stabTil x.2⟩
  rw [show (⟨(x : G), c.T_le_stabTil (Subgroup.mem_subgroupOf.1 hxT)⟩ :
      stabTil (⊥ : Subgroup G) c.V) = ⟨(x : G), c.L_le_stabTil x.2⟩ from Subtype.ext rfl]

theorem commutator_H_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ⁅c.H hV, c.H hV⁆ = c.H hV := by
  have htopL : (⊤ : Subgroup ↥c.L).map c.L.subtype = c.L := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype (H := c.L)
  have hperfectL : commutator ↥c.L = ⊤ := by
    have hmap : (commutator ↥c.L).map c.L.subtype =
        (⊤ : Subgroup ↥c.L).map c.L.subtype := by
      rw [Subgroup.map_subtype_commutator, c.hL.1.2.1, htopL]
    exact Subgroup.map_subtype_inj.mp hmap
  have hperfectH : commutator ↥(c.H hV) = ⊤ := by
    have h := map_commutator_eq (f := c.phiL hV)
    rw [MonoidHom.range_eq_top.mpr (c.phiL_surjective hV)] at h
    rw [commutator_def, ← h, hperfectL,
      Subgroup.map_top_of_surjective _ (c.phiL_surjective hV)]
  rw [← Subgroup.map_subtype_commutator (c.H hV), hperfectH]
  rw [← MonoidHom.range_eq_map]
  exact Subgroup.range_subtype (H := c.H hV)

theorem exists_isNaturalClassicalModule (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) :
    ∃ hV : IsElemAbelian 2 c.V,
      IsNaturalClassicalModule (barSub (⊥ : Subgroup G) c.V hV c.L) (CFSG.Open.pRank 2 D.Z) := by
  obtain ⟨hV, n', hcardU0, hnat⟩ := h2 h1930 c
  have hU0 : c.U0 = D.Z := (h3 h1930 c).trans (h4 h1930 c).1
  have hcardZ : Nat.card D.Z = 2 ^ n' := by rw [← hU0]; exact hcardU0
  have hZel : IsElemAbelian 2 D.Z := c.isElemAbelian_Z h4 h1930
  have hZcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZel
  have hpow : 2 ^ n' = 2 ^ CFSG.Open.pRank 2 D.Z := by
    rw [← hcardZ, hZcard]
  have hn' : n' = CFSG.Open.pRank 2 D.Z :=
    Nat.pow_right_injective (by norm_num : (1 : ℕ) < 2) hpow
  exact ⟨hV, hn' ▸ hnat⟩

@[expose] noncomputable def Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup (c.W hV) :=
  imgTil (⊥ : Subgroup G) c.V hV D.Z

theorem card_Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Nat.card (c.Ztil hV) = Nat.card D.Z := by
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  rw [Ctx23L.Ztil, imgTil,
    Subgroup.card_map_of_injective (TwelveShort.mkTilEquiv c.V hV).injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleV).toEquiv

theorem phiL_apply_mkTil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (x : ↥c.L) (v : IntMod c.V hV) :
    (c.phiL hV x : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV
        (actStab (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ v) :=
  actTil_mk (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ v

private theorem phiL_apply_mkTil_of_mem_centralizer (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {x : ↥c.L}
    (hcent : (x : G) ∈ Subgroup.centralizer (D.Z : Set G)) (v : IntMod c.V hV)
    (hvZ : v.val ∈ D.Z) :
    (c.phiL hV x : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV v := by
  rw [c.phiL_apply_mkTil hV x v]
  have hcomm : (x : G) * v.val * (x : G)⁻¹ = v.val := by
    have hc := (Subgroup.mem_centralizer_iff.mp hcent) v.val hvZ
    calc (x : G) * v.val * (x : G)⁻¹ = v.val * (x : G) * (x : G)⁻¹ := by rw [hc]
      _ = v.val := by group
  have hact : actStab (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ v = v := by
    apply IntMod.val_injective
    rw [actStab_apply_val, hcomm]
  rw [hact]

private theorem image_Ztil_le_of_mem_normalizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {x : ↥c.L} (hxN : (x : G) ∈ Subgroup.normalizer (D.Z : Set G)) :
    (c.Ztil hV).map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom ≤ c.Ztil hV := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
  rw [Ctx23L.Ztil, mem_imgTil] at hz ⊢
  obtain ⟨v, hvZ, rfl⟩ := hz
  refine ⟨actStab (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩ v, ?_, ?_⟩
  · rw [actStab_apply_val]
    have hmap : D.Z.map (MulAut.conj (x : G)).toMonoidHom = D.Z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    have hmem : (MulAut.conj (x : G)) v.val ∈ D.Z := by
      have h' : (MulAut.conj (x : G)) v.val ∈
          D.Z.map (MulAut.conj (x : G)).toMonoidHom := Subgroup.mem_map_of_mem _ hvZ
      rwa [hmap] at h'
    simpa [MulAut.conj_apply] using hmem
  · rw [← c.phiL_apply_mkTil hV x v]
    rfl

private theorem mem_normalizer_of_image_Ztil_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {x : ↥c.L}
    (h : (c.Ztil hV).map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom = c.Ztil hV) :
    (x : G) ∈ Subgroup.normalizer (D.Z : Set G) := by
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · intro w hw
    obtain ⟨v, hvZ, rfl⟩ := Subgroup.mem_map.1 hw
    have hvV : v ∈ c.V := hZleV hvZ
    let v' : c.W hV := mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hvV⟩)
    have hv' : v' ∈ c.Ztil hV := by
      rw [Ctx23L.Ztil, mem_imgTil]
      exact ⟨IntMod.mk hV ⟨v, hvV⟩, hvZ, rfl⟩
    have hmem : (c.phiL hV x : MulAut (c.W hV)) v' ∈ c.Ztil hV := by
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hv'
    rw [Ctx23L.Ztil, mem_imgTil] at hmem
    obtain ⟨u, huZ, hu⟩ := hmem
    have hcalc : (c.phiL hV x : MulAut (c.W hV)) v' =
        mkTil (⊥ : Subgroup G) c.V hV
          (actStab (⊥ : Subgroup G) c.V hV ⟨x, c.L_le_stabTil x.2⟩
            (IntMod.mk hV ⟨v, hvV⟩)) := c.phiL_apply_mkTil hV x _
    rw [hcalc, mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val] at hu
    have hu' : u.val = (x : G) * v * (x : G)⁻¹ := mul_inv_eq_one.mp hu
    change (x : G) * v * (x : G)⁻¹ ∈ D.Z
    rw [← hu']
    exact huZ
  · rw [Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective]

private theorem image_Ztil_eq_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (x : ↥c.L) :
    (c.Ztil hV).map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom = c.Ztil hV ↔
      (x : G) ∈ Subgroup.normalizer (D.Z : Set G) := by
  constructor
  · exact mem_normalizer_of_image_Ztil_eq c hV
  · intro hxN
    refine le_antisymm (image_Ztil_le_of_mem_normalizer c hV hxN) ?_
    intro w hw
    have hxinv : (x : G)⁻¹ ∈ Subgroup.normalizer (D.Z : Set G) :=
      (Subgroup.normalizer (D.Z : Set G)).inv_mem hxN
    have hsub := image_Ztil_le_of_mem_normalizer c hV (x := x⁻¹) hxinv
    rw [Subgroup.mem_map]
    refine ⟨(c.phiL hV x⁻¹ : MulAut (c.W hV)) w, ?_, ?_⟩
    · exact hsub (Subgroup.mem_map_of_mem _ hw)
    · change (c.phiL hV x : MulAut (c.W hV))
        ((c.phiL hV x⁻¹ : MulAut (c.W hV)) w) = w
      rw [← MulAut.mul_apply]
      have hmulH : c.phiL hV x * c.phiL hV x⁻¹ = c.phiL hV (x * x⁻¹) := by
        rw [← map_mul]
      have hmul : (c.phiL hV x : MulAut (c.W hV)) *
          (c.phiL hV x⁻¹ : MulAut (c.W hV)) =
          (c.phiL hV (x * x⁻¹) : MulAut (c.W hV)) := congrArg Subtype.val hmulH
      have h1 : (c.phiL hV (x * x⁻¹) : MulAut (c.W hV)) = 1 := by
        have h2 : c.phiL hV (x * x⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
        exact congrArg Subtype.val h2
      rw [hmul, h1, MulAut.one_apply]

theorem fixedPointSubgroup_sylowStar_eq_Ztil (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hmain := hA (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat (c.commutator_H_eq hV)
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  letI : MulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  have hcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (c.isElemAbelian_Z h4 h1930)
  have hℓcard : Nat.card (fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)) =
      2 ^ CFSG.Open.pRank 2 D.Z := (hmain (c.sylowStar hV)).1
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · intro z hz
    change z ∈ FixedPoints.subgroup ↥(c.sylowStar hV) (c.W hV)
    rw [FixedPoints.mem_subgroup]
    intro s
    have hs : (s : ↥(c.H hV)) ∈ (D.T.subgroupOf c.L).map (c.phiL hV) := by
      rw [← c.sylowStar_coe hV]
      exact s.2
    obtain ⟨y, hy, hyφ⟩ := Subgroup.mem_map.1 hs
    have hyT : (y : G) ∈ D.T := Subgroup.mem_subgroupOf.1 hy
    rw [Ctx23L.Ztil, mem_imgTil] at hz
    obtain ⟨v, hvZ, rfl⟩ := hz
    have hsmul : s • mkTil (⊥ : Subgroup G) c.V hV v =
        (c.phiL hV y : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) := by
      simp only [MulAction.compHom_smul_def, MulAut.smul_def, MonoidHom.comp_apply,
        show (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype s = c.phiL hV y from hyφ.symm]
      rfl
    have hcent : (y : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
      le_centralizer_omegaOneCenterIn D.T hyT
    have hfix := c.phiL_apply_mkTil_of_mem_centralizer hV hcent v hvZ
    rw [hsmul, hfix]
  · rw [hℓcard, c.card_Ztil hV, hcard]

theorem phiL_mem_stabilizer_Ztil_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (x : ↥c.L) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    c.phiL hV x ∈ MulAction.stabilizer ↥(c.H hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) ↔ (x : G) ∈ D.M := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    have hUZ : D.U = D.Z := (h4 h1930 c).1
    rw [← hUZ]
    exact D.normalizer_U_eq
  rw [← hNZ, MulAction.mem_stabilizer_iff]
  have hcoe : (c.phiL hV x) • (c.Ztil hV : Set (c.W hV)) =
      (((c.Ztil hV).map (c.phiL hV x : MulAut (c.W hV)).toMonoidHom) :
        Set (c.W hV)) := by
    rw [Subgroup.coe_map, ← Set.image_smul]
    rfl
  rw [hcoe]
  constructor
  · intro h
    exact (c.image_Ztil_eq_iff hV x).1 (Subgroup.ext (Set.ext_iff.mp h))
  · intro h
    have := (c.image_Ztil_eq_iff hV x).2 h
    rw [this]

theorem phiL_mem_fixingSubgroup_Ztil_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (x : ↥c.L) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    c.phiL hV x ∈ fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) ↔
      (x : G) ∈ Subgroup.centralizer (D.Z : Set G) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  rw [fixingSubgroupOf, mem_fixingSubgroup_iff]
  constructor
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : z ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hz
    have hz' : mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩) ∈ c.Ztil hV := by
      rw [Ctx23L.Ztil, mem_imgTil]
      exact ⟨IntMod.mk hV ⟨z, hzV⟩, hz, rfl⟩
    have h := hfix _ hz'
    have h' : (c.phiL hV x : MulAut (c.W hV))
        (mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩)) =
        mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨z, hzV⟩) := by
      simpa [MulAction.compHom_smul_def, MulAut.smul_def] using h
    rw [c.phiL_apply_mkTil hV x (IntMod.mk hV ⟨z, hzV⟩),
      mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val] at h'
    have hxz : (x : G) * z * (x : G)⁻¹ = z := mul_inv_eq_one.mp h'
    have h3 := congrArg (· * (x : G)) hxz
    simpa [mul_assoc] using h3.symm
  · intro hcent
    intro y hy
    change y ∈ c.Ztil hV at hy
    rw [Ctx23L.Ztil, mem_imgTil] at hy
    obtain ⟨v, hvZ, rfl⟩ := hy
    change (c.phiL hV x : MulAut (c.W hV)) (mkTil (⊥ : Subgroup G) c.V hV v) =
      mkTil (⊥ : Subgroup G) c.V hV v
    exact c.phiL_apply_mkTil_of_mem_centralizer hV hcent v hvZ

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
