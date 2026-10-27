module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootClique
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

theorem commute_conj_iff' {G : Type*} [Group G] (g a b : G) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := by
  rw [commute_iff_eq, commute_iff_eq,
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group,
    show g * b * g⁻¹ * (g * a * g⁻¹) = g * (b * a) * g⁻¹ by group, mul_left_inj, mul_right_inj]

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

@[expose] def hOrbit
    (ρ : sliceGroup lab Y →* stdGroup) (u : fixedL) : Set fixedL :=
  {u' | ∃ h : sliceGroup lab Y, u' = actStar (SemidirectProduct.inl (ρ h)) u}

theorem mem_hOrbit
    {ρ : sliceGroup lab Y →* stdGroup} {u u' : fixedL} :
    u' ∈ hOrbit ρ u ↔ ∃ h : sliceGroup lab Y, u' = actH ρ h u :=
  Iff.rfl

theorem mem_hOrbit_self
    (ρ : sliceGroup lab Y →* stdGroup) (u : fixedL) : u ∈ hOrbit ρ u :=
  ⟨1, by change u = actH ρ 1 u; rw [map_one, Equiv.Perm.one_apply]⟩

theorem actH_mem_hOrbit
    (ρ : sliceGroup lab Y →* stdGroup) {u w : fixedL} (hw : w ∈ hOrbit ρ u)
    (g : sliceGroup lab Y) : actH ρ g w ∈ hOrbit ρ u := by
  obtain ⟨h, rfl⟩ := hw
  exact ⟨g * h, by change _ = actH ρ (g * h) u; rw [map_mul, Equiv.Perm.mul_apply]; rfl⟩

theorem hOrbit_eq_of_mem
    {ρ : sliceGroup lab Y →* stdGroup} {u w : fixedL}
    (hw : w ∈ hOrbit ρ u) : hOrbit ρ w = hOrbit ρ u := by
  obtain ⟨g, rfl⟩ := hw
  ext u'
  constructor
  · rintro ⟨h, rfl⟩
    exact actH_mem_hOrbit ρ ⟨g, rfl⟩ h
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    change actH ρ h u = actH ρ (h * g⁻¹) (actH ρ g u)
    rw [map_mul, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply (actH ρ g⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Equiv.Perm.one_apply]

theorem disjoint_hOrbit_of_ncard_ne
    {ρ : sliceGroup lab Y →* stdGroup} {u u' : fixedL}
    (h : (hOrbit ρ u).ncard ≠ (hOrbit ρ u').ncard) : Disjoint (hOrbit ρ u) (hOrbit ρ u') := by
  rw [Set.disjoint_left]
  intro w hw hw'
  exact h (by rw [← hOrbit_eq_of_mem hw, ← hOrbit_eq_of_mem hw'])

theorem ncard_hOrbit_mul
    (ρ : sliceGroup lab Y →* stdGroup) (u : fixedL) :
    (hOrbit ρ u).ncard * Nat.card (stabH ρ u) = Nat.card (sliceGroup lab Y) := by
  let _ := MulAction.compHom fixedL (actH ρ)
  have h1 : hOrbit ρ u = MulAction.orbit (sliceGroup lab Y) u := by
    ext u'
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
  have h2 : stabH ρ u = MulAction.stabilizer (sliceGroup lab Y) u := by
    ext g
    rw [mem_stabH, MulAction.mem_stabilizer_iff]
    rfl
  rw [h1, h2, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]

theorem hOrbit_subset_rootVecSet
    {ρ : sliceGroup lab Y →* stdGroup} {u : fixedL}
    (hu : u ∈ rootVecSet) : hOrbit ρ u ⊆ rootVecSet := by
  rintro _ ⟨h, rfl⟩
  rw [actStar_inl_eq_gL]
  exact gL_mem_rootVecSet hu _

theorem rho_lab_act
    (hS : IsFischerSlice act lab Y) (ρ : sliceGroup lab Y →* stdGroup)
    (h : sliceGroup lab Y) (y : Y) (hy : act (h : S) y ∈ Y) :
    ρ ⟨lab (act (h : S) y), lab_mem_sliceGroup hy⟩ = ρ h * ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ *
      (ρ h)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hS.lab_act _ _)

theorem ncard_commute_conj
    (hS : IsFischerSlice act lab Y) (ρ : sliceGroup lab Y →* stdGroup)
    (q : stdGroup) (h : sliceGroup lab Y) :
    {y : Y | Commute (ρ h * q * (ρ h)⁻¹) (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard =
      {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard := by
  have e : {y : Y | Commute (ρ h * q * (ρ h)⁻¹) (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} =
      (slicePerm act lab Y hS.mapsTo h) ''
        {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} := by
    ext y
    constructor
    · intro hy
      refine ⟨(slicePerm act lab Y hS.mapsTo h).symm y, ?_, Equiv.apply_symm_apply _ _⟩
      set y' := (slicePerm act lab Y hS.mapsTo h).symm y
      have hyy : (slicePerm act lab Y hS.mapsTo h) y' = y := Equiv.apply_symm_apply _ _
      have e1 := rho_lab_act hS ρ h y' ((slicePerm act lab Y hS.mapsTo h) y').2
      have e2 : (⟨lab (act (h : S) y'),
          lab_mem_sliceGroup ((slicePerm act lab Y hS.mapsTo h) y').2⟩ : sliceGroup lab Y) =
          ⟨lab y, lab_mem_sliceGroup y.2⟩ := by
        rw [← hyy]
        rfl
      rw [e2] at e1
      change Commute q (ρ ⟨lab y', lab_mem_sliceGroup y'.2⟩)
      rw [← commute_conj_iff' (ρ h), ← e1]
      exact hy
    · rintro ⟨y', hy', rfl⟩
      change Commute _ (ρ ⟨lab (act (h : S) y'), _⟩)
      rw [rho_lab_act hS ρ h y' (hS.mapsTo _ h.2 _ y'.2), commute_conj_iff']
      exact hy'
  rw [e, Set.ncard_image_of_injective _ (Equiv.injective _)]

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
  {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
  {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
  (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
  {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)

include H hΦ in
theorem card_sliceGroup :
    Nat.card (sliceGroup lab Y) = 64561751654400 := by
  obtain ⟨ψ, -, -, -, -, hcard, -⟩ := H.canonical_identification hΦ
  rw [Nat.card_congr ψ.toEquiv, hcard]

include H in
theorem card_setStab : Nat.card (setStab act lab Y C) = 454164480 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((ptStab act lab Y C).subgroupOf (setStab act lab Y C)), Nat.card_congr θ.toEquiv,
    CFSG.Sporadic.Mathieu.card_M22,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ptStab_le_setStab C)).toEquiv, H.card_ptStab]
  norm_num

include H in
theorem card_stabilizer_clique (c₀ : C) :
    letI := MulAction.compHom C (setStabPerm act lab Y C)
    Nat.card (MulAction.stabilizer (setStab act lab Y C) c₀) = 20643840 := by
  let _ := MulAction.compHom C (setStabPerm act lab Y C)
  have horbit : MulAction.orbit (setStab act lab Y C) c₀ = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨f, hf, hfc⟩ := H.slice.exists_setStab H.clique c₀.2 c.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfc⟩
  have hC : Nat.card C = 22 := by
    rw [Nat.card_congr η, Nat.card_eq_fintype_card, Fintype.card_coe, card_X₀]
  have hidx := MulAction.index_stabilizer (setStab act lab Y C) c₀
  rw [horbit, Set.ncard_univ, hC] at hidx
  have hmul := (MulAction.stabilizer (setStab act lab Y C) c₀).card_mul_index
  rw [hidx, H.card_setStab] at hmul
  omega

include H hroot hΨ in
theorem psi_act (h : sliceGroup lab Y) (y : Y) (hy : act (h : S) y ∈ Y) :
    Ψ (ncommVec lab Y ⟨act (h : S) y, hy⟩) = actH ρ h (Ψ (ncommVec lab Y y)) := by
  rw [hΨ, hΨ, actH_eq_gL]
  exact H.slice.adjVec_act hroot h y hy

include H hroot hΨ in
theorem mem_setStab_of_zeroSet
    {w : fixedL}
    (hw : ∀ y : Y, bracketL w (Ψ (ncommVec lab Y y)) = 0 ↔ (y : V) ∈ C)
    {h : sliceGroup lab Y} (hh : actH ρ h w = w) : (h : S) ∈ setStab act lab Y C := by
  refine ⟨h.2, fun v => ?_⟩
  by_cases hv : v ∈ Y
  · have hmem : act (h : S) v ∈ Y := H.slice.mapsTo _ h.2 v hv
    have h1 := hw ⟨act (h : S) v, hmem⟩
    have h2 := hw ⟨v, hv⟩
    change _ ↔ (act (h : S) v) ∈ C at h1
    change _ ↔ v ∈ C at h2
    have key : bracketL w (Ψ (ncommVec lab Y ⟨act (h : S) v, hmem⟩)) =
        gL (ρ h) (bracketL w (Ψ (ncommVec lab Y ⟨v, hv⟩))) := by
      rw [H.psi_act hroot hΨ h ⟨v, hv⟩ hmem, actH_eq_gL]
      conv_lhs => rw [← hh, actH_eq_gL]
      exact bracketL_gL _ _ _
    rw [← h1, ← h2, key, (gL_injective (ρ h)).eq_iff' (map_zero _)]
  · have h1 : act (h : S) v ∉ Y := fun h' =>
      hv ((act_mem_iff_of_mapsTo act Y (sliceGroup lab Y) H.slice.mapsTo h v).1 h')
    exact iff_of_false (fun hc => h1 (H.clique.1.1 hc)) (fun hc => hv (H.clique.1.1 hc))

include H hΦ hroot hΨ in
theorem actH_cliqueFixedVec_iff
    (hρ : Function.Injective ρ) (h : sliceGroup lab Y) :
    actH ρ h (cliqueFixedVec Φ Ψ) = cliqueFixedVec Φ Ψ ↔ (h : S) ∈ setStab act lab Y C := by
  constructor
  · exact H.mem_setStab_of_zeroSet hroot hΨ
      (H.bracketL_cliqueFixedVec_eq_zero_iff hΦ hρ hroot hΨ)
  · intro hh
    have hz := (Set.ext_iff.1 (H.fixed_setStab_eq hΦ hroot hΨ) (cliqueFixedVec Φ Ψ)).2
      (Or.inr rfl)
    exact hz ⟨h, hh⟩

include H hroot hΨ in
theorem psi_ncommVec_injective
    (hρ : Function.Injective ρ) :
    Function.Injective fun y : Y => Ψ (ncommVec lab Y y) := by
  intro y y' e
  simp only [hΨ] at e
  have e1 := bijOn_rootVecOf.injOn (hroot y) (hroot y') e
  have e2 := congrArg Subtype.val (hρ e1)
  exact Subtype.ext (H.slice.injOn y.2 y'.2 e2)

include H hΦ hρ hroot hΨ in
theorem actH_cliqueFixedVec_add_iff
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) (h : sliceGroup lab Y) :
    actH ρ h (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) =
        cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀) ↔
      (h : S) ∈ setStab act lab Y C ∧ act (h : S) y₀ = y₀ := by
  have hmem : ∀ h' : sliceGroup lab Y, act (h' : S) y₀ ∈ Y := fun h' =>
    H.slice.mapsTo _ h'.2 _ y₀.2
  constructor
  · intro hh
    have hF := H.mem_setStab_of_zeroSet hroot hΨ
      (H.bracketL_cliqueFixedVec_add_eq_zero_iff hΦ hρ hroot hΨ hy₀) hh
    refine ⟨hF, ?_⟩
    have hz := (H.actH_cliqueFixedVec_iff hΦ hroot hΨ hρ h).2 hF
    have e : actH ρ h (Ψ (ncommVec lab Y y₀)) = Ψ (ncommVec lab Y y₀) := by
      rw [actH_eq_gL, map_add, ← actH_eq_gL, hz, ← actH_eq_gL] at hh
      exact add_left_cancel hh
    rw [← H.psi_act hroot hΨ h y₀ (hmem h)] at e
    exact congrArg Subtype.val (H.psi_ncommVec_injective hroot hΨ hρ e)
  · rintro ⟨hF, hy⟩
    have hz := (H.actH_cliqueFixedVec_iff hΦ hroot hΨ hρ h).2 hF
    rw [actH_eq_gL, map_add, ← actH_eq_gL, hz, ← actH_eq_gL,
      ← H.psi_act hroot hΨ h y₀ (hmem h)]
    congr 3
    exact Subtype.ext hy

include H hΦ hroot hΨ in
theorem card_stabH_cliqueFixedVec
    (hρ : Function.Injective ρ) :
    Nat.card (stabH ρ (cliqueFixedVec Φ Ψ)) = 454164480 := by
  have e : stabH ρ (cliqueFixedVec Φ Ψ) ≃ setStab act lab Y C :=
    { toFun := fun h => ⟨h.1, (H.actH_cliqueFixedVec_iff hΦ hroot hΨ hρ h.1).1 (mem_stabH.1 h.2)⟩
      invFun := fun f => ⟨⟨f.1, f.2.1⟩,
        mem_stabH.2 ((H.actH_cliqueFixedVec_iff hΦ hroot hΨ hρ _).2 f.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, H.card_setStab]

include H hΦ hρ hroot hΨ in
theorem card_stabH_cliqueFixedVec_add
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) :
    Nat.card (stabH ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) = 20643840 := by
  let _ := MulAction.compHom C (setStabPerm act lab Y C)
  have hiff := H.actH_cliqueFixedVec_add_iff hΦ hρ hroot hΨ hy₀
  have e : stabH ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) ≃
      MulAction.stabilizer (setStab act lab Y C) (⟨y₀, hy₀⟩ : C) :=
    { toFun := fun h => ⟨⟨h.1, ((hiff h.1).1 (mem_stabH.1 h.2)).1⟩,
        MulAction.mem_stabilizer_iff.2 (Subtype.ext ((hiff h.1).1 (mem_stabH.1 h.2)).2)⟩
      invFun := fun f => ⟨⟨f.1.1, f.1.2.1⟩, mem_stabH.2 ((hiff _).2
        ⟨f.1.2, congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 f.2)⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, H.card_stabilizer_clique]

include H hΦ hρ hroot hΨ in
theorem ncard_hOrbit_cliqueFixedVec :
    (hOrbit ρ (cliqueFixedVec Φ Ψ)).ncard = 142155 := by
  have h := ncard_hOrbit_mul ρ (cliqueFixedVec Φ Ψ)
  rw [H.card_stabH_cliqueFixedVec hΦ hroot hΨ hρ, H.card_sliceGroup hΦ] at h
  omega

include H hΦ hρ hroot hΨ in
theorem ncard_hOrbit_cliqueFixedVec_add
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) :
    (hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))).ncard = 3127410 := by
  have h := ncard_hOrbit_mul ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))
  rw [H.card_stabH_cliqueFixedVec_add hΦ hρ hroot hΨ hy₀, H.card_sliceGroup hΦ] at h
  omega

include H hroot hΨ in
theorem hOrbit_psi (y₀ : Y) :
    hOrbit ρ (Ψ (ncommVec lab Y y₀)) = Set.range fun y : Y => Ψ (ncommVec lab Y y) := by
  ext u
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨⟨act (h : S) y₀, H.slice.mapsTo _ h.2 _ y₀.2⟩, H.psi_act hroot hΨ h y₀ _⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨g, hg, hgy⟩ := H.slice.transitive y₀ y₀.2 y y.2
    refine ⟨⟨g, hg⟩, ?_⟩
    change _ = actH ρ ⟨g, hg⟩ _
    rw [← H.psi_act hroot hΨ ⟨g, hg⟩ y₀ (hgy ▸ y.2)]
    congr 2
    exact Subtype.ext hgy.symm

include H hroot hΨ in
theorem ncard_range_psi
    (hρ : Function.Injective ρ) :
    (Set.range fun y : Y => Ψ (ncommVec lab Y y)).ncard = 3510 := by
  rw [Set.ncard_range_of_injective (H.psi_ncommVec_injective hroot hΨ hρ), Nat.card_coe_set_eq,
    H.slice.ncard]

include H in
theorem ncard_commute_of_mem_hOrbit
    {u₀ u : fixedL} (hu : u ∈ hOrbit ρ u₀) {q₀ q : stdGroup}
    (hq₀ : IsConj rootInv q₀) (hq : IsConj rootInv q) (h₀ : rootVecOf q₀ = u₀)
    (h : rootVecOf q = u) :
    {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard =
      {y : Y | Commute q₀ (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard := by
  obtain ⟨g, rfl⟩ := hu
  have e : q = ρ g * q₀ * (ρ g)⁻¹ := bijOn_rootVecOf.injOn hq (conj_mem_rootClass hq₀ _) (by
    rw [h, rootVecOf_conj hq₀, h₀, ← actStar_inl_eq_gL])
  rw [e, ncard_commute_conj H.slice ρ q₀ g]

end FullIntertwinerHyp

namespace IsFischerSlice

theorem two_additional_ambient_root_orbits
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) :
    (∀ h : sliceGroup lab Y, actStar (SemidirectProduct.inl (ρ h)) (cliqueFixedVec Φ Ψ) =
      cliqueFixedVec Φ Ψ ↔ (h : S) ∈ setStab act lab Y C) ∧
    (∀ h : sliceGroup lab Y,
      actStar (SemidirectProduct.inl (ρ h)) (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) =
        cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀) ↔
      (h : S) ∈ setStab act lab Y C ∧ act (h : S) y₀ = y₀) ∧
    hOrbit ρ (Ψ (ncommVec lab Y y₀)) = Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∧
    (Set.range fun y : Y => Ψ (ncommVec lab Y y)).ncard = 3510 ∧
    (hOrbit ρ (cliqueFixedVec Φ Ψ)).ncard = 142155 ∧
    (hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))).ncard = 3127410 ∧
    Disjoint (Set.range fun y : Y => Ψ (ncommVec lab Y y)) (hOrbit ρ (cliqueFixedVec Φ Ψ)) ∧
    Disjoint (Set.range fun y : Y => Ψ (ncommVec lab Y y))
      (hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) ∧
    Disjoint (hOrbit ρ (cliqueFixedVec Φ Ψ))
      (hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) ∧
    (Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
      hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) ⊆
        rootVecOf '' {q : stdGroup | IsConj rootInv q} ∧
    (∀ u ∈ hOrbit ρ (cliqueFixedVec Φ Ψ), ∀ q : stdGroup, IsConj rootInv q → rootVecOf q = u →
      {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 22) ∧
    (∀ u ∈ hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)), ∀ q : stdGroup,
      IsConj rootInv q → rootVecOf q = u →
      {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 22) ∧
    (rootVecOf '' {q : stdGroup | IsConj rootInv q} \
      (Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
        hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)))).ncard = 694980 ∧
    ∀ h : sliceGroup lab Y, ∀ u ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} \
      (Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
        hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))),
      actStar (SemidirectProduct.inl (ρ h)) u ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} \
        (Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
          hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  have := finite_fixedL
  have hlab := H.hOrbit_psi hroot hΨ y₀
  have h1 := H.ncard_hOrbit_cliqueFixedVec hΦ hρ hroot hΨ
  have h2 := H.ncard_hOrbit_cliqueFixedVec_add hΦ hρ hroot hΨ hy₀
  have h0 := H.ncard_range_psi hroot hΨ hρ
  have hd01 : Disjoint (Set.range fun y : Y => Ψ (ncommVec lab Y y))
      (hOrbit ρ (cliqueFixedVec Φ Ψ)) := by
    rw [← hlab]
    exact disjoint_hOrbit_of_ncard_ne (by rw [hlab, h0, h1]; norm_num)
  have hd02 : Disjoint (Set.range fun y : Y => Ψ (ncommVec lab Y y))
      (hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) := by
    rw [← hlab]
    exact disjoint_hOrbit_of_ncard_ne (by rw [hlab, h0, h2]; norm_num)
  have hd12 : Disjoint (hOrbit ρ (cliqueFixedVec Φ Ψ))
      (hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) :=
    disjoint_hOrbit_of_ncard_ne (by rw [h1, h2]; norm_num)
  have hz := H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
  have hza := H.cliqueFixedVec_add_mem_rootVecSet hΦ hρ hroot hΨ hy₀
  have hsub : Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
      hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) ⊆ rootVecSet := by
    refine Set.union_subset (Set.union_subset ?_ (hOrbit_subset_rootVecSet hz))
      (hOrbit_subset_rootVecSet hza)
    rintro _ ⟨y, rfl⟩
    exact psi_mem_rootVecSet hroot hΨ y
  have hU : (Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
      hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))).ncard = 3273075 := by
    rw [Set.ncard_union_eq (Disjoint.union_left hd02 hd12), Set.ncard_union_eq hd01, h0, h1, h2]
  have hinv : ∀ (g : sliceGroup lab Y) (u : fixedL), u ∈ Set.range
      (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
        hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) →
      actH ρ g u ∈ Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪
        hOrbit ρ (cliqueFixedVec Φ Ψ) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) := by
    rintro g u ((hu | hu) | hu)
    · rw [← hlab] at hu ⊢
      exact Or.inl (Or.inl (actH_mem_hOrbit ρ hu g))
    · exact Or.inl (Or.inr (actH_mem_hOrbit ρ hu g))
    · exact Or.inr (actH_mem_hOrbit ρ hu g)
  obtain ⟨q₀, hq₀, hq₀z⟩ := hz
  obtain ⟨q₁, hq₁, hq₁z⟩ := hza
  refine ⟨fun h => H.actH_cliqueFixedVec_iff hΦ hroot hΨ hρ h,
    fun h => H.actH_cliqueFixedVec_add_iff hΦ hρ hroot hΨ hy₀ h, hlab, h0, h1, h2, hd01, hd02,
    hd12, hsub, fun u hu q hq hqu => ?_, fun u hu q hq hqu => ?_, ?_, fun h u hu => ?_⟩
  · rw [H.ncard_commute_of_mem_hOrbit hu hq₀ hq hq₀z hqu]
    have e : {y : Y | Commute q₀ (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | (y : V) ∈ C} := by
      ext y
      exact H.commute_cliqueFixedVec_iff hΦ hρ hroot hΨ hq₀ hq₀z y
    rw [e, H.ncard_clique]
  · rw [H.ncard_commute_of_mem_hOrbit hu hq₁ hq hq₁z hqu]
    have e : {y : Y | Commute q₁ (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | (y : V) ∈ C} := by
      ext y
      exact H.commute_cliqueFixedVec_add_iff hΦ hρ hroot hΨ hy₀ hq₁ hq₁z y
    rw [e, H.ncard_clique]
  · rw [Set.ncard_sdiff hsub, ncard_rootVecSet, hU]
  · refine ⟨?_, fun hmem => hu.2 ?_⟩
    · rw [actStar_inl_eq_gL]
      exact gL_mem_rootVecSet hu.1 _
    · have := hinv h⁻¹ _ hmem
      change actH ρ h⁻¹ (actH ρ h u) ∈ _ at this
      rwa [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply] at this

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
