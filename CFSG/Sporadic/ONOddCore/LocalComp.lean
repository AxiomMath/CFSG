module

public import CFSG.Sporadic.ONOddCore.FullGroup
public import CFSG.Sporadic.SuzOddCore.CompQuot

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalCores CFSG.ComponentClassification
open UnbalancedCatalog.EvenCatalog (oddCore_eq_bot_of_mulEquiv)

theorem center_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg e (Subgroup.mem_center_iff.1 hx (e.symm g))
    simpa using h1
  · intro hy
    refine ⟨e.symm y, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    have h1 := congrArg e.symm (Subgroup.mem_center_iff.1 hy (e g))
    simpa using h1

theorem card_quotient_center_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (H ⧸ Subgroup.center H) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (center_map_mulEquiv e)).toEquiv

theorem component_card_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {B : Subgroup G} (hB : IsComponent B) :
    IsComponent (B.map e.toMonoidHom) ∧ Nat.card (B ⧸ Subgroup.center B) =
      Nat.card (B.map e.toMonoidHom ⧸ Subgroup.center (B.map e.toMonoidHom)) :=
  ⟨isComponent_map_mulEquiv e hB,
    card_quotient_center_mulEquiv (B.equivMapOfInjective e.toMonoidHom e.injective)⟩

theorem not_comm_of_center_bot {G : Type*} [Group G] [Nontrivial G]
    (h : Subgroup.center G = ⊥) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  have hall : ∀ a b : G, a * b = b * a := fun a b => by_contra fun h' => hc ⟨a, b, h'⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  have hz : a ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => hall g a
  rw [h, Subgroup.mem_bot] at hz
  exact ha hz

theorem XR_index :
    XR.index = 2 := by
  have h := XR.card_mul_index
  rw [Nat.card_congr XREquiv.toEquiv, card_onX, card_RM] at h
  omega

theorem XR_simple :
    IsSimpleGroup XR :=
  (XREquiv.trans thetaX.symm).isSimpleGroup

theorem XR_noncomm :
    ∃ a b : XR, a * b ≠ b * a := by
  have : Nontrivial S3 := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_S3]
    norm_num
  obtain ⟨a, b, hab⟩ := not_comm_of_center_bot center_S3
  set φ : S3 ≃* XR := (XREquiv.trans thetaX.symm).symm
  refine ⟨φ a, φ b, fun h => hab (φ.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem card_component_M
    (B : Subgroup onM) (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 20160 := by
  have hker : Group.IsSolvable piR.ker := by
    rw [ker_piR]
    have hp : IsPGroup 2 (onQ.subgroupOf onM) :=
      IsPGroup.of_card (n := 2) (by rw [card_onQ_subgroupOf_M]; norm_num)
    have : Group.IsNilpotent (onQ.subgroupOf onM) := hp.isNilpotent
    infer_instance
  rw [SuzOddCore.card_quotient_center_of_component piR piR_surjective hker XR XR_index XR_simple
    XR_noncomm hB, Nat.card_congr XREquiv.toEquiv, card_onX]

theorem centralizer_P_equiv_M
    {a : Pv} (ha : orderOf a = 2) :
    Nonempty (Subgroup.centralizer {a} ≃* onM) := by
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2
    (by rw [Subgroup.orderOf_coe]; exact ha)
  set gP : Pv := ⟨g, hg⟩
  have hφa : MulAut.conj gP⁻¹ a = zP := by
    apply Subtype.ext
    show (g⁻¹ * (a : Equiv.Perm (Fin N)) * g⁻¹⁻¹) = onz
    rw [hga]
    group
  have e := centralizerCongr (MulAut.conj gP⁻¹) a
  rw [hφa, centralizer_zP] at e
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe onM_le)⟩

theorem cti_on_involution_local_components_projective_linear_quotient_order
    {T : Type*}
    [Group T] (hT : Nonempty (T ≃* Blueprint.NativeSporadic.ON)) (t : T) (ht : orderOf t = 2)
    (B : Subgroup (Subgroup.centralizer ({t} : Set T))) (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 20160 := by
  obtain ⟨e⟩ := hT
  set f : T ≃* Pv := e.trans onEquivPv
  have hft : orderOf (f t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨g⟩ := centralizer_P_equiv_M hft
  set h : Subgroup.centralizer ({t} : Set T) ≃* onM := (centralizerCongr f t).trans g
  obtain ⟨hB', hcard⟩ := component_card_of_mulEquiv h hB
  rw [hcard]
  exact card_component_M _ hB'

end CFSG.Sporadic.ONOddCore
