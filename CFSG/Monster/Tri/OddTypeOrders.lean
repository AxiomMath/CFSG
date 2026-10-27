module

public import CFSG.Monster.Existence.TwoPoint.OddAssembly
public import CFSG.Monster.Existence.TwoPoint.ShapeSixCover
public import CFSG.Monster.GMS.Uniqueness
public import CFSG.Monster.GMS.Facts.Section4Coh

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section Conj

variable {G : Type} [Group G]

theorem cent2_conj (h a b : G) :
    cent2 (h * a * h⁻¹) (h * b * h⁻¹) = (cent2 a b).map (MulAut.conj h).toMonoidHom := by
  ext u
  constructor
  · intro hu
    refine ⟨h⁻¹ * u * h, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := conj_mem_inf_centralizer h⁻¹ hu
    have e1 : h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a := by group
    have e2 : h⁻¹ * (h * b * h⁻¹) * h⁻¹⁻¹ = b := by group
    rw [e1, e2, inv_inv] at this
    exact this
  · rintro ⟨v, hv, rfl⟩
    exact conj_mem_inf_centralizer h hv

theorem natCard_cent2_conj (h a b : G) :
    Nat.card ↥(cent2 (h * a * h⁻¹) (h * b * h⁻¹)) = Nat.card ↥(cent2 a b) := by
  rw [cent2_conj, Subgroup.card_map_of_injective (MulAut.conj h).injective]

end Conj

section Centralizer

variable {G : Type*} [Group G]

theorem map_subtype_centralizer (T : Subgroup G) (s : T) :
    (Subgroup.centralizer ({s} : Set T)).map T.subtype = T ⊓ Subgroup.centralizer {(s : G)} := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine Subgroup.mem_inf.2 ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hv)
  · intro hu
    obtain ⟨huT, huC⟩ := Subgroup.mem_inf.1 hu
    refine ⟨⟨u, huT⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 huC

theorem centralizer_eq_map_symm {T K : Type*} [Group T] [Group K] (ψ : T ≃* K) (s : T) :
    Subgroup.centralizer ({s} : Set T) =
      (Subgroup.centralizer ({ψ s} : Set K)).map ψ.symm.toMonoidHom := by
  ext u
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hu
    refine ⟨ψ u, Subgroup.mem_centralizer_singleton_iff.2 ?_, by simp⟩
    rw [← map_mul, ← map_mul, hu]
  · rintro ⟨v, hv, rfl⟩
    have hv' := Subgroup.mem_centralizer_singleton_iff.1 hv
    apply ψ.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hv'

theorem inf_centralizer_sup_eq_of_mulEquiv {K : Type*} [Group K] (T : Subgroup G) (ψ : T ≃* K)
    (s₁ s₂ : T)
    (hK : Subgroup.centralizer ({ψ s₁} : Set K) ⊔ Subgroup.centralizer {ψ s₂} = ⊤) :
    (T ⊓ Subgroup.centralizer {(s₁ : G)}) ⊔ (T ⊓ Subgroup.centralizer {(s₂ : G)}) = T := by
  have hT : Subgroup.centralizer ({s₁} : Set T) ⊔ Subgroup.centralizer {s₂} = ⊤ := by
    rw [centralizer_eq_map_symm ψ s₁, centralizer_eq_map_symm ψ s₂, ← Subgroup.map_sup, hK,
      Subgroup.map_top_of_surjective _ ψ.symm.surjective]
  rw [← map_subtype_centralizer, ← map_subtype_centralizer, ← Subgroup.map_sup, hT,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Centralizer

section MGriess

open CFSG.Monster.Griess

@[expose] def ThInvolutionCentralizersGenerate : Prop :=
  ∀ t₁ t₂ : Th, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ →
    Subgroup.centralizer ({t₁} : Set Th) ⊔ Subgroup.centralizer {t₂} = ⊤

variable (I : GMSInterfaces (phiB uBar) MGriess) (hex : OddExhaustive tGriess xGriess)
  (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
  (hCa : Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess)) = twoBabyOrder)
  (hTh : Finite TauCeti.SporadicName.Th.Group ∧
    Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
  (hThCard : Nat.card Th = CFSG.Open.monsterThOrder)
  (hHN : ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 5 ∧
    IsConj xGriess w ∧ w ∈ cent2 α β ∧ ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
      Nonempty (K ≃* HN))

include I in
theorem exists_conj_oddRep
    {k : Fin 3} {y₀ : MGriess}
    (hy₀ : y₀ ∈ oddNbr tGriess xGriess tGriess ∧ OddNbrType xGriess tGriess y₀ k) {x y : MGriess}
    (hx : IsConj tGriess x) (hy : y ∈ oddNbr tGriess xGriess x) (hk : OddNbrType xGriess x y k) :
    ∃ h : MGriess, h * tGriess * h⁻¹ = x ∧ h * y₀ * h⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  have hy' : g⁻¹ * y * g ∈ oddNbr tGriess xGriess tGriess := by
    have := oddNbr_conj g⁻¹ hy
    rwa [inv_inv, conj_base_eq hg] at this
  have hk' : OddNbrType xGriess tGriess (g⁻¹ * y * g) k := by
    have := oddNbrType_conj g⁻¹ hk
    rwa [inv_inv, conj_base_eq hg] at this
  obtain ⟨c, hc, hcy⟩ := s348_orbit I.sls I.tableV I.leech I.leechOddPair I.tableIV
    gmsF1Type_MGriess_uncond (IsConj.refl _) hy₀.1 hy' hy₀.2 hk'
  have hct : c * tGriess = tGriess * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  refine ⟨g * c, ?_, ?_⟩
  · rw [← hg]
    calc g * c * tGriess * (g * c)⁻¹ = g * (c * tGriess) * c⁻¹ * g⁻¹ := by group
      _ = g * (tGriess * c) * c⁻¹ * g⁻¹ := by rw [hct]
      _ = g * tGriess * g⁻¹ := by group
  · calc g * c * y₀ * (g * c)⁻¹ = g * (c * y₀ * c⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hcy]
      _ = y := by group

include I hex hcard hCa hTh hThCard hHN in
theorem oddTypeOrdersCF_MGriess :
    OddTypeOrdersCF tGriess xGriess := by
  obtain ⟨y, hy, -, h1, h2, -, -⟩ := oddShapes_MGriess I hex hcard hCa hTh hThCard hHN
  intro x z k hk0 hx hz hzk
  obtain ⟨h, hht, hhy⟩ := exists_conj_oddRep I (hy k) hx hz hzk
  have e : Nat.card ↥(Subgroup.centralizer ({x} : Set MGriess) ⊓ Subgroup.centralizer {z}) =
      Nat.card ↥(cent2 tGriess (y k)) := by
    rw [← natCard_cent2_conj h tGriess (y k), hht, hhy]
  rw [e]
  fin_cases k
  · exact absurd rfl hk0
  · obtain ⟨φ⟩ := h1
    show Nat.card ↥(cent2 tGriess (y 1)) = oddTypeStab 1
    rw [Nat.card_congr φ.toEquiv, hThCard]
    rfl
  · obtain ⟨φ⟩ := h2
    show Nat.card ↥(cent2 tGriess (y 2)) = oddTypeStab 2
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.HN.card_HN]
    rfl

include I hex hcard hCa hTh hThCard hHN in
theorem threeCGenerated_MGriess_of
    (hgen : ThInvolutionCentralizersGenerate) :
    ThreeCGenerated tGriess xGriess := by
  obtain ⟨y, hy, -, h1, -, -, -⟩ := oddShapes_MGriess I hex hcard hCa hTh hThCard hHN
  intro b x t₁ t₂ hb hx ht₁ ht₂ ho₁ ho₂ hne
  obtain ⟨h, hht, hhy⟩ := exists_conj_oddRep I (hy 1) hb hx.1 hx.2
  obtain ⟨φ⟩ := h1
  set T := Subgroup.centralizer ({b} : Set MGriess) ⊓ Subgroup.centralizer {x} with hTdef
  have hTe : T = (cent2 tGriess (y 1)).map (MulAut.conj h).toMonoidHom := by
    rw [hTdef, ← hht, ← hhy]
    exact cent2_conj h tGriess (y 1)
  let ι : ↥(cent2 tGriess (y 1)) ≃* ↥T :=
    ((cent2 tGriess (y 1)).equivMapOfInjective (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hTe.symm)
  let ψ : ↥T ≃* Th := ι.symm.trans φ
  have hψo : ∀ s : T, orderOf (s : MGriess) = 2 → orderOf (ψ s) = 2 := by
    intro s hs
    rw [MulEquiv.orderOf_eq, ← hs]
    exact (Subgroup.orderOf_coe s).symm
  have hne' : ψ ⟨t₁, ht₁⟩ ≠ ψ ⟨t₂, ht₂⟩ := fun e => hne (congrArg Subtype.val (ψ.injective e))
  exact @inf_centralizer_sup_eq_of_mulEquiv _ _ Th Units.instGroup T ψ ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    (hgen (ψ ⟨t₁, ht₁⟩) (ψ ⟨t₂, ht₂⟩) (hψo ⟨t₁, ht₁⟩ ho₁) (hψo ⟨t₂, ht₂⟩ ho₂) hne')

end MGriess

section Gmat

open CFSG.Monster.Griess CFSG.Monster.Generated

@[expose] def BasePointProp (P : ∀ {G : Type} [Group G], G → G → Prop)
    (S : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) : Prop :=
  ∀ (ht : CFSG.Monster.B.Short.tStar ∈ S) (hx : xmat ∈ S),
    P (⟨CFSG.Monster.B.Short.tStar, ht⟩ : S) ⟨xmat, hx⟩

theorem basePoint_Gmat_of_MGriess
    (P : ∀ {G : Type} [Group G], G → G → Prop)
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder) (h : P tGriess xGriess) :
    P tGmat xGmat := by
  have hP : BasePointProp P AutO := fun _ _ => h
  have hP' : BasePointProp P Gmat := (congrArg (BasePointProp P) (Gmat_eq_AutO hcard)).mpr hP
  exact hP' _ _

theorem oddTypeOrdersCF_Gmat
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (h : OddTypeOrdersCF tGriess xGriess) : OddTypeOrdersCF tGmat xGmat :=
  basePoint_Gmat_of_MGriess (fun a z₀ => OddTypeOrdersCF a z₀) hcard h

theorem threeCGenerated_Gmat
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (h : ThreeCGenerated tGriess xGriess) : ThreeCGenerated tGmat xGmat :=
  basePoint_Gmat_of_MGriess (fun a z₀ => ThreeCGenerated a z₀) hcard h

end Gmat

end CFSG.Monster.Existence
