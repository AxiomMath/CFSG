module

public import CFSG.Monster.B.TwoA.Amalgam.StdIsoBuilding

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4

@[expose] def nativeAct :
    Eam →* Equiv.Perm Chamber where
  toFun e := chamberMulPerm e⁻¹
  map_one' := by
    ext z
    simp [chamberMulPerm_apply, chamberMul_one]
  map_mul' e h := by
    ext z
    simp only [chamberMulPerm_apply, Equiv.Perm.coe_mul, Function.comp_apply, mul_inv_rev,
      chamberMul_mul]

theorem nativeAct_apply
    (e : Eam) (z : Chamber) : nativeAct e z = chamberMul z e⁻¹ := rfl

theorem ker_nativeAct :
    nativeAct.ker = Subgroup.zpowers cE' := by
  obtain ⟨-, -, hker, -⟩ := short_F4_chamber_action_central_kernel
  ext e
  rw [MonoidHom.mem_ker]
  have h1 : nativeAct e = 1 ↔ ∀ z, chamberMul z e⁻¹ = z := by
    rw [Equiv.ext_iff]
    rfl
  rw [h1, hker]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, zpow_neg, show ((cE' : Eam) : Dfull) = Sp8.cQ from rfl, hk,
      Subgroup.coe_inv, inv_inv]
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    rw [← zpow_neg, Subgroup.coe_zpow]
    rfl

theorem nativeAct_dist
    {δ : Chamber → Chamber → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
      chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i)
    (e : Eam) (x y : Chamber) : δ (nativeAct e x) (nativeAct e y) = δ x y :=
  dist_typeAut hδ (typeAut_le_of_adj hδ hadj (chamberMulPerm_mem_typeAut_F4 e⁻¹)) x y

theorem dist_eq_of_simple_iff
    {C : Type*} {δ δ' : C → C → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hδ' : IsWeylDistanceBuilding (coxeterSystem .F4) δ')
    (h : ∀ i x y, δ x y = (coxeterSystem .F4).simple i ↔ δ' x y = (coxeterSystem .F4).simple i)
    (x y : C) : δ' x y = δ x y :=
  dist_map_eq hδ hδ' (J := Set.univ) (a := x) (f := id) (fun y _ z _ i e => (h i y z).mp e)
    (self_mem_residue _ x) (by rw [residue_univ hδ]; trivial)

theorem lift_nativeAct_injective :
    Function.Injective (QuotientGroup.lift (Subgroup.zpowers cE') nativeAct ker_nativeAct.ge) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with | H e => ?_
  rw [QuotientGroup.lift_mk, ← MonoidHom.mem_ker, ker_nativeAct] at hq
  exact (QuotientGroup.eq_one_iff e).mpr hq

theorem permCongr_mem_autA
    {δ : Chamber → Chamber → WeylGroup .F4}
    {e₀ : Chamber ≃ C2E6Std.stdChamber} (he₀ : ∀ x y, stdDistanceF4 (e₀ x) (e₀ y) = δ x y)
    {p : Equiv.Perm Chamber} (hp : ∀ x y, δ (p x) (p y) = δ x y) :
    Equiv.permCongrHom e₀ p ∈ autA := by
  rw [← mem_typeAut_F4_iff]
  refine (mem_typeAut (coxeterSystem .F4) stdDistanceF4).mpr fun x y i => ?_
  obtain ⟨u, rfl⟩ := e₀.surjective x
  obtain ⟨v, rfl⟩ := e₀.surjective y
  change stdDistanceF4 (e₀ (p (e₀.symm (e₀ u)))) (e₀ (p (e₀.symm (e₀ v)))) = _ ↔ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, he₀, he₀, hp]
  exact Iff.rfl

theorem map_permCongr_le_autA
    {δ : Chamber → Chamber → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
      chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i)
    {e₀ : Chamber ≃ C2E6Std.stdChamber} (he₀ : ∀ x y, stdDistanceF4 (e₀ x) (e₀ y) = δ x y) :
    (QuotientGroup.lift (Subgroup.zpowers cE') nativeAct ker_nativeAct.ge).range.map
      (Equiv.permCongrHom e₀).toMonoidHom ≤ autA := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  induction q using QuotientGroup.induction_on with | H e => ?_
  exact permCongr_mem_autA he₀ (nativeAct_dist hδ hadj e)

theorem card_map_permCongr {Q X Y : Type*} [Group Q] {ρ : Q →* Equiv.Perm X}
    (hρ : Function.Injective ρ) (e : X ≃ Y) :
    Nat.card (ρ.range.map (Equiv.permCongrHom e).toMonoidHom) = Nat.card Q :=
  (Nat.card_congr (Subgroup.equivMapOfInjective ρ.range _
    (Equiv.permCongrHom e).injective).toEquiv).symm.trans
      (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm

theorem exists_mulEquiv_of_conj_map {E Γ P Q : Type*} [Group E] [Group Γ] [MulAction Γ Q]
    {N : Subgroup E} [N.Normal] {act : E →* Equiv.Perm P} (hker : act.ker = N) (e₀ : P ≃ Q)
    {ψ : Γ →* Equiv.Perm Q} (hψ : Function.Injective ψ) (hψa : ∀ γ x, ψ γ x = γ • x)
    {a : Equiv.Perm Q}
    (hmap : ((QuotientGroup.lift N act hker.ge).range.map (Equiv.permCongrHom e₀).toMonoidHom).map
      (MulAut.conj a).toMonoidHom = ψ.range) :
    ∃ θ : E ⧸ N ≃* Γ, ∀ (z : P) (e : E), a (e₀ (act e z)) = θ (QuotientGroup.mk e) • a (e₀ z) := by
  set ρ : E ⧸ N →* Equiv.Perm P := QuotientGroup.lift N act hker.ge with hρdef
  have hρmk : ∀ e : E, ρ (QuotientGroup.mk e) = act e := fun _ => rfl
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with | H e => ?_
    rw [hρmk, ← MonoidHom.mem_ker, hker] at hq
    exact (QuotientGroup.eq_one_iff e).mpr hq
  set σ := Equiv.permCongrHom e₀
  set K : Subgroup (Equiv.Perm Q) := ρ.range.map σ.toMonoidHom
  have hσ : ∀ (p : Equiv.Perm P) (z : P), σ p (e₀ z) = e₀ (p z) := fun p z => by
    change e₀.permCongr p (e₀ z) = e₀ (p z)
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  set θ : E ⧸ N ≃* Γ :=
    (MonoidHom.ofInjective hρ).trans
      ((Subgroup.equivMapOfInjective ρ.range σ.toMonoidHom σ.injective).trans
        ((Subgroup.equivMapOfInjective K (MulAut.conj a).toMonoidHom
          (MulAut.conj a).injective).trans ((MulEquiv.subgroupCongr hmap).trans
            (MonoidHom.ofInjective hψ).symm)))
  have hθ : ∀ q, ψ (θ q) = a * σ (ρ q) * a⁻¹ := by
    intro q
    set r := (MulEquiv.subgroupCongr hmap) ((Subgroup.equivMapOfInjective K
      (MulAut.conj a).toMonoidHom (MulAut.conj a).injective) ((Subgroup.equivMapOfInjective
        ρ.range σ.toMonoidHom σ.injective) (MonoidHom.ofInjective hρ q))) with hr
    have h1 : θ q = (MonoidHom.ofInjective hψ).symm r := rfl
    have h2 := congrArg Subtype.val ((MonoidHom.ofInjective hψ).apply_symm_apply r)
    rw [MonoidHom.ofInjective_apply] at h2
    rw [h1, h2, hr, MulEquiv.subgroupCongr_apply]
    rfl
  refine ⟨θ, fun z e => ?_⟩
  rw [← hψa, hθ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply, hρmk, hσ]

theorem short_F4_standard_twisted_E6_quotient :
    ∃ (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (f : Chamber ≃ C2E6Std.stdChamber),
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
        stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i) ∧
      (∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
        (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
          chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
        ∀ x y, stdDistanceF4 (f x) (f y) = δ x y) ∧
      ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z := by
  obtain ⟨-, -, -, -, ⟨δ, hδ, hadj, -⟩, -, ⟨hH⟩, hcardH, -⟩ :=
    short_F4_deck_triviality_and_native_order
  obtain ⟨⟨F₀, hF₀, -⟩, -⟩ := native_standard_F4_building_isomorphism.2 δ hδ hadj
  have hδS := isWeylDistanceBuilding_stdDistanceF4
  let e₀ : Chamber ≃ C2E6Std.stdChamber := Equiv.ofBijective F₀ (Set.bijOn_univ.mp hF₀.1)
  have he₀ : ∀ x y, stdDistanceF4 (e₀ x) (e₀ y) = δ x y := IsTypeIso.dist_eq_univ hδ hδS hF₀
  obtain ⟨-, -, -, -, -, -, -, -, -, hconj⟩ := standard_F4_building_action_conjugacy
  obtain ⟨⟨a, haA, hmap⟩, -⟩ := hconj _ (map_permCongr_le_autA hδ hadj he₀)
    ((card_map_permCongr lift_nativeAct_injective e₀).trans
      ((Nat.card_congr hH.toEquiv).trans hcardH))
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_of_conj_map ker_nativeAct e₀ starPerm_injective
    starPerm_apply hmap
  have ha : ∀ u v, stdDistanceF4 (a u) (a v) = stdDistanceF4 u v :=
    dist_typeAut hδS ((mem_typeAut_F4_iff _).mpr haA)
  refine ⟨θ, e₀.trans a, fun i x y => ?_, fun δ' hδ' hadj' x y => ?_, fun z e => hθ z e⟩
  · change chamberCS.adj i x y ↔ stdDistanceF4 (a (e₀ x)) (a (e₀ y)) = 1 ∨
      stdDistanceF4 (a (e₀ x)) (a (e₀ y)) = (coxeterSystem .F4).simple i
    rw [ha, he₀, hadj]
    exact Iff.rfl
  · change stdDistanceF4 (a (e₀ x)) (a (e₀ y)) = δ' x y
    rw [ha, he₀]
    refine (dist_eq_of_simple_iff hδ hδ' (fun i u v => ?_) x y).symm
    rw [native_eq_simple_iff hδ hadj, native_eq_simple_iff hδ' hadj']

end CFSG.Monster.B.TwoA.Amalgam
