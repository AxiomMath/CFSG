module

public import CFSG.Monster.B.Geometry.ChamberCoverAction
public import CFSG.Monster.B.TwoA.Amalgam.CoverCensus

public section

open scoped Pointwise

namespace CFSG.Monster.B.Geometry

namespace ChamberSystem

variable {I C : Type*} {X : ChamberSystem I C} {c₀ : C}

variable (X c₀) in
@[expose] noncomputable def liftResidueStab (H : Subgroup X.typeAut) (J : Set I)
    (a : X.Cover c₀) : Subgroup (X.LiftPair c₀) :=
  X.liftSubgroup c₀ H ⊓ MulAction.stabilizer (X.LiftPair c₀) ((X.universalCover c₀).residue J a)

variable (X) in
@[expose] def residueSetStab (H : Subgroup X.typeAut) (J : Set I) (x : C) : Subgroup X.typeAut :=
  H ⊓ MulAction.stabilizer X.typeAut (X.residue J x)

theorem mem_liftResidueStab {H : Subgroup X.typeAut} {J : Set I} {a : X.Cover c₀}
    {z : X.LiftPair c₀} :
    z ∈ X.liftResidueStab c₀ H J a ↔ z ∈ X.liftSubgroup c₀ H ∧
      (fun d : X.Cover c₀ => z • d) '' (X.universalCover c₀).residue J a =
        (X.universalCover c₀).residue J a := by
  rw [liftResidueStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Set.image_smul]

theorem mem_residueSetStab {H : Subgroup X.typeAut} {J : Set I} {x : C} {h : X.typeAut} :
    h ∈ X.residueSetStab H J x ↔ h ∈ H ∧ (h : Equiv.Perm C) '' X.residue J x = X.residue J x := by
  rw [residueSetStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, ← Set.image_smul]
  rfl

theorem bijOn_liftResidueStab (hX : X.Connected) (H : Subgroup X.typeAut) {J : Set I}
    {a : X.Cover c₀} (hR : IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) J a) :
    Set.BijOn (X.liftProj c₀) (X.liftResidueStab c₀ H J a)
      (X.residueSetStab H J (X.coverProj c₀ a)) := by
  have h := bijOn_liftProj_stabilizer hX H hR
  have e1 : (X.liftResidueStab c₀ H J a : Set (X.LiftPair c₀)) =
      {z | z ∈ X.liftSubgroup c₀ H ∧ (fun d : X.Cover c₀ => z • d) ''
        (X.universalCover c₀).residue J a = (X.universalCover c₀).residue J a} :=
    Set.ext fun _ => mem_liftResidueStab
  have e2 : (X.residueSetStab H J (X.coverProj c₀ a) : Set X.typeAut) =
      {h | h ∈ H ∧ (h : Equiv.Perm C) '' X.residue J (X.coverProj c₀ a) =
        X.residue J (X.coverProj c₀ a)} :=
    Set.ext fun _ => mem_residueSetStab
  rw [e1, e2]
  exact h

theorem liftResidueStab_mono (H : Subgroup X.typeAut) {J K : Set I} (hJK : J ⊆ K)
    (a : X.Cover c₀) : X.liftResidueStab c₀ H J a ≤ X.liftResidueStab c₀ H K a := by
  intro z hz
  rw [mem_liftResidueStab] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have hza : z • a ∈ (X.universalCover c₀).residue K a := by
    have : z • a ∈ (X.universalCover c₀).residue J a :=
      hz.2 ▸ ⟨a, self_mem_residue J a, rfl⟩
    exact (X.universalCover c₀).residue_mono hJK a this
  have h := image_residue_of_mem_typeAut (liftPerm_mem_typeAut (c₀ := c₀) z) K a
  have hf : (⇑(X.liftPerm c₀ z) : X.Cover c₀ → X.Cover c₀) = fun d => z • d :=
    funext fun d => liftPerm_apply z d
  rw [hf] at h
  rw [h]
  exact residue_eq_of_mem hza

theorem smul_eq_self_iff_of_mem_liftResidueStab {H : Subgroup X.typeAut} {J : Set I}
    {a : X.Cover c₀} (hinj : Set.InjOn (X.coverProj c₀) ((X.universalCover c₀).residue J a))
    {z : X.LiftPair c₀} (hz : z ∈ X.liftResidueStab c₀ H J a) :
    z • a = a ↔ (X.liftProj c₀ z : Equiv.Perm C) (X.coverProj c₀ a) = X.coverProj c₀ a := by
  refine ⟨fun h => by rw [liftProj_apply, ← coverProj_smul, h], fun h => ?_⟩
  have hza : z • a ∈ (X.universalCover c₀).residue J a :=
    (mem_liftResidueStab.mp hz).2 ▸ ⟨a, self_mem_residue J a, rfl⟩
  exact hinj hza (self_mem_residue J a) (by rw [coverProj_smul, ← liftProj_apply]; exact h)

theorem iInf_liftResidueStab_eq {ι : Type*} [Nonempty ι] (hX : X.Connected)
    (H : Subgroup X.typeAut) {J : ι → Set I} {K : Set I} (hKJ : ∀ i, K ⊆ J i) {a : X.Cover c₀}
    (hJ : ∀ i, Set.InjOn (X.coverProj c₀) ((X.universalCover c₀).residue (J i) a))
    (hnat : ⨅ i, X.residueSetStab H (J i) (X.coverProj c₀ a) =
      X.residueSetStab H K (X.coverProj c₀ a)) :
    ⨅ i, X.liftResidueStab c₀ H (J i) a = X.liftResidueStab c₀ H K a := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hK : IsResidueIso (X.universalCover c₀) X (X.coverProj c₀) K a :=
    isResidueIso_coverProj_of_injOn
      ((hJ i₀).mono ((X.universalCover c₀).residue_mono (hKJ i₀) a))
  refine le_antisymm (fun z hz => ?_) (le_iInf fun i => liftResidueStab_mono H (hKJ i) a)
  rw [Subgroup.mem_iInf] at hz
  have hpz : X.liftProj c₀ z ∈ X.residueSetStab H K (X.coverProj c₀ a) := by
    rw [← hnat, Subgroup.mem_iInf]
    exact fun i => (bijOn_liftResidueStab hX H (isResidueIso_coverProj_of_injOn (hJ i))).mapsTo
      (hz i)
  obtain ⟨z', hz', he⟩ := (bijOn_liftResidueStab hX H hK).surjOn hpz
  have hz'i₀ := liftResidueStab_mono H (hKJ i₀) a hz'
  have := (bijOn_liftResidueStab hX H (isResidueIso_coverProj_of_injOn (hJ i₀))).injOn hz'i₀
    (hz i₀) he
  rw [← this]
  exact hz'

end ChamberSystem

theorem exists_mulEquiv_quotient_of_bijOn {G G' E : Type*} [Group G] [Group G'] [Group E]
    (p : G →* G') (ρ : E →* G') {A : Subgroup G} {S : Subgroup E}
    (hA : Set.BijOn p A (S.map ρ)) :
    ∃ e : A ≃* S ⧸ ρ.ker.subgroupOf S,
      ∀ (z : A) (g : S), e z = (g : S ⧸ ρ.ker.subgroupOf S) ↔ p (z : G) = ρ (g : E) := by
  set ρS := ρ.comp S.subtype with hρS
  have hker : ρS.ker = ρ.ker.subgroupOf S := by
    ext g
    simp [hρS, Subgroup.mem_subgroupOf]
  have hrange : ∀ y, y ∈ ρS.range ↔ y ∈ S.map ρ := fun y => by
    simp [hρS, Subgroup.mem_map]
  let f : A →* ρS.range :=
    { toFun := fun z => ⟨p z, (hrange _).mpr (hA.mapsTo z.2)⟩
      map_one' := Subtype.ext (map_one p)
      map_mul' := fun z w => Subtype.ext (map_mul p (z : G) (w : G)) }
  have hf : Function.Bijective f := by
    refine ⟨fun z w hzw => Subtype.ext (hA.injOn z.2 w.2 (congrArg Subtype.val hzw)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := hA.surjOn ((hrange y).mp hy)
    exact ⟨⟨z, hz⟩, rfl⟩
  let e₁ : A ≃* ρS.range := MulEquiv.ofBijective f hf
  let e₂ : S ⧸ ρ.ker.subgroupOf S ≃* ρS.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρS)
  refine ⟨e₁.trans e₂.symm, fun z g => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    exact h1
  · intro h
    exact Subtype.ext h

theorem exists_mulEquiv_quotient_of_bijOn' {G G' E : Type*} [Group G] [Group G'] [Group E]
    (p : G →* G') (ρ : E →* G') {A : Subgroup G} {S : Subgroup E} (N : Subgroup S) [N.Normal]
    (hN : ρ.ker.subgroupOf S = N) (hA : Set.BijOn p A (S.map ρ)) :
    ∃ e : A ≃* S ⧸ N, ∀ (z : A) (g : S), e z = (g : S ⧸ N) ↔ p (z : G) = ρ (g : E) := by
  subst hN
  exact exists_mulEquiv_quotient_of_bijOn p ρ hA

theorem exists_quotient_hom_of_bijOn {G G' E P M : Type*} [Group G] [Group G'] [Group E]
    [Group P] [Group M] (p : G →* G') (ρ : E →* G') (ι : P →* E) {A : Subgroup G}
    {S : Subgroup E} (hS : ∀ x, x ∈ S ↔ ∃ g, ι g = x) (hA : Set.BijOn p A (S.map ρ))
    (φ : P →* M) (hφ : Function.Surjective φ) (hker : ∀ g : P, ρ (ι g) = 1 → φ g = 1) :
    ∃ θ : A →* M, Function.Surjective θ ∧
      (∀ (z : A) (g : P), p (z : G) = ρ (ι g) → θ z = φ g) ∧
      ∀ z : A, θ z = 1 ↔ ∃ g : P, φ g = 1 ∧ p (z : G) = ρ (ι g) := by
  set ρ' : P →* G' := ρ.comp ι with hρ'
  have hR : ∀ y, y ∈ ρ'.range ↔ y ∈ S.map ρ := fun y => by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ι g, (hS _).mpr ⟨g, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g, rfl⟩ := (hS x).mp hx
      exact ⟨g, rfl⟩
  let f : A →* ρ'.range :=
    { toFun := fun z => ⟨p z, (hR _).mpr (hA.mapsTo z.2)⟩
      map_one' := Subtype.ext (map_one p)
      map_mul' := fun z w => Subtype.ext (map_mul p (z : G) (w : G)) }
  have hf : Function.Bijective f := by
    refine ⟨fun z w hzw => Subtype.ext (hA.injOn z.2 w.2 (congrArg Subtype.val hzw)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := hA.surjOn ((hR y).mp hy)
    exact ⟨⟨z, hz⟩, rfl⟩
  let e₁ : A ≃* ρ'.range := MulEquiv.ofBijective f hf
  let e₂ : P ⧸ ρ'.ker ≃* ρ'.range := QuotientGroup.quotientKerEquivRange ρ'
  have hk : ρ'.ker ≤ φ.ker := fun g hg => hker g hg
  let θ : A →* M := (QuotientGroup.lift _ φ hk).comp (e₂.symm.toMonoidHom.comp e₁.toMonoidHom)
  have hkey : ∀ (z : A) (g : P), p (z : G) = ρ (ι g) → e₂.symm (e₁ z) = (g : P ⧸ ρ'.ker) := by
    intro z g h
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext h
  have hval : ∀ (z : A) (g : P), p (z : G) = ρ (ι g) → θ z = φ g := by
    intro z g h
    show QuotientGroup.lift _ φ hk (e₂.symm (e₁ z)) = φ g
    rw [hkey z g h]
    exact QuotientGroup.lift_mk _ hk g
  have hpre : ∀ z : A, ∃ g : P, p (z : G) = ρ (ι g) := by
    intro z
    obtain ⟨g, hg⟩ := (hR _).mpr (hA.mapsTo z.2)
    exact ⟨g, hg.symm⟩
  refine ⟨θ, fun m => ?_, hval, fun z => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := hφ m
    obtain ⟨z, hz, hze⟩ := hA.surjOn ⟨ι g, (hS _).mpr ⟨g, rfl⟩, rfl⟩
    exact ⟨⟨z, hz⟩, hval ⟨z, hz⟩ g hze⟩
  · obtain ⟨g, hg⟩ := hpre z
    exact ⟨g, (hval z g hg).symm.trans h, hg⟩
  · rintro ⟨g, hg, hpg⟩
    rw [hval z g hpg, hg]

end CFSG.Monster.B.Geometry
