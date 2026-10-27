module

public import CFSG.RankThree.PartOne.KE6.E6LEmb

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE

abbrev GL27 (K : Type) [Field K] : Type := (Module.End K (Fin e6Data.d →₀ K))ˣ

section Preserving

variable {τ : Tag} {K : Type} [Field K]

theorem m27Emb_comp_injective [M27Ok τ] {f f' : Module.End K (Fin e6Data.d →₀ K)}
    (h : m27Emb τ K ∘ₗ f = m27Emb τ K ∘ₗ f') : f = f' :=
  LinearMap.ext fun v => m27Emb_injective (LinearMap.congr_fun h v)

theorem one_comp_m27Emb [M27Ok τ] :
    ((1 : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ ((1 : GL27 K) : Module.End K (Fin e6Data.d →₀ K)) := by
  rw [Units.val_one, Units.val_one, Module.End.one_eq_id, Module.End.one_eq_id,
    LinearMap.id_comp, LinearMap.comp_id]

theorem mul_comp_m27Emb [M27Ok τ] {g h : ModGL τ K} {g' h' : GL27 K}
    (hg : (g : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (g' : Module.End K (Fin e6Data.d →₀ K)))
    (hh : (h : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (h' : Module.End K (Fin e6Data.d →₀ K))) :
    ((g * h : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ ((g' * h' : GL27 K) : Module.End K (Fin e6Data.d →₀ K)) := by
  rw [Units.val_mul, Units.val_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, hh, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]

theorem inv_comp_m27Emb [M27Ok τ] {g : ModGL τ K} {g' : GL27 K}
    (hg : (g : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (g' : Module.End K (Fin e6Data.d →₀ K))) :
    ((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ ((g'⁻¹ : GL27 K) : Module.End K (Fin e6Data.d →₀ K)) := by
  have e : ∀ v, (g : Module.End K (RootModule τ K))
      (((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (m27Emb τ K v)) =
      (g : Module.End K (RootModule τ K)) (m27Emb τ K
        (((g'⁻¹ : GL27 K) : Module.End K (Fin e6Data.d →₀ K)) v)) := by
    intro v
    have h1 := LinearMap.congr_fun hg (((g'⁻¹ : GL27 K) : Module.End K _) v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [h1, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply]
  refine LinearMap.ext fun v => ?_
  have hinj : Function.Injective (g : Module.End K (RootModule τ K)) := fun x y hxy => by
    have := congrArg ((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) hxy
    rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply] at this
  exact hinj (e v)

variable (τ K) in
@[expose] def m27Preserving [M27Ok τ] : Subgroup (ModGL τ K) where
  carrier := {g | ∃ g' : GL27 K,
    (g : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (g' : Module.End K (Fin e6Data.d →₀ K))}
  mul_mem' := by
    rintro g h ⟨g', hg⟩ ⟨h', hh⟩
    exact ⟨g' * h', mul_comp_m27Emb hg hh⟩
  one_mem' := ⟨1, one_comp_m27Emb⟩
  inv_mem' := by
    rintro g ⟨g', hg⟩
    exact ⟨g'⁻¹, inv_comp_m27Emb hg⟩

theorem m27Preserving_partner_unique [M27Ok τ] {g : ModGL τ K} {g' g'' : GL27 K}
    (h' : (g : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (g' : Module.End K (Fin e6Data.d →₀ K)))
    (h'' : (g : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (g'' : Module.End K (Fin e6Data.d →₀ K))) : g' = g'' :=
  Units.ext (m27Emb_comp_injective (h'.symm.trans h''))

variable (τ K) in
@[expose] def m27PreservingRes [M27Ok τ] : m27Preserving τ K →* GL27 K where
  toFun g := g.2.choose
  map_one' := m27Preserving_partner_unique (1 : m27Preserving τ K).2.choose_spec one_comp_m27Emb
  map_mul' g h := m27Preserving_partner_unique (g * h).2.choose_spec
    (mul_comp_m27Emb g.2.choose_spec h.2.choose_spec)

theorem m27PreservingRes_spec [M27Ok τ] (g : m27Preserving τ K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (m27PreservingRes τ K g : Module.End K (Fin e6Data.d →₀ K)) :=
  g.2.choose_spec

theorem m27PreservingRes_eq [M27Ok τ] {g : m27Preserving τ K} {g' : GL27 K}
    (h : ((g : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ m27Emb τ K =
      m27Emb τ K ∘ₗ (g' : Module.End K (Fin e6Data.d →₀ K))) : m27PreservingRes τ K g = g' :=
  m27Preserving_partner_unique (m27PreservingRes_spec g) h

end Preserving

section Units

variable {τ : Tag} [E6Sub τ] {K : Type} [Field K]

theorem xUnit_mem_m27Preserving [M27Ok τ] (j : Fin Tag.E6.rank) (c : K) :
    xUnit τ K (e6Idx j) c ∈ m27Preserving τ K := by
  refine ⟨e6Data_valid.xu K (Pi.single j 1) c, ?_⟩
  rw [e6Data_valid.xu_val]
  exact xOp_comp_m27Emb j c

theorem yUnit_mem_m27Preserving [M27Ok τ] (j : Fin Tag.E6.rank) (c : K) :
    yUnit τ K (e6Idx j) c ∈ m27Preserving τ K := by
  refine ⟨e6Data_valid.xu K (-Pi.single j 1) c, ?_⟩
  rw [e6Data_valid.xu_val]
  exact yOp_comp_m27Emb j c

theorem subsystemGroup_le_m27Preserving [M27Ok τ] {A : Set (Fin τ.rank)}
    (hA : ∀ i ∈ A, i.val < Tag.E6.rank) : subsystemGroup τ K A ≤ m27Preserving τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (hA i hi)
    exact xUnit_mem_m27Preserving k c
  · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (hA i hi)
    exact yUnit_mem_m27Preserving k c

variable (K) in
@[expose] def m27Res [M27Ok τ] {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank) :
    subsystemGroup τ K A →* GL27 K :=
  (m27PreservingRes τ K).comp (Subgroup.inclusion (subsystemGroup_le_m27Preserving hA))

theorem m27Res_apply [M27Ok τ] {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    (g : subsystemGroup τ K A) (v : Fin e6Data.d →₀ K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (m27Emb τ K v) =
      m27Emb τ K ((m27Res K hA g : Module.End K (Fin e6Data.d →₀ K)) v) :=
  LinearMap.congr_fun (m27PreservingRes_spec (Subgroup.inclusion
    (subsystemGroup_le_m27Preserving hA) g)) v

theorem m27Res_eq [M27Ok τ] {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    {g : subsystemGroup τ K A} {g' : GL27 K}
    (h : ∀ v, ((g : ModGL τ K) : Module.End K (RootModule τ K)) (m27Emb τ K v) =
      m27Emb τ K ((g' : Module.End K (Fin e6Data.d →₀ K)) v)) : m27Res K hA g = g' :=
  m27PreservingRes_eq (LinearMap.ext h)

theorem m27Res_xUnit [M27Ok τ] {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    (j : Fin Tag.E6.rank) (hj : e6Idx (τ := τ) j ∈ A) (c : K) :
    m27Res K hA ⟨xUnit τ K (e6Idx j) c, xUnit_mem_subsystemGroup hj c⟩ =
      e6Data_valid.xu K (Pi.single j 1) c := by
  refine m27Res_eq hA fun v => ?_
  rw [e6Data_valid.xu_val]
  exact LinearMap.congr_fun (xOp_comp_m27Emb j c) v

theorem m27Res_yUnit [M27Ok τ] {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    (j : Fin Tag.E6.rank) (hj : e6Idx (τ := τ) j ∈ A) (c : K) :
    m27Res K hA ⟨yUnit τ K (e6Idx j) c, yUnit_mem_subsystemGroup hj c⟩ =
      e6Data_valid.xu K (-Pi.single j 1) c := by
  refine m27Res_eq hA fun v => ?_
  rw [e6Data_valid.xu_val]
  exact LinearMap.congr_fun (yOp_comp_m27Emb j c) v

end Units

end CFSG.RankThree.PartOne.KE6
