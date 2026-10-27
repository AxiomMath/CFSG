module

public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin

namespace GoldAmalgam

variable {A C B A' C' B' : Type*} [Group A] [Group C] [Group B] [Group A'] [Group C'] [Group B']

structure Iso (X : GoldAmalgam A C B) (Y : GoldAmalgam A' C' B') where
  eA : A ≃* A'
  eC : C ≃* C'
  eB : B ≃* B'
  comm_toA : ∀ c, eA (X.toA c) = Y.toA (eC c)
  comm_toB : ∀ c, eB (X.toB c) = Y.toB (eC c)

@[expose] def IsIso (X : GoldAmalgam A C B) (Y : GoldAmalgam A' C' B') : Prop :=
  Nonempty (X.Iso Y)

theorem IsIso.refl (X : GoldAmalgam A C B) : X.IsIso X :=
  ⟨⟨MulEquiv.refl _, MulEquiv.refl _, MulEquiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

theorem IsIso.symm {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} (h : X.IsIso Y) :
    Y.IsIso X := by
  obtain ⟨f⟩ := h
  refine ⟨⟨f.eA.symm, f.eC.symm, f.eB.symm, fun c => ?_, fun c => ?_⟩⟩
  · apply f.eA.injective
    rw [MulEquiv.apply_symm_apply, f.comm_toA, MulEquiv.apply_symm_apply]
  · apply f.eB.injective
    rw [MulEquiv.apply_symm_apply, f.comm_toB, MulEquiv.apply_symm_apply]

theorem IsIso.trans {A'' C'' B'' : Type*} [Group A''] [Group C''] [Group B'']
    {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} {Z : GoldAmalgam A'' C'' B''}
    (h : X.IsIso Y) (h' : Y.IsIso Z) : X.IsIso Z := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := h'
  refine ⟨⟨f.eA.trans g.eA, f.eC.trans g.eC, f.eB.trans g.eB, fun c => ?_, fun c => ?_⟩⟩
  · simp [f.comm_toA, g.comm_toA]
  · simp [f.comm_toB, g.comm_toB]

theorem Iso.map_comap_toA {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} (f : X.Iso Y)
    (K : Subgroup C') :
    (K.comap f.eC.toMonoidHom).map X.toA = (K.map Y.toA).comap f.eA.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨f.eC c, hc, (f.comm_toA c).symm⟩
  · rintro ⟨k, hk, hkx⟩
    refine ⟨f.eC.symm k, by simpa using hk, ?_⟩
    apply f.eA.injective
    rw [f.comm_toA, MulEquiv.apply_symm_apply]
    exact hkx

theorem Iso.map_comap_toB {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} (f : X.Iso Y)
    (K : Subgroup C') :
    (K.comap f.eC.toMonoidHom).map X.toB = (K.map Y.toB).comap f.eB.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨f.eC c, hc, (f.comm_toB c).symm⟩
  · rintro ⟨k, hk, hkx⟩
    refine ⟨f.eC.symm k, by simpa using hk, ?_⟩
    apply f.eB.injective
    rw [f.comm_toB, MulEquiv.apply_symm_apply]
    exact hkx

theorem IsIso.isFaithful {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} (h : X.IsIso Y)
    (hf : X.IsFaithful) : Y.IsFaithful := by
  obtain ⟨f⟩ := h
  intro K hKA hKB
  have hA : ((K.comap f.eC.toMonoidHom).map X.toA).Normal := by
    rw [f.map_comap_toA]
    exact Subgroup.Normal.comap hKA _
  have hB : ((K.comap f.eC.toMonoidHom).map X.toB).Normal := by
    rw [f.map_comap_toB]
    exact Subgroup.Normal.comap hKB _
  have h0 := hf _ hA hB
  refine (Subgroup.eq_bot_iff_forall K).mpr fun k hk => ?_
  have hmem : f.eC.symm k ∈ K.comap f.eC.toMonoidHom := by simpa using hk
  rw [h0] at hmem
  have : f.eC.symm k = 1 := by simpa using hmem
  simpa using congrArg f.eC this

@[expose] def inducedAut (i : C →* A) : Subgroup (MulAut C) where
  carrier := {α | ∃ f : MulAut A, ∀ c, f (i c) = i (α c)}
  one_mem' := ⟨1, fun c => rfl⟩
  mul_mem' := by
    rintro α β ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f * g, fun c => by rw [MulAut.mul_apply, hg c, hf (β c)]; rfl⟩
  inv_mem' := by
    rintro α ⟨f, hf⟩
    refine ⟨f⁻¹, fun c => ?_⟩
    apply f.injective
    rw [MulAut.apply_inv_self, hf (α⁻¹ c), MulAut.apply_inv_self]

theorem mem_inducedAut_iff {i : C →* A} {α : MulAut C} :
    α ∈ inducedAut i ↔ ∃ f : MulAut A, ∀ c, f (i c) = i (α c) := Iff.rfl

theorem exists_mem_inducedAut_of_map_range_eq {i : C →* A} (hi : Function.Injective i)
    (f : MulAut A) (hf : i.range.map f.toMonoidHom = i.range) :
    ∃ α ∈ inducedAut i, ∀ c, f (i c) = i (α c) := by
  let e : C ≃* i.range := MonoidHom.ofInjective hi
  let φ : i.range ≃* i.range :=
    (MulEquiv.subgroupMap f i.range).trans (MulEquiv.subgroupCongr hf)
  let α : MulAut C := (e.trans φ).trans e.symm
  have hα : ∀ c, f (i c) = i (α c) := by
    intro c
    have h1 : e (α c) = φ (e c) := by simp [α]
    have h2 : (e (α c) : A) = i (α c) := rfl
    have h3 : (φ (e c) : A) = f (i c) := rfl
    rw [← h2, h1, h3]
  exact ⟨α, ⟨f, hα⟩, hα⟩

theorem map_range_eq_of_forall_eq {i : C →* A} {α : MulAut C} {f : MulAut A}
    (hf : ∀ c, f (i c) = i (α c)) : i.range.map f.toMonoidHom = i.range := by
  ext a
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨α c, (hf c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨i (α.symm c), ⟨α.symm c, rfl⟩, ?_⟩
    show f (i (α.symm c)) = i c
    rw [hf]
    simp

@[expose] def glue (iA : C →* A) (iB : C →* B) (hA : Function.Injective iA)
    (hB : Function.Injective iB) (θ : MulAut C) : GoldAmalgam A C B :=
  ⟨iA, iB.comp θ.toMonoidHom, hA, hB.comp θ.injective⟩

theorem isIso_glue_iff {iA : C →* A} {iB : C →* B} (hA : Function.Injective iA)
    (hB : Function.Injective iB) (θ θ' : MulAut C) :
    (glue iA iB hA hB θ).IsIso (glue iA iB hA hB θ') ↔
      θ' ∈ DoubleCoset.doubleCoset θ (inducedAut iB : Set (MulAut C))
        (inducedAut iA : Set (MulAut C)) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨f⟩
    have hcA : ∀ c, f.eA (iA c) = iA (f.eC c) := f.comm_toA
    have hcB : ∀ c, f.eB (iB (θ c)) = iB (θ' (f.eC c)) := f.comm_toB
    have hα : f.eC ∈ inducedAut iA := ⟨f.eA, hcA⟩
    refine ⟨θ' * f.eC * θ⁻¹, ⟨f.eB, fun x => ?_⟩, f.eC⁻¹, (inducedAut iA).inv_mem hα, ?_⟩
    · have := hcB (θ⁻¹ x)
      rw [MulAut.apply_inv_self] at this
      rw [this]
      rfl
    · ext c
      simp
  · rintro ⟨β, ⟨fB, hfB⟩, α, hα, rfl⟩
    obtain ⟨fA, hfA⟩ := (inducedAut iA).inv_mem hα
    refine ⟨⟨fA, α⁻¹, fB, hfA, fun c => ?_⟩⟩
    show fB (iB (θ c)) = iB ((β * θ * α) (α⁻¹ c))
    rw [hfB]
    simp

end GoldAmalgam

end CFSG.Quasithin
