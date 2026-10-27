module

public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def hGens (H : Subgroup (GLV V)) : Set (Module.End (ZMod 2) V) :=
  {f | ∃ h ∈ H, f = (h : V →ₗ[ZMod 2] V)}

@[expose] def hAlg (H : Subgroup (GLV V)) : Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  Algebra.adjoin (ZMod 2) (hGens H)

variable {H : Subgroup (GLV V)}

theorem hAlg_mem_of_mem {h : GLV V} (hh : h ∈ H) : (h : V →ₗ[ZMod 2] V) ∈ hAlg H :=
  Algebra.subset_adjoin ⟨h, hh, rfl⟩

@[expose] def HRing (H : Subgroup (GLV V)) : Type := ↥(hAlg H)

noncomputable instance : Ring (HRing H) := inferInstanceAs (Ring ↥(hAlg H))

noncomputable instance : Algebra (ZMod 2) (HRing H) := inferInstanceAs (Algebra (ZMod 2) ↥(hAlg H))

noncomputable instance : Module (HRing H) V := inferInstanceAs (Module ↥(hAlg H) V)

instance : IsScalarTower (ZMod 2) (HRing H) V :=
  inferInstanceAs (IsScalarTower (ZMod 2) ↥(hAlg H) V)

@[expose] def HRing.val (a : HRing H) : Module.End (ZMod 2) V := (a : ↥(hAlg H)).1

theorem HRing.val_mem (a : HRing H) : a.val ∈ hAlg H := (a : ↥(hAlg H)).2

@[simp] theorem HRing.smul_def (a : HRing H) (v : V) : a • v = a.val v := rfl

@[expose] def genElem (H : Subgroup (GLV V)) (h : H) : HRing H :=
  (⟨(h : GLV V), hAlg_mem_of_mem h.2⟩ : ↥(hAlg H))

@[simp] theorem genElem_smul (h : H) (v : V) : genElem H h • v = (h : GLV V) v := rfl

theorem stable_of_invariant {J : Submodule (ZMod 2) V} (hJ : Invariant H J)
    {a : Module.End (ZMod 2) V} (ha : a ∈ hAlg H) {v : V} (hv : v ∈ J) : a v ∈ J := by
  induction ha using Algebra.adjoin_induction generalizing v with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact hJ h hh v hv
  | algebraMap c =>
    rw [Module.algebraMap_end_apply]
    exact J.smul_mem c hv
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply]
    exact J.add_mem (hx hv) (hy hv)
  | mul x y _ _ hx hy =>
    rw [Module.End.mul_apply]
    exact hx (hy hv)

@[expose] def ofInvariant (J : Submodule (ZMod 2) V) (hJ : Invariant H J) :
    Submodule (HRing H) V where
  carrier := J
  add_mem' := J.add_mem
  zero_mem' := J.zero_mem
  smul_mem' a _ hv := stable_of_invariant hJ a.val_mem hv

theorem restrictScalars_ofInvariant (J : Submodule (ZMod 2) V) (hJ : Invariant H J) :
    (ofInvariant J hJ).restrictScalars (ZMod 2) = J := rfl

theorem invariant_restrictScalars (J' : Submodule (HRing H) V) :
    Invariant H (J'.restrictScalars (ZMod 2)) := fun h hh _ hv =>
  J'.smul_mem (genElem H ⟨h, hh⟩) hv

theorem map_smul_of_gens {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (HRing H) M] [Module (HRing H) N] [Module (ZMod 2) M] [Module (ZMod 2) N]
    [IsScalarTower (ZMod 2) (HRing H) M] [IsScalarTower (ZMod 2) (HRing H) N]
    (f : M →ₗ[ZMod 2] N) (hf : ∀ (h : H) (x : M), f (genElem H h • x) = genElem H h • f x)
    (a : HRing H) (x : M) : f (a • x) = a • f x := by
  have hadd : ∀ a b : HRing H, (∀ x, f (a • x) = a • f x) → (∀ x, f (b • x) = b • f x) →
      ∀ x, f ((a + b) • x) = (a + b) • f x := fun a b ha hb x => by
    rw [add_smul, add_smul, map_add, ha x, hb x]
  have hmul : ∀ a b : HRing H, (∀ x, f (a • x) = a • f x) → (∀ x, f (b • x) = b • f x) →
      ∀ x, f ((a * b) • x) = (a * b) • f x := fun a b ha hb x => by
    rw [mul_smul, mul_smul, ha (b • x), hb x]
  have halg : ∀ (c : ZMod 2) (x : M),
      f (algebraMap (ZMod 2) (HRing H) c • x) = algebraMap (ZMod 2) (HRing H) c • f x :=
    fun c x => by rw [algebraMap_smul, algebraMap_smul, map_smul]
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction generalizing x with
  | mem y hy =>
    obtain ⟨h, hh, rfl⟩ := hy
    exact hf ⟨h, hh⟩ x
  | algebraMap c => exact halg c x
  | add y z hy hz hy' hz' => exact hadd ⟨y, hy⟩ ⟨z, hz⟩ hy' hz' x
  | mul y z hy hz hy' hz' => exact hmul ⟨y, hy⟩ ⟨z, hz⟩ hy' hz' x

theorem isIrr_iff_isAtom {J' : Submodule (HRing H) V} :
    IsIrr H (J'.restrictScalars (ZMod 2)) ↔ IsAtom J' := by
  constructor
  · intro hJ
    refine ⟨?_, fun b hb => ?_⟩
    · rintro rfl
      exact hJ.ne_bot (by simp)
    · have hle : b.restrictScalars (ZMod 2) ≤ J'.restrictScalars (ZMod 2) := hb.le
      rcases hJ.eq_bot_or_eq (invariant_restrictScalars b) hle with h | h
      · exact Submodule.restrictScalars_injective (ZMod 2) (HRing H) V (by simpa using h)
      · exact absurd (Submodule.restrictScalars_injective (ZMod 2) (HRing H) V h) hb.ne
  · intro hJ
    refine ⟨invariant_restrictScalars J', bot_lt_iff_ne_bot.2 ?_, ?_⟩
    · intro h
      exact hJ.1 (Submodule.restrictScalars_injective (ZMod 2) (HRing H) V (by simpa using h))
    · intro K hK _ hKJ
      have hle : ofInvariant K hK ≤ J' := hKJ
      rcases eq_or_lt_of_le hle with h | h
      · exact Or.inr (by rw [← restrictScalars_ofInvariant K hK, h])
      · left
        have := hJ.2 _ h
        rw [← restrictScalars_ofInvariant K hK, this]
        simp

theorem exists_linearEquiv_of_hIso {m m' : Submodule (HRing H) V}
    (h : HIso H (m.restrictScalars (ZMod 2)) (m'.restrictScalars (ZMod 2))) :
    Nonempty (m ≃ₗ[HRing H] m') := by
  obtain ⟨φ, hφ⟩ := h
  let φ₀ : m →ₗ[ZMod 2] m' :=
    { toFun := fun x => ⟨(φ ⟨x.1, x.2⟩ : V), (φ ⟨x.1, x.2⟩).2⟩
      map_add' := fun x y => Subtype.ext (congrArg Subtype.val (map_add φ ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
      map_smul' := fun c x => Subtype.ext (congrArg Subtype.val (map_smul φ c ⟨x.1, x.2⟩)) }
  have hgen : ∀ (h : H) (x : m), φ₀ (genElem H h • x) = genElem H h • φ₀ x := by
    intro h x
    apply Subtype.ext
    exact (hφ h.1 h.2 ⟨x.1, x.2⟩ ⟨((genElem H h • x : m) : V), (genElem H h • x).2⟩ rfl).symm
  have hlin : ∀ (a : HRing H) (x : m), φ₀ (a • x) = a • φ₀ x :=
    map_smul_of_gens (H := H) (M := m) (N := m') φ₀ hgen
  let φA : m →ₗ[HRing H] m' :=
    { toFun := φ₀
      map_add' := φ₀.map_add
      map_smul' := fun a x => hlin a x }
  refine ⟨LinearEquiv.ofBijective φA ⟨fun x y hxy => ?_, fun y => ?_⟩⟩
  · have := φ.injective (Subtype.ext (congrArg Subtype.val hxy) :
      φ ⟨x.1, x.2⟩ = φ ⟨y.1, y.2⟩)
    exact Subtype.ext (congrArg Subtype.val this)
  · refine ⟨⟨(φ.symm ⟨y.1, y.2⟩ : V), (φ.symm ⟨y.1, y.2⟩).2⟩, ?_⟩
    exact Subtype.ext (congrArg Subtype.val (φ.apply_symm_apply ⟨y.1, y.2⟩))

theorem exists_equiv_of_atom (hfix : fixedSpace H = ⊥) (hhom : Homogeneous H)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus H I) {m : Submodule (HRing H) V} (hm : IsAtom m) :
    Nonempty (m ≃ₗ[HRing H] ofInvariant I hI.1) := by
  have hmI : IsIrr H (m.restrictScalars (ZMod 2)) := isIrr_iff_isAtom.2 hm
  exact exists_linearEquiv_of_hIso (hhom _ _ (hmI.irrPlus hfix) hI)

end E11

end G11

end CFSG.Quasithin
