module

public import CFSG.Quasithin.Background.E11Alg
public import CFSG.Quasithin.Background.E11Stmt

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

section EndEquiv

variable {I : Submodule (ZMod 2) V} (hI : Invariant H I)

omit hI in
theorem mem_endOn_iff (g : Module.End (ZMod 2) ↥I) (hI : Invariant H I) :
    g ∈ endOn H I ↔ ∀ (h : GLV V) (hh : h ∈ H), ∀ i : ↥I,
      h ((g i : ↥I) : V) = ((g ⟨h (i : V), hI h hh i i.2⟩ : ↥I) : V) := by
  rw [endOn, Subalgebra.mem_centralizer_iff]
  constructor
  · intro hc h hh i
    have := hc _ ⟨h, hI.conjSub_eq hh, hh, rfl⟩
    exact congrArg (fun T : Module.End (ZMod 2) ↥I => ((T i : ↥I) : V)) this
  · rintro hc _ ⟨h, hh, hhH, rfl⟩
    refine LinearMap.ext fun i => Subtype.ext ?_
    exact hc h hhH i

@[expose] def endToF2 (f : Module.End (HRing H) (ofInvariant I hI)) : Module.End (ZMod 2) ↥I where
  toFun i := ⟨(f ⟨i.1, i.2⟩ : V), (f ⟨i.1, i.2⟩).2⟩
  map_add' i j := Subtype.ext (congrArg Subtype.val (map_add f ⟨i.1, i.2⟩ ⟨j.1, j.2⟩))
  map_smul' c i :=
    Subtype.ext (congrArg Subtype.val (map_smul (f.restrictScalars (ZMod 2)) c ⟨i.1, i.2⟩))

theorem endToF2_mem (f : Module.End (HRing H) (ofInvariant I hI)) : endToF2 hI f ∈ endOn H I := by
  refine (mem_endOn_iff _ hI).2 fun h hh i => ?_
  exact (congrArg Subtype.val (f.map_smul (genElem H ⟨h, hh⟩) ⟨i.1, i.2⟩)).symm

@[expose] def endToOn : Module.End (HRing H) (ofInvariant I hI) →+* endOn H I where
  toFun f := ⟨endToF2 hI f, endToF2_mem hI f⟩
  map_one' := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_zero' := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

@[expose] noncomputable def onToEnd (g : endOn H I) : Module.End (HRing H) (ofInvariant I hI) :=
  let g₁ : ↥(ofInvariant I hI) →ₗ[ZMod 2] ↥(ofInvariant I hI) :=
    { toFun := fun x => ⟨(g.1 ⟨x.1, x.2⟩ : V), (g.1 ⟨x.1, x.2⟩).2⟩
      map_add' := fun x y =>
        Subtype.ext (congrArg Subtype.val (map_add g.1 ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
      map_smul' := fun c x =>
        Subtype.ext (congrArg Subtype.val (map_smul g.1 c ⟨x.1, x.2⟩)) }
  have hgen : ∀ (h : H) (x : ↥(ofInvariant I hI)),
      g₁ (genElem H h • x) = genElem H h • g₁ x := fun h x =>
    Subtype.ext ((mem_endOn_iff g.1 hI).1 g.2 h h.2 ⟨x.1, x.2⟩).symm
  { toFun := g₁
    map_add' := g₁.map_add
    map_smul' := fun a x =>
      map_smul_of_gens (H := H) (M := ↥(ofInvariant I hI)) (N := ↥(ofInvariant I hI)) g₁ hgen a x }

theorem endToOn_bijective : Function.Bijective (endToOn hI) := by
  refine ⟨fun f g h => ?_, fun g => ⟨onToEnd hI g, ?_⟩⟩
  · refine LinearMap.ext fun x => ?_
    have := congrArg (fun T : endOn H I => ((T.1 ⟨x.1, x.2⟩ : ↥I) : V)) h
    exact Subtype.ext this
  · exact Subtype.ext (LinearMap.ext fun i => Subtype.ext rfl)

@[expose] noncomputable def endAlgEquiv :
    endOn H I ≃ₐ[ZMod 2] Module.End (HRing H) (ofInvariant I hI) :=
  (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (endToOn hI) (endToOn_bijective hI))
    (fun c => RingHom.congr_fun (RingHom.ext_zmod
      ((endToOn hI).comp (algebraMap (ZMod 2) (Module.End (HRing H) (ofInvariant I hI))))
      (algebraMap (ZMod 2) (endOn H I))) c)).symm

end EndEquiv

end E11

end G11

end CFSG.Quasithin
