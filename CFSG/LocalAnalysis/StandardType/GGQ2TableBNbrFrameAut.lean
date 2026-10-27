module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def NbrWeylDataVx (R : RawFrameData) (v : R.V) : Prop :=
  ∀ k : R.Code, v ≠ 0 → R.admissible k → R.occurs ((ZMod 3) ∙ v) k →
    3 + finrank (ZMod 3) (R.cent k) ≤ finrank (ZMod 3) R.V → Nonempty (CodeWeylDatum R k)

theorem nbrWeylData_iff_forall (R : RawFrameData) : NbrWeylData R ↔ ∀ v, NbrWeylDataVx R v :=
  Iff.rfl

namespace FrameAut

variable {R : RawFrameData} (A : FrameAut R)

noncomputable def codeWeylDatum {k : R.Code} (D : CodeWeylDatum R k) : CodeWeylDatum R (A.σ k) where
  ι := D.ι
  coxeter := D.coxeter
  cartan := D.cartan
  coroot i := A.g (D.coroot i)
  root i := (D.root i).comp (A.g.symm : R.V →ₗ[ZMod 3] R.V)
  isWeyl := D.isWeyl
  isCartan := D.isCartan
  pairing i j := by simp [D.pairing]
  refl i := MulAut.conj A.g (D.refl i)
  refl_apply i v := by
    simp [MulAut.conj_apply, D.refl_apply]
  closure_refl := by
    rw [A.normalizerGroup_eq, ← D.closure_refl, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  ker_iff v := by
    rw [A.cent_eq, Submodule.mem_map_equiv]
    exact D.ker_iff (A.g.symm v)

theorem nbrWeylDataVx_map {v : R.V} (h : NbrWeylDataVx R v) : NbrWeylDataVx R (A.g v) := by
  intro k' hv hk hocc hcod
  obtain ⟨k, rfl⟩ := A.σ.surjective k'
  rw [A.admissible_iff] at hk
  rw [A.occurs_span_iff] at hocc
  rw [A.cent_eq, LinearEquiv.finrank_map_eq] at hcod
  obtain ⟨D⟩ := h k (fun h0 => hv (by rw [h0, map_zero])) hk hocc hcod
  exact ⟨A.codeWeylDatum D⟩

end FrameAut

end CFSG.StandardType.GGQ2Frame

end
