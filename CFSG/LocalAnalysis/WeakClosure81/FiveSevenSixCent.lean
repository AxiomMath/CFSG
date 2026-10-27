module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem card_fstar_inf_centralizer_eq_card_fixedPoints {H : Subgroup G} {n : ℕ}
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) (φ : ↥H →* MulAut (alternatingGroup (Fin n)))
    (hφ : ∀ (x : ↥H) (f : ↥(Fstar H)),
      ((e.symm (φ x (e f)) : ↥(Fstar H)) : G) = (x : G) * (f : G) * (x : G)⁻¹) (a : ↥H) :
    Nat.card ↥(Fstar H ⊓ Subgroup.centralizer ({(a : G)} : Set G)) =
      Nat.card {l : alternatingGroup (Fin n) // φ a l = l} := by
  have hfix : ∀ y : ↥(Fstar H ⊓ Subgroup.centralizer ({(a : G)} : Set G)),
      φ a (e ⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩) = e ⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩ := by
    intro y
    have hy := Subgroup.mem_inf.1 y.2
    have hc : (y : G) * (a : G) = (a : G) * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 hy.2
    apply e.symm.injective
    apply Subtype.ext
    rw [hφ a ⟨(y : G), hy.1⟩, MulEquiv.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.2 hc.symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => (⟨e ⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩, hfix y⟩ :
      {l : alternatingGroup (Fin n) // φ a l = l})) ⟨?_, ?_⟩)
  · intro y y' hyy
    have h1 : e ⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩ =
        e ⟨(y' : G), (Subgroup.mem_inf.1 y'.2).1⟩ :=
      congrArg (fun z : {l : alternatingGroup (Fin n) // φ a l = l} => z.1) hyy
    have h2 := e.injective h1
    exact Subtype.ext (congrArg (fun z : ↥(Fstar H) => (z : G)) h2)
  · rintro ⟨l, hl⟩
    have hf : ((e.symm l : ↥(Fstar H)) : G) * (a : G) =
        (a : G) * ((e.symm l : ↥(Fstar H)) : G) := by
      have h1 := hφ a (e.symm l)
      rw [MulEquiv.apply_symm_apply, hl] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
    refine ⟨⟨((e.symm l : ↥(Fstar H)) : G), Subgroup.mem_inf.2
      ⟨(e.symm l).2, Subgroup.mem_centralizer_singleton_iff.2 hf⟩⟩, ?_⟩
    apply Subtype.ext
    show e ⟨((e.symm l : ↥(Fstar H)) : G), _⟩ = l
    exact e.apply_symm_apply l

end CFSG.LocalAnalysis.WeakClosure81
