module

public import CFSG.RankThree.PartOne.A6N.Reduce
public import CFSG.RankThree.PartOne.A6N.Sylow3
public import CFSG.RankThree.PartOne.N1322.Pure

public section

namespace CFSG.RankThree.PartOne.A6N

open CFSG.RankThree.PartOne.N1322 CFSG.RepresentationTheory Equiv


theorem kf1322ThreeA6Norm_holds : KF1322ThreeA6Norm := by
  intro p _ hp5 H hirr hperf hcard ⟨e⟩ g hg
  let V : Val p := ⟨H, hirr, hperf, hcard, e⟩
  obtain ⟨u, hu5, hEu⟩ := V.exists_u
  obtain ⟨s, hs2, hEs, hsu⟩ := V.exists_s hu5 hEu
  obtain ⟨h, hgu, hgs, -⟩ := V.reduce hu5 hEu hs2 hEs hsu hg
  have hg' : ∀ x ∈ V.H, ((h : GL (Fin 3) (ZMod p)) * g) * x *
      ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ ∈ V.H := by
    intro x hx
    have e : ((h : GL (Fin 3) (ZMod p)) * g) * x * ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ =
        (h : GL (Fin 3) (ZMod p)) * (g * x * g⁻¹) * (h : GL (Fin 3) (ZMod p))⁻¹ := by group
    rw [e]
    exact V.H.mul_mem (V.H.mul_mem h.2 (hg x hx)) (V.H.inv_mem h.2)
  obtain ⟨ψ, hψ⟩ := V.exists_induced (V.conjAut hg')
  have hαu : V.conjAut hg' u = u := by
    apply Subtype.ext
    rw [Val.coe_conjAut]
    calc ((h : GL (Fin 3) (ZMod p)) * g) * (u : GL (Fin 3) (ZMod p)) *
        ((h : GL (Fin 3) (ZMod p)) * g)⁻¹
        = (((h : GL (Fin 3) (ZMod p)) * g) * (u : GL (Fin 3) (ZMod p))) *
          ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ := rfl
      _ = ((u : GL (Fin 3) (ZMod p)) * ((h : GL (Fin 3) (ZMod p)) * g)) *
          ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ := by rw [hgu]
      _ = (u : GL (Fin 3) (ZMod p)) := by group
  have hαs : V.conjAut hg' s = s := by
    apply Subtype.ext
    rw [Val.coe_conjAut]
    calc ((h : GL (Fin 3) (ZMod p)) * g) * (s : GL (Fin 3) (ZMod p)) *
        ((h : GL (Fin 3) (ZMod p)) * g)⁻¹
        = (((h : GL (Fin 3) (ZMod p)) * g) * (s : GL (Fin 3) (ZMod p))) *
          ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ := rfl
      _ = ((s : GL (Fin 3) (ZMod p)) * ((h : GL (Fin 3) (ZMod p)) * g)) *
          ((h : GL (Fin 3) (ZMod p)) * g)⁻¹ := by rw [hgs]
      _ = (s : GL (Fin 3) (ZMod p)) := by group
  have ha : ψ a₀A = a₀A := by rw [← hEu, ← hψ, hαu]
  have hs : ψ s₀A = s₀A := by rw [← hEs, ← hψ, hαs]
  rcases aut_dichotomy ψ ha hs with hid | ⟨hy, -⟩
  ·
    have hα : (V.conjAut hg').toMonoidHom = MonoidHom.id V.H :=
      V.perfect_hom_eq _ _ (fun x => by
        rw [← V.E_eq_one_iff, map_mul, map_inv]
        have := hψ x
        rw [hid, MulEquiv.refl_apply] at this
        simp [this])
    have hcomm : ∀ y : GL (Fin 3) (ZMod p), y ∈ V.H →
        ((h : GL (Fin 3) (ZMod p)) * g) * y = y * ((h : GL (Fin 3) (ZMod p)) * g) := by
      intro y hy
      have h1 := congrArg (fun w : V.H => (w : GL (Fin 3) (ZMod p)))
        (DFunLike.congr_fun hα ⟨y, hy⟩)
      simp only [MulEquiv.coe_toMonoidHom, Val.coe_conjAut, MonoidHom.id_apply] at h1
      calc ((h : GL (Fin 3) (ZMod p)) * g) * y
          = (((h : GL (Fin 3) (ZMod p)) * g) * y * ((h : GL (Fin 3) (ZMod p)) * g)⁻¹) *
            ((h : GL (Fin 3) (ZMod p)) * g) := by group
        _ = y * ((h : GL (Fin 3) (ZMod p)) * g) := by rw [h1]
    obtain ⟨c, hc⟩ := scalar_commutant_of_noncomm V.irr V.exists_noncomm
      ((((h : GL (Fin 3) (ZMod p)) * g : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p))) (fun y hy => by
        have := congrArg (fun w : GL (Fin 3) (ZMod p) => (w : Matrix (Fin 3) (Fin 3) (ZMod p)))
          (hcomm y hy)
        simpa using this.symm)
    refine ⟨((h⁻¹ : V.H) : GL (Fin 3) (ZMod p)), (h⁻¹).2, (h : GL (Fin 3) (ZMod p)) * g,
      fun y => (central_of_scalar hc y).symm, ?_⟩
    simp
  · exact (V.tau_false hp5 hg' hψ ha hs hy).elim

end CFSG.RankThree.PartOne.A6N
