module

public import CFSG.Monster.SpinLattice.Cocode
public import CFSG.Monster.Spin.Extraspecial

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.SpinLattice

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Subgroup
open scoped commutatorElement

@[expose] noncomputable def XQ (e : Parker) : Q := ⟨XU e, XU_mem_Q e⟩

@[expose] noncomputable def DQ (δ : Cocode) : Q := ⟨DU δ, DU_mem_Q δ⟩

theorem XQ_eq (e : Parker) : XQ e = spinEquiv ⟨e.sign, e.code, thetaD e.code⟩ :=
  Subtype.ext (XU_eq_toGL e)

theorem DQ_eq (δ : Cocode) : DQ δ = spinEquiv ⟨0, 0, δ⟩ := Subtype.ext (DU_eq_toGL δ)

@[expose] noncomputable def phi : (Q ⧸ center Q) ≃* Multiplicative L2 :=
  quotCenterEquiv.trans (AddEquiv.toMultiplicative phi0Equiv.toAddEquiv)

theorem phi_mk (g : Q) :
    phi (QuotientGroup.mk g) = Multiplicative.ofAdd (phi0 (Multiplicative.toAdd (projQ g))) := rfl

theorem phi_mk_spinEquiv (x : SpinCoord) :
    phi (QuotientGroup.mk (spinEquiv x)) = Multiplicative.ofAdd (phi0 (x.a, x.δ)) := by
  rw [phi_mk, projQ_spinEquiv]
  rfl

theorem phi_XQ (e : Parker) : phi (QuotientGroup.mk (XQ e)) = Multiplicative.ofAdd (lamX e.code) :=
  (congrArg (fun g => phi (QuotientGroup.mk g)) (XQ_eq e)).trans
    ((phi_mk_spinEquiv _).trans (congrArg Multiplicative.ofAdd (phi0_thetaD e.code)))

theorem lamT_zero : lamT 0 = 0 := lamTHom.map_zero

theorem phi0_zero_left (δ : Cocode) : phi0 (0, δ) = lamCocode δ := by
  rw [phi0_apply, lamT_zero, zero_add]

theorem phi_DQ (δ : Cocode) : phi (QuotientGroup.mk (DQ δ)) = Multiplicative.ofAdd (lamCocode δ) :=
  (congrArg (fun g => phi (QuotientGroup.mk g)) (DQ_eq δ)).trans
    ((phi_mk_spinEquiv _).trans (congrArg Multiplicative.ofAdd (phi0_zero_left δ)))

theorem eq_phi {ψ : (Q ⧸ center Q) →* Multiplicative L2}
    (hX : ∀ e : Parker, ψ (QuotientGroup.mk (XQ e)) = Multiplicative.ofAdd (lamX e.code))
    (hD : ∀ δ : Cocode, ψ (QuotientGroup.mk (DQ δ)) = Multiplicative.ofAdd (lamCocode δ)) :
    ψ = phi.toMonoidHom := by
  refine QuotientGroup.monoidHom_ext _ ?_
  refine MonoidHom.eq_of_eqOn_dense (closure_preimage_eq_top (Set.range XU ∪ Set.range DU)) ?_
  rintro g (⟨e, he⟩ | ⟨δ, hδ⟩)
  · have hg : g = XQ e := Subtype.ext he.symm
    exact (congrArg (fun g => ψ (QuotientGroup.mk g)) hg).trans ((hX e).trans
      ((phi_XQ e).symm.trans (congrArg (fun g => phi (QuotientGroup.mk g)) hg.symm)))
  · have hg : g = DQ δ := Subtype.ext hδ.symm
    exact (congrArg (fun g => ψ (QuotientGroup.mk g)) hg).trans ((hD δ).trans
      ((phi_DQ δ).symm.trans (congrArg (fun g => phi (QuotientGroup.mk g)) hg.symm)))

theorem z_pow_val (e : ZMod 2) : SpinCoord.z ^ e.val = ⟨e, 0, 0⟩ := by
  have : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  rcases this e with rfl | rfl
  · rfl
  · rw [ZMod.val_one, pow_one]
    rfl

theorem zQ_pow_val (e : ZMod 2) : zQ ^ e.val = spinEquiv ⟨e, 0, 0⟩ := by
  rw [zQ, ← map_pow, z_pow_val]

theorem pair_eq_of_sq {x : SpinCoord} {e : ZMod 2} (h : spinEquiv x ^ 2 = zQ ^ e.val) :
    pair x.a x.δ = e := by
  have h' : spinEquiv (x ^ 2) = spinEquiv ⟨e, 0, 0⟩ :=
    (map_pow spinEquiv x 2).trans (h.trans (zQ_pow_val e))
  have := spinEquiv.injective h'
  rw [SpinCoord.sq_eq] at this
  exact congrArg SpinCoord.s this

theorem pair_add_eq_of_commutator {x y : SpinCoord} {f : ZMod 2}
    (h : ⁅spinEquiv x, spinEquiv y⁆ = zQ ^ f.val) : pair x.a y.δ + pair y.a x.δ = f := by
  have h' : spinEquiv ⁅x, y⁆ = spinEquiv ⟨f, 0, 0⟩ :=
    (map_commutatorElement spinEquiv x y).trans (h.trans (zQ_pow_val f))
  have := spinEquiv.injective h'
  rw [SpinCoord.commutatorElement_eq] at this
  exact congrArg SpinCoord.s this

theorem qL_phi_of_sq {r : Q} {e : ZMod 2} (h : r ^ 2 = zQ ^ e.val) :
    qL (Multiplicative.toAdd (phi (QuotientGroup.mk r))) = e :=
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  calc qL (Multiplicative.toAdd (phi (QuotientGroup.mk r)))
      = qL (Multiplicative.toAdd (phi (QuotientGroup.mk (spinEquiv (spinEquiv.symm r))))) :=
        congrArg (fun g => qL (Multiplicative.toAdd (phi (QuotientGroup.mk g)))) hx.symm
    _ = qL (phi0 ((spinEquiv.symm r).a, (spinEquiv.symm r).δ)) :=
        congrArg (fun y => qL (Multiplicative.toAdd y)) (phi_mk_spinEquiv _)
    _ = pair (spinEquiv.symm r).a (spinEquiv.symm r).δ := qL_phi0 _ _
    _ = e := pair_eq_of_sq ((congrArg (· ^ 2) hx).trans h)

theorem bL_phi_of_commutator {r t : Q} {f : ZMod 2} (h : ⁅r, t⁆ = zQ ^ f.val) :
    QuadraticMap.polarBilin qL (Multiplicative.toAdd (phi (QuotientGroup.mk r)))
      (Multiplicative.toAdd (phi (QuotientGroup.mk t))) = f :=
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have hy : spinEquiv (spinEquiv.symm t) = t := spinEquiv.apply_symm_apply t
  calc QuadraticMap.polarBilin qL (Multiplicative.toAdd (phi (QuotientGroup.mk r)))
        (Multiplicative.toAdd (phi (QuotientGroup.mk t)))
      = QuadraticMap.polarBilin qL
          (Multiplicative.toAdd (phi (QuotientGroup.mk (spinEquiv (spinEquiv.symm r)))))
          (Multiplicative.toAdd (phi (QuotientGroup.mk (spinEquiv (spinEquiv.symm t))))) :=
        congrArg₂ (fun g k => QuadraticMap.polarBilin qL
          (Multiplicative.toAdd (phi (QuotientGroup.mk g)))
          (Multiplicative.toAdd (phi (QuotientGroup.mk k)))) hx.symm hy.symm
    _ = QuadraticMap.polarBilin qL (phi0 ((spinEquiv.symm r).a, (spinEquiv.symm r).δ))
          (phi0 ((spinEquiv.symm t).a, (spinEquiv.symm t).δ)) :=
        congrArg₂ (fun u v => QuadraticMap.polarBilin qL (Multiplicative.toAdd u)
          (Multiplicative.toAdd v)) (phi_mk_spinEquiv _) (phi_mk_spinEquiv _)
    _ = pair (spinEquiv.symm r).a (spinEquiv.symm t).δ +
          pair (spinEquiv.symm t).a (spinEquiv.symm r).δ := bL_phi0 _ _ _ _
    _ = f := pair_add_eq_of_commutator ((congrArg₂ (fun u v => ⁅u, v⁆) hx hy).trans h)

theorem lamX_eq (a : C) :
    lamX a = cls (fun k => if P (a : Fin 24 → ZMod 2) = 0 then 2 * bitLift ((a : Fin 24 → ZMod 2) k)
      else 2 * (1 - bitLift ((a : Fin 24 → ZMod 2) k)))
      (by
        have h := lamCode_mem a.2
        have hP : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
        rcases hP (P (a : Fin 24 → ZMod 2)) with hp | hp
        · rw [lamCode_of_P_zero hp] at h; simpa [hp] using h
        · rw [lamCode_of_P_one hp] at h; simpa [hp] using h) := by
  have hP : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rw [lamX, lamCodeCls]
  apply cls_congr
  rcases hP (P (a : Fin 24 → ZMod 2)) with hp | hp
  · rw [lamCode_of_P_zero hp]; simp [hp]
  · rw [lamCode_of_P_one hp]; simp [hp]

theorem lamCocode_eq_sum (v : Fin 24 → ZMod 2) :
    lamCocode (Submodule.Quotient.mk v) =
      ∑ i, v i • cls (fun k => 1 - 4 * (Pi.single i (1 : ℤ) : Fin 24 → ℤ) k)
        (lamSum_single i ▸ lamSum_mem _) := by
  rw [lamCocode_mk, lamVec_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact cls_congr _ (lamSum_single i)

theorem spin_lattice_quadratic_isometry :
    center Q = zpowers zQ ∧
    (∀ e : Parker, phi (QuotientGroup.mk (XQ e)) = Multiplicative.ofAdd (lamX e.code)) ∧
    (∀ δ : Cocode, phi (QuotientGroup.mk (DQ δ)) = Multiplicative.ofAdd (lamCocode δ)) ∧
    (∀ ψ : (Q ⧸ center Q) →* Multiplicative L2,
      (∀ e : Parker, ψ (QuotientGroup.mk (XQ e)) = Multiplicative.ofAdd (lamX e.code)) →
      (∀ δ : Cocode, ψ (QuotientGroup.mk (DQ δ)) = Multiplicative.ofAdd (lamCocode δ)) →
      ψ = phi.toMonoidHom) ∧
    (∀ (r : Q) (e : ZMod 2), r ^ 2 = zQ ^ e.val →
      qL (Multiplicative.toAdd (phi (QuotientGroup.mk r))) = e) ∧
    (∀ (r t : Q) (f : ZMod 2), ⁅r, t⁆ = zQ ^ f.val →
      QuadraticMap.polarBilin qL (Multiplicative.toAdd (phi (QuotientGroup.mk r)))
        (Multiplicative.toAdd (phi (QuotientGroup.mk t))) = f) :=
  ⟨center_Q, phi_XQ, phi_DQ, fun _ hX hD => eq_phi hX hD, fun _ _ h => qL_phi_of_sq h,
    fun _ _ _ h => bL_phi_of_commutator h⟩

end CFSG.Monster.SpinLattice
