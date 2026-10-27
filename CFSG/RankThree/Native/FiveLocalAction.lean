module

public import CFSG.RankThree.Native.FiveLocalBasic
public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.CentralExtension.InvariantComplement

public section

namespace CFSG.RankThree.Native.FiveLocal

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

variable {G : Type*} [Group G]

theorem conj_pow' (g y : G) (n : ℕ) : g⁻¹ * y ^ n * g = (g⁻¹ * y * g) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    group

variable [Finite G]

namespace Rel

variable {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z)
include hR

theorem conj_q_mem_of_K {g : G} (hg : g ∈ K x h q) (i : Fin 4) : g⁻¹ * q i * g ∈ Q q :=
  hR.conj_mem_of_mem_K hg (q_mem i)

theorem crd_conj {g : G} (hg : g ∈ K x h q) {u : G} (hu : u ∈ Q q) :
    crd q z (g⁻¹ * u * g) = crd q z u ᵥ* A q z g :=
  hR.commData.coord_conj (hR.conj_q_mem_of_K hg) hu

theorem A_mul {g g' : G} (hg : g ∈ K x h q) (hg' : g' ∈ K x h q) :
    A q z (g * g') = A q z g * A q z g' :=
  hR.commData.actMat_mul (hR.conj_q_mem_of_K hg) (hR.conj_q_mem_of_K hg')

omit [Finite G] in
theorem A_one : A q z 1 = 1 := hR.commData.actMat_one

omit [Finite G] in
theorem A_of_mem_Q {g : G} (hg : g ∈ Q q) : A q z g = 1 := hR.commData.actMat_of_mem hg

omit [Finite G] in
theorem A_x : A q z x = f5X := hR.commData.actMat_eq f5X xc hR.conj_x

omit [Finite G] in
theorem A_h : A q z h = f5H := hR.commData.actMat_eq f5H hc hR.conj_h

@[expose] noncomputable def AU : K x h q →* GL (Fin 4) (ZMod 5) where
  toFun g := ⟨A q z g, A q z (g : G)⁻¹,
    by rw [← hR.A_mul g.2 (inv_mem g.2), mul_inv_cancel, hR.A_one],
    by rw [← hR.A_mul (inv_mem g.2) g.2, inv_mul_cancel, hR.A_one]⟩
  map_one' := Units.ext hR.A_one
  map_mul' g g' := Units.ext (hR.A_mul g.2 g'.2)

theorem AU_val (g : K x h q) : ((hR.AU g : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
    A q z g := rfl

theorem AU_x : hR.AU ⟨x, x_mem_K⟩ = f5XU := Units.ext hR.A_x

theorem AU_of_mem_Q {g : K x h q} (hg : (g : G) ∈ Q q) : hR.AU g = 1 := Units.ext (hR.A_of_mem_Q hg)

end Rel

end CFSG.RankThree.Native.FiveLocal
