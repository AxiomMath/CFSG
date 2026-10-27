module

public import CFSG.Quasithin.Recognition.SzR1Kernel

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem Vf_injective (C : FamCtx K1 L2 S Zs Ω) {i j : Ω}
    (h : C.D.Vf (conjClosure Zs L2) i = C.D.Vf (conjClosure Zs L2) j) : i = j := by
  by_contra hij
  have hzj : C.zf j ∈ C.D.Vf (conjClosure Zs L2) i := h ▸ C.zf_mem j
  have hcomm : C.zf i * C.zf j = C.zf j * C.zf i := C.Vf_comm (C.zf_mem i) hzj
  apply C.cm_ne_one hij
  show C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹ = 1
  rw [hcomm]
  group

@[expose] noncomputable def permOf (C : FamCtx K1 L2 S Zs Ω) (g : ↥(K1 ⊔ S)) (ω : Ω) : Ω :=
  (C.exists_conjSub_Vf_of_mem_sup g.2 ω).choose

theorem conjSub_permOf (C : FamCtx K1 L2 S Zs Ω) (g : ↥(K1 ⊔ S)) (ω : Ω) :
    conjSub (g : G) (C.D.Vf (conjClosure Zs L2) ω) =
      C.D.Vf (conjClosure Zs L2) (permOf C g ω) :=
  (C.exists_conjSub_Vf_of_mem_sup g.2 ω).choose_spec

theorem permOf_eq_of_conjSub (C : FamCtx K1 L2 S Zs Ω) {g : ↥(K1 ⊔ S)} {ω ω' : Ω}
    (h : conjSub (g : G) (C.D.Vf (conjClosure Zs L2) ω) = C.D.Vf (conjClosure Zs L2) ω') :
    permOf C g ω = ω' :=
  Vf_injective C (by rw [← conjSub_permOf, h])

theorem permOf_mul (C : FamCtx K1 L2 S Zs Ω) (g h : ↥(K1 ⊔ S)) (ω : Ω) :
    permOf C (g * h) ω = permOf C g (permOf C h ω) :=
  permOf_eq_of_conjSub C (by
    rw [show (((g * h : ↥(K1 ⊔ S)) : G)) = (g : G) * (h : G) from rfl, conjSub_mul,
      conjSub_permOf, conjSub_permOf])

theorem permOf_one (C : FamCtx K1 L2 S Zs Ω) (ω : Ω) : permOf C 1 ω = ω :=
  permOf_eq_of_conjSub C (by
    rw [show (((1 : ↥(K1 ⊔ S)) : G)) = 1 from rfl, conjSub_one])

@[expose] noncomputable def permHom (C : FamCtx K1 L2 S Zs Ω) : ↥(K1 ⊔ S) →* Equiv.Perm Ω :=
  MonoidHom.mk'
    (fun g =>
      { toFun := permOf C g
        invFun := permOf C g⁻¹
        left_inv := fun ω => by rw [← permOf_mul, inv_mul_cancel, permOf_one]
        right_inv := fun ω => by rw [← permOf_mul, mul_inv_cancel, permOf_one] })
    (fun g h => Equiv.ext fun ω => permOf_mul C g h ω)

@[simp] theorem permHom_apply (C : FamCtx K1 L2 S Zs Ω) (g : ↥(K1 ⊔ S)) (ω : Ω) :
    permHom C g ω = permOf C g ω := rfl

theorem conjSub_permHom (C : FamCtx K1 L2 S Zs Ω) (g : ↥(K1 ⊔ S)) (ω : Ω) :
    conjSub (g : G) (C.D.Vf (conjClosure Zs L2) ω) =
      C.D.Vf (conjClosure Zs L2) (permHom C g ω) :=
  conjSub_permOf C g ω

theorem permHom_K1 (C : FamCtx K1 L2 S Zs Ω) (k : ↥K1) :
    permHom C ⟨(k : G), Subgroup.mem_sup_left k.2⟩ = C.D.act k :=
  Equiv.ext fun ω => permOf_eq_of_conjSub C (C.D.conjSub_Vf C.hVn k ω)

theorem permHom_eq_one_iff (C : FamCtx K1 L2 S Zs Ω) (g : ↥(K1 ⊔ S)) :
    permHom C g = 1 ↔ (g : G) ∈ C.kerM := by
  rw [C.mem_kerM]
  refine ⟨fun h => ⟨g.2, fun ω => ?_⟩, fun h => Equiv.ext fun ω => ?_⟩
  · rw [conjSub_permHom, h]
    rfl
  · exact permOf_eq_of_conjSub C (h.2 ω)

end CFSG.Quasithin.Background.Harris.R1
