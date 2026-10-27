
module

public import CFSG.Assembly.Defs
public import CFSG.Monster.B.Fischer.Fi22GraphBase

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22P_le_R : fi22P ≤ fi22R := fun _ hg =>
  Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)

theorem fi22U_mem_R : fi22U ∈ fi22R := Subgroup.subset_closure (Set.mem_insert _ _)

instance : Finite (MulAut fi22P) :=
  Finite.of_injective (fun α : MulAut fi22P => (α : fi22P → fi22P)) fun _ _ h =>
    MulEquiv.ext fun x => congrFun h x

instance fi22Inn_normal : (MulAut.conj : fi22P →* MulAut fi22P).range.Normal :=
  ⟨fun α ⟨g, hg⟩ β => ⟨β g, by
    rw [← hg]
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]⟩⟩

end CFSG.Monster.B.Fischer
