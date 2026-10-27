module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoCtx
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOddGrp
public import CFSG.LocalAnalysis.WeakClosure81.W183CF
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Rad

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem tail1812Two_hfac (hB : ListBNonabelian) (hComp : OddTranspositionCompFactorInput)
    {g : G} (cx : Tail1812TwoCtx G D V₀ V H i g) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) :
    ∀ (X : Type) [Group X], (∃ φ : ↥L →* X, Function.Surjective φ ∧
        ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ kerMV V H) → IsSimpleGroup X →
        (∃ u v : X, u * v ≠ v * u) → OddTranspFactor X := by
  obtain ⟨Y, hYgrp, hYfin, π, a₁, Kk, P, hS⟩ := tail1812Two_exists_setting hB cx
  letI : Group Y := hYgrp
  haveI : Finite Y := hYfin
  intro X _
  rintro ⟨φ, hφs, hφk⟩ hsimple hnab
  have hLH : L ≤ H := hL.2.2.1
  have hsub : (L.subgroupOf H).IsSubnormal :=
    CFSG.Open.IsSubnormal.subgroupOf hL.2.2.2.1
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  let ψ : ↥(L.subgroupOf H) →* X := φ.comp (e : ↥(L.subgroupOf H) →* ↥L)
  have hψ : Function.Surjective ψ := hφs.comp e.surjective
  have hHfac : CFSG.Quasithin.E1.IsCompositionFactor ↥H X :=
    CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection hsub hsimple ψ hψ
  have hKs : Group.IsSolvable ↥(kerMV V H) :=
    cx.cex.kerMV_isSolvable_182 cx.h172 cx.h5_4 cx.h5_11 cx.h5_13 cx.not_concl
  haveI := hKs
  let ι : ↥π.ker →* ↥(kerMV V H) :=
    { toFun := fun x => ⟨((x.1 : ↥H) : G), hS.ker_le x.1 (MonoidHom.mem_ker.mp x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥(kerMV V H) => (z : G)) hab))
  have hker : Group.IsSolvable ↥π.ker :=
    Group.isSolvable_of_isSolvable_injective (f := ι) hι
  have hYfac : CFSG.Quasithin.E1.IsCompositionFactor Y X :=
    isCompositionFactor_of_surjective_of_isSolvable_ker π hS.surj hker hHfac hnab
  obtain ⟨X₁, haX, -, hord, hodd, hnormalclosure, -, -, hCF⟩ :=
    exists_oddClassGroup (Y := Y) (a := π a₁) (Kk := Kk) (P := P)
      hS.ord hS.comm_or_conj hS.o2 hS.p_normal hS.two_quot hS.le_of_not_le hS.not_mem
  exact hComp ↥X₁ ⟨π a₁, haX⟩ hord hodd hnormalclosure X (hCF X hYfac hnab) hnab

end CFSG.LocalAnalysis.WeakClosure81

end
