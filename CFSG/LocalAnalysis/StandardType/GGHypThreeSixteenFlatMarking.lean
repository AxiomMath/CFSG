module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Transport

theorem largeEvenMarking_true_of_surjective_ker_le_center {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center A)
    (h : LargeEvenMarking A fun _ _ _ _ _ _ => True) :
    LargeEvenMarking B fun _ _ _ _ _ _ => True := by
  obtain ⟨hA, lab, hlab, hraw⟩ := h
  have hAp : Group.IsPerfect A := ⟨hA⟩
  have hBp : Group.IsPerfect B := Group.IsPerfect.ofSurjective hf
  have hc : Subgroup.center A = ((QuotientGroup.mk' (Subgroup.center B)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hAp f hf hker]
  let e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))
  refine ⟨hBp.commutator_eq_top, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, -⟩
  exact ⟨hs, hna, e.symm.trans θ, trivial⟩

end Transport

section Implications

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggHypRestIVFlat_of_componentwise (h : GGHypRestIVComponentwise p E) :
    GGHypRestIVFlat p E := by
  intro x hx hx1 C hC
  obtain ⟨hq, hm⟩ := h x hx hx1 C hC
  obtain ⟨hCX, -, hcomp, -⟩ := hC
  set X : Subgroup W := Subgroup.centralizer ({x} : Set W) with hX
  set π : ↥X →* ↥X ⧸ LargeEvenPPrimeCore p ↥X :=
    QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X) with hπ
  let ψ : ↥C →* ↥((C.subgroupOf X).map π) :=
    (π.subgroupMap (C.subgroupOf X)).comp (Subgroup.subgroupOfEquivOfLe hCX).symm.toMonoidHom
  have hψ : Function.Surjective ψ :=
    (MonoidHom.subgroupMap_surjective π (C.subgroupOf X)).comp
      (Subgroup.subgroupOfEquivOfLe hCX).symm.surjective
  have hqn : CFSG.IsQuasisimple ↥C :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  have hbq : CFSG.IsQuasisimple ↥((C.subgroupOf X).map π) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hcomp.2.2
  have hker : ψ.ker ≤ Subgroup.center ↥C := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqn ψ.normal_ker with htop | hcen
    · exfalso
      have := CFSG.LocalCores.isQuasisimple_nontrivial hbq
      obtain ⟨a, b, hab⟩ := exists_pair_ne ↥((C.subgroupOf X).map π)
      obtain ⟨a', rfl⟩ := hψ a
      obtain ⟨b', rfl⟩ := hψ b
      have ha : ψ a' = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top a')
      have hb : ψ b' = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top b')
      exact hab (ha.trans hb.symm)
    · exact hcen
  exact largeEvenMarking_true_of_surjective_ker_le_center ψ hψ hker hm

end Implications

end CFSG.StandardType
