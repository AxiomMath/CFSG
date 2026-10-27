
module

public import CFSG.Quasithin.Recognition.CertTitsSimpleInputs

@[expose] public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] titsPairO titsPairStrong titsGens titsStrong

noncomputable def unitsClosurePairEquiv {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (f g : Function.End (Fin n)) (hf : ⇑σ = f) (hg : ⇑τ = g) :
    (Submonoid.closure ({f, g} : Set (Function.End (Fin n))))ˣ ≃*
      Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin n))) := by
  subst hf hg
  have : Finite (Function.End (Fin n)) := inferInstanceAs (Finite (Fin n → Fin n))
  have hmap : (Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin n)))).map
      Equiv.Perm.equivUnitsEnd.toMonoidHom =
      Subgroup.closure {Equiv.Perm.equivUnitsEnd σ, Equiv.Perm.equivUnitsEnd τ} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  exact (CFSG.Blueprint.NativeSporadic.unitSeedEquiv (Equiv.Perm.equivUnitsEnd σ)
    (Equiv.Perm.equivUnitsEnd τ)).trans
    ((MulEquiv.subgroupCongr hmap.symm).trans (Equiv.Perm.equivUnitsEnd.subgroupMap _).symm)

private theorem titsPairO_size : titsPairO.size = 2 := by simp [titsPairO]

private theorem titsPairO_zero : titsPairO[0]! = titsA := by simp [titsPairO]

private theorem titsPairO_one : titsPairO[1]! = titsB := by simp [titsPairO]

private theorem titsGens_zero' : titsGens[0]! = titsArray CFSG.Open.quasithinTitsData1 := by
  simp [titsGens]

private theorem titsGens_one' : titsGens[1]! = titsArray CFSG.Open.quasithinTitsData2 := by
  simp [titsGens]

private theorem titsGens_size' : titsGens.size = 2 := by simp [titsGens]

end CFSG.Quasithin
