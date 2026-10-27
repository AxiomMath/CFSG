module

public import CFSG.Sporadic.Schreier.TitsStab
public import Certificates.Data.RuF45Geom

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RuF45

@[expose] noncomputable def genPerm (G : Array (Array ℕ)) (j : ℕ) : Equiv.Perm (Fin 1755) :=
  permOfArr 1755 G[j]!

theorem genH_mem {j : ℕ}
    (hj : j < 9) :
    genPerm titsHArrs j ∈ titsH := by
  have hsz : j < titsQH.strongCount := by
    show j < titsHArrs.size
    rw [titsHArrs_size]
    exact hj
  have h1 := titsQH.strong_get_mem_originalSubgroup titsQH_facts.1 ⟨j, hsz⟩
  rw [titsQH_facts.2.2.1] at h1
  have h2 : titsQH.strong.get ⟨j, hsz⟩ = genPerm titsHArrs j :=
    RawSchreierDatum.ofArrays_strong_get (j := ⟨j, hsz⟩)
  rw [h2] at h1
  exact h1

theorem genN_mem {j : ℕ}
    (hj : j < 10) : genPerm titsNArrs j ∈ titsN := by
  have hsz : j < titsQN.strongCount := by
    show j < titsNArrs.size
    rw [titsNArrs_size]
    exact hj
  have h1 := titsQN.strong_get_mem_originalSubgroup titsQN_facts.1 ⟨j, hsz⟩
  rw [titsQN_facts.2.2.1] at h1
  have h2 : titsQN.strong.get ⟨j, hsz⟩ = genPerm titsNArrs j :=
    RawSchreierDatum.ofArrays_strong_get (j := ⟨j, hsz⟩)
  rw [h2] at h1
  exact h1

theorem titsH_eq_closure :
    titsH = Subgroup.closure (genPerm titsHArrs '' Set.Iio 9) := by
  have e1 : titsQH.levelSubgroup 0 = titsQH.originalSubgroup :=
    titsQH.levelSubgroup_zero_eq_original titsQH_facts.1
  have e2 : titsQH.originalSubgroup = titsH := titsQH_facts.2.2.1
  have hset : {s | s ∈ titsQH.levelGenerators 0} = genPerm titsHArrs '' Set.Iio 9 := by
    ext g
    rw [Set.mem_ofPred_eq, RawSchreierDatum.levelGenerators_zero,
      schreier_vector_mem_toList_iff_get]
    constructor
    · rintro ⟨j, rfl⟩
      have hj : (j : ℕ) < 9 := by
        have := j.2
        change (j : ℕ) < titsHArrs.size at this
        rwa [titsHArrs_size] at this
      exact ⟨j, hj, (RawSchreierDatum.ofArrays_strong_get j).symm⟩
    · rintro ⟨j, hj, rfl⟩
      have hsz : j < titsQH.strongCount := by
        show j < titsHArrs.size
        rw [titsHArrs_size]
        exact hj
      exact ⟨⟨j, hsz⟩, RawSchreierDatum.ofArrays_strong_get ⟨j, hsz⟩⟩
  have e3 : titsQH.levelSubgroup 0 = Subgroup.closure (genPerm titsHArrs '' Set.Iio 9) := by
    unfold RawSchreierDatum.levelSubgroup
    rw [hset]
  exact e2.symm.trans (e1.symm.trans e3)

end CFSG.Quasithin.TitsGeo
