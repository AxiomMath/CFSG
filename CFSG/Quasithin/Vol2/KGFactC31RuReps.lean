module

public import CFSG.Quasithin.Vol2.KGFactC31RuGens

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native

@[expose] noncomputable def abG (w : List ℤ) : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] w

@[expose] noncomputable def repsZG : List (Equiv.Perm (Fin 4060)) :=
  hWordsZ.map (fun w => abG w * ruZ * (abG w)⁻¹) ++ otherZW.map wG

@[expose] noncomputable def repsAG : List (Equiv.Perm (Fin 4060)) :=
  hWordsA.map (fun w => abG w * ruA0 * (abG w)⁻¹) ++ otherAW.map abG

theorem abG_mem (w : List ℤ) : abG w ∈ ruP := evalSigned_ab_mem w

theorem repsZG_mem : ∀ r ∈ repsZG, r ∈ ruP := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact ruP.mul_mem (ruP.mul_mem (abG_mem w) ruZ_mem) (ruP.inv_mem (abG_mem w))
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact wG_mem w

theorem repsAG_mem : ∀ r ∈ repsAG, r ∈ ruP := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact ruP.mul_mem (ruP.mul_mem (abG_mem w) ruA0_mem) (ruP.inv_mem (abG_mem w))
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact abG_mem w

end CFSG.Quasithin.KGC31.Ru

end
