module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_15_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# proposition_12_15_c
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
private theorem CFSG.section12_sylow_inf_comm {M N : Subgroup G} {p : Nat.Primes}
    (R : Sylow p.val (M ⊓ N : Subgroup G)) :
    ∃ R' : Sylow p.val (N ⊓ M : Subgroup G),
      section10AmbientSylowSubgroup (N ⊓ M) R' =
        section10AmbientSylowSubgroup (M ⊓ N) R := by
  classical
  have : Fact (Nat.Prime p.val) := ⟨p.property⟩
  let e : (M ⊓ N : Subgroup G) ≃* (N ⊓ M : Subgroup G) :=
    MulEquiv.subgroupCongr (by rw [inf_comm])
  let Rsub : Subgroup (N ⊓ M : Subgroup G) :=
    (R : Subgroup (M ⊓ N : Subgroup G)).map e.toMonoidHom
  have hcard_Rsub :
      Nat.card Rsub = p.val ^ Nat.factorization (Nat.card (N ⊓ M : Subgroup G)) p.val := by
    have hmap : Nat.card Rsub = Nat.card (R : Subgroup (M ⊓ N : Subgroup G)) := by
      simpa [Rsub] using
        Subgroup.card_map_of_injective (K := (R : Subgroup (M ⊓ N : Subgroup G)))
          (f := e.toMonoidHom) e.injective
    have hcard_inf :
        Nat.card (M ⊓ N : Subgroup G) = Nat.card (N ⊓ M : Subgroup G) :=
      Nat.card_congr e.toEquiv
    rw [hmap, Sylow.card_eq_multiplicity R, hcard_inf]
  let R' : Sylow p.val (N ⊓ M : Subgroup G) := Sylow.ofCard Rsub hcard_Rsub
  refine ⟨R', ?_⟩
  ext x
  constructor
  · intro hx
    change x ∈ (R' : Subgroup (N ⊓ M : Subgroup G)).map (N ⊓ M : Subgroup G).subtype at hx
    change x ∈ Rsub.map (N ⊓ M : Subgroup G).subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    change y ∈ Rsub at hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hyz⟩
    exact Subgroup.mem_map.mpr ⟨z, hz, by
      calc
        (z : G) = (e z : G) := by rfl
        _ = (y : G) := congrArg Subtype.val hyz⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    change ((z : (M ⊓ N : Subgroup G)) : G) ∈
      (R' : Subgroup (N ⊓ M : Subgroup G)).map (N ⊓ M : Subgroup G).subtype
    change ((z : (M ⊓ N : Subgroup G)) : G) ∈
      Rsub.map (N ⊓ M : Subgroup G).subtype
    refine Subgroup.mem_map.mpr ?_
    refine ⟨e z, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem e.toMonoidHom hz
    · rfl

omit [IsMinCE G] in
private theorem CFSG.section12_exists_sylow_left_eq_inf_sylow_comm
    {M N : Subgroup G} {p : Nat.Primes}
    (S : Sylow p.val (M ⊓ N : Subgroup G))
    (hnorm : Subgroup.normalizer
        (section10AmbientSylowSubgroup (M ⊓ N) S : Set G) ≤ M) :
    ∃ P : Sylow p.val N,
      section10AmbientSylowSubgroup N P =
        section10AmbientSylowSubgroup (M ⊓ N) S := by
  classical
  have : Fact (Nat.Prime p.val) := ⟨p.property⟩
  rcases section12_sylow_inf_comm (M := M) (N := N) (p := p) S with ⟨S', hS'⟩
  have hnorm10' :
      Subgroup.normalizer
          (section10AmbientSylowSubgroup (N ⊓ M) S' : Set G) ≤ M := by
    rw [hS']
    exact hnorm
  have hnorm' :
      Subgroup.normalizer
          (section8SubgroupInAmbient (S' : Subgroup (N ⊓ M : Subgroup G)) : Set G) ≤ M := by
    simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hnorm10'
  rcases section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le
      (G := G) (p := p.val) (M := M) (N := N) S' hnorm' with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  calc
    section10AmbientSylowSubgroup N P = section10AmbientSylowSubgroup (N ⊓ M) S' := by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hP
    _ = section10AmbientSylowSubgroup (M ⊓ N) S := hS'

/-- Proposition 12.15(c). -/
public theorem CFSG.proposition_12_15_c
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S) :
    section12SylowSubgroupIn q (section10AmbientSylowSubgroup (M ⊓ Mstar) S) Mstar := by
  classical
  have hnorm :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤ M :=
    proposition_12_15_b (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  exact section12_exists_sylow_left_eq_inf_sylow_comm
    (M := M) (N := Mstar) (p := q) S hnorm

end Section12
