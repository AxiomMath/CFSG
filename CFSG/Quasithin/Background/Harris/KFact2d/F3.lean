module

public import CFSG.Quasithin.Background.Harris.KFact2d.F3L3
public import CFSG.Quasithin.Background.Harris.KFact2d.F3U3
public import CFSG.Quasithin.Background.Harris.KFact2d.F0

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

theorem fix_of_normalizes {X : Type} [Group X] {S : Subgroup X} (hZ : Nat.card ↥(E2P.zOf S) = 2)
    {u : X} (hu : u ∈ Subgroup.normalizer (S : Set X)) : u ∈ Subgroup.centralizer (E2P.zOf S : Set X) := by
  have hmem : ∀ z ∈ E2P.zOf S, u * z * u⁻¹ ∈ E2P.zOf S := by
    intro z hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp hu z).1 hz.1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : u⁻¹ * s * u ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hu) s).1 hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hs'
    calc s * (u * z * u⁻¹) = u * ((u⁻¹ * s * u) * z) * u⁻¹ := by group
      _ = u * (z * (u⁻¹ * s * u)) * u⁻¹ := by rw [h1]
      _ = (u * z * u⁻¹) * s := by group
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  by_cases hz1 : z = 1
  · simp [hz1]
  · have hw := hmem z hz
    have hone : u * z * u⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
    have hw' : (⟨u * z * u⁻¹, hw⟩ : ↥(E2P.zOf S)) ≠ 1 := fun h => hone (congrArg Subtype.val h)
    have hz' : (⟨z, hz⟩ : ↥(E2P.zOf S)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp hZ
    have hm : ∀ t : ↥(E2P.zOf S), t = x ∨ t = y := fun t => by
      have : t ∈ ({x, y} : Set ↥(E2P.zOf S)) := by rw [hset]; trivial
      simpa using this
    have heq : (⟨u * z * u⁻¹, hw⟩ : ↥(E2P.zOf S)) = ⟨z, hz⟩ := by
      rcases hm 1 with h1 | h1 <;> rcases hm ⟨u * z * u⁻¹, hw⟩ with h2 | h2 <;>
        rcases hm ⟨z, hz⟩ with h3 | h3 <;> simp_all
    have := congrArg Subtype.val heq
    simp only at this
    calc z * u = (u * z * u⁻¹) * u := by rw [this]
      _ = u * z := by group

theorem f3_holds :
    F3Stmt := by
  intro X _ _ K S p hp hp2 hK hKn hC hS u huu huK huN b hb hodd
  haveI : Fact p.Prime := ⟨hp⟩
  have huz := fix_of_normalizes (f0_holds X K S p hp hp2 hK hS) huN
  rcases hK with ⟨hp4, hL⟩ | ⟨hp4, hL⟩
  · exact f3_psu hp4 hL hS hKn hC huu huK huz b hb hodd
  · exact f3_psl hp4 hL hS hKn hC huu huK huz b hb hodd

end CFSG.Quasithin.Background.Harris.KFact2d
