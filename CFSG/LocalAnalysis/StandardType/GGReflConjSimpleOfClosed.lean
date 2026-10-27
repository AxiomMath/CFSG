module

public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
public import CFSG.LocalAnalysis.StandardType.GGTBWInputDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggReflConjSimple_of_reflClosed {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) {L : Subgroup G}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hRC : GGReflClosed (fun i : Λ => ggLin (p := p) ι (φ i))) :
    GGReflConjSimple p (ggAutomizer L Bs) φ := by
  unfold GGReflConjSimple
  rw [hAL]
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hmap : (Subgroup.closure (Set.range φ)).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ i)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]; rfl
  intro t ht hrefl
  have hr := (ggIsReflection_iff (p := p) ι t).mp hrefl
  have ht1 : ggLin (p := p) ι t ≠ 1 := by
    intro h1
    have hc := hr.2
    rw [h1] at hc
    have he : Nat.card {v : V // (1 : V ≃ₗ[ZMod p] V) v = v} = Nat.card V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun v => rfl)
    rw [he] at hc
    have hpos : 0 < Nat.card V := Nat.card_pos
    have : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hc)
    exact (Fact.out : p.Prime).one_lt.ne' this
  have htW : ggLin (p := p) ι t ∈
      Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ i)) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ ht
  obtain ⟨xv, fv, hfv, hlinv⟩ := exists_of_ggIsReflection ι hrefl
  obtain ⟨u, hu, i, hui⟩ := hRC _ htW hr.1 ht1 ⟨xv, fv, hlinv⟩
  rw [← hmap] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨w, hw, i, ggLin_injective (p := p) ι ?_⟩
  rw [hui, map_mul, map_mul, map_inv]

end CFSG.StandardType

end
