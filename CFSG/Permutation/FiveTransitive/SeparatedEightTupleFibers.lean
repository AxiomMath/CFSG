module

public import CFSG.Permutation.FiveTransitive.FourDoubleTwoFiber
public import CFSG.Permutation.FiveTransitive.NormalizedOrbitFamilies

public section

namespace CFSG

namespace FiveTransitive.SeparatedEightTupleFibers

open MulAction Equiv CyclePatternRoots OyamaFourFiberGeometry

variable {G X : Type*} [Group G] [MulAction G X] [Finite X]

theorem exists_fibers (b : Fin 4 ↪ X) (F : Set X) (u v w : X)
    (hF : F = Set.range b ∪ {u,v}) (hu : u ∉ Set.range b) (hv : v ∉ Set.range b)
    (hvu : v ∉ orbit (stabilizer G b) u)
    (huCard : 1 < Nat.card (orbit (stabilizer G b) u))
    (hvCard : 1 < Nat.card (orbit (stabilizer G b) v))
    (hw : w ∉ Set.range b ∪ orbit (stabilizer G b) u ∪ orbit (stabilizer G b) v)
    (a : G) (ha : orderOf a = 4)
    (hbase : ∀ i, a • b i = b (CyclePatternFinite.doubleTwo i))
    (hfix : fixedBy X a = F \ Set.range b) (hsquare : fixedBy X (a ^ 2) = F) :
    ∃ e : Fin 3 → Fiber (G := G) b,
      ∀ i j : Fin 3, i ≠ j → ∀ c d : Bool,
        ¬ orbitRel (stabilizer G b) X (cycleTuple b (e i) (if c then 1 else 0))
          (cycleTuple b (e j) (if d then 1 else 0)) := by
  have hau : a • u = u := by
    change u ∈ fixedBy X a
    rw [hfix,hF]
    exact ⟨by simp,hu⟩
  have hav : a • v = v := by
    change v ∈ fixedBy X a
    rw [hfix,hF]
    exact ⟨by simp,hv⟩
  have hnormal := NormalizedOrbitFamilies.normalizes_base b a CyclePatternFinite.doubleTwo hbase
  have hpointwise : ∀ (h : stabilizer G b) (x : X), x ∈ Set.range b → h • x = x := by
    intro h x hx
    obtain ⟨i,rfl⟩ := hx
    exact DFunLike.congr_fun h.property i
  obtain ⟨z,hz,hsep⟩ := NormalizedOrbitFamilies.exists_family
    (stabilizer G b) (Set.range b) F u v w hpointwise hF hu hv hvu huCard hvCard hw a hnormal hau hav
  have ha4 : a ^ 4 = 1 := by rw [← ha,pow_orderOf_eq_one]
  let roots : Fin 3 → FourRoot (toPerm a : Perm X) := fun i =>
    FourDoubleTwoFiber.rootOutside a ha4 F hsquare (z i) (hz i)
  let e : Fin 3 → Fiber (G := G) b := fun i => FourDoubleTwoFiber.ofRoot b a hbase (roots i)
  have he (i : Fin 3) (c : Bool) : cycleTuple b (e i) (if c then 1 else 0) =
      (if c then a • z i else z i) := by
    cases c <;> rfl
  refine ⟨e,?_⟩
  intro i j hij c d
  rw [he,he]
  exact hsep i j hij c d

end FiveTransitive.SeparatedEightTupleFibers

end CFSG
