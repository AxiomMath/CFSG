module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeBasic

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem injective_of_locInj {V W : Type*} {Δ : SimpleGraph V} {Γ : SimpleGraph W}
    (hΔ : Δ.Connected) (hΓ : Γ.IsTree) (f : V → W)
    (hf : ∀ u v, Δ.Adj u v → Γ.Adj (f u) (f v))
    (hloc : ∀ u a b, Δ.Adj u a → Δ.Adj u b → f a = f b → a = b) : Function.Injective f := by
  classical
  intro v w hvw
  by_contra hne
  obtain ⟨p, hp, -⟩ := (hΔ v w).exists_path_of_dist
  have hpos : p.length ≠ 0 := fun h0 => hne (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  let P : Arc Γ p.length :=
    { vert := fun i => f (p.getVert i)
      adj := fun i hi => hf _ _ (p.adj_getVert_succ hi)
      nb := fun i hi h => by
        have h1 := hloc (p.getVert (i + 1)) (p.getVert i) (p.getVert (i + 2))
          (p.adj_getVert_succ (by omega)).symm (p.adj_getVert_succ (by omega)) h
        have := hp.getVert_injOn (show i ≤ p.length by omega) (show i + 2 ≤ p.length by omega) h1
        omega }
  have hd := Arc.dist_eq hΓ P p.length le_rfl
  have e0 : P.vert 0 = f v := by simp [P]
  have e1 : P.vert p.length = f w := by simp [P]
  rw [e0, e1, hvw, dist_self] at hd
  exact hpos hd.symm

end CFSG.Quasithin.Fan86
