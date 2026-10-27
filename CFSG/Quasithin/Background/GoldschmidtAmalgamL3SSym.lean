module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SDih

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

theorem b5SymInput : B5SymInput.{u} := by
  intro D _ _ A B z V h hU hb p γ hcfg
  have hP0 := h.pair_of_symConfigFive hU hb hcfg
  obtain ⟨hp0, hp, -, -, -⟩ := hcfg
  have hw0 : Walk4 A B (p 1) (p 2) (p 3) (p 4) (p 5) :=
    ⟨hp.vtype_true_of_odd rfl hp0 (by omega) (by decide), hp.adj (i := 1) (by omega),
      hp.adj (i := 2) (by omega), hp.adj (i := 3) (by omega), hp.adj (i := 4) (by omega),
      hp.ne (i := 1) (j := 3) (by omega) (by omega), hp.ne (i := 2) (j := 4) (by omega)
        (by omega), hp.ne (i := 3) (j := 5) (by omega) (by omega)⟩
  refine h.false_of_pair_walk4 hb (fun s₀ s₁ s₂ s₃ s₄ hs => ?_)
  obtain ⟨g, g0, g1, g2, g3, g4⟩ := Walk4.exists_smul_of_card h hU hw0 hs
  have := h.pair_smul hP0 g
  rw [g0, g1, g2, g3, g4] at this
  exact this

end GoldAmL3

end F6

end CFSG.Quasithin
