module

public import CFSG.Quasithin.Background.P4GLCore
public import CFSG.Quasithin.Background.P4GLAut

public section

namespace CFSG.Quasithin.G11.P4GL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def UTm (m : ℕ) : Subgroup (Gm m) :=
  (unitriangular (m + 3) (ZMod 2)).map (slEquiv (m + 3)).toMonoidHom

theorem isUT_UTm (m : ℕ) : IsUT (UTm m) := by
  intro g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hg
    have hdet : (g : Mt m).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
      have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
      simpa using h2
    refine ⟨⟨(g : Mt m), hdet⟩, hg, ?_⟩
    apply Units.ext
    rfl

theorem exists_sylow_UTm (m : ℕ) : ∃ Q : Sylow 2 (Gm m), (Q : Subgroup (Gm m)) = UTm m := by
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := m + 3) (by omega)
  have hsurj : Function.Surjective (slEquiv (m + 3)).toMonoidHom :=
    (slEquiv (m + 3)).surjective
  refine ⟨Q.mapSurjective hsurj, ?_⟩
  show (Q : Subgroup _).map (slEquiv (m + 3)).toMonoidHom = UTm m
  rw [hQ]
  rfl

end CFSG.Quasithin.G11.P4GL
