module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T1Core
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T1

open S35.Std S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem step1 (hS : Sit H M S) (_hII : CaseII H M) (nbt : NbarThat H M) (rc : RCent H M)
    (rkz : RkZvEq H M) : Step1 H M := by
  intro β α' m γ' hp hb htr hV hW hWm δ l ρ hδ hl hρ hne
  have h := arc_main hS hp hb htr hV hW hWm nbt rc rkz
  obtain ⟨-, hγ5, hne', -, -⟩ := back_facts hp hb
  obtain ⟨g, hg1, hg2, hg3⟩ :=
    arc_trans hS hγ5 (mem_nbrs_symm.mp hb.2.1) hb.1 hne'.symm hδ hl hρ hne
  have := (arcFull_smul g γ' m α').mpr h
  rw [hg1, hg2, hg3] at this
  exact this

end S35.T1

end F53.Stellmacher

end CFSG.Quasithin
