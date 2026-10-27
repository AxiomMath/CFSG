module

public import CFSG.Quasithin.MS93.S46R468Q4N
public import CFSG.Quasithin.MS93.S46R468Q4K
public import CFSG.Quasithin.MS93.S46R468C4
public import CFSG.Quasithin.MS93.S46R468N

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_other_pt (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {Q : Subgroup (puAmalgam c.pu.le).Universal}
    (hQ : IsPtOn (puAmalgam c.pu.le) x β Q) :
    ∃ R, IsPtOn (puAmalgam c.pu.le) x β R ∧ R ≠ Q := by
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨p, hpW, hp1, hQU, hQp⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hQ
  have hW2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ).1
  have hlt : p < fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) :=
    lt_of_le_of_ne hpW fun he => by rw [← he, hp1] at hW2; omega
  obtain ⟨w, hwW, hwp⟩ := IsConcreteLE.exists_of_lt hlt
  have hw0 : w ≠ 0 := fun h => hwp (h ▸ p.zero_mem)
  obtain ⟨R, hR, hRU, hRc⟩ := exists_isPtOn_span h464 h465 c hx hxβ hψs hψ hwW hw0
  refine ⟨R, hR, fun he => hwp ?_⟩
  have h1 := (S45.eq_iff_of_natVec_iff hψ hRU hQU hRc hQp).mp he
  rw [← h1]
  exact Submodule.mem_span_singleton_self w

theorem BadConf.false_of_four (h464 : I464) (h465 : I465) (h466a : I466a) {c : Hyp46 M T L φ}
    {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α') (hfar : FarNonDeg c α α')
    (hq : 4 ≤ Fintype.card F) : False := by
  have hc := hB.crit
  have hb4 := c.b4
  have hα := hc.1
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit hb4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  obtain ⟨δ₀, q₀, hδ₀, hq₀, hU⟩ := hB.exists_ptSub h464 h465 h466a hfar
  obtain ⟨P, hP, hne⟩ := exists_other_pt h464 h465 c hγ hβγ.symm hq₀
  obtain ⟨p, hp, hY⟩ :=
    exists_pencil_le_ptQ h464 h465 h466a c hα hαβ hγ hβγ.symm hP (hB.nondeg.1 _ hP)
  obtain ⟨ψ, hψs, hψU, hPc, hT⟩ := exists_coord_pt h464 h465 h466a c hγ hβγ.symm hP
  rcases hB.natural_pencil h464 h465 h466a hα hαβ hγ hβγ.symm hδ₀ hp hP hq₀ hne hY hU hψs hψU
      hPc hT with htriv | ⟨N, βv, hUN, hNY, -, hβker, hodd, hβeq⟩
  · exact hB.false_of_key h464 h465 h466a hγ hβγ.symm hP
      (key_of_trivial h464 h465 h466a c hγ hP hψs hψU hPc htriv)
  · exact hB.false_of_key h464 h465 h466a hγ hβγ.symm hP
      (key_of_natural h464 h465 h466a (c := c) hq hγ hβγ.symm hP hψs hψU hPc hT hUN hNY hβker
        hodd hβeq)

end CFSG.Quasithin.MS93.S46R
