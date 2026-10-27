module

public import CFSG.Quasithin.MS93.S46R468C1A
public import CFSG.Quasithin.MS93.S46R468B2

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem BadConf.relIndex_qv_zm (h464 : I464) (h465 : I465) (h466a : I466a)
    {c : Hyp46 M T L φ} {α α' : Vtx (puAmalgam c.pu.le)} (hB : BadConf c α α') :
    (Qv (puAmalgam c.pu.le) α).relIndex (ZM _ α') = Fintype.card F := by
  have hc := hB.crit
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α (geo _ α α' 1) := by
    have := adj_geo_crit c.b4 hc (i := 0) (by omega)
    rwa [geo_zero] at this
  obtain ⟨p₀, hp₀, hZp⟩ := hB.exists_center h464 h465 h466a
  have hp₀c := card_of_isPtOn h464 h465 c hc.1 hαβ hp₀
  have : Finite ↥p₀ := Nat.finite_of_card_ne_zero (by rw [hp₀c]; exact Fintype.card_ne_zero)
  have hle := relIndex_qv_le_of_commutator_mem h464 h465 h466a c hc.1 hαβ (P := p₀)
    (A := ZM _ α') (fun a ha => (hZp ha).1) fun a ha z hz => (mem_ptQ.mp (hZp ha).2).2.2 z hz
  rw [hp₀c] at hle
  refine le_antisymm hle ?_
  rw [← relIndex_zm_comm c.pu c.via c.pu.centHyp hc]
  rcases crit_type c.pu c.via c.pu.centHyp hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
  · rw [h]
    exact Nat.le_self_pow (by norm_num) _
  · rw [h]
  · rw [h]

end CFSG.Quasithin.MS93.S46R
