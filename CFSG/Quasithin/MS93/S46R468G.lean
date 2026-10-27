module

public import CFSG.Quasithin.MS93.S46R468GM
public import CFSG.Quasithin.MS93.S46R468D
public import CFSG.Quasithin.MS93.S46R468Deg

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

@[expose] def S468DegN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
    ¬ ⁅Vv (puAmalgam c.pu.le) α, Vv _ α⁆ ≤ Uloc c.pu.le L α →
    (∀ α', IsCritical (puAmalgam c.pu.le) α α' → geo _ α α' 1 = β →
      ¬ S468Via (puAmalgam c.pu.le) α β (geo _ α α' 2) →
      ¬ NonDeg c α β (geo _ α α' 2) ∨ ¬ FarNonDeg c α α') →
    S468At (puAmalgam c.pu.le) α β

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem vv_comm_le_uloc_smul (c : Hyp46 M T L φ) {α : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hV : ⁅Vv (puAmalgam c.pu.le) α, Vv _ α⁆ ≤ Uloc c.pu.le L α) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) :
    ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ Uloc c.pu.le L x := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hα hx
  rw [show Vv (puAmalgam c.pu.le) (g • α) = (Vv _ α).map (MulAut.conj g).toMonoidHom from
    vi_smul _ g α 2, uloc_smul c.pu g α, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hV

theorem not_degW_of_comm_le (h43 : S43) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h467 : I467) (c : Hyp46 M T L φ)
    (hN : ∀ x, IsMVtx (puAmalgam c.pu.le) x →
      ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ Uloc c.pu.le L x)
    {α₀ β₀ : Vtx (puAmalgam c.pu.le)} (hbad : ¬ S468At (puAmalgam c.pu.le) α₀ β₀)
    (hα₀ : IsMVtx (puAmalgam c.pu.le) α₀) (hα₀β₀ : (puAmalgam c.pu.le).treeGraph.Adj α₀ β₀)
    {x x' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical (puAmalgam c.pu.le) x x') :
    ¬ DegW c x x' := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb4 := c.b4
  have hγ : IsMVtx (puAmalgam c.pu.le) (geo _ x x' 2) := isMVtx_geo_two' hb4 hc
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj (geo _ x x' 1) (geo _ x x' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  intro h
  apply h
  rw [← usup_geo_two_eq_of_comm_le h43 h464 h465 h466a h467 c hN hbad hα₀ hα₀β₀ hc]
  exact le_bot_iff.mp ((inf_le_inf_right _ (usup_le_uloc' c.pu hfull hγ hβγ.symm)).trans
    (uloc_inf_zloc c.pu hfull _).le)

theorem s468Deg_of_s468DegN (h43 : S43) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h467 : I467) (hN : S468DegN) : S468Deg := by
  intro G _ _ M T L F _ _ φ c α β hα hαβ hDeg
  by_cases hV : ⁅Vv (puAmalgam c.pu.le) α, Vv _ α⁆ ≤ Uloc c.pu.le L α
  · by_contra hbad
    have hN' : ∀ x, IsMVtx (puAmalgam c.pu.le) x →
        ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ Uloc c.pu.le L x :=
      fun x hx => vv_comm_le_uloc_smul c hα hV hx
    obtain ⟨α', hc, hg1, hbadV⟩ := exists_crit_of_not_s468At h43 h467 c hα hαβ hbad
    subst hg1
    obtain ⟨hnd, hfar⟩ := nonDeg_and_farNonDeg_of h464 h465 h467 c hc hbadV
      fun x x' hx => not_degW_of_comm_le h43 h464 h465 h466a h467 c hN' hbad hα hαβ hx
    exact (hDeg α' hc rfl hbadV).elim (· hnd) (· hfar)
  · exact hN G M T L F φ c α β hα hαβ hV hDeg

end CFSG.Quasithin.MS93.S46R
