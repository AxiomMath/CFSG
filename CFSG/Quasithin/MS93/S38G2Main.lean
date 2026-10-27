module

public import CFSG.Quasithin.MS93.S38G2Ms23
public import CFSG.Quasithin.MS93.S38G2End
public import CFSG.Quasithin.MS93.S38EndStmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.H13
open scoped commutatorElement

namespace S38G

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem g2Hyp
    (hR : G2Rep h f φ) (hX : Xq M = Z0q M T)
    (hW : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      imM h.le (Uq M T L ⊓ Zq M L) ≤
        ⁅ZM (puAmalgam h.le) (baseA (puAmalgam h.le)), ZM (puAmalgam h.le) α'⁆)
    (hb : 2 < critDist (puAmalgam h.le)) :
    G2Hyp (puAmalgam h.le) (puTrans h.le L) (puTrans h.le (Uq M T L))
      (puTrans h.le (Uq M T L ⊓ Zq M L)) where
  h20 := h.hyp20
  cent := h.centHyp
  b4 := by
    obtain ⟨α, α', hc⟩ := exists_isCritical _ h.hyp20
    exact (hR.ms23_aSub hX hW hb hc).1
  fin := fun _ hγ => finite_stab h hγ
  lt_le := fun γ _ => puTrans_le_stab h.le L γ
  lt_nor := fun γ _ => stab_le_normalizer_puTrans h.le (l_normal h) γ
  lt_perf := fun _ hγ => lt_perf h hγ
  lt_sup := fun _ _ hγ hγρ => lt_sup h hγ hγρ
  lt_gen := fun _ _ hγ hγρ _ hx hxQ => h.puTrans_L_le_closure hγ hγρ hx hxQ
  ut_le := fun _ hγ => ut_le h hγ
  ut_nor := fun γ _ => stab_le_normalizer_puTrans h.le (uq_normal h) γ
  wt_eq := fun _ hγ => wt_eq h hγ
  zm_comm := fun _ hγ => zm_comm h hγ
  xm_eq := fun _ hγ => xm_eq h hX hγ
  off_cent := fun _ _ hc => hR.offCent hc
  off_fix := fun _ _ hc => hR.offFix hc
  r_le := fun _ _ hc => hR.rLe hc
  w_le_r := fun _ _ hc => wLeR h hW hc
  r_eq := fun _ _ hc => hR.rEq hW hc
  r_card := fun _ _ hc => hR.rCard hc
  off_idx := fun _ _ hc => hR.offIdx hc
  two_gen := fun _ _ hc => hR.twoGen hc
  a_nor := fun γ γ' hc g hg u hu hut => by
    have hN := (hR.ms23_aSub hX hW hb hc).2 hg
    have hA := (Subgroup.mem_normalizer_iff.mp hN u).mp ((mem_aSub h).mpr ⟨hu, hut⟩)
    exact (mem_aSub h).mp hA
  a_cent := fun γ γ' hc u hu hut => by
    have hA := (mem_aSub h).mpr ⟨hu, hut⟩
    exact Subgroup.le_centralizer_iff.mp (hR.lt_le_centralizer_aSub hX hW hb hc) hA
  comm_off := fun _ _ hγ hγρ => hR.commOff hγ hγρ
  hV := fun _ _ hc => hR.vv_not_le hb hc
  nat := fun _ hγ => hR.natHyp_at hγ

end G2Rep

end S38G

theorem s38G2_holds :
    S38G2 := by
  intro G _ _ M T L h _ _ hG2 hb
  obtain ⟨hX, -, ⟨_, hnat⟩, hV⟩ := hG2
  obtain ⟨f, φ, hR⟩ := S38G.PUHyp.exists_g2Rep h hnat
  exact (hR.g2Hyp hX (fun α' hc => (hV α' hc).2) hb).false

end CFSG.Quasithin.MS93
