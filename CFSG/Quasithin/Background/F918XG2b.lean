module

public import CFSG.Quasithin.Vol2.Ch11SecAKDi
public import CFSG.Quasithin.Background.F918X1

public section

namespace CFSG.Quasithin.F918X

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.SecA.C10KH


theorem g2Natural_stableMod {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (h : G2Natural L ⊤ ⊥ n) : StableMod L ∧ Subgroup.center ↥L = ⊥ := by
  obtain ⟨K, _, _, hK, hR⟩ := h
  have hch : CharP K 2 := Vol2.KGNat.charP_two_of_card (by omega) hK
  obtain ⟨c, hc0, hc1⟩ := Vol2.KGNat.exists_ne_zero_ne_one (K := K) (by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    rw [hK]
    omega)
  have hG : quasithinG2 K = cayleyGroup K :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [hG, cayley_commutator_eq hc0 hc1]
  have hR' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes L ⊤ ⊥ := by
    rw [hc, ← hG]
    exact hR
  obtain ⟨π, e, he⟩ := exists_model_action
    (FFModel.zornQ_isActionModel ⁅quasithinG2 K, quasithinG2 K⁆ (g2D_le K))
    (FFC.zornQ_faithful _ (g2D_le K)) hR'
  refine ⟨stableMod_of_forall fun α => ?_, ?_⟩
  · have hα : α ∈ indH L := by
      rw [mem_indH_iff (g2QA K) π e he, indM_g2_eq_top hn hK]
      exact Subgroup.mem_top _
    obtain ⟨φ, hφ⟩ := hα
    exact mem_realized.mpr ⟨φ, fun l => (hφ l).symm⟩
  · have hZ : Subgroup.center (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam = ⊥ :=
      center_g2D_eq_bot hc hc0 hc1
    have h3 := Subgroup.map_center_eq π
    rw [hZ, Subgroup.map_bot] at h3
    exact h3.symm

theorem case4TwistBig_holds : Case4TwistBig := by
  intro V _ _ _ G L n hn _ hG2 hL
  subst hL
  obtain ⟨hstable, hZ⟩ := g2Natural_stableMod hn hG2
  exact ⟨hstable, Or.inl hZ⟩

end CFSG.Quasithin.F918X
