module

public import CFSG.Monster.B.TwoA.Amalgam.DeckCentralizer
public import CFSG.Monster.B.TwoA.Amalgam.DeckTriv
public import CFSG.Monster.B.TwoA.Amalgam.DeckOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem coverK_eq_bot :
    coverK = ⊥ := by
  obtain ⟨⟨δ, hδ, hadj, -⟩, -, -, -, hρ, -⟩ := short_F4_universal_building_cover
  have ha : chamberCS.coverProj baseChamber (chamberCS.coverBase baseChamber) = baseChamber :=
    coverProj_coverBase
  obtain ⟨-, -, -, -, -, -, ⟨θ₁, -, hθ₁, -⟩, ⟨θ₄, -, hθ₄, -⟩⟩ :=
    short_F4_lifted_parabolic_stabilizers _ ha
  obtain ⟨-, -, -, hU, hO⟩ := short_F4_deck_centralizer_classical_images _ ha θ₁ hθ₁ θ₄ hθ₄
  obtain ⟨φ₁, hφ₁s, hφ₁⟩ := exists_surj_liftParabolic ha 0
  obtain ⟨φ₄, hφ₄s, hφ₄⟩ := exists_surj_liftParabolic ha 3
  refine deck_trivial_of chamberCS_connected hδ hadj
    (fun J g h => mem_residue_chamberCS_iff J g h) ha hφ₁s
    (fun g c => (congrArg (fun h : chamberCS.typeAut => (h : Equiv.Perm Chamber) c)
      (hφ₁ g)).trans (hρ _ c)) (fun g => hθ₁ _ g (hφ₁ g)) hφ₄s
    (fun g c => (congrArg (fun h : chamberCS.typeAut => (h : Equiv.Perm Chamber) c)
      (hφ₄ g)).trans (hρ _ c)) (fun g => hθ₄ _ g (hφ₄ g))
    (T := ((deckCent coverHt coverK ⊓
      liftBorel chamberCS chamberCS_adj_iff (chamberCS.coverBase baseChamber) :
        Subgroup (chamberCS.LiftPair baseChamber)) : Set (chamberCS.LiftPair baseChamber)))
    (fun t ht => ?_) (fun t ht k hk => ?_) (fun u hu => ?_) (fun d hd => ?_)
  · exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ht).2).2
  · exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ht).1).2 k hk
  · obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.1 (hU hu)
    exact ⟨z, Subgroup.mem_subgroupOf.1 hz, hzu⟩
  · obtain ⟨z, hz, hzd⟩ := Subgroup.mem_map.1 (hO hd)
    exact ⟨z, Subgroup.mem_subgroupOf.1 hz, hzd⟩

theorem short_F4_deck_triviality_and_native_order :
    coverK = ⊥ ∧
      Function.Bijective (chamberCS.coverProj baseChamber) ∧
      (∀ (i : Fin Tag.F4.rank) (A B : chamberCS.Cover baseChamber),
        (chamberCS.universalCover baseChamber).adj i A B ↔
          chamberCS.adj i (chamberCS.coverProj baseChamber A)
            (chamberCS.coverProj baseChamber B)) ∧
      Finite Chamber ∧
      (∃ δ : Chamber → Chamber → WeylGroup .F4,
        IsWeylDistanceBuilding (coxeterSystem .F4) δ ∧
        (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
          chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) ∧
        ∀ (i : Fin Tag.F4.rank) (x : Chamber),
          (panel (coxeterSystem .F4) δ i x).encard = if (i : ℕ) < 2 then 3 else 5) ∧
      Nat.card Chamber = 371231385525 ∧
      Nonempty (Eam ⧸ Subgroup.zpowers cE' ≃* coverH) ∧
      Nat.card coverH = 153064959367549707878400 ∧
      Nat.card Eam = 306129918735099415756800 ∧
      ((Pc 0).subgroupOf Eam).index = 3968055 := by
  have hK := coverK_eq_bot
  obtain ⟨⟨δ, hδ, hadj, -⟩, -, -, hcard, -, -, hc, hH, -, -, -, -, -, -, hEK, hPK⟩ :=
    short_F4_universal_building_cover
  obtain ⟨h1, h2, ⟨δX, hδX, hadjX⟩, h4, h5, h6, h7⟩ :=
    native_order_of_pi2_eq_bot chamberCS_connected hK hδ hadj hcard hEK hPK hc hH
  refine ⟨hK, h1, h2, Nat.finite_of_card_ne_zero (by rw [h4]; norm_num),
    ⟨δX, hδX, hadjX, fun i x => ?_⟩, h4, hH, h7, h5, h6⟩
  have hpan : panel (coxeterSystem .F4) δX i x = chamberCS.residue {i} x := by
    ext y
    rw [mem_panel_iff hδX, mem_residue_singleton, hadjX]
  rw [hpan]
  exact chamberCS_encard_panel i x

end CFSG.Monster.B.TwoA.Amalgam
