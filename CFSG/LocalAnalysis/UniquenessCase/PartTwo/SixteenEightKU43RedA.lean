module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s16ku43_center_fixes_only_one {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (hirr : IsIrrOn H ⊤ ⊥) {z : MulAut W} (hz : z ∈ H) (hzc : ∀ h ∈ H, h * z = z * h)
    (hz1 : z ≠ 1) {w : W} (hw : z w = w) : w = 1 := by
  let C : Subgroup W :=
    { carrier := {u : W | z u = u}
      one_mem' := map_one z
      mul_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hstable : StableUnder H C := by
    intro h hh u hu
    change z (h u) = h u
    calc z (h u) = (z * h) u := rfl
      _ = (h * z) u := by rw [← hzc h hh]
      _ = h (z u) := rfl
      _ = h u := by
            have hu' : z u = u := hu
            rw [hu']
  rcases hirr.2.2.2 C hstable bot_le le_top with hC | hC
  · have hwC : w ∈ C := hw
    rw [hC] at hwC
    exact Subgroup.mem_bot.1 hwC
  · exfalso
    apply hz1
    refine MulEquiv.ext fun u => ?_
    show z u = u
    exact hC.ge (Subgroup.mem_top u)

theorem s16ku43_card_le_orbit_mul {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {w : W} (hw : w ≠ 1) :
    Nat.card ↥H ≤ (Nat.card W - 1) * Nat.card ↥(ptCent H w) := by
  classical
  have hcard : Nat.card ↥H =
      Nat.card (MulAction.orbit ↥H w) * Nat.card (MulAction.stabilizer ↥H w) := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥H w)
    rw [Nat.card_prod] at h
    exact h.symm
  have hstab : MulAction.stabilizer ↥H w = (ptCent H w).subgroupOf H := by
    ext h
    simp only [Subgroup.mem_subgroupOf, ptCent, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def, MulAut.smul_def]
    exact ⟨fun hh => ⟨h.2, hh⟩, fun hh => hh.2⟩
  have hstab_card : Nat.card (MulAction.stabilizer ↥H w) = Nat.card ↥(ptCent H w) := by
    rw [hstab]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : ptCent H w ≤ H)).toEquiv
  have hcompl : Nat.card {u : W // u ≠ 1} = Nat.card W - 1 := by
    haveI := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun u : W => u = 1),
      Fintype.card_subtype_eq (1 : W), ← Nat.card_eq_fintype_card]
  have horbit : Nat.card (MulAction.orbit ↥H w) ≤ Nat.card W - 1 := by
    have hsub : MulAction.orbit ↥H w ⊆ {u : W | u ≠ 1} := by
      intro u hu
      obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hu
      change (h : MulAut W) w ≠ 1
      intro h1
      have h1' : (h : MulAut W) w = 1 := by simpa using h1
      have h2 := congrArg (fun v => (h : MulAut W).symm v) h1'
      exact hw (by simpa using h2)
    have hmono := Nat.card_le_card_of_injective
      (fun x : MulAction.orbit ↥H w => (⟨x.1, hsub x.2⟩ : {u : W // u ≠ 1}))
      (fun x y hxy => Subtype.ext (congrArg (fun z : {u : W // u ≠ 1} => z.1) hxy))
    rw [hcompl] at hmono
    exact hmono
  calc Nat.card ↥H
      = Nat.card (MulAction.orbit ↥H w) * Nat.card (MulAction.stabilizer ↥H w) := hcard
    _ ≤ (Nat.card W - 1) * Nat.card (MulAction.stabilizer ↥H w) :=
        Nat.mul_le_mul_right _ horbit
    _ = (Nat.card W - 1) * Nat.card ↥(ptCent H w) := by rw [hstab_card]

theorem s16ku43_noncyclic_in_subgroup {W : Type} [CommGroup W] (X : Subgroup (MulAut W))
    {S : Type} [Group S] [Finite S] (ψ : ↥X →* S) (hψ : Function.Injective ψ)
    (hG : ∀ Y : Subgroup S, Y.index ≤ 1365 →
      ∃ B : Subgroup S, B ≤ Y ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B)
    (hidx : ψ.range.index ≤ 1365) :
    ∃ B : Subgroup (MulAut W), B ≤ X ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B := by
  obtain ⟨Bbar, hBbar_le, hBbar_p, hBbar_nc⟩ := hG ψ.range hidx
  let B₁ : Subgroup ↥X := Bbar.comap ψ
  have hmap : B₁.map ψ = Bbar := Subgroup.map_comap_eq_self hBbar_le
  have hB₁_p : IsPGroup 3 ↥B₁ := hBbar_p.comap_of_injective ψ hψ
  have hB₁_nc : ¬ IsCyclic ↥B₁ := by
    intro hc
    apply hBbar_nc
    have he : ↥B₁ ≃* ↥Bbar := hmap ▸ Subgroup.equivMapOfInjective B₁ ψ hψ
    exact (MulEquiv.isCyclic he).mp hc
  refine ⟨B₁.map X.subtype, Subgroup.map_subtype_le B₁, ?_, ?_⟩
  · exact hB₁_p.map X.subtype
  · intro hc
    exact hB₁_nc
      ((MulEquiv.isCyclic (Subgroup.equivMapOfInjective B₁ X.subtype
        X.subtype_injective)).mpr hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
