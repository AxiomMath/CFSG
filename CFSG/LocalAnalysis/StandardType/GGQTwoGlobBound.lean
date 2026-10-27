module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData

public section

namespace CFSG.StandardType.QTwo

theorem qTwoGlobBnd_ainf_le_induced
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G) :
    ggAInf 3 B Bs x L D J ≤ ggInducedSubgroup ⊤ Bs := by
  rw [← ggAutomizer_eq ⊤ Bs]
  simp only [ggAInf]
  refine sup_le ?_ ?_
  · exact ggAutomizer_mono Bs le_top
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun _ => ?_
    exact ggAutomizer_mono Bs le_top

theorem qTwoGlobBnd_vx_ne_zero
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {m : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
    (hLM : QTwoLocalModel m Bs L x) (hx1 : x ≠ 1) :
    ι (Additive.ofMul (⟨x, hLM.mem⟩ : ↥Bs)) ≠ 0 := by
  intro h0
  have hzero : ι ((1 : ↥Bs) : Additive ↥Bs) = 0 := map_zero ι
  have hι : ι (⟨x, hLM.mem⟩ : ↥Bs) = ι (1 : ↥Bs) := h0.trans hzero.symm
  have h1 : (⟨x, hLM.mem⟩ : ↥Bs) = 1 := ι.injective hι
  exact hx1 (congrArg Subtype.val h1)

theorem qTwoGlobBnd_actionCard_le
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}
    {m : ℕ} (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ) :
    Nat.card Abar ≤ 3 ^ Module.finrank (ZMod 3) U * 2 * m.factorial := by
  classical
  let A : Type := ↥(ggAInf 3 B Bs x L D J)
  let b0 : ↥Bs := ⟨x, hLM.mem⟩
  letI : MulAction A ↥Bs :=
    MulAction.compHom ↥Bs (Subgroup.subtype (ggAInf 3 B Bs x L D J))
  haveI hfinV : Finite V := Finite.of_injective (⇑ι.symm) ι.symm.injective
  haveI hfinU : Finite ↥U := Subtype.finite
  haveI hfinUmod : Module.Finite (ZMod 3) ↥U := Module.Finite.of_finite
  haveI hfinBs : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI hfinMulAut : Fintype (MulAut ↥Bs) :=
    Fintype.ofInjective (fun e : MulAut ↥Bs => (e : ↥Bs → ↥Bs))
      (fun a b h => MulEquiv.ext (fun y => congrArg (fun f : ↥Bs → ↥Bs => f y) h))
  haveI hfinA : Fintype A := Fintype.ofFinite A
  haveI hfinOrb : Fintype (MulAction.orbit A b0) := Fintype.ofFinite _
  haveI hfinStab : Fintype (MulAction.stabilizer A b0) := Fintype.ofFinite _
  have hcardU : Nat.card ↥U = 3 ^ Module.finrank (ZMod 3) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ↥U), Nat.card_zmod]
  have hOS :
      Nat.card (MulAction.orbit A b0) * Nat.card (MulAction.stabilizer A b0) = Nat.card A := by
    rw [Nat.card_eq_fintype_card (α := MulAction.orbit A b0),
      Nat.card_eq_fintype_card (α := MulAction.stabilizer A b0),
      Nat.card_eq_fintype_card (α := A)]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group A b0
  have horbit : Nat.card (MulAction.orbit A b0) ≤ Nat.card ↥U := by
    let f : MulAction.orbit A b0 → ↥U := fun y =>
      ⟨ι y.1 - ι (Additive.ofMul b0), by
        obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp y.2
        have hdiff :
            ι y.1 - ι (Additive.ofMul b0) =
              ggLin (p := 3) ι (a : MulAut ↥Bs) (ι (Additive.ofMul b0)) -
                ι (Additive.ofMul b0) := by
          rw [← ha, ggLin_apply_ofMul]
          rfl
        rw [hdiff]
        exact hD.2.2.2.2.1 (a : MulAut ↥Bs) a.2 (ι (Additive.ofMul b0))⟩
    refine Nat.card_le_card_of_injective f ?_
    intro y1 y2 h
    have hz : ι y1.1 - ι (Additive.ofMul b0) =
        ι y2.1 - ι (Additive.ofMul b0) := congrArg Subtype.val h
    have hz' : ι y1.1 = ι y2.1 := by
      have := congrArg (fun z : V => z + ι (Additive.ofMul b0)) hz
      simpa using this
    exact Subtype.ext (ι.injective hz')
  have hstab : Nat.card (MulAction.stabilizer A b0) ≤
      Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} := by
    let f : MulAction.stabilizer A b0 →
        {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} := fun s =>
      ⟨(s.1 : MulAut ↥Bs), qTwoGlobBnd_ainf_le_induced B Bs L D J x s.1.2, s.2⟩
    refine Nat.card_le_card_of_injective f ?_
    intro s t h
    have h1 : (s.1 : MulAut ↥Bs) = (t.1 : MulAut ↥Bs) :=
      congrArg (fun z : {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} =>
        (z : MulAut ↥Bs)) h
    exact Subtype.ext (Subtype.ext h1)
  have hstab' : Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} ≤
      2 * m.factorial := hLM.stab
  have hA : Nat.card A ≤ 3 ^ Module.finrank (ZMod 3) U * (2 * m.factorial) := by
    rw [← hOS]
    exact Nat.mul_le_mul (hcardU ▸ horbit) (le_trans hstab hstab')
  have hcard : Nat.card Abar = Nat.card A := (Nat.card_congr ρ.toEquiv).symm
  calc
    Nat.card Abar = Nat.card A := hcard
    _ ≤ 3 ^ Module.finrank (ZMod 3) U * (2 * m.factorial) := hA
    _ = 3 ^ Module.finrank (ZMod 3) U * 2 * m.factorial := by ring

theorem qTwoGlobBnd_stab_le
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}
    {m : ℕ} (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (u : ↥U) (hu : (u : V) = ι (Additive.ofMul (⟨x, hLM.mem⟩ : ↥Bs))) :
    Nat.card {g : ↥Abar // ((g : ↥U ≃ₗ[ZMod 3] ↥U)) u = u} ≤ 2 * m.factorial := by
  classical
  let b0 : ↥Bs := ⟨x, hLM.mem⟩
  haveI hfinBs : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI hfinMulAut : Fintype (MulAut ↥Bs) :=
    Fintype.ofInjective (fun e : MulAut ↥Bs => (e : ↥Bs → ↥Bs))
      (fun a b h => MulEquiv.ext (fun y => congrArg (fun f : ↥Bs → ↥Bs => f y) h))
  have hfinTarget : Fintype {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} :=
    Fintype.ofFinite _
  have hfix : ∀ g : {g : ↥Abar // ((g : ↥U ≃ₗ[ZMod 3] ↥U)) u = u},
      (((ρ.symm g.1 : ↥(ggAInf 3 B Bs x L D J)) : MulAut ↥Bs) b0 = b0) := by
    intro g
    have hres := hD.2.2.2.1 (ρ.symm g.1) u
    simp only [MulEquiv.apply_symm_apply] at hres
    have hgu : ((g.1 : ↥Abar) : ↥U ≃ₗ[ZMod 3] ↥U) u = u := g.2
    rw [hgu, hu] at hres
    exact (ggLin_fix_iff (p := 3) ι
      ((ρ.symm g.1 : ↥(ggAInf 3 B Bs x L D J)) : MulAut ↥Bs) b0).mpr hres.symm
  let f : {g : ↥Abar // ((g : ↥U ≃ₗ[ZMod 3] ↥U)) u = u} →
      {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} := fun g =>
    ⟨((ρ.symm g.1 : ↥(ggAInf 3 B Bs x L D J)) : MulAut ↥Bs),
      qTwoGlobBnd_ainf_le_induced B Bs L D J x (ρ.symm g.1).2, hfix g⟩
  have hstab : Nat.card {g : ↥Abar // ((g : ↥U ≃ₗ[ZMod 3] ↥U)) u = u} ≤
      Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} := by
    refine Nat.card_le_card_of_injective f ?_
    intro g1 g2 h
    have h1 : ((ρ.symm g1.1 : ↥(ggAInf 3 B Bs x L D J)) : MulAut ↥Bs) =
        ((ρ.symm g2.1 : ↥(ggAInf 3 B Bs x L D J)) : MulAut ↥Bs) :=
      congrArg (fun z : {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} =>
        (z : MulAut ↥Bs)) h
    have h2 : (ρ.symm g1.1 : ↥(ggAInf 3 B Bs x L D J)) =
        (ρ.symm g2.1 : ↥(ggAInf 3 B Bs x L D J)) := Subtype.ext h1
    have h3 : g1.1 = g2.1 := by
      have := congrArg (fun a => ρ a) h2
      simpa using this
    exact Subtype.ext h3
  exact le_trans hstab hLM.stab

end CFSG.StandardType.QTwo

end
