module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen

public section

namespace CFSG.StandardType.QTwo

theorem qTwo_bar_weylConnGen
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs)
    (hW : GGWeylReflectionGroup p A) :
    GGLinConnGen (A.map (ggLin (p := p) ι)) := by
  exact ggLinConnGen_of_weyl hp2 ι hNT
    (show A ≤ Subgroup.closure (ggInduced ⊤ Bs) from hA) hW

private lemma qTwoGBA_big
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) :
    (⨆ (y : G) (K : Subgroup G) (_ : GGNbr 3 B x D J y K),
        (ggAutomizer K Bs).map (ggLin (p := 3) ι)) =
      (⨆ (q : {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2}),
        (ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι)) := by
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
    exact le_iSup (fun q : {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2} =>
      (ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι)) ⟨(y, K), h⟩
  · refine iSup_le fun q => ?_
    exact le_iSup_of_le q.1.1 (le_iSup_of_le q.1.2 (le_iSup_of_le q.2 le_rfl))

private lemma qTwoGBA_sup_iSup
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {α : Type}
    (AL : Subgroup (V ≃ₗ[ZMod 3] V)) (AK : α → Subgroup (V ≃ₗ[ZMod 3] V)) :
    AL ⊔ (⨆ q : α, (AL ⊔ AK q)) = AL ⊔ ⨆ q : α, AK q := by
  apply le_antisymm
  · refine sup_le le_sup_left (iSup_le fun q => ?_)
    exact sup_le le_sup_left (le_sup_of_le_right (le_iSup AK q))
  · refine sup_le le_sup_left (iSup_le fun q => ?_)
    exact le_sup_of_le_right (le_trans le_sup_right (le_iSup (fun q => AL ⊔ AK q) q))

theorem qTwo_bar_iSup_eq
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) :
    (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) ι) =
      (⨆ X : Option {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2},
        match X with
        | none => (ggAutomizer L Bs).map (ggLin (p := 3) ι)
        | some q => (ggAutomizer L Bs ⊔ ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι)) := by
  have hbig := qTwoGBA_big B Bs L D J x ι
  calc
    (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) ι)
        = (ggAutomizer L Bs).map (ggLin (p := 3) ι) ⊔
            (⨆ (y : G) (K : Subgroup G) (_ : GGNbr 3 B x D J y K),
              (ggAutomizer K Bs).map (ggLin (p := 3) ι)) := by
          simp only [ggAInf, Subgroup.map_sup, Subgroup.map_iSup]
    _ = (ggAutomizer L Bs).map (ggLin (p := 3) ι) ⊔
            (⨆ (q : {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2}),
              (ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι)) :=
          congrArg (fun S => (ggAutomizer L Bs).map (ggLin (p := 3) ι) ⊔ S) hbig
    _ = (⨆ X : Option {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2},
          match X with
          | none => (ggAutomizer L Bs).map (ggLin (p := 3) ι)
          | some q => (ggAutomizer L Bs ⊔ ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι)) := by
          rw [iSup_option]
          simp only [Subgroup.map_sup]
          exact (qTwoGBA_sup_iSup ((ggAutomizer L Bs).map (ggLin (p := 3) ι))
            (fun q : {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2} =>
              (ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι))).symm

theorem qTwo_bar_fix
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1) :
    ggLinFix (qTwoBarA B Bs L D J x ι : Set (V ≃ₗ[ZMod 3] V)) = ⊥ := by
  change ggLinFix (((ggAInf 3 B Bs x L D J).map (ggLin (p := 3) ι) :
    Subgroup (V ≃ₗ[ZMod 3] V)) : Set (V ≃ₗ[ZMod 3] V)) = ⊥
  exact ggLinFix_map_eq_bot (p := 3) ι (ggAInf 3 B Bs x L D J) hC

private lemma qTwoGBA_ainf_le_induced
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G) :
    ggAInf 3 B Bs x L D J ≤ ggInducedSubgroup ⊤ Bs := by
  rw [← ggAutomizer_eq ⊤ Bs]
  simp only [ggAInf]
  refine sup_le ?_ ?_
  · exact ggAutomizer_mono Bs le_top
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun _ => ?_
    exact ggAutomizer_mono Bs le_top

theorem qTwo_bar_notr
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hNT : GGNoTransvection 3 Bs)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ qTwoBarA B Bs L D J x ι) :
    g ≠ 1 → ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
  intro _ h
  change g ∈ (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) ι) at hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  have htr : GGIsTransvection 3 φ := (ggIsTransvection_iff_ggLin (p := 3) ι φ).mpr h
  exact hNT φ (qTwoGBA_ainf_le_induced B Bs L D J x hφ) htr

end CFSG.StandardType.QTwo

end
