module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobBar
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDim
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobLin

public section

namespace CFSG.StandardType.QTwo

theorem qTwo_barData {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 5 ≤ m)
    (hLM : QTwoLocalModel m Bs L x)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (U : Submodule (ZMod 3) V) (Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U))
      (ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar),
      GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ ∧
        (Module.finrank (ZMod 3) U = m ∨ Module.finrank (ZMod 3) U + 1 = m) := by
  classical
  haveI : Finite V := Finite.of_injective (ι.symm : V → Additive ↥Bs) ι.symm.injective
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hW' : GGSecFiveWeylCase' 3 B Bs x D J := hcfg.2.1
  let I : Type := Option {q : G × Subgroup G // GGNbr 3 B x D J q.1 q.2}
  let AX : I → Subgroup (V ≃ₗ[ZMod 3] V) := fun X =>
    match X with
    | none => (ggAutomizer L Bs).map (ggLin (p := 3) ι)
    | some q => (ggAutomizer L Bs ⊔ ggAutomizer q.1.2 Bs).map (ggLin (p := 3) ι)
  let AJ : Subgroup (V ≃ₗ[ZMod 3] V) := (ggAutomizer L Bs).map (ggLin (p := 3) ι)
  let Ag : Subgroup (V ≃ₗ[ZMod 3] V) := qTwoBarA B Bs L D J x ι
  have hI : Nonempty I := ⟨none⟩
  have hX : ∀ X : I, GGLinConnGen (AX X) := by
    intro X
    cases X with
    | none =>
      have hW : GGWeylReflectionGroup 3 (ggAutomizer L Bs) :=
        ⟨Fin (m - 1), CoxeterMatrix.A (m - 1),
          Or.inl ⟨m - 1, Equiv.refl _, by omega, Or.inl rfl⟩, hLM.weyl⟩
      exact qTwo_bar_weylConnGen (p := 3) ι (by norm_num) hNT (ggAutomizer_mono Bs le_top) hW
    | some q =>
      have hWn : GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer q.1.2 Bs) :=
        hcfg.1.2.2.2.2.1 q.1.1 q.1.2 q.2 (hW' q.1.1 q.1.2 q.2) (Or.inr hW')
      exact qTwo_bar_weylConnGen (p := 3) ι (by norm_num) hNT
        (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)) hWn
  have hJ : ∀ X : I, AJ ≤ AX X := by
    intro X
    cases X with
    | none => exact le_refl AJ
    | some q => exact Subgroup.map_mono le_sup_left
  have hJr : ∃ r ∈ AJ, GGLinRefl r := by
    obtain ⟨e, he⟩ := hLM.weyl
    let i0 : Fin (m - 1) := ⟨0, by omega⟩
    refine ⟨ggLin (p := 3) ι
      (((e ((CoxeterMatrix.A (m - 1)).simple i0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem (ggLin (p := 3) ι)
        (e ((CoxeterMatrix.A (m - 1)).simple i0)).2
    · exact (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) ι
        (((e ((CoxeterMatrix.A (m - 1)).simple i0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))).mp
        (he i0)
  have hAg : Ag = ⨆ X : I, AX X := by
    dsimp only [Ag, qTwoBarA, AX, I]
    exact qTwo_bar_iSup_eq (B := B) (Bs := Bs) (L := L) (D := D) (J := J) (x := x) (V := V) ι
  have hfix : ggLinFix (Ag : Set (V ≃ₗ[ZMod 3] V)) = ⊥ := by
    simpa only [Ag] using qTwo_bar_fix B Bs L D J x ι hC
  have hnotr : ∀ g ∈ Ag, g ≠ 1 →
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg
    have hg' : g ∈ qTwoBarA B Bs L D J x ι := by simpa only [Ag] using hg
    exact qTwo_bar_notr B Bs L D J x ι hNT hg'
  have hdim3 : 3 ≤ Module.finrank (ZMod 3)
      (ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V))) := by
    have h := (qTwo_bar_dim B Bs L D J x ι hm hLM).1
    simpa only [Ag, qTwoBarU, qTwoBarA] using h
  have hdim : Module.finrank (ZMod 3) (ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V))) = m ∨
      Module.finrank (ZMod 3) (ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V))) + 1 = m := by
    have h := (qTwo_bar_dim B Bs L D J x ι hm hLM).2
    simpa only [Ag, qTwoBarU, qTwoBarA] using h
  obtain ⟨Abar, ρ', hRG, hAI, hres, htriv, hrefl, hneg⟩ :=
    ggLin_bar_linear_data (p := 3) (by norm_num) (I := I) AX hX AJ hJ hJr Ag hAg hfix hnotr
      (ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V))) rfl hdim3
  let ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar :=
    (Subgroup.equivMapOfInjective (ggAInf 3 B Bs x L D J) (ggLin (p := 3) ι)
      (ggLin_injective (p := 3) ι)).trans ρ'
  refine ⟨ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V)), Abar, ρ, ?_, hdim⟩
  refine ⟨hdim3, hRG, hAI, ?_, ?_, ?_, hneg⟩
  · intro a u
    exact hres (Subgroup.equivMapOfInjective (ggAInf 3 B Bs x L D J) (ggLin (p := 3) ι)
      (ggLin_injective (p := 3) ι) a) u
  · intro a ha v
    exact htriv (ggLin (p := 3) ι a) (Subgroup.mem_map_of_mem (ggLin (p := 3) ι) ha) v
  · intro a
    have h1 : GGIsReflection 3 (a : MulAut ↥Bs) ↔ GGLinRefl (ggLin (p := 3) ι a) :=
      ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) ι (a : MulAut ↥Bs)
    have h2 : GGLinRefl (ggLin (p := 3) ι a) ↔
        ZS.IsRefl 3 ((ρ a : ↥Abar) : ↥(ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V))) ≃ₗ[ZMod 3]
          ↥(ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V)))) :=
      hrefl ⟨ggLin (p := 3) ι a, Subgroup.mem_map_of_mem (ggLin (p := 3) ι) a.2⟩
    exact h1.trans h2

theorem qTwo_ainf_weyl {G : Type} [Group G] [Finite G]
    (hZS : ZS.UseInput) {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m N : ℕ} (hm : 5 ≤ m) (hN1 : m + 1 ≤ N)
    (hN2 : N ≤ m + 2)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hLM : QTwoLocalModel m Bs L x)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1) :
    GGWeylReflectionGroup 3 (ggAInf 3 B Bs x L D J) := by
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hLM.elemAb
  obtain ⟨U, Abar, ρ, hD, hdim⟩ := qTwo_barData hcfg hm hLM hC ι
  haveI : Finite V := Finite.of_injective (ι.symm : V → Additive ↥Bs) ι.symm.injective
  haveI : Finite ↥U := Subtype.finite
  haveI : Module.Finite (ZMod 3) ↥U := Module.Finite.of_finite
  have hFam : ZS.Family 3 Abar :=
    hZS (p := 3) (U := ↥U) (A := Abar) (by norm_num) hD.1 hD.2.1 hD.2.2.1
  exact ggSecFive_weyl_of_linWeyl hD
    (qTwo_family_linWeyl (B := B) (Bs := Bs) (L := L) (D := D) (J := J) (x := x) (𝒦 := 𝒦)
      hcfg hm hN1 hN2 hA hLM hD hdim hFam)

end CFSG.StandardType.QTwo

end
