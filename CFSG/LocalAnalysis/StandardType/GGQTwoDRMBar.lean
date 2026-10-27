module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSel
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobBar

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Bar

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {𝒦 : Finset (Subgroup G)}

theorem qTwoD_barData
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hAL : GGWeylReflectionGroup 3 (ggAutomizer L Bs))
    (hJr : ∃ r ∈ ggAutomizer L Bs, GGIsReflection 3 r)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (hdim3 : 3 ≤ Module.finrank (ZMod 3)
      (ggLinCom (qTwoBarA B Bs L D J x ι : Set (V ≃ₗ[ZMod 3] V)))) :
    ∃ (U : Submodule (ZMod 3) V) (Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U))
      (ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar),
      GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ ∧
        U = ggLinCom (qTwoBarA B Bs L D J x ι : Set (V ≃ₗ[ZMod 3] V)) := by
  classical
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have : Finite V := Finite.of_injective (ι.symm : V → Additive ↥Bs) ι.symm.injective
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
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
      exact qTwo_bar_weylConnGen (p := 3) ι (by norm_num) hNT (ggAutomizer_mono Bs le_top) hAL
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
  have hJr' : ∃ r ∈ AJ, GGLinRefl r := by
    obtain ⟨r, hrA, hr⟩ := hJr
    exact ⟨ggLin (p := 3) ι r, Subgroup.mem_map_of_mem (ggLin (p := 3) ι) hrA,
      (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) ι r).mp hr⟩
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
  obtain ⟨Abar, ρ', hRG, hAI, hres, htriv, hrefl, hneg⟩ :=
    ggLin_bar_linear_data (p := 3) (by norm_num) (I := I) AX hX AJ hJ hJr' Ag hAg hfix hnotr
      (ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V))) rfl hdim3
  let ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar :=
    (Subgroup.equivMapOfInjective (ggAInf 3 B Bs x L D J) (ggLin (p := 3) ι)
      (ggLin_injective (p := 3) ι)).trans ρ'
  refine ⟨ggLinCom (Ag : Set (V ≃ₗ[ZMod 3] V)), Abar, ρ, ?_, rfl⟩
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

end Bar

section Top

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι}

theorem qtwoD_fix_com (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 2 ≤ m)
    (β : Additive ↥Bs ≃+ DVec m)
    (hsel : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) = dEven m) :
    (∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1) ∧
      ggLinCom (qTwoBarA B Bs L D J x β : Set (DVec m ≃ₗ[ZMod 3] DVec m)) = ⊤ := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hle : dEven m ≤ qTwoBarA B Bs L D J x β := by
    rw [← hsel]
    exact Subgroup.map_mono (qTwoGlobSel_join_le_ggAInf hcfg)
  refine ⟨fun b hb => ?_, ?_⟩
  · have hv : ggLin (p := 3) β (1 : MulAut ↥Bs) = 1 := map_one _
    have h0 := dEven_fix_zero hm (β (Additive.ofMul b)) (fun g hg => by
      obtain ⟨φ, hφ, rfl⟩ := (Subgroup.mem_map.mp ((hsel ▸ hg :
        g ∈ (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β))))
      rw [ggLin_apply_ofMul, hb φ ((qTwoGlobSel_join_le_ggAInf hcfg) hφ)])
    have h1 : b = 1 := by
      have := β.injective (h0.trans (map_zero β).symm)
      exact Additive.ofMul.injective (this.trans (ofMul_one).symm)
    exact h1
  · rw [eq_top_iff, ← dEven_comm_top hm]
    refine iSup₂_le fun a ha => ?_
    exact le_iSup₂ (f := fun a (_ : a ∈ ((qTwoBarA B Bs L D J x β : Subgroup _) : Set _)) =>
      ggLinMove a) a (hle ha)

end Top

end CFSG.StandardType.QTwo

end
