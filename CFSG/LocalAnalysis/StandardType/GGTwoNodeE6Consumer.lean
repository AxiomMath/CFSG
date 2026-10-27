module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6Frame
public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6C_card_coxeterE6 :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 :=
    CFSG.LieType.Chevalley.cartanE_eq 6
  have hmat : CoxeterMatrix.E₆ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) := by
    have h := coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
      (M := CoxeterMatrix.E₆)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)
      (hc.symm ▸ ggIntCartan_E₆)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E6 = (CoxeterMatrix.E₆).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) =
      Nat.card (CoxeterMatrix.E₆).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E6

theorem ggTwoNodeIndepAtL_e6
    (hAll : LR6E6All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hBs : Nat.card ↥Bs ≤ 3 ^ 7)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) (hCL : GGIntCartan ML CL)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hfL : ML.Group ≃* ↥(ggAutomizer L Bs))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have F := ggXDatumE6_indep_frame hFix hp3 hH hx e hML hCL hφ hpair hAL hind
  have hmove := ggIndep_moving_K hFixK hH hx
  have hcardAL : Nat.card ↥(ggAutomizer L Bs) = 51840 := by
    subst hML
    calc Nat.card ↥(ggAutomizer L Bs) = Nat.card (CoxeterMatrix.E₆.reindex e).Group :=
          (Nat.card_congr hfL.toEquiv).symm
      _ = Nat.card (CoxeterMatrix.E₆).Group :=
          Nat.card_congr ((CoxeterMatrix.E₆).reindexGroupEquiv e).toEquiv
      _ = 51840 := e6C_card_coxeterE6
  subst hp3
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hdim : Module.finrank (ZMod 3) V ≤ 7 := by
    rw [hcardV] at hBs
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hBs
  let r : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 6) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hφsup : ∀ i, φ i ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun i =>
    Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup (ggIndep_reflGenerated_of_closure hrefl hAL) hH.2.2.2.2.2.1
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (MulAut ↥Bs), A' = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hA'] at hgen' hA hφsup
  have hrA : ∀ i : Fin 6, r i ∈ A'.map (ggLin (p := 3) ι) := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφsup (e i), rfl⟩
  have hgenA : A'.map (ggLin (p := 3) ι) =
      Subgroup.closure {s | s ∈ A'.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
    apply le_antisymm
    · calc A'.map (ggLin (p := 3) ι)
          = (Subgroup.closure {ψ | ψ ∈ A' ∧ GGIsReflection 3 ψ}).map (ggLin (p := 3) ι) := by
            rw [← hgen']
        _ = Subgroup.closure ((ggLin (p := 3) ι) '' {ψ | ψ ∈ A' ∧ GGIsReflection 3 ψ}) :=
            MonoidHom.map_closure _ _
        _ ≤ Subgroup.closure {s | s ∈ A'.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
            apply Subgroup.closure_mono
            rintro _ ⟨ψ, ⟨hψA, hψr⟩, rfl⟩
            exact ⟨Subgroup.mem_map.mpr ⟨ψ, hψA, rfl⟩,
              (ggRC_isReflection_iff_linRefl (p := 3) ι ψ).mp hψr⟩
    · rw [Subgroup.closure_le]
      intro z hz
      exact hz.1
  have hnt : ∀ g ∈ A'.map (ggLin (p := 3) ι),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hmem := hA hψA
      rw [ggAutomizer_eq] at hmem
      exact hmem
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hcardA : Nat.card ↥(A'.map (ggLin (p := 3) ι)) ≤ 3 ^ 7 * (6 * (3 - 1) * 51840) := by
    have hstab := hOrb G 3 B Bs x L D J y K hH hx
    rw [← hA'] at hstab
    have hjoin := ggIndep_card_join_le A' ⟨x, hx⟩ hstab
    calc Nat.card ↥(A'.map (ggLin (p := 3) ι)) = Nat.card ↥A' :=
          (Nat.card_congr (Subgroup.equivMapOfInjective A' (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := hjoin
      _ ≤ 3 ^ 7 * ((3 - 1) * 6 * 51840) := by
          rw [hcardAL]
          exact Nat.mul_le_mul_right _ hBs
      _ = 3 ^ 7 * (6 * (3 - 1) * 51840) := by ring
  obtain ⟨t, htK, htrefl, htmove⟩ := hmove
  have hmoveA : ∃ s ∈ A'.map (ggLin (p := 3) ι), GGLinRefl s ∧
      s (ι (Additive.ofMul ⟨x, hx⟩)) ≠ ι (Additive.ofMul ⟨x, hx⟩) := by
    refine ⟨ggLin (p := 3) ι t, Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩,
      (ggRC_isReflection_iff_linRefl (p := 3) ι t).mp htrefl, ?_⟩
    · rw [hA']
      exact Subgroup.mem_sup_right htK
    · intro hfix
      exact htmove ((ggLin_fix_iff (p := 3) ι t ⟨x, hx⟩).mpr hfix)
  have hlin := hAll 3 rfl V hdim (fun i => h (e i)) (fun i => α (e i))
    (ι (Additive.ofMul ⟨x, hx⟩)) r F hr (A'.map (ggLin (p := 3) ι)) hrA hgenA hnt hcardA hmoveA
  rw [← hA']
  exact ggRC_weylReflGroup_of_linWeyl ι A' hlin

theorem ggResTwoNodeIndepE6L
    (hAll : LR6E6All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hLoc : GGE6D4TwoNodeLocalInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallE6 p J L) (hxL : x ∈ L) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hRowN, -⟩, htag⟩ := hrow
  have hp3 : p = 3 := by
    rcases hRowN with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, hp, -, -⟩ | ⟨-, hp, -, -⟩
    · exfalso
      subst hX
      simp at htag
    · exfalso
      subst hX
      simp at htag
    · exact hp
    · exact hp
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  subst hp3
  obtain ⟨hcard, -, -, hdat, -, -⟩ := hLoc G B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ labX
    hJΛ hXΛ hJl hXl hRowN htag
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩, hAL,
    hind⟩ := hdat
  letI := i1; letI := i2; letI := i3; letI := i4
  have hBs : Nat.card ↥Bs ≤ 3 ^ 7 := by
    rcases hcard with h6 | h7
    · rw [h6]
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [h7]
  exact ggTwoNodeIndepAtL_e6 hAll hOrb hFix hFixK rfl hH hx hBs e hMeq hC hφ hrefl hpair f hAL
    (hind hxL)

end CFSG.StandardType

end
