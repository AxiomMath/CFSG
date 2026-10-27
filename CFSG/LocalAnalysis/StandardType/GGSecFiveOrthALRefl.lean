module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

theorem ggOrth_simple_conj {ι : Type} (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M) (hle : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (i j : ι) :
    ∃ g : M.Group, M.simple j = g * M.simple i * g⁻¹ :=
  ggSimplyLaced_simple_conj (ggSimplyLacedConnected_of_weyl hM hle) i j

private theorem ct_alr_automizer_le_induced {G : Type} [Group G] {L Bs : Subgroup G} :
    ggAutomizer L Bs ≤ ggInduced ⊤ Bs := by
  intro φ hφ
  rw [ggAutomizer_eq] at hφ
  change φ ∈ ggInduced L Bs at hφ
  obtain ⟨g, hgL, hgN, hgφ⟩ := hφ
  exact ⟨g, trivial, hgN, hgφ⟩

private theorem ct_alr_refl_conj_of_pres
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι)
    {ιW : Type} (M : CoxeterMatrix ιW) (hM : GGIsWeylMatrix M)
    (hle : ∀ i j : ιW, i ≠ j → M.M i j ≤ 3)
    (f : M.Group ≃* ↥(ggAutomizer L Bs))
    (hf : ∀ i : ιW,
      GGIsReflection 3 ((f (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) :
    ggAutomizer L Bs = Subgroup.closure {a | a ∈ ggAutomizer L Bs ∧ GGIsReflection 3 a} ∧
      ∀ a ∈ ggAutomizer L Bs, ∀ b ∈ ggAutomizer L Bs, GGIsReflection 3 a →
        GGIsReflection 3 b → ∃ g ∈ ggAutomizer L Bs, b = g * a * g⁻¹ := by
  classical
  have hAind : ggAutomizer L Bs ≤ ggInduced ⊤ Bs := ct_alr_automizer_le_induced
  have hstar : GGBstar 3 B Bs := S.cfg.1.1.2.1
  have hEl : IsElemAbelian 3 Bs := hstar.2.1
  have hNT : GGNoTransvection 3 Bs := S.cfg.1.2.2.2.1
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  have hG2 : ¬ ∃ e : Fin 2 ≃ ιW, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, rfl⟩
    have hne : e 0 ≠ e 1 := by
      intro hh
      have hv := congrArg Fin.val (e.injective hh)
      norm_num at hv
    have h := hle (e 0) (e 1) hne
    have hlab : ((CoxeterMatrix.G₂).reindex e).M (e 0) (e 1) = 6 := by
      rw [CoxeterMatrix.reindex_apply]
      simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
    rw [hlab] at h
    omega
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  have hmem : ∀ x : ↥A, (x : MulAut ↥Bs) ∈ A := fun x => x.2
  constructor
  ·
    apply le_antisymm
    ·
      have hgen : Subgroup.closure (Set.range M.simple) = ⊤ :=
        M.toCoxeterSystem.subgroup_closure_range_simple
      let C : Subgroup ↥A :=
        (Subgroup.closure {a : MulAut ↥Bs | a ∈ A ∧ GGIsReflection 3 a}).comap A.subtype
      have hfac : Subgroup.comap (f : M.Group →* ↥A) C = ⊤ := by
        have hle : Subgroup.closure (Set.range M.simple) ≤
            Subgroup.comap (f : M.Group →* ↥A) C := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro _ ⟨i, rfl⟩
          exact (Subgroup.mem_comap).mpr ((Subgroup.mem_comap).mpr
            (Subgroup.subset_closure ⟨(f (M.simple i)).2, hf i⟩))
        rw [hgen] at hle
        exact le_antisymm le_top hle
      intro a ha
      have hx : (⟨a, ha⟩ : ↥A) ∈ C := by
        have hy : f.symm (⟨a, ha⟩ : ↥A) ∈ Subgroup.comap (f : M.Group →* ↥A) C := by
          rw [hfac]
          exact Subgroup.mem_top _
        simpa using hy
      exact hx
    · exact (Subgroup.closure_le A).mpr (fun x hx => hx.1)
  ·
    rintro a haA b hbA haR hbR
    have hroot : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G), p.Prime →
        p ≠ 2 → IsElemAbelian p Bs → GGNoTransvection p Bs →
        ∀ (A : Subgroup (MulAut ↥Bs)), A ≤ ggInduced ⊤ Bs →
        ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
        (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
        ∀ f : M.Group ≃* ↥A,
          (∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) →
        ∀ a : ↥A, GGIsReflection p (a : MulAut ↥Bs) →
          ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹) :=
      SecFiveRootRefl.ggSecFiveRootReflInput_holds
    obtain ⟨i, g, hai⟩ :=
      hroot G 3 Bs hp3 hp32 hEl hNT A hAind ιW M hM hG2 f hf ⟨a, haA⟩ haR
    obtain ⟨j, h, hbj⟩ :=
      hroot G 3 Bs hp3 hp32 hEl hNT A hAind ιW M hM hG2 f hf ⟨b, hbA⟩ hbR
    obtain ⟨w, hw⟩ := ggOrth_simple_conj M hM hle i j
    let uA : ↥A := f (h * w * g⁻¹)
    refine ⟨(uA : MulAut ↥Bs), uA.2, ?_⟩
    have hEq : (⟨b, hbA⟩ : ↥A) = uA * ⟨a, haA⟩ * uA⁻¹ := by
      rw [hbj, hai, hw]
      simp only [uA, map_mul, map_inv]
      group
    have := congrArg (Subtype.val) hEq
    simpa [uA] using this

theorem GGOrthSetup.refl_conj
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    ggAutomizer L Bs = Subgroup.closure {a | a ∈ ggAutomizer L Bs ∧ GGIsReflection 3 a} ∧
      ∀ a ∈ ggAutomizer L Bs, ∀ b ∈ ggAutomizer L Bs, GGIsReflection 3 a → GGIsReflection 3 b → ∃ g ∈ ggAutomizer L Bs, b = g * a * g⁻¹ := by
  obtain ⟨t, n, f, ψ, hloc, hstd, hTB⟩ :=
    s2jn_exists_tableBFrame (G := G) (p := 3) B Bs x L D J 𝒦 S.cfg S.split
  obtain ⟨ε, hεrefl, -⟩ := hTB
  obtain ⟨hW, hle3⟩ := ggTag_weylMatrix (t := t) (n := n) (f := f)
    hloc.2.1.2.2.1 hloc.1.2.2.1
  exact ct_alr_refl_conj_of_pres S
    (CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType) hW hle3 ε hεrefl

end CFSG.StandardType.OrthF3

end
