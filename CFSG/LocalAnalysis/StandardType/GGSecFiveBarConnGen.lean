module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleBarAbs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleAdj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflCartan
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma range_eq_closure_simple {H : Type} [Group H] {ι' : Type} {M : CoxeterMatrix ι'}
    (F : M.Group →* H) :
    F.range = Subgroup.closure (Set.range fun i => F (M.simple i)) := by
  rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1

private lemma ggIsWeylMatrixFixed_of_ggIsWeylMatrix {ι' : Type} {M : CoxeterMatrix ι'}
    (hM : GGIsWeylMatrix M) : GGIsWeylMatrixFixed M := by
  rcases hM with ⟨n, e, hn, h | ⟨hn2, h⟩ | ⟨hn4, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact Or.inl ⟨n, e, hn, Or.inl h⟩
  · exact Or.inl ⟨n, e, hn, Or.inr (Or.inl ⟨hn2, h⟩)⟩
  · exact Or.inl ⟨n, e, hn, Or.inr (Or.inr ⟨hn4, h⟩)⟩
  · exact Or.inr (Or.inl ⟨e, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, h⟩))))

private lemma exists_ggIntCartan_of_ggIsWeylMatrix {ι' : Type} {M : CoxeterMatrix ι'}
    (hM : GGIsWeylMatrix M) : ∃ C : Matrix ι' ι' ℤ, GGIntCartan M C := by
  rcases hM with ⟨n, e, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩
  · exact ⟨Matrix.reindex e e (CartanMatrix.A n), by rw [h]; exact (ggIntCartan_A n).reindex e⟩
  · exact ⟨Matrix.reindex e e (CartanMatrix.B n), by rw [h]; exact (ggIntCartan_B n).reindex e⟩
  · exact ⟨Matrix.reindex e e (CartanMatrix.D n), by rw [h]; exact (ggIntCartan_D n).reindex e⟩
  · exact ⟨Matrix.reindex e e (CartanMatrix.E 6), by rw [h]; exact ggIntCartan_E₆.reindex e⟩
  · exact ⟨Matrix.reindex e e (CartanMatrix.E 7), by rw [h]; exact ggIntCartan_E₇.reindex e⟩
  · exact ⟨Matrix.reindex e e (CartanMatrix.E 8), by rw [h]; exact ggIntCartan_E₈.reindex e⟩
  · exact ⟨Matrix.reindex e e CartanMatrix.F₄, by rw [h]; exact ggIntCartan_F₄.reindex e⟩
  · exact ⟨Matrix.reindex e e CartanMatrix.G₂, by rw [h]; exact ggIntCartan_G₂.reindex e⟩

private lemma eqvGen_of_reflTransGen {α : Type*} {r p : α → α → Prop}
    (h : ∀ a b, r a b → p a b) {a b : α} (hab : Relation.ReflTransGen r a b) :
    Relation.EqvGen p a b := by
  induction hab with
  | refl => exact Relation.EqvGen.refl _
  | tail hab hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (h _ _ hbc))

private lemma eqvGen_connected_of_ggIsWeylMatrix {ι' : Type} {M : CoxeterMatrix ι'}
    (hM : GGIsWeylMatrix M) :
    ∀ i j : ι', Relation.EqvGen (fun a b : ι' => 3 ≤ M a b) i j := by
  obtain ⟨C, hC⟩ := exists_ggIntCartan_of_ggIsWeylMatrix hM
  have hfixed := ggIsWeylMatrixFixed_of_ggIsWeylMatrix hM
  have hconn : (TauCeti.diagramGraph C).Connected :=
    connected_diagramGraph_of_ggIsWeylMatrix hfixed hC
  have hle : (TauCeti.diagramGraph C).Adj ≤ (fun a b : ι' => 3 ≤ M a b) := by
    intro i j hij
    rw [TauCeti.diagramGraph_adj] at hij
    rcases hC.entries hij.1 with ⟨hm, h0, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
    · exact absurd h0 hij.2.1
    · exact by omega
    · exact by omega
    · exact by omega
  intro i j
  exact eqvGen_of_reflTransGen hle
    ((SimpleGraph.reachable_iff_reflTransGen i j).mp (hconn.preconnected i j))

theorem ggLinConnGen_of_weyl
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ Subgroup.closure (ggInduced ⊤ Bs))
    (hW : GGWeylReflectionGroup p A) :
    GGLinConnGen (A.map (ggLin (p := p) ι)) := by
  classical
  obtain ⟨ι', M, hM, f, hf⟩ := hW
  let F : M.Group →* MulAut ↥Bs := A.subtype.comp f.toMonoidHom
  let g : ι' → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (F (M.simple i))
  have hFrange : F.range = A := by
    ext a
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact (f x).2
    · intro ha
      refine ⟨f.symm ⟨a, ha⟩, ?_⟩
      show ((f (f.symm ⟨a, ha⟩) : ↥A) : MulAut ↥Bs) = a
      rw [f.apply_symm_apply]
  have hgen : A.map (ggLin (p := p) ι) = Subgroup.closure (Set.range g) := by
    rw [← hFrange, MonoidHom.map_range, range_eq_closure_simple]
    rfl
  have hrefl : ∀ r ∈ Set.range g, GGLinRefl r := by
    rintro r ⟨i, rfl⟩
    exact (ggIsReflection_iff_ggLinRefl hp2 ι (F (M.simple i))).mp (hf i)
  have hnotrMap : ∀ ψ ∈ A,
      ¬ (Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
        ggLinMove (ggLin (p := p) ι ψ) ≤ ggLinFix {ggLin (p := p) ι ψ}) := by
    intro ψ hψ
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have h1 : ψ ∈ ggAutomizer ⊤ Bs := hA hψ
      rwa [ggAutomizer_eq] at h1
    have h2 := hNT ψ hψind
    rwa [ggIsTransvection_iff_ggLin (p := p) ι ψ] at h2
  have hadj : ∀ i j, 3 ≤ M i j → GGLinAdj (g i) (g j) := by
    intro i j hij
    have hrefli : GGLinRefl (g i) :=
      (ggIsReflection_iff_ggLinRefl hp2 ι (F (M.simple i))).mp (hf i)
    have hreflj : GGLinRefl (g j) :=
      (ggIsReflection_iff_ggLinRefl hp2 ι (F (M.simple j))).mp (hf j)
    have hFinj : Function.Injective F := fun a b hab => f.injective (Subtype.ext hab)
    have hnc : g i * g j ≠ g j * g i := by
      intro h
      have hφ : F (M.simple i) * F (M.simple j) = F (M.simple j) * F (M.simple i) :=
        ggLin_injective (p := p) ι (by
          rw [map_mul, map_mul]
          exact h)
      have hsimple : M.simple i * M.simple j = M.simple j * M.simple i :=
        hFinj (by rw [map_mul, map_mul]; exact hφ)
      have hsi : M.simple i * M.simple i = 1 := by
        rw [← pow_two]
        exact M.toCoxeterSystem.simple_sq i
      have hsj : M.simple j * M.simple j = 1 := by
        rw [← pow_two]
        exact M.toCoxeterSystem.simple_sq j
      have h2 : (M.simple i * M.simple j) ^ 2 = 1 := by
        rw [pow_two]
        calc (M.simple i * M.simple j) * (M.simple i * M.simple j)
            = M.simple i * (M.simple j * M.simple i) * M.simple j := by group
          _ = M.simple i * (M.simple i * M.simple j) * M.simple j := by rw [← hsimple]
          _ = (M.simple i * M.simple i) * (M.simple j * M.simple j) := by group
          _ = 1 := by rw [hsi, hsj, mul_one]
      have ho : orderOf (M.simple i * M.simple j) = M i j := by
        have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
        rw [CoxeterMatrix.toCoxeterSystem_simple] at h
        exact h
      have hle2 : orderOf (M.simple i * M.simple j) ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) h2
      omega
    have hnotr : ∀ w ∈ Subgroup.closure ({g i, g j} : Set (V ≃ₗ[ZMod p] V)), w ≠ 1 →
        ¬ (Module.finrank (ZMod p) (ggLinMove w) = 1 ∧ ggLinMove w ≤ ggLinFix {w}) := by
      intro w hw _
      have hwA : w ∈ A.map (ggLin (p := p) ι) := by
        have hle : Subgroup.closure ({g i, g j} : Set (V ≃ₗ[ZMod p] V)) ≤
            A.map (ggLin (p := p) ι) :=
          (Subgroup.closure_le _).mpr (by
            intro x hx
            rcases hx with rfl | rfl
            · exact Subgroup.mem_map_of_mem (ggLin (p := p) ι) (f (M.simple i)).2
            · exact Subgroup.mem_map_of_mem (ggLin (p := p) ι) (f (M.simple j)).2)
        exact hle hw
      obtain ⟨ψ, hψA, hψeq⟩ := (Subgroup.mem_map (f := ggLin (p := p) ι)).mp hwA
      have h3 := hnotrMap ψ hψA
      rwa [hψeq] at h3
    exact ggLin_adj_of_not_commute hp2 (g i) (g j) hrefli hreflj hnc hnotr
  let R : (V ≃ₗ[ZMod p] V) → (V ≃ₗ[ZMod p] V) → Prop :=
    fun a b => a ∈ Set.range g ∧ b ∈ Set.range g ∧ GGLinAdj a b
  have hidx := eqvGen_connected_of_ggIsWeylMatrix hM
  refine ⟨Set.range g, hrefl, ?_, hgen⟩
  rintro r ⟨i, rfl⟩ s ⟨j, rfl⟩
  exact Relation.EqvGen.recOn (hidx i j)
    (motive := fun a b _ => Relation.EqvGen R (g a) (g b))
    (fun a b hab =>
      Relation.EqvGen.rel _ _ ⟨Set.mem_range_self a, Set.mem_range_self b, hadj a b hab⟩)
    (fun a => Relation.EqvGen.refl _)
    (fun a b _ ih => ih.symm)
    (fun a b c _ _ ihab ihbc => Relation.EqvGen.trans (g a) (g b) (g c) ihab ihbc)

end CFSG.StandardType

end
