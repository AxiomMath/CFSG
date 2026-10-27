module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.LocalAnalysis.StandardType.GGF4OrbCore
public import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem exists_f4Triple_map_of_weyl {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {ι' : Type} {M' : CoxeterMatrix ι'}
    (ε : M'.Group ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ i, GGIsReflection p ((ε (M'.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι') (hM : ∀ k l, M' (σ k) (σ l) = CoxeterMatrix.B 3 k l) :
    ∃ φ : M'.Group →* CoxeterMatrix.F₄.Group,
      (∀ u, ((e (φ u) : ↥A) : MulAut ↥Bs) = ((ε u : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) ∧
      (∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (φ (M'.simple (σ k)))) ∧
      orderOf (φ (M'.simple (σ 0)) * φ (M'.simple (σ 1))) = 3 ∧
      orderOf (φ (M'.simple (σ 1)) * φ (M'.simple (σ 2))) = 4 ∧
      orderOf (φ (M'.simple (σ 0)) * φ (M'.simple (σ 2))) = 2 ∧
      ∀ z, z ∈ Subgroup.closure (Set.range fun k => φ (M'.simple (σ k))) ↔
        ((e z : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs := by
  let φ : M'.Group →* CoxeterMatrix.F₄.Group :=
    e.symm.toMonoidHom.comp ((Subgroup.inclusion hXA).comp ε.toMonoidHom)
  have hφinj : Function.Injective φ :=
    e.symm.injective.comp ((Subgroup.inclusion_injective hXA).comp ε.injective)
  have hφe : ∀ u, ((e (φ u) : ↥A) : MulAut ↥Bs) = ((ε u : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
    intro u
    simp [φ]
  let a : Fin 3 → CoxeterMatrix.F₄.Group := fun k => φ (M'.simple (σ k))
  have hG2 : ¬ ∃ e' : Fin 2 ≃ Fin 4, CoxeterMatrix.F₄ = CoxeterMatrix.G₂.reindex e' := by
    rintro ⟨e', -⟩
    have h := Fintype.card_congr e'
    simp at h
  have hrefl : ∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (a k) := by
    intro k
    obtain ⟨i, g, hig⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hEl hNT A
      hAind (Fin 4) CoxeterMatrix.F₄ hpres.1 hG2 e hpres.2 (e (a k))
      (by rw [hφe]; exact hεrefl (σ k))
    refine ⟨g, i, ?_⟩
    have h := e.injective hig
    rw [h, CoxeterMatrix.toCoxeterSystem_simple]
  have hord : ∀ k l, orderOf (a k * a l) = CoxeterMatrix.B 3 k l := by
    intro k l
    have h1 : a k * a l = φ (M'.simple (σ k) * M'.simple (σ l)) := (map_mul φ _ _).symm
    rw [h1, orderOf_injective φ hφinj, ← hM k l]
    have h2 := M'.toCoxeterSystem.orderOf_simple_mul_simple (σ k) (σ l)
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using h2
  refine ⟨φ, hφe, hrefl, ?_, ?_, ?_, ?_⟩
  · rw [hord]; decide
  · rw [hord]; decide
  · rw [hord]; decide
  intro z
  constructor
  · intro hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hφe]
      exact (ε _).2
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul, Subgroup.coe_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv, Subgroup.coe_inv]; exact inv_mem hx
  · intro hz
    have hu : ε.symm ⟨_, hz⟩ ∈ Subgroup.closure (Set.range M'.simple) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple, M'.toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top _
    have hz' : φ (ε.symm ⟨_, hz⟩) = z := by
      apply e.injective
      apply Subtype.ext
      rw [hφe, MulEquiv.apply_symm_apply]
    rw [← hz']
    have hmap : (Subgroup.closure (Set.range M'.simple)).map φ ≤ Subgroup.closure (Set.range a) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨σ.symm i, by simp [a]⟩
    exact hmap ⟨_, hu, rfl⟩

theorem exists_f4Triple_of_weyl {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {ι' : Type} {M' : CoxeterMatrix ι'}
    (ε : M'.Group ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ i, GGIsReflection p ((ε (M'.simple i) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι') (hM : ∀ k l, M' (σ k) (σ l) = CoxeterMatrix.B 3 k l) :
    ∃ a : Fin 3 → CoxeterMatrix.F₄.Group,
      (∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (a k)) ∧
      orderOf (a 0 * a 1) = 3 ∧ orderOf (a 1 * a 2) = 4 ∧ orderOf (a 0 * a 2) = 2 ∧
      ∀ z, z ∈ Subgroup.closure (Set.range a) ↔ ((e z : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs := by
  obtain ⟨φ, -, h⟩ := exists_f4Triple_map_of_weyl hp hp2 hEl hNT hAind hpres hXA ε hεrefl σ hM
  exact ⟨fun k => φ (M'.simple (σ k)), h⟩

theorem ggF4QGeFourOrb_of_triples {G : Type} [Group G] {Bs L K : Subgroup G}
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    {a b : Fin 3 → CoxeterMatrix.F₄.Group}
    (ha : ∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (a k))
    (hb : ∀ k, CoxeterMatrix.F₄.toCoxeterSystem.IsReflection (b k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb01 : orderOf (b 0 * b 1) = 3)
    (hb12 : orderOf (b 1 * b 2) = 4) (hb02 : orderOf (b 0 * b 2) = 2)
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) ↔
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (hbK : ∀ z, z ∈ Subgroup.closure (Set.range b) ↔
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer K Bs)
    (i j : Fin 4) :
    ∃ (w : CoxeterMatrix.F₄.Group) (X Y : Subgroup G), (X = L ∨ X = K) ∧ (Y = L ∨ Y = K) ∧
      (X = Y ∨ CoxeterMatrix.F₄ i j = 3) ∧
      (↑(e (w * CoxeterMatrix.F₄.simple i * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer X Bs ∧
      (↑(e (w * CoxeterMatrix.F₄.simple j * w⁻¹)) : MulAut ↥Bs) ∈ ggAutomizer Y Bs := by
  have hgen : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    let ι : CoxeterMatrix.F₄.Group →* MulAut ↥Bs :=
      (ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom
    have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
    have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤
        (Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b)).map ι := by
      refine sup_le ?_ ?_
      · intro m hm
        refine ⟨e.symm ⟨m, le_sup_left (a := ggAutomizer L Bs) hm⟩,
          le_sup_left (a := Subgroup.closure (Set.range a)) ((haL _).mpr ?_), ?_⟩
        · simpa using hm
        · simp [ι]
      · intro m hm
        refine ⟨e.symm ⟨m, le_sup_right (a := ggAutomizer L Bs) hm⟩,
          le_sup_right (a := Subgroup.closure (Set.range a)) ((hbK _).mpr ?_), ?_⟩
        · simpa using hm
        · simp [ι]
    obtain ⟨z', hz', hzz'⟩ := hle (e z).2
    have : z' = z := hι (by simpa [ι] using hzz')
    rwa [← this]
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hsimp : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k; rw [hRs k, CoxeterMatrix.toCoxeterSystem_simple]
  obtain ⟨w, X', Y', hX', hY', hXY, hi, hj⟩ :=
    R.orb_core (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (ha k))
      (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (hb k)) ha01 ha12 ha02 hb01 hb12 hb02 hgen i j
  rw [hsimp] at hi hj
  rcases hXY with rfl | hlab
  · rcases hX' with rfl | rfl
    · exact ⟨w, L, L, Or.inl rfl, Or.inl rfl, Or.inl rfl, (haL _).mp hi, (haL _).mp hj⟩
    · exact ⟨w, K, K, Or.inr rfl, Or.inr rfl, Or.inl rfl, (hbK _).mp hi, (hbK _).mp hj⟩
  · rcases hX' with rfl | rfl <;> rcases hY' with rfl | rfl
    · exact ⟨w, L, L, Or.inl rfl, Or.inl rfl, Or.inl rfl, (haL _).mp hi, (haL _).mp hj⟩
    · exact ⟨w, L, K, Or.inl rfl, Or.inr rfl, Or.inr hlab, (haL _).mp hi, (hbK _).mp hj⟩
    · exact ⟨w, K, L, Or.inr rfl, Or.inl rfl, Or.inr hlab, (hbK _).mp hi, (haL _).mp hj⟩
    · exact ⟨w, K, K, Or.inr rfl, Or.inr rfl, Or.inl rfl, (hbK _).mp hi, (hbK _).mp hj⟩

private theorem cartanC_eq_cartanMatrixB' (n : ℕ) : Symplectic.cartanC n = CartanMatrix.B n := by
  ext i j
  simp only [Symplectic.cartanC, CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

section Inputs

theorem coxeterMatrix_PSp_three (f : ℕ) :
    coxeterMatrix (ggU .PSp 3 f).D.isFiniteType = CoxeterMatrix.B 3 := by
  have hC : GGIntCartan (CoxeterMatrix.B 3) (Symplectic.cartanC 3) := by
    rw [cartanC_eq_cartanMatrixB']
    exact ggIntCartan_B 3
  exact coxeterMatrix_eq_of_ggIntCartan _ hC

theorem ggF4QGeFourOrbInput_S1_of_kgPos (hKG : GGF4QGeFourKGPosInput .S1) :
    GGF4QGeFourOrbInput .S1 := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow i j
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  obtain ⟨-, -, -, εL, hεL, -⟩ := hpos.1
  obtain ⟨-, -, -, εK, hεK, -⟩ := hpos.2
  have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_PSp_three]
    rfl
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _) hM
  obtain ⟨b, hb, hb01, hb12, hb02, hbK⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK (Equiv.refl _) hM
  exact ggF4QGeFourOrb_of_triples ha hb ha01 ha12 ha02 hb01 hb12 hb02 haL hbK i j

end Inputs

end CFSG.StandardType
