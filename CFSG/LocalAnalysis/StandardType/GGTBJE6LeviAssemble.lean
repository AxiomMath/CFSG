module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Monster.B.Geometry

private theorem e6lv_weylFixed_of_weyl {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) : GGIsWeylMatrixFixed M := hM

theorem ggResSideDatum_of_weylMatrix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hWM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (b : Λ) (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Λ | j ≠ b}))
    (h3 : 3 ≤ Fintype.card {j : Λ // j ≠ b}) :
    GGResSideDatum p Bs X J := by
  have hWMJ' : GGIsWeylMatrixFixed (parMatrix M {j : Λ | j ≠ b}) :=
    e6lv_weylFixed_of_weyl hWMJ
  have hCJ : GGIntCartan (parMatrix M {j : Λ | j ≠ b})
      (C.submatrix Subtype.val Subtype.val) := ggLeviDatum_ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Λ // j ≠ b}, α (i : Λ) (h (j : Λ)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Λ // j ≠ b} => ψ j) :=
    ggReflConjSimple_of_weylMatrix hp hWMJ' h3 hCJ ι
      (fun j : {j : Λ // j ≠ b} => ψ j) (fun j : {j : Λ // j ≠ b} => h j)
      (fun j : {j : Λ // j ≠ b} => α j) hpairJ (fun i w => hlin i w) hJ
  let fJ : (parMatrix M {j : Λ | j ≠ b}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Λ | j ≠ b} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Λ | j ≠ b}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Λ, inferInstance, inferInstance, b, M, C, parMatrix M {j : Λ | j ≠ b}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hWM, hMC, hWMJ, fun _ _ => rfl, hlin, hrefl, hpair,
    ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

theorem ggResLeviSideDatumLE3_of_weylMatrix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hWM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (S : Finset (Λ)) (hS1 : 2 ≤ S.card) (hS2 : S.card ≤ 3)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Λ | j ∉ S}))
    (h3 : 3 ≤ Fintype.card {j : Λ // j ∉ S}) :
    GGResLeviSideDatumLE3 p Bs X J := by
  have hWMJ' : GGIsWeylMatrixFixed (parMatrix M {j : Λ | j ∉ S}) :=
    e6lv_weylFixed_of_weyl hWMJ
  have hCJ : GGIntCartan (parMatrix M {j : Λ | j ∉ S})
      (C.submatrix Subtype.val Subtype.val) := ggLeviDatum_ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Λ // j ∉ S}, α (i : Λ) (h (j : Λ)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Λ // j ∉ S} => ψ j) :=
    ggReflConjSimple_of_weylMatrix hp hWMJ' h3 hCJ ι
      (fun j : {j : Λ // j ∉ S} => ψ j) (fun j : {j : Λ // j ∉ S} => h j)
      (fun j : {j : Λ // j ∉ S} => α j) hpairJ (fun i w => hlin i w) hJ
  let fJ : (parMatrix M {j : Λ | j ∉ S}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Λ | j ∉ S} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Λ | j ∉ S}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Λ, inferInstance, inferInstance, S, M, C, parMatrix M {j : Λ | j ∉ S}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hS1, hS2, hWM, hMC, hWMJ, fun _ _ => rfl, hlin,
    hrefl, hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

private theorem e6lv_parabolic_weyl {S : Finset (Fin 6)}
    (hWM : GGIsWeylMatrix (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)))
    (hMC : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6))
    (hne : Nonempty {i : Fin 6 // i ∉ S})
    (hdel : GGDeletedConnectedS CoxeterMatrix.E₆ S) :
    GGIsWeylMatrix (parMatrix CoxeterMatrix.E₆ {i | i ∉ S}) :=
  l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S CoxeterMatrix.E₆ (Tag.cartan .E6)
    hWM hMC hdel hne

private theorem e6lv_side {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {ψ : Fin 6 → MulAut ↥Bs} {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod p) V}
    (hWM : GGIsWeylMatrix (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)))
    (hMC : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6))
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (Tag.cartan .E6 i j : ZMod p))
    {f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (S : Finset (Fin 6)) (b : Fin 6) (hSb : S = {b})
    (hne : Nonempty {i : Fin 6 // i ∉ S})
    (hdel : GGDeletedConnectedS CoxeterMatrix.E₆ S)
    (h3 : 3 ≤ Fintype.card {j : Fin 6 // j ≠ b})
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 6 // j ∉ S} => ψ j)) :
    GGResSideDatum p Bs X J := by
  subst hSb
  have hJ' : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 6 // j ≠ b} => ψ j) := by
    rw [hJ, ← ggLeviDatum_range_ne_eq ψ (S := ({b} : Finset (Fin 6))) rfl]
  exact ggResSideDatum_of_weylMatrix hp hWM hMC hlin hrefl hpair hf hclos b hJ'
    (ggLeviDatum_side_weyl (e6lv_parabolic_weyl hWM hMC hne hdel)) h3

private theorem e6lv_levi {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {ψ : Fin 6 → MulAut ↥Bs} {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod p) V}
    (hWM : GGIsWeylMatrix (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)))
    (hMC : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6))
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (Tag.cartan .E6 i j : ZMod p))
    {f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (S : Finset (Fin 6)) (hS1 : 2 ≤ S.card) (hS2 : S.card ≤ 3)
    (hne : Nonempty {i : Fin 6 // i ∉ S})
    (hdel : GGDeletedConnectedS CoxeterMatrix.E₆ S)
    (h3 : 3 ≤ Fintype.card {j : Fin 6 // j ∉ S})
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 6 // j ∉ S} => ψ j)) :
    GGResLeviSideDatumLE3 p Bs X J :=
  ggResLeviSideDatumLE3_of_weylMatrix hp hWM hMC hlin hrefl hpair hf hclos S hS1 hS2 hJ
    (e6lv_parabolic_weyl hWM hMC hne hdel) h3

theorem ggE6LeviDatum_of_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs X J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin 6 → MulAut ↥Bs} {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (Tag.cartan .E6 i j : ZMod p))
    {f : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.E₆.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (u : CoxeterMatrix.E₆.Group) {S : Finset (Fin 6)} (hS : S ∈ e6LeviDel)
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Fin 6 // j ∉ S} =>
      (f u : MulAut ↥Bs) * φ j * (f u : MulAut ↥Bs)⁻¹)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hWM : GGIsWeylMatrix (CoxeterMatrix.E₆ : CoxeterMatrix (Fin 6)) :=
    Or.inr (Or.inl ⟨Equiv.refl (Fin 6), by ext i j; rfl⟩)
  have hMC : GGIntCartan CoxeterMatrix.E₆ (Tag.cartan .E6) := by
    rw [show Tag.cartan .E6 = Tag.cartanE 6 from rfl, cartanE_eq]
    exact ggIntCartan_E₆
  obtain ⟨h', α', f', hlin', hrefl', hpair', hf', hclos', -⟩ :=
    ggLeviDatum_conj hlin hrefl hpair hf hclos u
  let ψ : Fin 6 → MulAut ↥Bs := fun i => (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹
  have hS' : S = {0} ∨ S = {5} ∨ S = {1} ∨ S = {0, 5} ∨ S = {0, 1} ∨ S = {1, 5} ∨
      S = {0, 2} ∨ S = {4, 5} ∨ S = {1, 4, 5} ∨ S = {0, 1, 5} ∨ S = {0, 4, 5} ∨
      S = {0, 2, 5} ∨ S = {0, 1, 2} := by
    simpa [e6LeviDel] using hS
  rcases hS' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact Or.inl (e6lv_side hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0} : Finset (Fin 6)) 0 rfl ⟨⟨1, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inl (e6lv_side hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({5} : Finset (Fin 6)) 5 rfl ⟨⟨0, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inl (e6lv_side hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({1} : Finset (Fin 6)) 1 rfl ⟨⟨0, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨1, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 1} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨2, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({1, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨0, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 2} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨1, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({4, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨0, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({1, 4, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨0, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 1, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨2, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 4, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨1, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 2, 5} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨1, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)
  ·
    exact Or.inr (e6lv_levi hp2 hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 1, 2} : Finset (Fin 6)) (by decide) (by decide) ⟨⟨3, by decide⟩⟩
      (ggDeletedConnectedS_of_reach (by decide +kernel))
      (by decide) hJ)

end CFSG.StandardType

end
