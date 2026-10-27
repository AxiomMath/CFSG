module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

@[expose] def ggLeviDiagReach {n : ℕ} (M : CoxeterMatrix (Fin n)) (S : Finset (Fin n))
    (s : Finset {i : Fin n // i ∉ S}) : Finset {i : Fin n // i ∉ S} :=
  s ∪ s.biUnion fun a => Finset.univ.filter fun b => b ≠ a ∧ M.M b a ≠ 2

@[expose] def ggLeviDiagReachN {n : ℕ} (M : CoxeterMatrix (Fin n)) (S : Finset (Fin n)) :
    ℕ → Finset {i : Fin n // i ∉ S} → Finset {i : Fin n // i ∉ S}
  | 0, s => s
  | k + 1, s => ggLeviDiagReach M S (ggLeviDiagReachN M S k s)

theorem ggLeviDiagReachN_mem_rtg {n : ℕ} {M : CoxeterMatrix (Fin n)} {S : Finset (Fin n)}
    {a : {i : Fin n // i ∉ S}} (k : ℕ) :
    ∀ {b : {i : Fin n // i ∉ S}}, b ∈ ggLeviDiagReachN M S k {a} →
      Relation.ReflTransGen (fun u v : {i : Fin n // i ∉ S} => u ≠ v ∧ M.M u v ≠ 2) a b := by
  induction k with
  | zero =>
    intro b hb
    simp only [ggLeviDiagReachN, Finset.mem_singleton] at hb
    subst hb
    exact .refl
  | succ k ih =>
    intro b hb
    simp only [ggLeviDiagReachN, ggLeviDiagReach, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb
    rcases hb with hb | ⟨a', ha', hb'⟩
    · exact ih hb
    · exact (ih ha').trans (.single ⟨hb'.1.symm, by
        rw [← M.isSymm.apply a' b]; exact hb'.2⟩)

theorem ggDeletedConnectedS_of_reach {n : ℕ} {M : CoxeterMatrix (Fin n)} {S : Finset (Fin n)}
    (h : ∀ i j : {i : Fin n // i ∉ S}, j ∈ ggLeviDiagReachN M S n {i}) :
    GGDeletedConnectedS M S :=
  fun i j => ggLeviDiagReachN_mem_rtg n (h i j)

theorem ggLeviDatum_ggIntCartan_parMatrix {ι : Type} (M : CoxeterMatrix ι) (C : Matrix ι ι ℤ)
    (T : Set ι) (h : GGIntCartan M C) :
    GGIntCartan (parMatrix M T) (C.submatrix Subtype.val Subtype.val) := by
  constructor
  · intro i
    exact h.1 i.val
  · intro i j hij
    exact h.2 i.val j.val (fun hh => hij (Subtype.ext hh))

theorem ggLeviDatum_isReflection_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) :
    GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

theorem ggLeviDatum_ggLin_conj {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) (u φ : MulAut E)
    {g : Module.Dual (ZMod p) V} {z : V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

theorem ggLeviDatum_map_conj {E : Type*} [Group E] (S : Subgroup E) (u : E)
    (hu : u ∈ S) : Subgroup.map (MulAut.conj u).toMonoidHom S = S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hy) (Subgroup.inv_mem _ hu)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨u⁻¹ * x * u, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx) hu
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

theorem ggLeviDatum_range_ne_eq {n : ℕ} {β : Type*} (f : Fin n → β) {S : Finset (Fin n)}
    {b : Fin n} (hSb : S = {b}) :
    Set.range (fun j : {j : Fin n // j ≠ b} => f j) =
      Set.range (fun j : {j : Fin n // j ∉ S} => f j) := by
  subst hSb
  let e : {j : Fin n // j ≠ b} ≃ {j : Fin n // j ∉ ({b} : Finset (Fin n))} :=
    Equiv.subtypeEquivRight (fun j => by simp)
  have h : (fun j : {j : Fin n // j ≠ b} => f j) =
      (fun j : {j : Fin n // j ∉ ({b} : Finset (Fin n))} => f j) ∘ e := rfl
  rw [h, Set.range_comp, e.surjective.range_eq, Set.image_univ]

theorem ggLeviDatum_side_weyl {n : ℕ} {M : CoxeterMatrix (Fin n)} {b : Fin n}
    (h : GGIsWeylMatrix (parMatrix M {j : Fin n | j ∉ ({b} : Finset (Fin n))})) :
    GGIsWeylMatrix (parMatrix M {j : Fin n | j ≠ b}) := by
  have hmat : parMatrix M {j : Fin n | j ≠ b} =
      (parMatrix M {j : Fin n | j ∉ ({b} : Finset (Fin n))}).reindex
        (Equiv.subtypeEquivRight (fun j => by simp)) := by
    ext i j
    rfl
  rw [hmat]
  exact l05nBL_weyl_reindex h _

theorem ggLeviDatum_linearIndependent_of_pair {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hC : IsUnit ((C.det : ℤ) : ZMod p)) (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) :
    LinearIndependent (ZMod p) h := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hM : (C.map (Int.cast : ℤ → ZMod p)).mulVec c = 0 := by
    funext i
    have hi := congrArg (α i) hc
    simp only [map_sum, map_smul, smul_eq_mul, hpair, map_zero] at hi
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hi
  have hdet : IsUnit (C.map (Int.cast : ℤ → ZMod p)) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Int.cast_det]
    exact hC
  have h0 := Matrix.mulVec_injective_of_isUnit hdet (hM.trans (Matrix.mulVec_zero _).symm)
  exact fun i => congrFun h0 i

theorem ggResSideDatum_of_indep {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n : ℕ} {M : CoxeterMatrix (Fin n)}
    (hWM : GGIsWeylMatrix M) {C : Matrix (Fin n) (Fin n) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (hind : LinearIndependent (ZMod p) h)
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (b : Fin n) (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin n // j ≠ b} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Fin n | j ≠ b})) :
    GGResSideDatum p Bs X J := by
  have hCJ : GGIntCartan (parMatrix M {j : Fin n | j ≠ b})
      (C.submatrix Subtype.val Subtype.val) := ggLeviDatum_ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Fin n // j ≠ b}, α (i : Fin n) (h (j : Fin n)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hFT : TauCeti.IsFiniteType
      (C.submatrix (Subtype.val : {j : Fin n // j ≠ b} → Fin n) Subtype.val) :=
    isFiniteType_of_ggIsWeylMatrixFixed hWMJ hCJ
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin n // j ≠ b} => ψ j) :=
    ggReflConjSimple_of_reflClosed ι (fun j : {j : Fin n // j ≠ b} => ψ j) hJ
      (ggReflClosed_of_indep hp hFT hCJ (fun j : {j : Fin n // j ≠ b} => h j)
        (fun j : {j : Fin n // j ≠ b} => α j) hpairJ (hind.comp _ Subtype.val_injective) _
        (fun j w => hlin j w))
  let fJ : (parMatrix M {j : Fin n | j ≠ b}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Fin n | j ≠ b} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Fin n | j ≠ b}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Fin n, inferInstance, inferInstance, b, M, C, parMatrix M {j : Fin n | j ≠ b}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hWM, hMC, hWMJ, fun _ _ => rfl, hlin, hrefl, hpair,
    ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

theorem ggResLeviSideDatumLE3_of_indep {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {n : ℕ} {M : CoxeterMatrix (Fin n)}
    (hWM : GGIsWeylMatrix M) {C : Matrix (Fin n) (Fin n) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Fin n → MulAut ↥Bs} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (hind : LinearIndependent (ZMod p) h)
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (S : Finset (Fin n)) (hS1 : 2 ≤ S.card) (hS2 : S.card ≤ 3)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin n // j ∉ S} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Fin n | j ∉ S})) :
    GGResLeviSideDatumLE3 p Bs X J := by
  have hCJ : GGIntCartan (parMatrix M {j : Fin n | j ∉ S})
      (C.submatrix Subtype.val Subtype.val) := ggLeviDatum_ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Fin n // j ∉ S}, α (i : Fin n) (h (j : Fin n)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hFT : TauCeti.IsFiniteType
      (C.submatrix (Subtype.val : {j : Fin n // j ∉ S} → Fin n) Subtype.val) :=
    isFiniteType_of_ggIsWeylMatrixFixed hWMJ hCJ
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin n // j ∉ S} => ψ j) :=
    ggReflConjSimple_of_reflClosed ι (fun j : {j : Fin n // j ∉ S} => ψ j) hJ
      (ggReflClosed_of_indep hp hFT hCJ (fun j : {j : Fin n // j ∉ S} => h j)
        (fun j : {j : Fin n // j ∉ S} => α j) hpairJ (hind.comp _ Subtype.val_injective) _
        (fun j w => hlin j w))
  let fJ : (parMatrix M {j : Fin n | j ∉ S}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Fin n | j ∉ S} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Fin n | j ∉ S}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Fin n, inferInstance, inferInstance, S, M, C, parMatrix M {j : Fin n | j ∉ S}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hS1, hS2, hWM, hMC, hWMJ, fun _ _ => rfl, hlin,
    hrefl, hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

theorem ggLeviDatum_conj {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    {Λ : Type} {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ)) (u : M.Group) :
    ∃ (h' : Λ → V) (α' : Λ → Module.Dual (ZMod p) V) (f' : M.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ i w, ggLin (p := p) ι ((f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹) w =
        w - α' i w • h' i) ∧
      (∀ i, GGIsReflection p ((f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹)) ∧
      (∀ i j, α' i (h' j) = (C i j : ZMod p)) ∧
      (∀ i, (f' (M.simple i) : MulAut ↥Bs) =
        (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹) ∧
      ggAutomizer X Bs = Subgroup.closure
        (Set.range fun i => (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹) ∧
      (LinearIndependent (ZMod p) h → LinearIndependent (ZMod p) h') := by
  classical
  let g : MulAut ↥Bs := (f u : MulAut ↥Bs)
  let W : V ≃ₗ[ZMod p] V := ggLin (p := p) ι g
  let h' : Λ → V := fun i => W (h i)
  let α' : Λ → Module.Dual (ZMod p) V :=
    fun i => (α i).comp (W.symm : V ≃ₗ[ZMod p] V).toLinearMap
  let f' : M.Group ≃* ↥(ggAutomizer X Bs) := (MulAut.conj u).trans f
  refine ⟨h', α', f', fun i v => ?_, fun i => ggLeviDatum_isReflection_conj (hrefl i) g,
    fun i j => ?_, fun i => ?_, ?_, fun hind => ?_⟩
  · have h1 := ggLeviDatum_ggLin_conj (p := p) ι g (φ i) (hlin i) v
    simpa only [α', h', W, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h1
  · simpa only [α', h', W, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] using hpair i j
  · show ((f (u * M.simple i * u⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = _
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf i]
  · have hgA : g ∈ ggAutomizer X Bs := (f u).2
    have hrange : Set.range (fun i => (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹) =
        (MulAut.conj g).toMonoidHom '' Set.range φ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨φ i, ⟨i, rfl⟩, (MulAut.conj_apply g (φ i)).symm⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, MulAut.conj_apply g (φ i)⟩
    rw [hrange, ← MonoidHom.map_closure, ← hclos]
    exact (ggLeviDatum_map_conj _ g hgA).symm
  · exact hind.map' W.toLinearMap (LinearEquiv.ker W)

end CFSG.StandardType

end
