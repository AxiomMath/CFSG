module

public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice

public section

namespace CFSG.StandardType

private abbrev r4o_Mat : Type := Matrix (Fin 5) (Fin 5) (ZMod 3)

private def r4o_refl (X : r4o_Mat) (k : Fin 5) : r4o_Mat :=
  Matrix.of fun i j => (if i = j then 1 else 0) - (if i = k then X k j else 0)

private def r4o_word (X : r4o_Mat) (w : List (Fin 5)) : r4o_Mat :=
  (w.map (r4o_refl X)).prod

private def r4o_rho (X : r4o_Mat) (w : List (Fin 5)) (k : Fin 5) : r4o_Mat :=
  r4o_word X w * r4o_refl X k * r4o_word X w.reverse

private noncomputable def r4o_leToLin {V : Type} [AddCommGroup V] [Module (ZMod 3) V] :
    (V ≃ₗ[ZMod 3] V) →* (V →ₗ[ZMod 3] V) where
  toFun e := e.toLinearMap
  map_one' := LinearEquiv.coe_toLinearMap_one
  map_mul' := fun _ _ => LinearEquiv.coe_toLinearMap_mul

private noncomputable def r4o_matHom {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (bs : Module.Basis (Fin 5) (ZMod 3) V) :
    (V →ₗ[ZMod 3] V) →* r4o_Mat where
  toFun f := LinearMap.toMatrix bs bs f
  map_one' := LinearMap.toMatrix_one bs
  map_mul' := fun f g => LinearMap.toMatrix_mul bs f g

private noncomputable def r4o_M {G : Type} [Group G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (bs : Module.Basis (Fin 5) (ZMod 3) V) : MulAut ↥Bs →* r4o_Mat :=
  (r4o_matHom bs).comp ((r4o_leToLin (V := V)).comp (ggLin ι))

private theorem r4o_M_injective {G : Type} [Group G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (bs : Module.Basis (Fin 5) (ZMod 3) V) : Function.Injective (r4o_M ι bs) := by
  intro φ ψ h
  have hmat : (LinearMap.toMatrix bs bs) (ggLin ι φ).toLinearMap =
      (LinearMap.toMatrix bs bs) (ggLin ι ψ).toLinearMap := h
  have hlin : (ggLin ι φ).toLinearMap = (ggLin ι ψ).toLinearMap :=
    (LinearMap.toMatrix bs bs).injective hmat
  exact ggLin_injective ι (LinearEquiv.toLinearMap_injective hlin)

private noncomputable def r4o_basis {G : Type} [Group G] [Fact (Nat.Prime 3)]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {c : Λ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤) (ee : Fin 5 ≃ Option Λ) :
    Module.Basis (Fin 5) (ZMod 3) V :=
  (Module.Basis.mk hD.indep hspan.ge).reindex ee.symm

private theorem r4o_basis_apply {G : Type} [Group G] [Fact (Nat.Prime 3)] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {c : Λ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤) (ee : Fin 5 ≃ Option Λ) (i : Fin 5) :
    r4o_basis hD hspan ee i = h' (ee i) := by
  rw [r4o_basis, Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.mk_apply]

private theorem r4o_matrix_entry {G : Type} [Group G] [Fact (Nat.Prime 3)] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {c : Λ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤)
    (ee : Fin 5 ≃ Option Λ) (k i j : Fin 5) :
    LinearMap.toMatrix (r4o_basis hD hspan ee) (r4o_basis hD hspan ee)
        (ggLin ι (φ' (ee k))).toLinearMap i j =
      (if i = j then 1 else 0) -
        (if i = k then ((ggAttachCartan C c (ee k) (ee j) : ℤ) : ZMod 3) else 0) := by
  rw [LinearMap.toMatrix_apply, r4o_basis_apply hD hspan ee j]
  change (r4o_basis hD hspan ee).repr ((ggLin ι (φ' (ee k))) (h' (ee j))) i =
    (if i = j then 1 else 0) -
      (if i = k then ((ggAttachCartan C c (ee k) (ee j) : ℤ) : ZMod 3) else 0)
  have hlin : (ggLin ι (φ' (ee k))) (h' (ee j)) =
      h' (ee j) - α' (ee k) (h' (ee j)) • h' (ee k) := hD.lin (ee k) (h' (ee j))
  have hpair : α' (ee k) (h' (ee j)) =
      ((ggAttachCartan C c (ee k) (ee j) : ℤ) : ZMod 3) := hD.pair (ee k) (ee j)
  rw [hlin, hpair, ← r4o_basis_apply hD hspan ee j, ← r4o_basis_apply hD hspan ee k]
  rw [map_sub, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  trans (Finsupp.single j (1 : ZMod 3)) i -
      (((↑(ggAttachCartan C c (ee k) (ee j)) : ZMod 3)) • (Finsupp.single k (1 : ZMod 3))) i
  · exact Finsupp.sub_apply _ _ _
  · rw [Finsupp.smul_apply, smul_eq_mul]
    by_cases hik : i = k
    · rw [hik, Finsupp.single_eq_same]
      by_cases hkj : k = j
      · rw [hkj]; simp
      · rw [Finsupp.single_eq_of_ne hkj]; simp [hkj]
    · rw [Finsupp.single_eq_of_ne hik]
      by_cases hij : i = j
      · subst hij; simp [hik]
      · rw [Finsupp.single_eq_of_ne hij]; simp [hik, hij]

private theorem r4o_assemble {G : Type} [Group G] [Fact (Nat.Prime 3)] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {c : Λ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤) {ee : Fin 5 ≃ Option Λ}
    {b : Λ} {n : Fin 4 → Λ} (hneb : ∀ i, n i ≠ b) {a : Fin 4 → Fin 5}
    (ha : ∀ i, ee (a i) = some (n i)) {X : r4o_Mat}
    (hM : ∀ k, r4o_M ι (r4o_basis hD hspan ee) (φ' (ee k)) = r4o_refl X k)
    {z : G} (hzB : z ∈ Bs) {cv : Fin 5 → ZMod 3}
    (hc : (r4o_basis hD hspan ee).repr (ι (Additive.ofMul ⟨z, hzB⟩)) = cv)
    {z1 z2 : Fin 5 → ZMod 3}
    (hdisj : cv = z1 ∨ cv = -z1 ∨ cv = z2 ∨ cv = -z2)
    {wc1 : List (Fin 5)} {k1 : Fin 5} {wc2 : List (Fin 5)} {k2 : Fin 5}
    (hfix1 : (r4o_rho X wc1 k1).mulVec z1 = z1 ∧ (r4o_rho X wc1 k1).mulVec (-z1) = -z1)
    (hfix2 : (r4o_rho X wc2 k2).mulVec z2 = z2 ∧ (r4o_rho X wc2 k2).mulVec (-z2) = -z2)
    (hinv1 : r4o_rho X wc1 k1 * r4o_rho X wc1 k1 = 1)
    (hinv2 : r4o_rho X wc2 k2 * r4o_rho X wc2 k2 = 1)
    (hord1 : (r4o_refl X (a 0) * r4o_refl X (a 1) * r4o_refl X (a 2) *
        (r4o_rho X wc1 k1 * r4o_refl X (a 3) * r4o_rho X wc1 k1)) ^ 5 = 1 ∧
      (r4o_refl X (a 0) * r4o_refl X (a 1) * r4o_refl X (a 2) *
        (r4o_rho X wc1 k1 * r4o_refl X (a 3) * r4o_rho X wc1 k1)) ≠ 1)
    (hord2 : (r4o_refl X (a 0) * r4o_refl X (a 1) * r4o_refl X (a 2) *
        (r4o_rho X wc2 k2 * r4o_refl X (a 3) * r4o_rho X wc2 k2)) ^ 5 = 1 ∧
      (r4o_refl X (a 0) * r4o_refl X (a 1) * r4o_refl X (a 2) *
        (r4o_rho X wc2 k2 * r4o_refl X (a 3) * r4o_rho X wc2 k2)) ≠ 1) :
    ∃ ρ ∈ ggAutomizer ⊤ Bs, ρ ⟨z, hzB⟩ = ⟨z, hzB⟩ ∧
      ∃ s : Fin 4 → MulAut ↥Bs, (∀ i, ∃ j : Λ, j ≠ b ∧ s i = φ' (some j)) ∧
        5 ∣ orderOf (s 0 * s 1 * s 2 * (ρ * s 3 * ρ⁻¹)) := by
  have hprime5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let bs : Module.Basis (Fin 5) (ZMod 3) V := r4o_basis hD hspan ee
  let s : Fin 4 → MulAut ↥Bs := fun i => φ' (ee (a i))
  have hmem_phi : ∀ o : Option Λ, φ' o ∈ ggAutomizer ⊤ Bs := fun o =>
    Subgroup.subset_closure (hD.mem o)
  have hprod_mem : ∀ l : List (Fin 5),
      ((l.map (fun k => φ' (ee k))).prod) ∈ ggAutomizer ⊤ Bs := by
    intro l
    induction l with
    | nil => simp
    | cons k l ih =>
        rw [List.map_cons, List.prod_cons]
        exact Subgroup.mul_mem _ (hmem_phi (ee k)) ih
  have hsz : ∀ i, ∃ j : Λ, j ≠ b ∧ s i = φ' (some j) := by
    intro i
    exact ⟨n i, hneb i, by simp only [s, ha i]⟩
  let ρ1 : MulAut ↥Bs :=
    (wc1.map (fun k => φ' (ee k))).prod * φ' (ee k1) *
      (wc1.reverse.map (fun k => φ' (ee k))).prod
  let ρ2 : MulAut ↥Bs :=
    (wc2.map (fun k => φ' (ee k))).prod * φ' (ee k2) *
      (wc2.reverse.map (fun k => φ' (ee k))).prod
  have hmem1 : ρ1 ∈ ggAutomizer ⊤ Bs := by
    simp only [ρ1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hprod_mem wc1) (hmem_phi (ee k1)))
      (hprod_mem wc1.reverse)
  have hmem2 : ρ2 ∈ ggAutomizer ⊤ Bs := by
    simp only [ρ2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hprod_mem wc2) (hmem_phi (ee k2)))
      (hprod_mem wc2.reverse)
  have hmap1 : (wc1.map ((r4o_M ι (r4o_basis hD hspan ee)) ∘ fun k => φ' (ee k))) =
      wc1.map (r4o_refl X) := by
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    exact hM k
  have hmap1r : (wc1.reverse.map ((r4o_M ι (r4o_basis hD hspan ee)) ∘ fun k => φ' (ee k))) =
      wc1.reverse.map (r4o_refl X) := by
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    exact hM k
  have hmap2 : (wc2.map ((r4o_M ι (r4o_basis hD hspan ee)) ∘ fun k => φ' (ee k))) =
      wc2.map (r4o_refl X) := by
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    exact hM k
  have hmap2r : (wc2.reverse.map ((r4o_M ι (r4o_basis hD hspan ee)) ∘ fun k => φ' (ee k))) =
      wc2.reverse.map (r4o_refl X) := by
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    exact hM k
  have hMρ1 : r4o_M ι (r4o_basis hD hspan ee) ρ1 = r4o_rho X wc1 k1 := by
    simp only [ρ1, r4o_rho, r4o_word, map_mul, map_list_prod, List.map_map]
    rw [hmap1, hmap1r]
    simp only [hM]
  have hMρ2 : r4o_M ι (r4o_basis hD hspan ee) ρ2 = r4o_rho X wc2 k2 := by
    simp only [ρ2, r4o_rho, r4o_word, map_mul, map_list_prod, List.map_map]
    rw [hmap2, hmap2r]
    simp only [hM]
  have hinv1' : ρ1 * ρ1 = 1 := by
    apply r4o_M_injective ι bs
    rw [map_mul, hMρ1, hinv1, map_one]
  have hinv2' : ρ2 * ρ2 = 1 := by
    apply r4o_M_injective ι bs
    rw [map_mul, hMρ2, hinv2, map_one]
  have hρ1inv : ρ1⁻¹ = ρ1 := inv_eq_of_mul_eq_one_right hinv1'
  have hρ2inv : ρ2⁻¹ = ρ2 := inv_eq_of_mul_eq_one_right hinv2'
  have hdvd1 : 5 ∣ orderOf (s 0 * s 1 * s 2 * (ρ1 * s 3 * ρ1⁻¹)) := by
    rw [hρ1inv]
    have hMprod : r4o_M ι bs (s 0 * s 1 * s 2 * (ρ1 * s 3 * ρ1)) =
        r4o_refl X (a 0) * r4o_refl X (a 1) * r4o_refl X (a 2) *
          (r4o_rho X wc1 k1 * r4o_refl X (a 3) * r4o_rho X wc1 k1) := by
      dsimp only [s, bs]
      simp only [map_mul]
      rw [hMρ1]
      simp only [hM]
    have hord : orderOf (r4o_M ι bs (s 0 * s 1 * s 2 * (ρ1 * s 3 * ρ1))) = 5 := by
      rw [hMprod]
      exact orderOf_eq_prime (hp := hprime5) hord1.1 hord1.2
    have hd := orderOf_map_dvd (r4o_M ι bs) (s 0 * s 1 * s 2 * (ρ1 * s 3 * ρ1))
    rwa [hord] at hd
  have hdvd2 : 5 ∣ orderOf (s 0 * s 1 * s 2 * (ρ2 * s 3 * ρ2⁻¹)) := by
    rw [hρ2inv]
    have hMprod : r4o_M ι bs (s 0 * s 1 * s 2 * (ρ2 * s 3 * ρ2)) =
        r4o_refl X (a 0) * r4o_refl X (a 1) * r4o_refl X (a 2) *
          (r4o_rho X wc2 k2 * r4o_refl X (a 3) * r4o_rho X wc2 k2) := by
      dsimp only [s, bs]
      simp only [map_mul]
      rw [hMρ2]
      simp only [hM]
    have hord : orderOf (r4o_M ι bs (s 0 * s 1 * s 2 * (ρ2 * s 3 * ρ2))) = 5 := by
      rw [hMprod]
      exact orderOf_eq_prime (hp := hprime5) hord2.1 hord2.2
    have hd := orderOf_map_dvd (r4o_M ι bs) (s 0 * s 1 * s 2 * (ρ2 * s 3 * ρ2))
    rwa [hord] at hd
  have hfix_vec : ∀ (ρ : MulAut ↥Bs) (A : r4o_Mat) (zz : Fin 5 → ZMod 3),
      r4o_M ι (r4o_basis hD hspan ee) ρ = A → A.mulVec zz = zz → cv = zz →
      ggLin (p := 3) ι ρ (ι (Additive.ofMul ⟨z, hzB⟩)) = ι (Additive.ofMul ⟨z, hzB⟩) := by
    intro ρ A zz hMA hfixA hcv
    apply bs.repr.injective
    ext i
    have hmat := LinearMap.toMatrix_mulVec_repr bs bs (ggLin (p := 3) ι ρ).toLinearMap
      (ι (Additive.ofMul ⟨z, hzB⟩))
    have hmat_i := congrFun hmat i
    calc (bs.repr ((ggLin (p := 3) ι ρ) (ι (Additive.ofMul ⟨z, hzB⟩)))) i
        = ((LinearMap.toMatrix bs bs (ggLin (p := 3) ι ρ).toLinearMap).mulVec
            (bs.repr (ι (Additive.ofMul ⟨z, hzB⟩)))) i := hmat_i.symm
      _ = ((LinearMap.toMatrix bs bs (ggLin (p := 3) ι ρ).toLinearMap).mulVec cv) i := by
            rw [hc]
      _ = ((LinearMap.toMatrix bs bs (ggLin (p := 3) ι ρ).toLinearMap).mulVec zz) i := by
            rw [hcv]
      _ = (A.mulVec zz) i := by
            rw [show (LinearMap.toMatrix bs bs (ggLin (p := 3) ι ρ).toLinearMap) = A from hMA]
      _ = zz i := congrFun hfixA i
      _ = (bs.repr (ι (Additive.ofMul ⟨z, hzB⟩))) i :=
            ((congrFun hc i).trans (congrFun hcv i)).symm
  have hfixvec1 : cv = z1 ∨ cv = -z1 →
      ggLin (p := 3) ι ρ1 (ι (Additive.ofMul ⟨z, hzB⟩)) = ι (Additive.ofMul ⟨z, hzB⟩) := by
    rintro (h | h)
    · exact hfix_vec ρ1 (r4o_rho X wc1 k1) z1 hMρ1 hfix1.1 h
    · exact hfix_vec ρ1 (r4o_rho X wc1 k1) (-z1) hMρ1 hfix1.2 h
  have hfixvec2 : cv = z2 ∨ cv = -z2 →
      ggLin (p := 3) ι ρ2 (ι (Additive.ofMul ⟨z, hzB⟩)) = ι (Additive.ofMul ⟨z, hzB⟩) := by
    rintro (h | h)
    · exact hfix_vec ρ2 (r4o_rho X wc2 k2) z2 hMρ2 hfix2.1 h
    · exact hfix_vec ρ2 (r4o_rho X wc2 k2) (-z2) hMρ2 hfix2.2 h
  rcases hdisj with h | h | h | h
  · refine ⟨ρ1, hmem1, ?_, s, hsz, hdvd1⟩
    exact (ggLin_fix_iff (p := 3) ι ρ1 ⟨z, hzB⟩).mpr (hfixvec1 (Or.inl h))
  · refine ⟨ρ1, hmem1, ?_, s, hsz, hdvd1⟩
    exact (ggLin_fix_iff (p := 3) ι ρ1 ⟨z, hzB⟩).mpr (hfixvec1 (Or.inr h))
  · refine ⟨ρ2, hmem2, ?_, s, hsz, hdvd2⟩
    exact (ggLin_fix_iff (p := 3) ι ρ2 ⟨z, hzB⟩).mpr (hfixvec2 (Or.inl h))
  · refine ⟨ρ2, hmem2, ?_, s, hsz, hdvd2⟩
    exact (ggLin_fix_iff (p := 3) ι ρ2 ⟨z, hzB⟩).mpr (hfixvec2 (Or.inr h))

private theorem r4o_root_coord {G : Type} [Group G] [Fact (Nat.Prime 3)] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {c : Λ} {φ' : Option Λ → MulAut ↥Bs}
    {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod 3) (Set.range h') = ⊤) (ee : Fin 5 ≃ Option Λ)
    (v : V) {co : Fin 5 → ZMod 3} (hc : (r4o_basis hD hspan ee).repr v = co) (k : Fin 5) :
    α' (ee k) v = ∑ j, co j * (ggAttachCartan C c (ee k) (ee j) : ZMod 3) := by
  have hv : v = ∑ j, co j • (r4o_basis hD hspan ee) j := by
    rw [← hc]
    exact (Module.Basis.sum_repr (r4o_basis hD hspan ee) v).symm
  rw [hv, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, r4o_basis_apply hD hspan ee j, hD.pair (ee k) (ee j)]

private def r4o_Xa : r4o_Mat :=
  !![2, 2, 0, 0, 0; 2, 2, 1, 0, 2; 0, 2, 2, 2, 0; 0, 0, 2, 2, 0; 0, 2, 0, 0, 2]

private def r4o_Xb : r4o_Mat :=
  !![2, 2, 0, 0, 0; 2, 2, 1, 0, 0; 0, 2, 2, 2, 2; 0, 0, 2, 2, 0; 0, 0, 2, 0, 2]

private def r4o_XaT : r4o_Mat :=
  !![2, 2, 0, 0, 0; 2, 2, 2, 0, 2; 0, 1, 2, 2, 0; 0, 0, 2, 2, 0; 0, 2, 0, 0, 2]

private def r4o_XbT : r4o_Mat :=
  !![2, 2, 0, 0, 0; 2, 2, 2, 0, 0; 0, 1, 2, 2, 2; 0, 0, 2, 2, 0; 0, 0, 2, 0, 2]

private theorem r4o_fin_Xa :
    (r4o_rho r4o_Xa [4, 0, 1] 2).mulVec ![1, 0, 0, 0, 2] = ![1, 0, 0, 0, 2] ∧
    (r4o_rho r4o_Xa [4, 0, 1] 2).mulVec (-![1, 0, 0, 0, 2]) = -![1, 0, 0, 0, 2] ∧
    (r4o_rho r4o_Xa [0, 1, 4, 2] 1).mulVec ![1, 0, 2, 1, 1] = ![1, 0, 2, 1, 1] ∧
    (r4o_rho r4o_Xa [0, 1, 4, 2] 1).mulVec (-![1, 0, 2, 1, 1]) = -![1, 0, 2, 1, 1] ∧
    r4o_rho r4o_Xa [4, 0, 1] 2 * r4o_rho r4o_Xa [4, 0, 1] 2 = 1 ∧
    r4o_rho r4o_Xa [0, 1, 4, 2] 1 * r4o_rho r4o_Xa [0, 1, 4, 2] 1 = 1 ∧
    (r4o_refl r4o_Xa 1 * r4o_refl r4o_Xa 2 * r4o_refl r4o_Xa 3 *
      (r4o_rho r4o_Xa [4, 0, 1] 2 * r4o_refl r4o_Xa 1 * r4o_rho r4o_Xa [4, 0, 1] 2)) ^ 5 = 1 ∧
    (r4o_refl r4o_Xa 1 * r4o_refl r4o_Xa 2 * r4o_refl r4o_Xa 3 *
      (r4o_rho r4o_Xa [4, 0, 1] 2 * r4o_refl r4o_Xa 1 * r4o_rho r4o_Xa [4, 0, 1] 2)) ≠ 1 ∧
    (r4o_refl r4o_Xa 1 * r4o_refl r4o_Xa 2 * r4o_refl r4o_Xa 3 *
      (r4o_rho r4o_Xa [0, 1, 4, 2] 1 * r4o_refl r4o_Xa 1 * r4o_rho r4o_Xa [0, 1, 4, 2] 1)) ^ 5 = 1 ∧
    (r4o_refl r4o_Xa 1 * r4o_refl r4o_Xa 2 * r4o_refl r4o_Xa 3 *
      (r4o_rho r4o_Xa [0, 1, 4, 2] 1 * r4o_refl r4o_Xa 1 * r4o_rho r4o_Xa [0, 1, 4, 2] 1)) ≠ 1 := by
  decide +kernel

private theorem r4o_fin_Xb :
    (r4o_rho r4o_Xb [4, 3, 2] 1).mulVec ![0, 0, 0, 1, 2] = ![0, 0, 0, 1, 2] ∧
    (r4o_rho r4o_Xb [4, 3, 2] 1).mulVec (-![0, 0, 0, 1, 2]) = -![0, 0, 0, 1, 2] ∧
    (r4o_rho r4o_Xb [3, 2, 4, 1] 2).mulVec ![1, 2, 0, 2, 2] = ![1, 2, 0, 2, 2] ∧
    (r4o_rho r4o_Xb [3, 2, 4, 1] 2).mulVec (-![1, 2, 0, 2, 2]) = -![1, 2, 0, 2, 2] ∧
    r4o_rho r4o_Xb [4, 3, 2] 1 * r4o_rho r4o_Xb [4, 3, 2] 1 = 1 ∧
    r4o_rho r4o_Xb [3, 2, 4, 1] 2 * r4o_rho r4o_Xb [3, 2, 4, 1] 2 = 1 ∧
    (r4o_refl r4o_Xb 0 * r4o_refl r4o_Xb 1 * r4o_refl r4o_Xb 2 *
      (r4o_rho r4o_Xb [4, 3, 2] 1 * r4o_refl r4o_Xb 2 * r4o_rho r4o_Xb [4, 3, 2] 1)) ^ 5 = 1 ∧
    (r4o_refl r4o_Xb 0 * r4o_refl r4o_Xb 1 * r4o_refl r4o_Xb 2 *
      (r4o_rho r4o_Xb [4, 3, 2] 1 * r4o_refl r4o_Xb 2 * r4o_rho r4o_Xb [4, 3, 2] 1)) ≠ 1 ∧
    (r4o_refl r4o_Xb 0 * r4o_refl r4o_Xb 1 * r4o_refl r4o_Xb 2 *
      (r4o_rho r4o_Xb [3, 2, 4, 1] 2 * r4o_refl r4o_Xb 2 * r4o_rho r4o_Xb [3, 2, 4, 1] 2)) ^ 5 = 1 ∧
    (r4o_refl r4o_Xb 0 * r4o_refl r4o_Xb 1 * r4o_refl r4o_Xb 2 *
      (r4o_rho r4o_Xb [3, 2, 4, 1] 2 * r4o_refl r4o_Xb 2 * r4o_rho r4o_Xb [3, 2, 4, 1] 2)) ≠ 1 := by
  decide +kernel

private theorem r4o_fin_XaT :
    (r4o_rho r4o_XaT [4, 0, 1] 2).mulVec ![1, 0, 0, 0, 2] = ![1, 0, 0, 0, 2] ∧
    (r4o_rho r4o_XaT [4, 0, 1] 2).mulVec (-![1, 0, 0, 0, 2]) = -![1, 0, 0, 0, 2] ∧
    (r4o_rho r4o_XaT [0, 1, 4, 2] 1).mulVec ![1, 0, 1, 2, 1] = ![1, 0, 1, 2, 1] ∧
    (r4o_rho r4o_XaT [0, 1, 4, 2] 1).mulVec (-![1, 0, 1, 2, 1]) = -![1, 0, 1, 2, 1] ∧
    r4o_rho r4o_XaT [4, 0, 1] 2 * r4o_rho r4o_XaT [4, 0, 1] 2 = 1 ∧
    r4o_rho r4o_XaT [0, 1, 4, 2] 1 * r4o_rho r4o_XaT [0, 1, 4, 2] 1 = 1 ∧
    (r4o_refl r4o_XaT 1 * r4o_refl r4o_XaT 2 * r4o_refl r4o_XaT 3 *
      (r4o_rho r4o_XaT [4, 0, 1] 2 * r4o_refl r4o_XaT 1 * r4o_rho r4o_XaT [4, 0, 1] 2)) ^ 5 = 1 ∧
    (r4o_refl r4o_XaT 1 * r4o_refl r4o_XaT 2 * r4o_refl r4o_XaT 3 *
      (r4o_rho r4o_XaT [4, 0, 1] 2 * r4o_refl r4o_XaT 1 * r4o_rho r4o_XaT [4, 0, 1] 2)) ≠ 1 ∧
    (r4o_refl r4o_XaT 1 * r4o_refl r4o_XaT 2 * r4o_refl r4o_XaT 3 *
      (r4o_rho r4o_XaT [0, 1, 4, 2] 1 * r4o_refl r4o_XaT 1 *
        r4o_rho r4o_XaT [0, 1, 4, 2] 1)) ^ 5 = 1 ∧
    (r4o_refl r4o_XaT 1 * r4o_refl r4o_XaT 2 * r4o_refl r4o_XaT 3 *
      (r4o_rho r4o_XaT [0, 1, 4, 2] 1 * r4o_refl r4o_XaT 1 *
        r4o_rho r4o_XaT [0, 1, 4, 2] 1)) ≠ 1 := by
  decide +kernel

private theorem r4o_fin_XbT :
    (r4o_rho r4o_XbT [4, 3, 2] 1).mulVec ![0, 0, 0, 1, 2] = ![0, 0, 0, 1, 2] ∧
    (r4o_rho r4o_XbT [4, 3, 2] 1).mulVec (-![0, 0, 0, 1, 2]) = -![0, 0, 0, 1, 2] ∧
    (r4o_rho r4o_XbT [3, 2, 4, 1] 2).mulVec ![1, 2, 0, 1, 1] = ![1, 2, 0, 1, 1] ∧
    (r4o_rho r4o_XbT [3, 2, 4, 1] 2).mulVec (-![1, 2, 0, 1, 1]) = -![1, 2, 0, 1, 1] ∧
    r4o_rho r4o_XbT [4, 3, 2] 1 * r4o_rho r4o_XbT [4, 3, 2] 1 = 1 ∧
    r4o_rho r4o_XbT [3, 2, 4, 1] 2 * r4o_rho r4o_XbT [3, 2, 4, 1] 2 = 1 ∧
    (r4o_refl r4o_XbT 0 * r4o_refl r4o_XbT 1 * r4o_refl r4o_XbT 2 *
      (r4o_rho r4o_XbT [4, 3, 2] 1 * r4o_refl r4o_XbT 2 * r4o_rho r4o_XbT [4, 3, 2] 1)) ^ 5 = 1 ∧
    (r4o_refl r4o_XbT 0 * r4o_refl r4o_XbT 1 * r4o_refl r4o_XbT 2 *
      (r4o_rho r4o_XbT [4, 3, 2] 1 * r4o_refl r4o_XbT 2 * r4o_rho r4o_XbT [4, 3, 2] 1)) ≠ 1 ∧
    (r4o_refl r4o_XbT 0 * r4o_refl r4o_XbT 1 * r4o_refl r4o_XbT 2 *
      (r4o_rho r4o_XbT [3, 2, 4, 1] 2 * r4o_refl r4o_XbT 2 *
        r4o_rho r4o_XbT [3, 2, 4, 1] 2)) ^ 5 = 1 ∧
    (r4o_refl r4o_XbT 0 * r4o_refl r4o_XbT 1 * r4o_refl r4o_XbT 2 *
      (r4o_rho r4o_XbT [3, 2, 4, 1] 2 * r4o_refl r4o_XbT 2 *
        r4o_rho r4o_XbT [3, 2, 4, 1] 2)) ≠ 1 := by
  decide +kernel

private theorem r4o_row_Xa {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) (hc : c = e 1)
    (ee : Fin 5 ≃ Option Λ) (hee : ∀ i, ee (Fin.castSucc i) = some (e i))
    (hee4 : ee (Fin.last 4) = none) (k j : Fin 5) :
    (ggAttachCartan C c (ee k) (ee j) : ZMod 3) = r4o_Xa k j := by
  have h0 : ee 0 = some (e 0) := by simpa using hee 0
  have h1 : ee 1 = some (e 1) := by simpa using hee 1
  have h2 : ee 2 = some (e 2) := by simpa using hee 2
  have h3 : ee 3 = some (e 3) := by simpa using hee 3
  have h4 : ee 4 = none := by simpa using hee4
  fin_cases k <;> fin_cases j <;>
    simp [r4o_Xa, ggAttachCartan, hC, hc, h0, h1, h2, h3, h4, e.injective.eq_iff,
      CartanMatrix.F₄] <;> decide

private theorem r4o_disj_Xa :
    ∀ cx cy : Fin 5 → ZMod 3,
      (∀ i : Fin 4, ∑ j, cx j * r4o_Xa (Fin.castSucc i) j = 0) →
      (∀ i : Fin 4, i ≠ 0 → ∑ j, cy j * r4o_Xa (Fin.castSucc i) j = 0) →
      (∑ j, cy j * r4o_Xa (Fin.last 4) j = 0) → cx ≠ 0 → cy ≠ 0 →
      cx + cy = ![1, 0, 0, 0, 2] ∨ cx + cy = -![1, 0, 0, 0, 2] ∨
        cx + cy = ![1, 0, 2, 1, 1] ∨ cx + cy = -![1, 0, 2, 1, 1] := by
  decide +kernel

private theorem r4o_row_Xb {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) (hc : c = e 2)
    (ee : Fin 5 ≃ Option Λ) (hee : ∀ i, ee (Fin.castSucc i) = some (e i))
    (hee4 : ee (Fin.last 4) = none) (k j : Fin 5) :
    (ggAttachCartan C c (ee k) (ee j) : ZMod 3) = r4o_Xb k j := by
  have h0 : ee 0 = some (e 0) := by simpa using hee 0
  have h1 : ee 1 = some (e 1) := by simpa using hee 1
  have h2 : ee 2 = some (e 2) := by simpa using hee 2
  have h3 : ee 3 = some (e 3) := by simpa using hee 3
  have h4 : ee 4 = none := by simpa using hee4
  fin_cases k <;> fin_cases j <;>
    simp [r4o_Xb, ggAttachCartan, hC, hc, h0, h1, h2, h3, h4, e.injective.eq_iff,
      CartanMatrix.F₄] <;> decide

private theorem r4o_disj_Xb :
    ∀ cx cy : Fin 5 → ZMod 3,
      (∀ i : Fin 4, ∑ j, cx j * r4o_Xb (Fin.castSucc i) j = 0) →
      (∀ i : Fin 4, i ≠ 3 → ∑ j, cy j * r4o_Xb (Fin.castSucc i) j = 0) →
      (∑ j, cy j * r4o_Xb (Fin.last 4) j = 0) → cx ≠ 0 → cy ≠ 0 →
      (cx + cy = ![0, 0, 0, 1, 2] ∨ cx + cy = -![0, 0, 0, 1, 2] ∨
        cx + cy = ![1, 2, 0, 2, 2] ∨ cx + cy = -![1, 2, 0, 2, 2]) := by
  decide +kernel

private theorem r4o_row_XaT {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i) (hc : c = e 1)
    (ee : Fin 5 ≃ Option Λ) (hee : ∀ i, ee (Fin.castSucc i) = some (e i))
    (hee4 : ee (Fin.last 4) = none) (k j : Fin 5) :
    (ggAttachCartan C c (ee k) (ee j) : ZMod 3) = r4o_XaT k j := by
  have h0 : ee 0 = some (e 0) := by simpa using hee 0
  have h1 : ee 1 = some (e 1) := by simpa using hee 1
  have h2 : ee 2 = some (e 2) := by simpa using hee 2
  have h3 : ee 3 = some (e 3) := by simpa using hee 3
  have h4 : ee 4 = none := by simpa using hee4
  fin_cases k <;> fin_cases j <;>
    simp [r4o_XaT, ggAttachCartan, hC, hc, h0, h1, h2, h3, h4, e.injective.eq_iff,
      CartanMatrix.F₄] <;> decide

private theorem r4o_disj_XaT :
    ∀ cx cy : Fin 5 → ZMod 3,
      (∀ i : Fin 4, ∑ j, cx j * r4o_XaT (Fin.castSucc i) j = 0) →
      (∀ i : Fin 4, i ≠ 0 → ∑ j, cy j * r4o_XaT (Fin.castSucc i) j = 0) →
      (∑ j, cy j * r4o_XaT (Fin.last 4) j = 0) → cx ≠ 0 → cy ≠ 0 →
      (cx + cy = ![1, 0, 0, 0, 2] ∨ cx + cy = -![1, 0, 0, 0, 2] ∨
        cx + cy = ![1, 0, 1, 2, 1] ∨ cx + cy = -![1, 0, 1, 2, 1]) := by
  decide +kernel

private theorem r4o_row_XbT {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i) (hc : c = e 2)
    (ee : Fin 5 ≃ Option Λ) (hee : ∀ i, ee (Fin.castSucc i) = some (e i))
    (hee4 : ee (Fin.last 4) = none) (k j : Fin 5) :
    (ggAttachCartan C c (ee k) (ee j) : ZMod 3) = r4o_XbT k j := by
  have h0 : ee 0 = some (e 0) := by simpa using hee 0
  have h1 : ee 1 = some (e 1) := by simpa using hee 1
  have h2 : ee 2 = some (e 2) := by simpa using hee 2
  have h3 : ee 3 = some (e 3) := by simpa using hee 3
  have h4 : ee 4 = none := by simpa using hee4
  fin_cases k <;> fin_cases j <;>
    simp [r4o_XbT, ggAttachCartan, hC, hc, h0, h1, h2, h3, h4, e.injective.eq_iff,
      CartanMatrix.F₄] <;> decide

private theorem r4o_disj_XbT :
    ∀ cx cy : Fin 5 → ZMod 3,
      (∀ i : Fin 4, ∑ j, cx j * r4o_XbT (Fin.castSucc i) j = 0) →
      (∀ i : Fin 4, i ≠ 3 → ∑ j, cy j * r4o_XbT (Fin.castSucc i) j = 0) →
      (∑ j, cy j * r4o_XbT (Fin.last 4) j = 0) → cx ≠ 0 → cy ≠ 0 →
      (cx + cy = ![0, 0, 0, 1, 2] ∨ cx + cy = -![0, 0, 0, 1, 2] ∨
        cx + cy = ![1, 2, 0, 1, 1] ∨ cx + cy = -![1, 2, 0, 1, 1]) := by
  decide +kernel

theorem ggR4_order_five {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {C : Matrix Λ Λ ℤ} {b c : Λ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod p) (Set.range h') = ⊤)
    (hcell : ∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
        (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧
      ((b = e 0 ∧ c = e 1) ∨ (b = e 3 ∧ c = e 2)))
    {x y : G} (hxB : x ∈ Bs) (hyB : y ∈ Bs) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx : ∀ i : Λ, α' (some i) (ι (Additive.ofMul ⟨x, hxB⟩)) = 0)
    (hy : ∀ o : Option Λ, o ≠ some b → α' o (ι (Additive.ofMul ⟨y, hyB⟩)) = 0) :
    ∃ ρ ∈ ggAutomizer ⊤ Bs, ρ ⟨x * y, mul_mem hxB hyB⟩ = ⟨x * y, mul_mem hxB hyB⟩ ∧
      ∃ s : Fin 4 → MulAut ↥Bs, (∀ i, ∃ j : Λ, j ≠ b ∧ s i = φ' (some j)) ∧
        5 ∣ orderOf (s 0 * s 1 * s 2 * (ρ * s 3 * ρ⁻¹)) := by
  subst hp3
  obtain ⟨e, horient, hcase⟩ := hcell
  let ee : Fin 5 ≃ Option Λ :=
    (finSuccEquivLast : Fin 5 ≃ Option (Fin 4)).trans (Equiv.optionCongr e)
  have hee : ∀ i : Fin 4, ee (Fin.castSucc i) = some (e i) := by
    intro i
    simp [ee, finSuccEquivLast_castSucc]
  have hee4 : ee (Fin.last 4) = none := by
    rw [show ee (Fin.last 4) =
        (Equiv.optionCongr e) (finSuccEquivLast (Fin.last 4)) from rfl, finSuccEquivLast_last]
    rfl
  have hee0 : ee 0 = some (e 0) := by simpa using hee 0
  have hee1 : ee 1 = some (e 1) := by simpa using hee 1
  have hee2 : ee 2 = some (e 2) := by simpa using hee 2
  have hee3 : ee 3 = some (e 3) := by simpa using hee 3
  have hprime5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let bs : Module.Basis (Fin 5) (ZMod 3) V := r4o_basis hD hspan ee
  let cx : Fin 5 → ZMod 3 := bs.repr (ι (Additive.ofMul ⟨x, hxB⟩))
  let cy : Fin 5 → ZMod 3 := bs.repr (ι (Additive.ofMul ⟨y, hyB⟩))
  have hrowx : ∀ i : Fin 4,
      ∑ j, cx j * (ggAttachCartan C c (some (e i)) (ee j) : ZMod 3) = 0 := by
    intro i
    have h := r4o_root_coord hD hspan ee (ι (Additive.ofMul ⟨x, hxB⟩)) rfl (Fin.castSucc i)
    rw [hee i] at h
    rw [← h]
    exact hx (e i)
  have hrowy : ∀ i : Fin 4, e i ≠ b →
      ∑ j, cy j * (ggAttachCartan C c (some (e i)) (ee j) : ZMod 3) = 0 := by
    intro i hi
    have h := r4o_root_coord hD hspan ee (ι (Additive.ofMul ⟨y, hyB⟩)) rfl (Fin.castSucc i)
    rw [hee i] at h
    rw [← h]
    exact hy (some (e i)) (fun hh => hi (Option.some.inj hh))
  have hrowyN : ∑ j, cy j * (ggAttachCartan C c none (ee j) : ZMod 3) = 0 := by
    have h := r4o_root_coord hD hspan ee (ι (Additive.ofMul ⟨y, hyB⟩)) rfl (Fin.last 4)
    rw [hee4] at h
    rw [← h]
    exact hy none (by simp)
  have hcx0 : cx ≠ 0 := by
    intro h0
    have hv : ι (Additive.ofMul ⟨x, hxB⟩) = 0 := by
      apply bs.repr.injective
      apply Finsupp.ext
      intro i
      have h0i : cx i = 0 := by rw [h0]; rfl
      simpa using h0i
    have hv' : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = 0 := by
      apply ι.injective
      rw [hv, map_zero]
    have h1 : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = Additive.ofMul (1 : ↥Bs) := by
      rw [hv']; rfl
    have : (⟨x, hxB⟩ : ↥Bs) = 1 := Additive.ofMul.injective h1
    exact hx1 (congrArg Subtype.val this)
  have hcy0 : cy ≠ 0 := by
    intro h0
    have hv : ι (Additive.ofMul ⟨y, hyB⟩) = 0 := by
      apply bs.repr.injective
      apply Finsupp.ext
      intro i
      have h0i : cy i = 0 := by rw [h0]; rfl
      simpa using h0i
    have hv' : Additive.ofMul (⟨y, hyB⟩ : ↥Bs) = 0 := by
      apply ι.injective
      rw [hv, map_zero]
    have h1 : Additive.ofMul (⟨y, hyB⟩ : ↥Bs) = Additive.ofMul (1 : ↥Bs) := by
      rw [hv']; rfl
    have : (⟨y, hyB⟩ : ↥Bs) = 1 := Additive.ofMul.injective h1
    exact hy1 (congrArg Subtype.val this)
  have hcxy : bs.repr (ι (Additive.ofMul ⟨x * y, mul_mem hxB hyB⟩)) = cx + cy := by
    have hofmul : Additive.ofMul (⟨x * y, mul_mem hxB hyB⟩ : ↥Bs) =
        Additive.ofMul (⟨x, hxB⟩ : ↥Bs) + Additive.ofMul (⟨y, hyB⟩ : ↥Bs) := rfl
    rw [hofmul, map_add, map_add]
    rfl
  rcases horient with hF | hFT
  · rcases hcase with ⟨hb, hc⟩ | ⟨hb, hc⟩
    ·
      have hM : ∀ k, r4o_M ι (r4o_basis hD hspan ee) (φ' (ee k)) = r4o_refl r4o_Xa k := by
        intro k
        ext i j
        change LinearMap.toMatrix (r4o_basis hD hspan ee) (r4o_basis hD hspan ee)
            (ggLin ι (φ' (ee k))).toLinearMap i j = (r4o_refl r4o_Xa k) i j
        rw [r4o_matrix_entry hD hspan ee k i j]
        rw [r4o_row_Xa e hF hc ee hee hee4 k j]
        rfl
      have hxL : ∀ i : Fin 4, ∑ j, cx j * r4o_Xa (Fin.castSucc i) j = 0 := by
        intro i
        have h := hrowx i
        rw [← hee i] at h
        have hsum : (∑ j, cx j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cx j * r4o_Xa (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_Xa e hF hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyL : ∀ i : Fin 4, i ≠ 0 → ∑ j, cy j * r4o_Xa (Fin.castSucc i) j = 0 := by
        intro i hi
        have h := hrowy i (by rw [hb]; exact fun hh => hi (e.injective hh))
        rw [← hee i] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_Xa (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_Xa e hF hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyN : ∑ j, cy j * r4o_Xa (Fin.last 4) j = 0 := by
        have h := hrowyN
        rw [← hee4] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.last 4)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_Xa (Fin.last 4) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_Xa e hF hc ee hee hee4 (Fin.last 4) j]
        rwa [hsum] at h
      have hdisj := r4o_disj_Xa cx cy hxL hyL hyN hcx0 hcy0
      obtain ⟨hf1, hf1n, hf2, hf2n, hi1, hi2, ho1, ho1ne, ho2, ho2ne⟩ := r4o_fin_Xa
      refine r4o_assemble (z := x * y) (hzB := mul_mem hxB hyB) hD hspan
        (b := b) (n := ![e 1, e 2, e 3, e 1])
        (hneb := by intro i; fin_cases i <;> simp [hb, e.injective.ne_iff])
        (a := ![1, 2, 3, 1]) (ha := by intro i; fin_cases i <;> simp [hee1, hee2, hee3])
        (X := r4o_Xa) (hM := hM) (hc := hcxy) (z1 := ![1, 0, 0, 0, 2]) (z2 := ![1, 0, 2, 1, 1])
        (wc1 := [4, 0, 1]) (k1 := 2) (wc2 := [0, 1, 4, 2]) (k2 := 1)
        (hdisj := hdisj) (hfix1 := ⟨hf1, hf1n⟩) (hfix2 := ⟨hf2, hf2n⟩)
        (hinv1 := hi1) (hinv2 := hi2)
        (hord1 := ⟨ho1, ho1ne⟩) (hord2 := ⟨ho2, ho2ne⟩)
    ·
      have hM : ∀ k, r4o_M ι (r4o_basis hD hspan ee) (φ' (ee k)) = r4o_refl r4o_Xb k := by
        intro k
        ext i j
        change LinearMap.toMatrix (r4o_basis hD hspan ee) (r4o_basis hD hspan ee)
            (ggLin ι (φ' (ee k))).toLinearMap i j = (r4o_refl r4o_Xb k) i j
        rw [r4o_matrix_entry hD hspan ee k i j]
        rw [r4o_row_Xb e hF hc ee hee hee4 k j]
        rfl
      have hxL : ∀ i : Fin 4, ∑ j, cx j * r4o_Xb (Fin.castSucc i) j = 0 := by
        intro i
        have h := hrowx i
        rw [← hee i] at h
        have hsum : (∑ j, cx j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cx j * r4o_Xb (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_Xb e hF hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyL : ∀ i : Fin 4, i ≠ 3 → ∑ j, cy j * r4o_Xb (Fin.castSucc i) j = 0 := by
        intro i hi
        have h := hrowy i (by rw [hb]; exact fun hh => hi (e.injective hh))
        rw [← hee i] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_Xb (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_Xb e hF hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyN : ∑ j, cy j * r4o_Xb (Fin.last 4) j = 0 := by
        have h := hrowyN
        rw [← hee4] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.last 4)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_Xb (Fin.last 4) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_Xb e hF hc ee hee hee4 (Fin.last 4) j]
        rwa [hsum] at h
      have hdisj := r4o_disj_Xb cx cy hxL hyL hyN hcx0 hcy0
      obtain ⟨hf1, hf1n, hf2, hf2n, hi1, hi2, ho1, ho1ne, ho2, ho2ne⟩ := r4o_fin_Xb
      refine r4o_assemble (z := x * y) (hzB := mul_mem hxB hyB) hD hspan
        (b := b) (n := ![e 0, e 1, e 2, e 2])
        (hneb := by intro i; fin_cases i <;> simp [hb, e.injective.ne_iff])
        (a := ![0, 1, 2, 2]) (ha := by intro i; fin_cases i <;> simp [hee0, hee1, hee2])
        (X := r4o_Xb) (hM := hM) (hc := hcxy) (z1 := ![0, 0, 0, 1, 2]) (z2 := ![1, 2, 0, 2, 2])
        (wc1 := [4, 3, 2]) (k1 := 1) (wc2 := [3, 2, 4, 1]) (k2 := 2)
        (hdisj := hdisj) (hfix1 := ⟨hf1, hf1n⟩) (hfix2 := ⟨hf2, hf2n⟩)
        (hinv1 := hi1) (hinv2 := hi2)
        (hord1 := ⟨ho1, ho1ne⟩) (hord2 := ⟨ho2, ho2ne⟩)
  · rcases hcase with ⟨hb, hc⟩ | ⟨hb, hc⟩
    ·
      have hM : ∀ k, r4o_M ι (r4o_basis hD hspan ee) (φ' (ee k)) = r4o_refl r4o_XaT k := by
        intro k
        ext i j
        change LinearMap.toMatrix (r4o_basis hD hspan ee) (r4o_basis hD hspan ee)
            (ggLin ι (φ' (ee k))).toLinearMap i j = (r4o_refl r4o_XaT k) i j
        rw [r4o_matrix_entry hD hspan ee k i j]
        rw [r4o_row_XaT e hFT hc ee hee hee4 k j]
        rfl
      have hxL : ∀ i : Fin 4, ∑ j, cx j * r4o_XaT (Fin.castSucc i) j = 0 := by
        intro i
        have h := hrowx i
        rw [← hee i] at h
        have hsum : (∑ j, cx j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cx j * r4o_XaT (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_XaT e hFT hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyL : ∀ i : Fin 4, i ≠ 0 → ∑ j, cy j * r4o_XaT (Fin.castSucc i) j = 0 := by
        intro i hi
        have h := hrowy i (by rw [hb]; exact fun hh => hi (e.injective hh))
        rw [← hee i] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_XaT (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_XaT e hFT hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyN : ∑ j, cy j * r4o_XaT (Fin.last 4) j = 0 := by
        have h := hrowyN
        rw [← hee4] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.last 4)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_XaT (Fin.last 4) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_XaT e hFT hc ee hee hee4 (Fin.last 4) j]
        rwa [hsum] at h
      have hdisj := r4o_disj_XaT cx cy hxL hyL hyN hcx0 hcy0
      obtain ⟨hf1, hf1n, hf2, hf2n, hi1, hi2, ho1, ho1ne, ho2, ho2ne⟩ := r4o_fin_XaT
      refine r4o_assemble (z := x * y) (hzB := mul_mem hxB hyB) hD hspan
        (b := b) (n := ![e 1, e 2, e 3, e 1])
        (hneb := by intro i; fin_cases i <;> simp [hb, e.injective.ne_iff])
        (a := ![1, 2, 3, 1]) (ha := by intro i; fin_cases i <;> simp [hee1, hee2, hee3])
        (X := r4o_XaT) (hM := hM) (hc := hcxy) (z1 := ![1, 0, 0, 0, 2]) (z2 := ![1, 0, 1, 2, 1])
        (wc1 := [4, 0, 1]) (k1 := 2) (wc2 := [0, 1, 4, 2]) (k2 := 1)
        (hdisj := hdisj) (hfix1 := ⟨hf1, hf1n⟩) (hfix2 := ⟨hf2, hf2n⟩)
        (hinv1 := hi1) (hinv2 := hi2)
        (hord1 := ⟨ho1, ho1ne⟩) (hord2 := ⟨ho2, ho2ne⟩)
    ·
      have hM : ∀ k, r4o_M ι (r4o_basis hD hspan ee) (φ' (ee k)) = r4o_refl r4o_XbT k := by
        intro k
        ext i j
        change LinearMap.toMatrix (r4o_basis hD hspan ee) (r4o_basis hD hspan ee)
            (ggLin ι (φ' (ee k))).toLinearMap i j = (r4o_refl r4o_XbT k) i j
        rw [r4o_matrix_entry hD hspan ee k i j]
        rw [r4o_row_XbT e hFT hc ee hee hee4 k j]
        rfl
      have hxL : ∀ i : Fin 4, ∑ j, cx j * r4o_XbT (Fin.castSucc i) j = 0 := by
        intro i
        have h := hrowx i
        rw [← hee i] at h
        have hsum : (∑ j, cx j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cx j * r4o_XbT (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_XbT e hFT hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyL : ∀ i : Fin 4, i ≠ 3 → ∑ j, cy j * r4o_XbT (Fin.castSucc i) j = 0 := by
        intro i hi
        have h := hrowy i (by rw [hb]; exact fun hh => hi (e.injective hh))
        rw [← hee i] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.castSucc i)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_XbT (Fin.castSucc i) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_XbT e hFT hc ee hee hee4 (Fin.castSucc i) j]
        rwa [hsum] at h
      have hyN : ∑ j, cy j * r4o_XbT (Fin.last 4) j = 0 := by
        have h := hrowyN
        rw [← hee4] at h
        have hsum : (∑ j, cy j * (ggAttachCartan C c (ee (Fin.last 4)) (ee j) : ZMod 3)) =
            ∑ j, cy j * r4o_XbT (Fin.last 4) j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [r4o_row_XbT e hFT hc ee hee hee4 (Fin.last 4) j]
        rwa [hsum] at h
      have hdisj := r4o_disj_XbT cx cy hxL hyL hyN hcx0 hcy0
      obtain ⟨hf1, hf1n, hf2, hf2n, hi1, hi2, ho1, ho1ne, ho2, ho2ne⟩ := r4o_fin_XbT
      refine r4o_assemble (z := x * y) (hzB := mul_mem hxB hyB) hD hspan
        (b := b) (n := ![e 0, e 1, e 2, e 2])
        (hneb := by intro i; fin_cases i <;> simp [hb, e.injective.ne_iff])
        (a := ![0, 1, 2, 2]) (ha := by intro i; fin_cases i <;> simp [hee0, hee1, hee2])
        (X := r4o_XbT) (hM := hM) (hc := hcxy) (z1 := ![0, 0, 0, 1, 2]) (z2 := ![1, 2, 0, 1, 1])
        (wc1 := [4, 3, 2]) (k1 := 1) (wc2 := [3, 2, 4, 1]) (k2 := 2)
        (hdisj := hdisj) (hfix1 := ⟨hf1, hf1n⟩) (hfix2 := ⟨hf2, hf2n⟩)
        (hinv1 := hi1) (hinv2 := hi2)
        (hord1 := ⟨ho1, ho1ne⟩) (hord2 := ⟨ho2, ho2ne⟩)

end CFSG.StandardType
