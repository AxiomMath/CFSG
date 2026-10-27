module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Frame
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

@[expose] def symJ (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem exists_symp_basis (S : AddSubgroup (Fin 4 → F.K)) (hcard : Nat.card S = 16)
    (hts : ∀ x ∈ S, herm F.σ x x = 0) (hcore : ∀ x ∈ S, x ≠ 0 → ∃ c : F.K, c • x ∉ S) :
    ∃ u : Fin 4 → (Fin 4 → F.K), (∀ i, u i ∈ S) ∧ AddSubgroup.closure (Set.range u) = S ∧
      ∀ i j, herm F.σ (u i) (u j) = symJ F.K i j := by
  classical
  haveI : CharP F.K 2 := charP_of_card_sq (p := 2) (f := 1) (by rw [F.card_K]; norm_num)
  letI : Algebra (ZMod 2) F.K := ZMod.algebra F.K 2
  haveI : Fintype F.K := Fintype.ofFinite F.K
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : F.K, ω ≠ 0 ∧ ω ≠ 1 := by
    have hcard2 : ({0, 1} : Finset F.K).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1} : Finset F.K)) (t := Finset.univ)
      (by rw [hcard2, Finset.card_univ, Fintype.card_eq_nat_card, F.card_K]; norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
    exact ⟨ω, hω.1, hω.2⟩
  have hω : ω ^ 2 + ω + 1 = 0 := TauCeti.sq_add_self_add_one_eq_zero F.card_K hω0 hω1
  have hωsq : ω ^ 2 = ω + 1 := by
    have h : ω ^ 2 + (ω + 1) = 0 := by rw [← add_assoc]; exact hω
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hval01 : ∀ x ∈ S, ∀ y ∈ S, herm F.σ x y = 0 ∨ herm F.σ x y = 1 := by
    intro x hx y hy
    have h0 : herm F.σ x y + herm F.σ y x = 0 := by
      have h := hts (x + y) (S.add_mem hx hy)
      rw [herm_add_left, herm_add_right, herm_add_right] at h
      simpa [hts x hx, hts y hy] using h
    rw [herm_conj F.σ F.isUnitary.invol x y, F.sigma_apply (herm F.σ x y)] at h0
    set c := herm F.σ x y with hc_def
    have hsq : c ^ 2 = c := by
      have h := eq_neg_of_add_eq_zero_right h0
      rwa [CharTwo.neg_eq] at h
    have hfac : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have homega_notMem : ∀ x ∈ S, x ≠ 0 → ω • x ∉ S := by
    intro x hx hx0 hmem
    obtain ⟨c, hc⟩ := hcore x hx hx0
    have huniv : c ∈ ({0, 1, ω, ω ^ 2} : Finset F.K) := by
      rw [← TauCeti.univ_eq_zero_one_root_sq F.card_K hω]
      exact Finset.mem_univ c
    simp only [Finset.mem_insert, Finset.mem_singleton] at huniv
    rcases huniv with rfl | rfl | rfl | rfl
    · exact hc (by simp)
    · exact hc (by simpa using hx)
    · exact hc hmem
    · exact hc (by rw [hωsq, add_smul, one_smul]; exact S.add_mem hmem hx)
  have homega_smul_eq_zero : ∀ x ∈ S, ω • x ∈ S → x = 0 := by
    intro x hx hxω
    by_contra hx0
    exact homega_notMem x hx hx0 hxω
  have hdecomp : ∀ z : Fin 4 → F.K, ∃ s ∈ S, ∃ s' ∈ S, z = s + ω • s' := by
    let φ : S × S → (Fin 4 → F.K) := fun p => (p.1 : Fin 4 → F.K) + ω • (p.2 : Fin 4 → F.K)
    have hinj : Function.Injective φ := by
      rintro ⟨s, s'⟩ ⟨t, t'⟩ h
      have h1 : ((s - t : S) : Fin 4 → F.K) = ω • ((t' - s' : S) : Fin 4 → F.K) := by
        simp only [AddSubgroup.coe_sub]
        rw [smul_sub]
        linear_combination h
      have ht's' : t' = s' := by
        have hzero : ((t' - s' : S) : Fin 4 → F.K) = 0 :=
          homega_smul_eq_zero _ (t' - s').2 (by rw [← h1]; exact (s - t).2)
        exact sub_eq_zero.mp (Subtype.ext hzero)
      have hs_eq : s = t := by
        have hzero : ((s - t : S) : Fin 4 → F.K) = 0 := by
          rw [h1, ht's']
          simp
        exact sub_eq_zero.mp (Subtype.ext hzero)
      exact Prod.ext hs_eq ht's'.symm
    have hcardF : Fintype.card S = 16 := by rw [Fintype.card_eq_nat_card, hcard]
    have hcard_dom : Fintype.card (S × S) = 256 := by rw [Fintype.card_prod, hcardF]
    have hcard_cod : Fintype.card (Fin 4 → F.K) = 256 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card, F.card_K]
      norm_num
    have hsurj : Function.Surjective φ := by
      refine (Finite.injective_iff_surjective_of_equiv
        (Fintype.equivOfCardEq ?_)).mp hinj
      rw [hcard_dom, hcard_cod]
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩
  have hnondeg : ∀ x ∈ S, (∀ y ∈ S, herm F.σ x y = 0) → x = 0 := by
    intro x hx horth
    refine eq_zero_of_herm F.σ ?_
    intro z
    obtain ⟨s, hs, s', hs', rfl⟩ := hdecomp z
    rw [herm_add_right, herm_smul_right, horth s hs, horth s' hs', mul_zero, add_zero]
  let chi : F.K →+ ZMod 2 :=
    { toFun := fun c => ((TauCeti.zmodTwoProdAddEquiv F.card_K hω).symm c).1
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add] }
  have chi_one : chi 1 = 1 := by simp [chi]
  have chi_inj : ∀ a b : F.K, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → chi a = chi b → a = b := by
    intro a b ha hb hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · simpa [chi, chi_one] using hab
    · simpa [chi, chi_one] using hab
    · rfl
  have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let B : LinearMap.BilinForm (ZMod 2) S :=
    LinearMap.mk₂ (ZMod 2) (fun x y => chi (herm F.σ (x : Fin 4 → F.K) (y : Fin 4 → F.K)))
      (fun x x' y => by rw [AddSubgroup.coe_add, herm_add_left, map_add])
      (fun c x y => by rcases hc2 c with rfl | rfl <;> simp)
      (fun x y y' => by rw [AddSubgroup.coe_add, herm_add_right, map_add])
      (fun c x y => by rcases hc2 c with rfl | rfl <;> simp)
  have hB_apply : ∀ x y : S, B x y = chi (herm F.σ (x : Fin 4 → F.K) (y : Fin 4 → F.K)) := by
    intro x y
    simp only [B, LinearMap.mk₂_apply]
  have hB_alt : B.IsAlt := by
    intro x
    rw [hB_apply, hts (x : Fin 4 → F.K) x.2, map_zero]
  have hB_nd : B.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      refine hnondeg (x : Fin 4 → F.K) x.2 ?_
      intro y hy
      have h := hx ⟨y, hy⟩
      rw [hB_apply] at h
      rcases hval01 (x : Fin 4 → F.K) x.2 y hy with h0 | h0
      · exact h0
      · rw [h0, chi_one] at h; exact absurd h one_ne_zero
    · intro x hx
      apply Subtype.ext
      refine hnondeg (x : Fin 4 → F.K) x.2 ?_
      intro y hy
      have h := hx ⟨y, hy⟩
      rw [hB_apply] at h
      rcases hval01 y hy (x : Fin 4 → F.K) x.2 with h0 | h0
      · have hc := herm_conj F.σ F.isUnitary.invol (x : Fin 4 → F.K) y
        rw [h0] at hc
        exact (map_eq_zero_iff F.σ F.σ.injective).mp hc.symm
      · rw [h0, chi_one] at h; exact absurd h one_ne_zero
  obtain ⟨m, b, hb⟩ := hB_alt.exists_basis_toMatrix_eq_J hB_nd
  have hfin : Module.finrank (ZMod 2) S = 4 := by
    haveI : Module.Finite (ZMod 2) S := by infer_instance
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
    rw [hcard, Nat.card_zmod] at h
    have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) S = 2 ^ 4 := h.symm
    exact Nat.pow_right_injective (by norm_num) h2
  have hm : m = 2 := by
    have h := Module.finrank_eq_card_basis b
    rw [hfin, Fintype.card_sum, Fintype.card_fin] at h
    omega
  subst hm
  let τ : Fin 4 → Fin 2 ⊕ Fin 2 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  let e4 : Fin 4 ≃ Fin 2 ⊕ Fin 2 := Equiv.ofBijective τ (by decide)
  let b' : Module.Basis (Fin 4) (ZMod 2) S := b.reindex e4.symm
  let u : Fin 4 → (Fin 4 → F.K) := fun i => (b' i : Fin 4 → F.K)
  have hb'_apply : ∀ i, b' i = b (e4 i) := by
    intro i
    simp [b', Module.Basis.reindex_apply]
  have hb' : ∀ i j, B (b' i) (b' j) = Matrix.J (Fin 2) (ZMod 2) (e4 i) (e4 j) := by
    intro i j
    have h := LinearMap.BilinForm.toMatrix_apply (b := b) (B := B) (e4 i) (e4 j)
    rw [hb] at h
    rw [hb'_apply i, hb'_apply j, h.symm]
  have hu_mem : ∀ i, u i ∈ S := fun i => (b' i).2
  have hu_gram : ∀ i j, herm F.σ (u i) (u j) = symJ F.K i j := by
    intro i j
    have hBval := hb' i j
    rw [hB_apply] at hBval
    have hchi : chi (herm F.σ (u i) (u j)) =
        Matrix.J (Fin 2) (ZMod 2) (e4 i) (e4 j) := hBval
    have hsym : chi (symJ F.K i j) =
        Matrix.J (Fin 2) (ZMod 2) (e4 i) (e4 j) := by
      fin_cases i <;> fin_cases j <;>
        simp [symJ, e4, τ, Matrix.J, Matrix.fromBlocks, chi_one] <;> decide
    refine chi_inj _ _ ?_ ?_ ?_
    · exact hval01 (u i) (hu_mem i) (u j) (hu_mem j)
    · fin_cases i <;> fin_cases j <;> simp [symJ]
    · rw [hchi, hsym]
  refine ⟨u, hu_mem, ?_, hu_gram⟩
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hu_mem i
  · intro x hx
    let xs : S := ⟨x, hx⟩
    have hrepr : (∑ i, b'.repr xs i • b' i) = xs := Module.Basis.sum_repr b' xs
    have hx_eq : x = ∑ i, b'.repr xs i • u i := by
      have h := congrArg (fun y : S => (y : Fin 4 → F.K)) hrepr
      have hcoe : ((∑ i, b'.repr xs i • b' i : S) : Fin 4 → F.K) =
          ∑ i, b'.repr xs i • u i := by
        rw [AddSubmonoidClass.coe_finsetSum]
        simp [u, AddSubgroupClass.coe_zmod_smul]
      rw [← hcoe]
      simpa only [xs] using h.symm
    rw [hx_eq]
    refine Finset.sum_induction (s := Finset.univ) (fun i => b'.repr xs i • u i)
      (fun y => y ∈ AddSubgroup.closure (Set.range u))
      (fun a b ha hb => (AddSubgroup.closure (Set.range u)).add_mem ha hb)
      (AddSubgroup.closure (Set.range u)).zero_mem ?_
    intro i _
    rcases hc2 (b'.repr xs i) with h | h
    · rw [h, zero_smul]; exact (AddSubgroup.closure (Set.range u)).zero_mem
    · rw [h, one_smul]; exact AddSubgroup.subset_closure ⟨i, rfl⟩

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
