module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeGraphTorus
public import CFSG.HardMathSupport.Timmesfeld.Proving.SimpleRootsCartan
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.CyclicImplementers

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.Proving

open scoped Pointwise

theorem f4_stabilizer_le_kernel
    {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : Fin Tag.F4.rank → Kˣ) (ha : ∀ i, a i ^ p = 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  have hp23 : p = 3 ∨ 3 < p := by
    have h2lt : 2 < p := by
      rcases lt_or_eq_of_le hp.two_le with h | h
      · exact h
      · exact absurd h.symm hp2
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt h2lt) with h | h
    · exact Or.inr h
    · exact Or.inl h.symm
  rcases hp23 with rfl | h3p
  · exact (ThreeExact.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three_without13604 a
      ha).le
  · intro w hw
    refine
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.mem_kernelReflectionGroup_of_coprime
            hp ha hw ?_
    exact Nat.coprime_comm.2 <|
      (hp.coprime_iff_not_dvd).2 fun h =>
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp h3p)
          (h.trans (orderOf_dvd_natCard w))

variable {τ : Tag} {K : Type} [Field K]

def goodWeylSubgroup
    (a : Fin τ.rank → Kˣ) : Subgroup (WeylGroup τ) where
  carrier := {w | canonicalRep (coxeterSystem τ) K w ∈ toralRootGroup τ K a}
  one_mem' := by
    show canonicalRep (coxeterSystem τ) K 1 ∈ toralRootGroup τ K a
    rw [canonicalRep_one]
    exact one_mem _
  mul_mem' := by
    intro u v hu hv
    show canonicalRep (coxeterSystem τ) K (u * v) ∈ toralRootGroup τ K a
    obtain ⟨k, hk, hk'⟩ := canonicalRep_mul_mem (R := K) u v
    have hrepr : canonicalRep (coxeterSystem τ) K (u * v) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) K u *
          canonicalRep (coxeterSystem τ) K v) := by
      rw [hk', inv_mul_cancel_left]
    rw [hrepr]
    exact mul_mem (inv_mem ((le_sup_left : torusGroup τ K ≤ toralRootGroup τ K a) hk)) (mul_mem hu
        hv)
  inv_mem' := by
    intro u hu
    show canonicalRep (coxeterSystem τ) K u⁻¹ ∈ toralRootGroup τ K a
    obtain ⟨k, hk, hk'⟩ := canonicalRep_inv_eq (K := K) u
    have hrepr : canonicalRep (coxeterSystem τ) K u⁻¹ =
        k⁻¹ * (canonicalRep (coxeterSystem τ) K u)⁻¹ := by
      rw [hk', inv_mul_cancel_left]
    rw [hrepr]
    exact mul_mem (inv_mem ((le_sup_left : torusGroup τ K ≤ toralRootGroup τ K a) hk)) (inv_mem hu)

theorem canonicalRep_conj_simple_mem_good
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ} {i : Fin τ.rank}
    (hα : w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ rootCharKernel a) :
    canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹) ∈ toralRootGroup τ K a := by
  set n := canonicalRep (coxeterSystem τ) K w
  set α : Fin τ.rank → ℤ := w • (Pi.single i 1 : Fin τ.rank → ℤ)
  have hnegα : -α ∈ rootCharKernel a := by
    refine ⟨IsRoot.neg hα.1, ?_⟩
    rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2, inv_one, mul_one]
  have hmapx := (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ i)
  have hmapy := (canonical_weyl_root_transport τ K).2.1 w _ (IsRoot.neg (isRoot_single τ i))
  rw [smul_neg] at hmapy
  have hU : ∀ β ∈ rootCharKernel a, rootSubgroup τ K β ≤ toralRootGroup τ K a := fun β hβ =>
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootCharKernel a) => rootSubgroup τ K γ) β hβ
      le_rfl).trans le_sup_right
  have hx : ∀ c : K, n * xUnit τ K i c * n⁻¹ ∈ toralRootGroup τ K a := fun c => by
    refine hU α hα ?_
    rw [← hmapx]
    exact ⟨_, xUnit_mem_rootSubgroup i c, rfl⟩
  have hy : ∀ c : K, n * yUnit τ K i c * n⁻¹ ∈ toralRootGroup τ K a := fun c => by
    refine hU (-α) hnegα ?_
    rw [← hmapy]
    exact ⟨_, yUnit_mem_rootSubgroup i c, rfl⟩
  have hm : n * weylElt τ K i 1 * n⁻¹ ∈ toralRootGroup τ K a := by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    have e : n * (xUnit τ K i ((1 : Kˣ) : K) *
        yUnit τ K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * xUnit τ K i ((1 : Kˣ) : K)) * n⁻¹ =
        (n * xUnit τ K i ((1 : Kˣ) : K) * n⁻¹) *
          (n * yUnit τ K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * n⁻¹) *
            (n * xUnit τ K i ((1 : Kˣ) : K) * n⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have hN : (canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ K i 1 * n⁻¹) ∈ monomialSubgroup τ K :=
    mul_mem (inv_mem (canonicalRep_mem_monomialSubgroup K _))
      (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K w)
        (weylElt_mem_monomialSubgroup i))
        (inv_mem (canonicalRep_mem_monomialSubgroup K w)))
  have hmaps : MapsRootLines ((canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ K i 1 * n⁻¹)) 1 := by
    have := (mapsRootLines_canonicalRep (R := K) (w * simple τ i * w⁻¹)).inv.mul
      (((mapsRootLines_canonicalRep (R := K) w).mul (mapsRootLines_weylElt i)).mul
        (mapsRootLines_canonicalRep (R := K) w).inv)
    rwa [inv_mul_cancel] at this
  have hT := mem_torusGroup_of_mapsRootLines_one hN hmaps
  have e : canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹) =
      (n * weylElt τ K i 1 * n⁻¹) *
        ((canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
          (n * weylElt τ K i 1 * n⁻¹))⁻¹ := by group
  rw [e]
  exact mul_mem hm (inv_mem ((le_sup_left : torusGroup τ K ≤ toralRootGroup τ K a) hT))

theorem kernelReflectionGroup_le_goodWeylSubgroup
    (a : Fin τ.rank → Kˣ) :
    kernelReflectionGroup a ≤ goodWeylSubgroup a := by
  unfold kernelReflectionGroup
  refine (Subgroup.closure_le (goodWeylSubgroup a)).2 ?_
  rintro r ⟨w, i, hα, rfl⟩
  exact canonicalRep_conj_simple_mem_good hα

section ComponentTorus

variable {L : Type} [Field L]

noncomputable def graphTorusHom_good {r : ℕ} (γ : Fin r → Fin τ.rank → ℤ)
    (G : Subgroup Lˣ) (z : ModGL τ L) : (Fin r → G) →* ModGL τ L where
  toFun u := z * rootDiagUnit τ (graphTorusChar γ fun j => (u j : Lˣ)) * z⁻¹
  map_one' := by
    have h : (fun j => ((1 : Fin r → G) j : Lˣ)) = 1 := by funext j; rfl
    have h1 : graphTorusChar γ (1 : Fin r → Lˣ) = 1 := by
      funext i
      simp [graphTorusChar]
    rw [h, h1, rootDiagUnit_one, mul_one, mul_inv_cancel]
  map_mul' u v := by
    have h : (fun j => ((u * v) j : Lˣ)) =
        (fun j => (u j : Lˣ)) * fun j => (v j : Lˣ) := by funext j; rfl
    have hm : graphTorusChar γ ((fun j => (u j : Lˣ)) * fun j => (v j : Lˣ)) =
        graphTorusChar γ (fun j => (u j : Lˣ)) * graphTorusChar γ (fun j => (v j : Lˣ)) := by
      funext i
      simp only [graphTorusChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
    rw [h, hm, rootDiagUnit_mul]
    group

theorem graphTorusHom_apply_good {r : ℕ} (γ : Fin r → Fin τ.rank → ℤ) (G : Subgroup Lˣ)
    (z : ModGL τ L) (u : Fin r → G) :
    graphTorusHom_good γ G z u =
      z * rootDiagUnit τ (graphTorusChar γ fun j => (u j : Lˣ)) * z⁻¹ :=
  rfl

theorem rootChar_graphTorusChar_good
    {r : ℕ} {γ : Fin r → Fin τ.rank → ℤ}
    (hγ : ∀ j, IsRoot τ (γ j)) (u : Fin r → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (graphTorusChar γ u) v = ∏ j, u j ^ corootPair (γ j) v := by
  simp only [rootChar, graphTorusChar]
  rw [show (∏ i, (∏ j, u j ^ corootPair (γ j) (Pi.single i 1)) ^ v i) =
      ∏ i, ∏ j, u j ^ (v i * corootPair (γ j) (Pi.single i 1)) by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_mul, mul_comm], Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [corootPair_eq_sum (hγ j) v, graphTorus_zpow_sum]

theorem rootDiagUnit_graphTorusChar_mulSingle_good
    {τ : Tag} {r : ℕ}
    {γ : Fin r → Fin τ.rank → ℤ} (hγ : ∀ j, IsRoot τ (γ j)) (j : Fin r) (t : Lˣ) :
    rootDiagUnit τ (graphTorusChar γ (Pi.mulSingle j t)) = rootSL2 τ L (γ j) (HSL t) := by
  rw [rootSL2_HSL_eq (hγ j)]
  congr 1
  funext i
  simp only [graphTorusChar]
  rw [Finset.prod_eq_single j (fun k _ hk => by rw [Pi.mulSingle_eq_of_ne hk, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

theorem graphTorusHom_eq_prod_good
    {τ : Tag} {r : ℕ} {γ : Fin r → Fin τ.rank → ℤ}
    (hγ : ∀ j, IsRoot τ (γ j)) (G : Subgroup Lˣ) (z : ModGL τ L) (u : Fin r → G) :
    graphTorusHom_good γ G z u = ((List.finRange r).map fun j =>
      z * rootSL2 τ L (γ j) (HSL (u j : Lˣ)) * z⁻¹).prod := by
  have hu : u = ((List.finRange r).map fun j => Pi.mulSingle j (u j)).prod := by
    rw [← Fin.prod_univ_def]
    exact (Finset.univ_prod_mulSingle u).symm
  conv_lhs => rw [hu]
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, graphTorusHom_apply_good]
  have h : (fun k => ((Pi.mulSingle j (u j) : Fin r → G) k : Lˣ)) =
      Pi.mulSingle j (u j : Lˣ) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.mulSingle_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk]; rfl
  rw [h, rootDiagUnit_graphTorusChar_mulSingle_good hγ]

theorem rootDiagUnit_graphTorusChar_mem_componentRootSpan_good
    {τ : Tag}
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {r : ℕ} (γ : Fin r → Fin τ.rank → ℤ)
    (hγ : ∀ j, γ j ∈ componentRoots χ i) (u : Fin r → Lˣ) :
    rootDiagUnit τ (graphTorusChar γ u) ∈ componentRootSpan L χ i := by
  classical
  have hγr : ∀ j, IsRoot τ (γ j) := fun j => isRoot_of_mem_componentRoots (hγ j)
  have hneg : ∀ j, -γ j ∈ componentRoots χ i := fun j =>
    (isRootComponent_componentRoots i).neg_mem _ (hγ j)
  set u' : Fin r → (⊤ : Subgroup Lˣ) := fun j => ⟨u j, Subgroup.mem_top _⟩ with hu'
  have hprod := graphTorusHom_eq_prod_good (γ := γ) (hγ := hγr) (G := ⊤) (z := 1) u'
  have hleft : graphTorusHom_good γ ⊤ 1 u' = rootDiagUnit τ (graphTorusChar γ u) := by
    rw [graphTorusHom_apply_good]
    have hcoe : (fun j => ((u' j : (⊤ : Subgroup Lˣ)) : Lˣ)) = u := rfl
    rw [hcoe]
    simp
  rw [hleft] at hprod
  rw [hprod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  have hmem : rootSL2 τ L (γ j) (HSL (u j)) ∈ rootSpan τ L {γ j, -γ j} :=
    rootSL2_mem_rootSpan_pair (hγr j) (HSL (u j))
  exact rootSpan_mono (by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hγ j
    · exact hneg j) hmem

theorem exists_torus_char_interpolation_good
    {τ : Tag} [IsAlgClosed L]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (l : Fin τ.rank → Lˣ) :
    ∃ t : Fin (simpleRoots (componentRoots χ i)).card → Lˣ,
      ∀ α ∈ componentRoots χ i,
        rootChar (graphTorusChar
          (fun k => ((simpleRoots (componentRoots χ i)).equivFin.symm k : Fin τ.rank → ℤ)) t) α =
          rootChar l α := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  set Δ := simpleRoots Ψ with hΔdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  set e : Fin Δ.card ≃ Δ := Δ.equivFin.symm with he
  set ν : Fin Δ.card → Fin τ.rank → ℤ := fun k => (e k : Fin τ.rank → ℤ) with hν
  set B : Matrix Δ Δ ℤ := fun β γ => corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) with hB
  have hBfin : TauCeti.IsFiniteType B := isFiniteType_simpleRoots_corootPair hΨ
  set A : Matrix (Fin Δ.card) (Fin Δ.card) ℤ := fun i j => B (e j) (e i) with hA
  have hAeq : A = (B.submatrix e e).transpose := by
    ext i j
    rfl
  have hdetA : A.det ≠ 0 := by
    rw [hAeq, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hBfin.det_ne_zero
  have hli : LinearIndependent ℚ (fun i : Fin Δ.card => fun j : Fin Δ.card => (A i j : ℚ)) := by
    have hdetAq : ((A.map (fun x : ℤ => (x : ℚ))) :
        Matrix (Fin Δ.card) (Fin Δ.card) ℚ).det ≠ 0 := by
      rw [← Int.cast_det]
      exact Int.cast_ne_zero.mpr hdetA
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdetAq
  obtain ⟨t, ht⟩ := algebraically_closed_lattice_character_interpolation L Δ.card Δ.card
    (fun i j => A i j) hli (fun i => rootChar l (ν i))
  refine ⟨t, fun α hα => ?_⟩
  obtain ⟨c, hc⟩ := exists_coords hΨ hα
  have hsum : α = ∑ k : Fin Δ.card, c (ν k) • ν k := by
    rw [hc, ← Finset.sum_coe_sort Δ]
    exact Fintype.sum_equiv Δ.equivFin (fun i : Δ => c i • (i : Fin τ.rank → ℤ))
      (fun k => c (ν k) • ν k) (fun i => by simp [ν, e])
  have hsum' : ∀ j : Fin Δ.card, corootPair (ν j) α =
      ∑ k : Fin Δ.card, c (ν k) * corootPair (ν j) (ν k) := by
    intro j
    have h := corootPair_sum (β := ν j) (simpleRoots_isRoot (e j).2) Finset.univ
      (fun k => c (ν k)) ν
    rw [hsum]
    simpa using h
  rw [rootChar_graphTorusChar_good (γ := ν) (u := t) (v := α)
    (hγ := fun j => simpleRoots_isRoot (e j).2)]
  calc ∏ j, t j ^ corootPair (ν j) α
      = ∏ j, t j ^ (∑ k : Fin Δ.card, c (ν k) * corootPair (ν j) (ν k)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hsum' j]
    _ = ∏ j, ∏ k : Fin Δ.card, (t j ^ corootPair (ν j) (ν k)) ^ c (ν k) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Finset.prod_zpow_eq_zpow_sum]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [mul_comm, zpow_mul]
    _ = ∏ k : Fin Δ.card, ∏ j : Fin Δ.card, (t j ^ corootPair (ν j) (ν k)) ^ c (ν k) :=
        Finset.prod_comm
    _ = ∏ k : Fin Δ.card, (rootChar l (ν k)) ^ c (ν k) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [Finset.prod_zpow, ht k]
    _ = rootChar l α := by
        rw [hsum, rootChar_sum]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [rootChar_zsmul]

end ComponentTorus
end CFSG.StandardType.F4ExplicitPos.CyclicImplementers
end

end
