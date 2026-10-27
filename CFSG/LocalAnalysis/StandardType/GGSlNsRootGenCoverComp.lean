module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwist
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative
open CFSG.StandardType.SuSplitRootGen

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [Fact p.Prime] {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}

theorem isComponentOf_pairBlock_centralizer (hp2 : p ≠ 2) (hgd : g ∣ cyclotomic p K)
    {i j : Fin s} (hij : i ≠ j) :
    IsComponentOf (pairBlock g ε i j)
      (Subgroup.centralizer (torusFix (torusSL ε hC hCp) (swapMap i j))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  haveI : Finite (AdjoinRoot g) := finite_adjoinRoot
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p := root_isPrimitiveRoot hp hpK' hgd
  have hal : Aligned hprim.pow_eq_one (pairVec (p := p) i j) := aligned_pairVec i j
  have hβ : torusSL ε hC hCp (ofAdd (pairVec (p := p) i j)) ∈
      torusFix (torusSL ε hC hCp) (swapMap i j) := by
    refine ⟨ofAdd (pairVec (p := p) i j), ?_, rfl⟩
    simpa using (swapMap_eq_self_iff (p := p) (i := i) (j := j)).mpr (by simp [pairVec])
  have hJle : pairBlock g ε i j ≤
      Subgroup.centralizer (torusFix (torusSL ε hC hCp) (swapMap i j)) := by
    intro x hx
    have hx' : x ∈ (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (theta g ε) := hx
    obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.mp hx'
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    have htij : toAdd a i = toAdd a j := swapMap_eq_self_iff.mp ha
    have hM' : M ∈ coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1) := by
      rw [classSet_pairVec]
      exact hM
    have hcomm : theta g ε M * SLNS.nsSL ε hC (fun m => (toAdd a m).val) =
        SLNS.nsSL ε hC (fun m => (toAdd a m).val) * theta g ε M :=
      comm_classBlock_of_torus (ε := ε) (hC := hC) (β := pairVec (p := p) i j) (c := 1)
        (k := fun m => (toAdd a m).val) ?_ hM'
    · rw [← ofAdd_toAdd a, torusSL_apply]
      exact hcomm.symm
    · intro m n hm hn
      have hm' : m = i ∨ m = j := by
        have h1 : m ∈ classSet (pairVec (p := p) i j) 1 := mem_classSet.mpr hm
        rw [classSet_pairVec] at h1
        simpa using h1
      have hn' : n = i ∨ n = j := by
        have h1 : n ∈ classSet (pairVec (p := p) i j) 1 := mem_classSet.mpr hn
        rw [classSet_pairVec] at h1
        simpa using h1
      rcases hm' with rfl | rfl <;> rcases hn' with rfl | rfl <;> simp [htij]
  have hHle : Subgroup.centralizer (torusFix (torusSL ε hC hCp) (swapMap i j)) ≤
      Subgroup.centralizer ({torusSL ε hC hCp (ofAdd (pairVec (p := p) i j))} :
        Set (SpecialLinearGroup (Fin n) K)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hβ)
  have hnorm : Subgroup.centralizer (torusFix (torusSL ε hC hCp) (swapMap i j)) ≤
      Subgroup.normalizer (pairBlock g ε i j : Set (SpecialLinearGroup (Fin n) K)) := by
    refine hHle.trans ?_
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hx' : x * SLNS.nsSL ε hC (fun m => (pairVec (p := p) i j m).val) =
        SLNS.nsSL ε hC (fun m => (pairVec (p := p) i j m).val) * x := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [torusSL_apply] at hcomm
      exact hcomm
    have hy' : y ∈ (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (theta g ε) := hy
    obtain ⟨N, hN, rfl⟩ := Subgroup.mem_map.mp hy'
    have hN' : N ∈ coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1) := by
      rw [classSet_pairVec]
      exact hN
    have hconj : x * theta g ε N * x⁻¹ ∈
        (coordBlockSL (AdjoinRoot g) (classSet (pairVec (p := p) i j) 1)).map (theta g ε) :=
      conj_mem_classBlock (hζ := hprim.pow_eq_one) (ε := ε) (hC := hC) hprim hal one_ne_zero
        hx' hN'
    simpa only [pairBlock, classSet_pairVec] using hconj
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hL4 : 4 ≤ Nat.card (AdjoinRoot g) := four_le_natCard_adjoinRoot hprim hp3
  have hq : CFSG.Assembly.IsQuasisimple (pairBlock g ε i j) := by
    have hcard : 2 ≤ ({i, j} : Finset (Fin s)).card := by rw [Finset.card_pair hij]
    have hq₀ : CFSG.IsQuasisimple (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))) :=
      isQuasisimple_coordBlockSL hcard hL4
    have hinj₀ : Function.Injective
        ((theta g ε).comp (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).subtype) :=
      fun x _ hxy => Subtype.ext (theta_injective (g := g) (ε := ε) hxy)
    have hrange : ((theta g ε).comp
        (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).subtype).range =
        (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (theta g ε) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hqmap : CFSG.IsQuasisimple
        ((coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (theta g ε)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((MonoidHom.ofInjective hinj₀).trans (MulEquiv.subgroupCongr hrange)) hq₀
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqmap
  refine ⟨hJle, CFSG.Assembly.IsSubnormal.step hJle ?_ (CFSG.Assembly.IsSubnormal.refl _), hq⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mpr hnorm

theorem isComponentOf_twistPairBlock_centralizer (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1) {i j : Fin s} (hij : i ≠ j) :
    IsComponentOf (twistPairBlock g hζ hpK ε i j)
      (Subgroup.centralizer (torusFix (torusSL ε hC hCp) (sswapMap i j))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  let N : SpecialLinearGroup (Fin n) K := negSL g hζ hpK ε j
  have hconj : ∀ t : Multiplicative (Fin s → ZMod p),
      (MulAut.conj N).toMonoidHom (torusSL ε hC hCp t) =
        torusSL ε hC hCp (ofAdd (negMap j (toAdd t))) := by
    intro t
    change MulAut.conj N (torusSL ε hC hCp t) =
      torusSL ε hC hCp (ofAdd (negMap j (toAdd t)))
    rw [MulAut.conj_apply]
    exact negSL_conj g hC hCp hζ hpK ε j (toAdd t)
  have hsub1 : torusFix (torusSL ε hC hCp) (sswapMap i j) ⊆
      (MulAut.conj N).toMonoidHom '' torusFix (torusSL ε hC hCp) (swapMap i j) := by
    rintro y ⟨a, ha, rfl⟩
    have ha' : sswapMap i j (toAdd a) = toAdd a := ha
    refine ⟨torusSL ε hC hCp (ofAdd (negMap j (toAdd a))), ?_, ?_⟩
    · refine ⟨ofAdd (negMap j (toAdd a)), ?_, rfl⟩
      have h2 : swapMap i j (negMap j (toAdd a)) = negMap j (toAdd a) := by
        have h1 : negMap j (swapMap i j (negMap j (toAdd a))) = toAdd a := ha'
        calc swapMap i j (negMap j (toAdd a))
            = negMap j (negMap j (swapMap i j (negMap j (toAdd a)))) := by
              rw [negMap_negMap]
          _ = negMap j (toAdd a) := by rw [h1]
      simpa using h2
    · rw [hconj]
      simp only [toAdd_ofAdd, negMap_negMap, ofAdd_toAdd]
  have hsub2 : (MulAut.conj N).toMonoidHom '' torusFix (torusSL ε hC hCp) (swapMap i j) ⊆
      torusFix (torusSL ε hC hCp) (sswapMap i j) := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hz
    have ht' : swapMap i j (toAdd t) = toAdd t := ht
    rw [hconj]
    refine ⟨ofAdd (negMap j (toAdd t)), ?_, rfl⟩
    show negMap j (swapMap i j (negMap j (negMap j (toAdd t)))) = negMap j (toAdd t)
    rw [negMap_negMap, ht']
  have hmap : (Subgroup.centralizer (torusFix (torusSL ε hC hCp) (swapMap i j))).map
        (MulAut.conj N).toMonoidHom =
      Subgroup.centralizer (torusFix (torusSL ε hC hCp) (sswapMap i j)) := by
    refine le_antisymm ?_ ?_
    · exact (Subgroup.map_centralizer_le_centralizer_image
        (torusFix (torusSL ε hC hCp) (swapMap i j)) (MulAut.conj N).toMonoidHom).trans
        (Subgroup.centralizer_le hsub1)
    · intro x hx
      obtain ⟨y, rfl⟩ : ∃ y, (MulAut.conj N).toMonoidHom y = x :=
        ⟨(MulAut.conj N).symm x, (MulAut.conj N).apply_symm_apply x⟩
      refine Subgroup.mem_map_of_mem _ ?_
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have hconjz : y * z * y⁻¹ = z := by
        apply (MulAut.conj N).injective
        rw [map_mul, map_mul, map_inv]
        have hcomm : MulAut.conj N z * MulAut.conj N y = MulAut.conj N y * MulAut.conj N z :=
          Subgroup.mem_centralizer_iff.mp hx _ (hsub2 ⟨z, hz, rfl⟩)
        rw [← hcomm]
        group
      have h2 : y * z = z * y := by
        calc y * z = (y * z * y⁻¹) * y := by group
          _ = z * y := by rw [hconjz]
      exact h2.symm
  obtain ⟨hKH, hsubn, hq⟩ :=
    isComponentOf_pairBlock_centralizer (ε := ε) (hC := hC) (hCp := hCp) hp2 hgd hij
  have hdef : twistPairBlock g hζ hpK ε i j =
      (pairBlock g ε i j).map (MulAut.conj N).toMonoidHom := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdef, ← hmap]
    exact Subgroup.map_mono hKH
  · rw [hdef, ← hmap]
    exact hsubn.map (MulAut.conj N).toMonoidHom
  · rw [hdef]
    exact (CFSG.Assembly.IsQuasisimple.congr
      ((pairBlock g ε i j).equivMapOfInjective (MulAut.conj N).toMonoidHom
        (MulAut.conj N).injective)).1 hq

theorem isComponentOf_zeroBlock_centralizer (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hK : 4 ≤ Nat.card K ∨ 1 ≤ r) (i : Fin s) :
    IsComponentOf (zeroBlock g ε i)
      (Subgroup.centralizer (torusFix (torusSL ε hC hCp) (negMap i))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p := root_isPrimitiveRoot hp hpK' hgd
  have hal : Aligned hprim.pow_eq_one (blockVec (p := p) i) := aligned_blockVec i
  have hz : zeroCoords ε (blockVec (p := p) i) = blockCoords ε i := zeroCoords_blockVec ε i
  have hdim : (rootPB g).dim = 2 := SpNS.rootPB_dim_eq_two hp hp2 hpK' hgd hpK
  have hf : (Finset.univ.filter fun m : Fin s => blockVec (p := p) i m = 0) = {i} := by
    ext m
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => blockVec_eq_zero_iff.mp h.2,
      fun h => ⟨Finset.mem_univ _, blockVec_eq_zero_iff.mpr h⟩⟩
  have hβ : torusSL ε hC hCp (ofAdd (blockVec (p := p) i)) ∈
      torusFix (torusSL ε hC hCp) (negMap i) := by
    refine ⟨ofAdd (blockVec (p := p) i), ?_, rfl⟩
    simpa using (negMap_eq_self_iff hp2 (p := p) (i := i)).mpr (by simp [blockVec])
  have hJle : zeroBlock g ε i ≤
      Subgroup.centralizer (torusFix (torusSL ε hC hCp) (negMap i)) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    have hti : toAdd a i = 0 := (negMap_eq_self_iff hp2).mp ha
    have hx' : x ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) := by
      rw [zeroCoords_blockVec]
      exact hx
    have hcomm : SLNS.nsSL ε hC (fun m => (toAdd a m).val) * x =
        x * SLNS.nsSL ε hC (fun m => (toAdd a m).val) :=
      comm_zeroBlock_of_torus (ε := ε) (hC := hC) (β := blockVec (p := p) i)
        (k := fun m => (toAdd a m).val) ?_ hx'
    · rw [← ofAdd_toAdd a, torusSL_apply]
      exact hcomm
    · intro m hm
      have hmi : m = i := blockVec_eq_zero_iff.mp hm
      rw [hmi]
      simpa using congrArg ZMod.val hti
  have hHle : Subgroup.centralizer (torusFix (torusSL ε hC hCp) (negMap i)) ≤
      Subgroup.centralizer ({torusSL ε hC hCp (ofAdd (blockVec (p := p) i))} :
        Set (SpecialLinearGroup (Fin n) K)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hβ)
  have hnorm : Subgroup.centralizer (torusFix (torusSL ε hC hCp) (negMap i)) ≤
      Subgroup.normalizer (zeroBlock g ε i : Set (SpecialLinearGroup (Fin n) K)) := by
    refine hHle.trans ?_
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hx' : x * SLNS.nsSL ε hC (fun m => (blockVec (p := p) i m).val) =
        SLNS.nsSL ε hC (fun m => (blockVec (p := p) i m).val) * x := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [torusSL_apply] at hcomm
      exact hcomm
    have hy' : y ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) := by
      rw [zeroCoords_blockVec]
      exact hy
    have hconj : x * y * x⁻¹ ∈ coordBlockSL K (zeroCoords ε (blockVec (p := p) i)) :=
      conj_mem_zeroBlock (hζ := hprim.pow_eq_one) (ε := ε) (hC := hC) hprim hal hx' hy'
    simpa only [zeroBlock, hz] using hconj
  have hcard : 2 ≤ (blockCoords ε i).card := by
    rw [← hz, card_zeroCoords ε (blockVec (p := p) i), hf, Finset.card_singleton, hdim]
    omega
  have hq : CFSG.Assembly.IsQuasisimple (zeroBlock g ε i) := by
    rcases hK with hK4 | hr
    · have hq₀ : CFSG.IsQuasisimple (coordBlockSL K (blockCoords ε i)) :=
        isQuasisimple_coordBlockSL hcard hK4
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq₀
    · have h3 : 3 ≤ (blockCoords ε i).card := by
        rw [← hz, card_zeroCoords ε (blockVec (p := p) i), hf, Finset.card_singleton, hdim]
        omega
      have hq₀ : CFSG.IsQuasisimple (coordBlockSL K (blockCoords ε i)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((MonoidHom.ofInjective (blockSLOn_injective (k := K) (blockCoords ε i))).trans
            (MulEquiv.subgroupCongr (range_blockSLOn (blockCoords ε i))))
          (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
            (blockCoords ε i).card K (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq₀
  refine ⟨hJle, CFSG.Assembly.IsSubnormal.step hJle ?_ (CFSG.Assembly.IsSubnormal.refl _), hq⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).mpr hnorm

theorem dvd_natCard_pairBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K)
    {i j : Fin s} (hij : i ≠ j) : p ∣ Nat.card (pairBlock g ε i j) := by
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hC : (rootMat g).det = 1 :=
    det_rootMat hp (SpNS.not_dvd_card_sub_one hp hp2 hpK) hpK' hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK' hgd
  let v : Fin s → ZMod p := Pi.single i 1 - Pi.single j 1
  have hti : v i = 1 := by simp [v, Pi.sub_apply, hij, Ne.symm hij]
  have ht0 : v ≠ 0 := by
    intro h
    exact one_ne_zero (by rw [← hti, h]; simp)
  have hmem : torusSL ε hC hCp (ofAdd v) ∈ pairBlock g ε i j :=
    torusSL_sub_single_mem_pairBlock hp2 hgd hij
  have hpow : (torusSL ε hC hCp (ofAdd v)) ^ p = 1 :=
    pow_torusSL (ε := ε) (hC := hC) (hCp := hCp) (MonoidHom.id _) v
  have hne : torusSL ε hC hCp (ofAdd v) ≠ 1 :=
    map_torusSL_ne_one (ε := ε) (hC := hC) (hCp := hCp) (φ := MonoidHom.id _)
      hp2 hpK hgd (fun x hx => hx) ht0
  have hdvd := Subgroup.orderOf_dvd_natCard (pairBlock g ε i j) hmem
  rwa [orderOf_eq_prime hpow hne] at hdvd

theorem dvd_natCard_twistPairBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1) {i j : Fin s} (hij : i ≠ j) :
    p ∣ Nat.card (twistPairBlock g hζ hpK ε i j) := by
  have h : p ∣ Nat.card (pairBlock g ε i j) := dvd_natCard_pairBlock hp2 hpK hgd hij
  rw [show twistPairBlock g hζ hpK ε i j =
      (pairBlock g ε i j).map (MulAut.conj (negSL g hζ hpK ε j)).toMonoidHom from rfl,
    Subgroup.card_map_of_injective (MulAut.conj (negSL g hζ hpK ε j)).injective]
  exact h

theorem dvd_natCard_zeroBlock (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K)
    (i : Fin s) : p ∣ Nat.card (zeroBlock g ε i) := by
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hC : (rootMat g).det = 1 :=
    det_rootMat hp (SpNS.not_dvd_card_sub_one hp hp2 hpK) hpK' hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK' hgd
  let v : Fin s → ZMod p := Pi.single i 1
  have hti : v i = 1 := by simp [v]
  have ht0 : v ≠ 0 := by
    intro h
    exact one_ne_zero (by rw [← hti, h]; simp)
  have hmem : torusSL ε hC hCp (ofAdd v) ∈ zeroBlock g ε i :=
    torusSL_single_mem_zeroBlock i
  have hpow : (torusSL ε hC hCp (ofAdd v)) ^ p = 1 :=
    pow_torusSL (ε := ε) (hC := hC) (hCp := hCp) (MonoidHom.id _) v
  have hne : torusSL ε hC hCp (ofAdd v) ≠ 1 :=
    map_torusSL_ne_one (ε := ε) (hC := hC) (hCp := hCp) (φ := MonoidHom.id _)
      hp2 hpK hgd (fun x hx => hx) ht0
  have hdvd := Subgroup.orderOf_dvd_natCard (zeroBlock g ε i) hmem
  rwa [orderOf_eq_prime hpow hne] at hdvd

end CFSG.StandardType.SlNsRootGen

end
