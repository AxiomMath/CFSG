module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphLayers
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.FirstCaseT2SwapOrderFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The root bridge for the Suzuki odd graph

The four conjugates commuting with the base line are exactly the four
non-base `Ĥ`-cosets containing no involution.  This identifies the graph
neighbourhood with the zero-fibre coset layer.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private lemma conjugateSubgroup_mul {G : Type*} [Group G]
    (H : Subgroup G) (g h : G) :
    conjugateSubgroup (conjugateSubgroup H h) g =
      conjugateSubgroup H (g * h) := by
  ext x
  simp [conjugateSubgroup, Subgroup.map_map]

private lemma order_three_disjoint {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hne : A ≠ B) : Disjoint A B := by
  rw [disjoint_iff_inf_le]
  intro x hx
  by_contra hxne
  have horder : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard A hx.1
      simpa [hA] using h
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact False.elim (hxne (orderOf_eq_one_iff.mp h1))
    · exact h3
  have hAgen : Subgroup.zpowers x = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hx.1
    · rw [Nat.card_zpowers, horder, hA]
  have hBgen : Subgroup.zpowers x = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hx.2
    · rw [Nat.card_zpowers, horder, hB]
  exact hne (hAgen.symm.trans hBgen)

private lemma conjugate_card {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (g : G) :
    Nat.card (conjugateSubgroup A g) = Nat.card A := by
  exact (Nat.card_congr
    (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm

private lemma pow_eq_sq_of_cyclic_order_four
    {G : Type*} [Group G] [Finite G] (a y : G)
    (ha : orderOf a = 4) (hy : y ∈ Subgroup.zpowers a)
    (hyI : IsInvolution y) : y = a ^ 2 := by
  let K : Subgroup G := Subgroup.zpowers a
  have hKcard : Nat.card K = 4 := by
    simpa [K, ha] using Nat.card_zpowers a
  have hcyc : IsCyclic K := Subgroup.isCyclic_zpowers a
  let xK : K := ⟨a, Subgroup.mem_zpowers a⟩
  let yK : K := ⟨y, hy⟩
  let tK : K := ⟨a ^ 2,
    Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2⟩
  have hxK4 : orderOf xK = 4 := by
    rw [← orderOf_submonoid (H := K.toSubmonoid) xK]
    exact ha
  have hyKne : yK ≠ 1 := by
    intro h
    exact hyI.1 (congrArg Subtype.val h)
  have hyK2 : yK ^ 2 = 1 := by
    apply Subtype.ext
    simpa [yK, pow_two] using hyI.2
  have htKne : tK ≠ 1 := by
    intro h
    have hpow : a ^ 2 = 1 := congrArg Subtype.val h
    have hd : orderOf a ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hpow
    rw [ha] at hd
    norm_num at hd
  have htK2 : tK ^ 2 = 1 := by
    apply Subtype.ext
    change (a ^ 2) ^ 2 = 1
    rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num]
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hyt : yK = tK :=
    unique_involution_of_cyclic_two_group hcyc (m := 2) (by norm_num) hKcard
      yK tK hyKne hyK2 htKne htK2
  exact congrArg Subtype.val hyt

/-- A conjugate commuting with the base line corresponds to an involution-free
`Ĥ`-coset. -/
public theorem firstCase_neighbor_coset_fiber_card_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c)
    (hV : lineNeighbor c V) :
    Nat.card (cosetInvolution_fiber c.Hhat
      ((cosetLineEquiv hmin c hfirst).symm V)) = 0 := by
  classical
  let q : G ⧸ c.Hhat := (cosetLineEquiv hmin c hfirst).symm V
  by_contra hqne
  have hqpos : 0 < Nat.card (cosetInvolution_fiber c.Hhat q) :=
    Nat.pos_of_ne_zero hqne
  obtain ⟨y, hy⟩ := (Nat.card_pos_iff.mp hqpos).1
  have hyI : IsInvolution y := hy.1
  have hyInv : y⁻¹ = y :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hyI.2)
  have hqmk : q = QuotientGroup.mk y := by
    calc
      q = cosetInvolution_proj c.Hhat y := hy.2.symm
      _ = QuotientGroup.mk (y⁻¹) := rfl
      _ = QuotientGroup.mk y := by rw [hyInv]
  have hVeq : V = y • UConjugates.base c := by
    have hmk : cosetLineEquiv hmin c hfirst (QuotientGroup.mk y) = V := by
      rw [← hqmk]
      exact (cosetLineEquiv hmin c hfirst).apply_symm_apply V
    rw [cosetLineEquiv_mk] at hmk
    exact hmk.symm
  let U : Subgroup G := c.U
  let W : Subgroup G := (V : Subgroup G)
  have hUW : U ≠ W := by
    intro h
    apply hV.1
    apply Subtype.ext
    simpa [U, W, UConjugates.base_val] using h.symm
  have hU3 : Nat.card U = 3 := by
    simpa [U] using firstCase_U_card_three hmin c hfirst d
  have hW3 : Nat.card W = 3 := by
    rcases V.2 with ⟨g, hg⟩
    rw [show W = conjugateSubgroup c.U g by exact hg, conjugate_card]
    exact hU3
  have hWmap : conjugateSubgroup U y = W := by
    have hv := congrArg Subtype.val hVeq
    simpa [U, W, UConjugates.smul_def, UConjugates.base_val] using hv.symm
  have hWcent : W ≤ Subgroup.centralizer (U : Set G) := by
    intro w hw u hu
    exact (hV.2 u hu w hw).eq
  have hWnorm : W ≤ Subgroup.normalizer (U : Set G) :=
    hWcent.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hdisj : Disjoint U W := order_three_disjoint U W hU3 hW3 hUW
  have hP0card : Nat.card (U ⊔ W : Subgroup G) = 9 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer U W hWnorm hdisj]
    rw [hU3, hW3]
  have hfac : (Nat.card G).factorization 3 = 2 := by
    rcases firstCase_index_card_of_countData c d with ⟨_, hG⟩
    rw [hG]
    rw [show (2 ^ 3 * 3 ^ 2 * 5 * 7 : ℕ) = 3 ^ 2 * (2 ^ 3 * 5 * 7) by ring]
    rw [Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [Nat.factorization_pow]
    simp [Nat.prime_three.factorization_self]
    exact Nat.factorization_eq_zero_of_not_dvd
      (by norm_num : ¬ 3 ∣ (2 ^ 3 * 5 * 7 : ℕ))
  let P : Sylow 3 G := Sylow.ofCard (U ⊔ W : Subgroup G) (by
    rw [hP0card, hfac]
    norm_num)
  have hUP : U ≤ (P : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact le_sup_left
  have hWP : W ≤ (P : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact le_sup_right
  have hWmap' : conjugateSubgroup W y = U := by
    calc
      conjugateSubgroup W y =
          conjugateSubgroup (conjugateSubgroup U y) y := by rw [hWmap]
      _ = conjugateSubgroup U (y * y) := conjugateSubgroup_mul U y y
      _ = U := by
        rw [show y * y = 1 by simpa [pow_two] using hyI.2]
        ext x
        simp [conjugateSubgroup]
  have hPmap : conjugateSubgroup (P : Subgroup G) y = (P : Subgroup G) := by
    rw [show (P : Subgroup G) = U ⊔ W by rw [Sylow.coe_ofCard]]
    change Subgroup.map (MulAut.conj y) (U ⊔ W) = U ⊔ W
    rw [Subgroup.map_sup]
    change conjugateSubgroup U y ⊔ conjugateSubgroup W y = U ⊔ W
    rw [hWmap, hWmap', sup_comm]
  have hyNP : y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hPmap
  let NP : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  let yNP : NP := ⟨y, hyNP⟩
  let Z : Subgroup NP := Subgroup.zpowers yNP
  have hZp : IsPGroup 2 Z := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    have hy2 : y ^ 2 = 1 := by simpa [pow_two] using hyI.2
    have hord : orderOf y = 2 := orderOf_eq_prime hy2 hyI.1
    rw [← orderOf_submonoid (H := NP.toSubmonoid) yNP, hord]
    norm_num
  obtain ⟨T2, hZT2⟩ := hZp.exists_le_sylow
  have hyT2 : yNP ∈ T2 := hZT2 (Subgroup.mem_zpowers yNP)
  have hyTg : y ∈ ((T2 : Subgroup (↥NP)).map NP.subtype : Subgroup G) :=
    Subgroup.mem_map.mpr ⟨yNP, hyT2, rfl⟩
  obtain ⟨a, _haTg, _haH, ha4, hagen, ha2H, _ha2ne, _, _⟩ :=
    firstCase_exists_t2_order_four_swap hmin c hfirst d P hUP T2
  have hySq : y = a ^ 2 := by
    apply pow_eq_sq_of_cyclic_order_four a y ha4
    · rw [hagen]
      simpa [NP] using hyTg
    · exact hyI
  have hyH : y ∈ c.Hhat := by
    rw [hySq]
    exact ha2H.2
  have hybase : y • UConjugates.base c = UConjugates.base c := by
    apply Subtype.ext
    rw [UConjugates.smul_def]
    change conjugateSubgroup c.U y = c.U
    have hnorm : y ∈ Subgroup.normalizer (c.U : Set G) := by
      rw [commutingGraph.hhat_normalizer_U hmin c hfirst]
      exact hyH
    simpa [conjugateSubgroup] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm)
  apply hV.1
  calc
    V = y • UConjugates.base c := hVeq
    _ = UConjugates.base c := hybase

/-- The graph-neighbour relation at `U` is exactly the non-base zero-fibre
coset layer under `cosetLineEquiv`. -/
public theorem firstCase_mem_lineNeighbors_iff_cosetLayer_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) (V : UConjugates c) :
    V ∈ lineNeighbors c ↔
      (cosetLineEquiv hmin c hfirst).symm V ≠
          cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat
          ((cosetLineEquiv hmin c hfirst).symm V)) = 0 := by
  classical
  let e := cosetLineEquiv hmin c hfirst
  let A : Set (UConjugates c) := lineNeighbors c
  let B : Set (UConjugates c) :=
    {W | e.symm W ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat (e.symm W)) = 0}
  have hbase : e (cosetInvolution_base c.Hhat) = UConjugates.base c := by
    unfold cosetInvolution_base
    simp only [inv_one]
    rw [show e (QuotientGroup.mk (1 : G)) =
        (1 : G) • UConjugates.base c by
      exact cosetLineEquiv_mk hmin c hfirst 1]
    simp
  have hsub : A ⊆ B := by
    intro W hW
    have hW' : lineNeighbor c W := by simpa [A] using hW
    refine ⟨?_, firstCase_neighbor_coset_fiber_card_zero
      hmin c hfirst d W hW'⟩
    intro hq
    apply hW'.1
    calc
      W = e (e.symm W) := (e.apply_symm_apply W).symm
      _ = e (cosetInvolution_base c.Hhat) := by rw [hq]
      _ = UConjugates.base c := hbase
  have hAcard : A.ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (lineNeighborSet c) = 4
    exact neighbor_card_eq_four hmin c hfirst d
  let eB : firstCaseCosetLayer c 0 ≃ {W : UConjugates c // W ∈ B} :=
    e.subtypeEquiv (fun q => by simp [B])
  have hBcard : B.ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    calc
      Nat.card {W : UConjugates c // W ∈ B} =
          Nat.card (firstCaseCosetLayer c 0) := (Nat.card_congr eB).symm
      _ = 4 := (firstCaseCosetLayer_card hmin c hfirst d).1
  have hAB : A = B :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hAcard, hBcard])
  change V ∈ A ↔ V ∈ B
  rw [hAB]

end CFSG.GorensteinWalter
