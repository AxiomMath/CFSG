module

public import CFSG.RankThree.PartOne.KF.ClsExcD4
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRoots
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KGD
open CFSG.Timmesfeld.ExceptionalOrders
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Coord

variable {τ : Tag} {K : Type} [Field K]

theorem torusCoordHom_eq_rootDiagUnit (c : Fin τ.rank → Kˣ) :
    ((torusCoordHom τ K c : torusGroup τ K) : ModGL τ K) =
      rootDiagUnit τ (zpowMatrix (G := Kˣ) τ.cartan c) := by
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)
  · change _ = rootDiag (zpowMatrix (G := Kˣ) τ.cartan c) (hVec τ K j)
    rw [rootDiag_hVec, coe_torusCoordHom, list_ofFn_torusElt, list_prod_torusElt_hVec]
  · change _ = rootDiag (zpowMatrix (G := Kˣ) τ.cartan c) (rootVec τ K α)
    rw [rootDiag_rootVec _ hα, coe_torusCoordHom, list_ofFn_torusElt,
      list_prod_torusElt_rootVec hα, List.map_ofFn, List.prod_ofFn]
    congr 2
    have e : ∏ i : Fin τ.rank, ((fun p : Fin τ.rank × Kˣ => p.2 ^ (∑ k, τ.cartan p.1 k * α k)) ∘
        (fun i => (i, c i))) i = ∏ k, (∏ i, c i ^ τ.cartan i k) ^ α k := by
      simp only [Function.comp_apply, ← prod_zpow_eq_zpow_sum, zpow_mul]
      rw [Finset.prod_comm]
      simp only [Finset.prod_zpow]
    rw [e]
    rfl

end Coord


section Central

theorem exists_unit_order_card_sub_one {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ g : Kˣ, orderOf g = 2 ^ n - 1 ∧ Units.map σ.toRingHom.toMonoidHom g = g := by
  have hQ1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hQ2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hu
  have hdiv : 2 ^ n - 1 ∣ (2 ^ n) ^ 3 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 3
    rwa [one_pow] at this
  have hpos : 0 < (2 ^ n) ^ 3 - 1 := by
    have : 1 < (2 ^ n) ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hm0 : ((2 ^ n) ^ 3 - 1) / (2 ^ n - 1) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hpos hdiv) (by omega)).ne'
  have hmdvd : ((2 ^ n) ^ 3 - 1) / (2 ^ n - 1) ∣ orderOf u := by
    rw [hu]
    exact Nat.div_dvd_of_dvd hdiv
  have hord : orderOf (u ^ (((2 ^ n) ^ 3 - 1) / (2 ^ n - 1))) = 2 ^ n - 1 := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hu]
    exact Nat.div_div_self hdiv hpos.ne'
  refine ⟨u ^ (((2 ^ n) ^ 3 - 1) / (2 ^ n - 1)), hord, ?_⟩
  set g : Kˣ := u ^ (((2 ^ n) ^ 3 - 1) / (2 ^ n - 1)) with hg
  have hg1 : g ^ (2 ^ n - 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hgQ : g ^ (2 ^ n) = g := by
    rw [← Nat.sub_add_cancel hQ1, pow_succ, hg1, one_mul]
  apply Units.ext
  change σ (g : K) = g
  rw [hσ, ← Units.val_pow_eq_pow_val, hgQ]

end Central


section Cartan

theorem d4_cartan_entries :
    TwistTag.D4.tag.cartan = !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem zpowMatrix_apply4 {G : Type*} [CommGroup G]
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (t : Fin TwistTag.D4.tag.rank → G) (j : Fin TwistTag.D4.tag.rank) :
    zpowMatrix M t j = t 0 ^ M 0 j * t 1 ^ M 1 j * t 2 ^ M 2 j * t 3 ^ M 3 j := by
  rw [zpowMatrix_apply]
  exact Fin.prod_univ_four (fun i : Fin 4 => t i ^ M i j)

@[expose] def cT {K : Type} [Field K] (g : Kˣ) (k : ℕ) : Fin TwistTag.D4.tag.rank → Kˣ :=
  ![g, g, g ^ k, g]

theorem zpowMatrix_cT_center {K : Type} [Field K] (g : Kˣ) (k : ℕ) :
    zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan (cT g k) 2 = g⁻¹ * g⁻¹ * (g ^ k) ^ 2 * g⁻¹ := by
  rw [zpowMatrix_apply4, d4_cartan_entries]
  show g ^ (-1 : ℤ) * g ^ (-1 : ℤ) * (g ^ k) ^ (2 : ℤ) * g ^ (-1 : ℤ) = _
  simp

theorem zpowMatrix_cT_outer {K : Type} [Field K] (g : Kˣ) (j : Fin TwistTag.D4.tag.rank)
    (hj : j = 0 ∨ j = 1 ∨ j = 3) :
    zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan (cT g 2) j = 1 := by
  rw [zpowMatrix_apply4, d4_cartan_entries]
  rcases hj with rfl | rfl | rfl
  · show g ^ (2 : ℤ) * g ^ (0 : ℤ) * (g ^ 2) ^ (-1 : ℤ) * g ^ (0 : ℤ) = 1
    simp
  · show g ^ (0 : ℤ) * g ^ (2 : ℤ) * (g ^ 2) ^ (-1 : ℤ) * g ^ (0 : ℤ) = 1
    simp
  · show g ^ (0 : ℤ) * g ^ (0 : ℤ) * (g ^ 2) ^ (-1 : ℤ) * g ^ (2 : ℤ) = 1
    simp

end Cartan


section Elt

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem cT_compat (σ : K ≃+* K) {g : Kˣ} (hg : Units.map σ.toRingHom.toMonoidHom g = g)
    (k : ℕ) : cT g k ∈ compatSubgroup (t := TwistTag.D4) σ.toRingHom := by
  rw [mem_compatSubgroup]
  have hgk : Units.map σ.toRingHom.toMonoidHom (g ^ k) = g ^ k := by rw [map_pow, hg]
  intro i
  fin_cases i
  · exact hg.symm
  · exact hg.symm
  · exact hgk.symm
  · exact hg.symm

omit [Finite K] in
theorem orderOf_cT (g : Kˣ) (k : ℕ) : orderOf (cT g k) = orderOf g := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    funext i
    fin_cases i
    · exact pow_orderOf_eq_one g
    · exact pow_orderOf_eq_one g
    · change (g ^ k) ^ orderOf g = 1
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    · exact pow_orderOf_eq_one g
  · apply orderOf_dvd_of_pow_eq_one
    have h := congrFun (pow_orderOf_eq_one (cT g k)) 0
    exact h

theorem exists_central_torus_elt {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n) {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ≠ Set.univ) :
    ∃ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf z = 2 ^ n - 1 ∧
      ∃ a : Fin TwistTag.D4.tag.rank → Kˣ,
        (z : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag a ∧
          ∀ j ∈ TwistTag.D4.orbitUnion J, a j = 1 := by
  classical
  obtain ⟨g, hgo, hgσ⟩ := exists_unit_order_card_sub_one hn hK hσ
  have hQ1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : Odd (Nat.card K - 1) := odd_card_sub_one_of_card_eq hn hK
  have hfinj : Function.Injective (torusCoordHom TwistTag.D4.tag K) :=
    Function.Injective.of_comp (f := (torusGroup TwistTag.D4.tag K).subtype)
      (coordHom_injective_D4 hodd)
  have hk : ∀ k : ℕ, ∃ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      orderOf z = 2 ^ n - 1 ∧ (z : ModGL TwistTag.D4.tag K) =
        rootDiagUnit TwistTag.D4.tag (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan (cT g k)) := by
    intro k
    have hc := cT_compat σ hgσ k
    refine ⟨⟨_, graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom
      (compatTorus_le_graphFixedRootTorus σ.toRingHom ⟨cT g k, hc, rfl⟩)⟩, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe]
      change orderOf ((torusCoordHom TwistTag.D4.tag K (cT g k) : torusGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) = _
      rw [Subgroup.orderOf_coe, orderOf_injective _ hfinj, orderOf_cT, hgo]
    · exact torusCoordHom_eq_rootDiagUnit (cT g k)
  have hgQ : g ^ (2 ^ n) = g := by
    have hg1 : g ^ (2 ^ n - 1) = 1 := by rw [← hgo]; exact pow_orderOf_eq_one g
    rw [← Nat.sub_add_cancel hQ1, pow_succ, hg1, one_mul]
  by_cases h0 : (0 : Fin TwistTag.D4.foldedTag.rank) ∈ J
  ·
    have h1 : (1 : Fin TwistTag.D4.foldedTag.rank) ∉ J := fun h1 => hJ (Set.eq_univ_of_forall fun a => by
      fin_cases a
      · exact h0
      · exact h1)
    obtain ⟨z, hzo, hzd⟩ := hk 2
    refine ⟨z, hzo, _, hzd, fun j hj => ?_⟩
    obtain ⟨b, hbJ, hjb⟩ := (TwistTag.mem_orbitUnion TwistTag.D4).1 hj
    have hb0 : b = 0 := by
      fin_cases b
      · rfl
      · exact absurd hbJ h1
    subst hb0
    have horb : ∀ j : Fin TwistTag.D4.tag.rank,
        j ∈ TwistTag.D4.orbit (0 : Fin TwistTag.D4.foldedTag.rank) → j = 0 ∨ j = 1 ∨ j = 3 := by
      decide
    exact zpowMatrix_cT_outer g j (horb j hjb)
  ·
    obtain ⟨z, hzo, hzd⟩ := hk (3 * 2 ^ (n - 1))
    refine ⟨z, hzo, _, hzd, fun j hj => ?_⟩
    obtain ⟨b, hbJ, hjb⟩ := (TwistTag.mem_orbitUnion TwistTag.D4).1 hj
    have hb1 : b = 1 := by
      fin_cases b
      · exact absurd hbJ h0
      · rfl
    subst hb1
    have horb : ∀ j : Fin TwistTag.D4.tag.rank,
        j ∈ TwistTag.D4.orbit (1 : Fin TwistTag.D4.foldedTag.rank) → j = 2 := by
      decide
    have hj2 := horb j hjb
    subst hj2
    rw [zpowMatrix_cT_center]
    have h2n : 2 * 2 ^ (n - 1) = 2 ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    have : (g ^ (3 * 2 ^ (n - 1))) ^ 2 = g ^ 3 := by
      have e : 3 * 2 ^ (n - 1) * 2 = 2 ^ n * 3 := by rw [← h2n]; ring
      rw [← pow_mul, e, pow_mul, hgQ]
    rw [this]
    group

end Elt

end CFSG.RankThree.PartOne.TCX.Tri
