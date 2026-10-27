module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeKG
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspD4
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossLin
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHighWit

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Chevalley (torusTorsion)
open CFSG.RankThree.Chevalley (units_map_entrywiseHom_eq_baseChangeGL_self
  fin_G2_cases torusTorsion_le_torusGroup rootDiagUnit_mem_torusTorsion_iff)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

private lemma torusTorsion_three_diag
    {K : Type} [Field K]
    {z : ModGL Tag.G2 K} (hz : z ∈ torusTorsion K 3) :
    ∃ c : Fin Tag.G2.rank → Kˣ, z = rootDiagUnit Tag.G2 c ∧ c ^ 3 = 1 := by
  have hH : z ∈ torusGroup Tag.G2 K := torusTorsion_le_torusGroup 3 hz
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
  refine ⟨c, hc, ?_⟩
  rw [hc] at hz
  exact (rootDiagUnit_mem_torusTorsion_iff 3 c).1 hz

private lemma not_diag_ia_eq_one
    {K : Type} [Field K] [Finite K]
    (h31 : 3 ∣ Nat.card K - 1)
    {z : adjointGroup Tag.G2 K} {c : Fin Tag.G2.rank → Kˣ}
    (hzc : (z : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 c)
    (hc3 : c ^ 3 = 1) (hz1 : z ≠ 1)
    (hC : Nat.card ↥(Subgroup.centralizer ({z} : Set (adjointGroup Tag.G2 K))) ≠
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :
    c g2ia ≠ 1 := by
  intro hia
  have hc : c = Pi.mulSingle g2ir (c g2ir) := by
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · rw [Pi.mulSingle_eq_of_ne (by decide : g2ia ≠ g2ir)]
      exact hia
    · rw [Pi.mulSingle_eq_same]
  have hzS : z ∈ g2ShortSL2 K := by
    rw [mem_g2ShortSL2_iff]
    refine ⟨HSL (c g2ir), ?_⟩
    rw [rhoV_HSL, ← hc, hzc]
  have hz3 : z ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hzc, rootDiagUnit_pow, hc3, rootDiagUnit_one]
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec4.E27.nonempty_centralizer_mulEquiv_SL3 h31 hzS hz3 hz1
  have hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set (adjointGroup Tag.G2 K))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := Nat.card_congr e.toEquiv
  rw [hcard, CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.card_SL_three] at hC
  exact hC rfl

private lemma weylElt_fixed_g2FieldHom
    {K : Type} [Field K] (σ : K ≃+* K)
    (i : Fin Tag.G2.rank) :
    g2FieldHom K σ (⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ :
      adjointGroup Tag.G2 K) =
      (⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup Tag.G2 K) := by
  apply Subtype.ext
  change (g2FieldHom K σ ⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ :
    ModGL Tag.G2 K) = weylElt Tag.G2 K i 1
  rw [coe_g2FieldHom]
  change Units.map (entrywiseHom σ.toRingHom) (weylElt Tag.G2 K i 1) =
    weylElt Tag.G2 K i 1
  rw [units_map_entrywiseHom_eq_baseChangeGL_self,
    CFSG.RankThree.Chevalley.baseChangeGL_weylElt_one]

private lemma zpow_cube_eq_one {G : Type} [CommGroup G] {x : G} (hx : x ^ 3 = 1) (k : ℤ) :
    (x ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast (x ^ k) 3, ← zpow_mul]
  rw [show k * ((3:ℕ):ℤ) = ((3:ℕ):ℤ) * k from mul_comm k _]
  rw [zpow_mul, zpow_natCast, hx, one_zpow]

private lemma weylElt_conj_mem_torusTorsion
    {K : Type} [Field K]
    (i : Fin Tag.G2.rank) {y : adjointGroup Tag.G2 K}
    (hy : (y : ModGL Tag.G2 K) ∈ torusTorsion K 3) :
    (((⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup Tag.G2 K) * y *
        (⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup Tag.G2 K)⁻¹ :
        adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ torusTorsion K 3 := by
  obtain ⟨a, hya, ha3⟩ := torusTorsion_three_diag hy
  have hcoe : (((⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ :
      adjointGroup Tag.G2 K) * y *
      (⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup Tag.G2 K)⁻¹ :
      adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      weylElt Tag.G2 K i 1 * rootDiagUnit Tag.G2 a * (weylElt Tag.G2 K i 1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hya]
  rw [hcoe, weylElt_conj_rootDiagUnit]
  refine (rootDiagUnit_mem_torusTorsion_iff 3
    (fun j => a j * a i ^ (-Tag.G2.cartan i j))).2 ?_
  funext j
  rw [Pi.pow_apply]
  have hj : a j ^ 3 = 1 := by simpa using congrFun ha3 j
  have hi : a i ^ 3 = 1 := by simpa using congrFun ha3 i
  calc (a j * a i ^ (-Tag.G2.cartan i j)) ^ 3
      = (a j) ^ 3 * (a i ^ (-Tag.G2.cartan i j)) ^ 3 := by rw [mul_pow]
    _ = 1 * 1 := by rw [hj, zpow_cube_eq_one hi]
    _ = 1 := by rw [mul_one]

private lemma tuple_eq_of_zpow_eq_conj
    {K : Type} [Field K]
    {c : Fin Tag.G2.rank → Kˣ} {z : adjointGroup Tag.G2 K}
    (hzc : (z : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 c)
    (i : Fin Tag.G2.rank) {k : ℤ}
    (hk : z ^ k = (⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ :
        adjointGroup Tag.G2 K) * z *
        (⟨weylElt Tag.G2 K i 1, weylElt_mem_adjointGroup i 1⟩ :
        adjointGroup Tag.G2 K)⁻¹) :
    c ^ k = fun j => c j * c i ^ (-Tag.G2.cartan i j) := by
  have hzpow : (z : ModGL Tag.G2 K) ^ k =
      ((z ^ k : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) :=
    (Subgroup.coe_zpow _ _ _).symm
  have hconj : ((z ^ k : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) =
      weylElt Tag.G2 K i 1 * (z : ModGL Tag.G2 K) * (weylElt Tag.G2 K i 1)⁻¹ := by
    rw [hk, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hcoe : (rootDiagUnit Tag.G2 c) ^ k =
      weylElt Tag.G2 K i 1 * rootDiagUnit Tag.G2 c * (weylElt Tag.G2 K i 1)⁻¹ := by
    calc (rootDiagUnit Tag.G2 c) ^ k = (z : ModGL Tag.G2 K) ^ k := by rw [hzc]
      _ = ((z ^ k : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) := hzpow
      _ = weylElt Tag.G2 K i 1 * (z : ModGL Tag.G2 K) * (weylElt Tag.G2 K i 1)⁻¹ := hconj
      _ = weylElt Tag.G2 K i 1 * rootDiagUnit Tag.G2 c * (weylElt Tag.G2 K i 1)⁻¹ := by
          rw [hzc]
  have hmap : (rootDiagUnit Tag.G2 c) ^ k = rootDiagUnit Tag.G2 (c ^ k) :=
    (map_zpow (rootDiagUnitHom Tag.G2 K) c k).symm
  rw [hmap, weylElt_conj_rootDiagUnit] at hcoe
  exact rootDiagUnit_injective hcoe

private lemma finite_check {K : Type} [Field K]
    (c : Fin Tag.G2.rank → Kˣ) (hc3 : c ^ 3 = 1) (hia : c g2ia ≠ 1)
    (h0 : ∃ k : ℤ, c ^ k = fun j => c j * c g2ia ^ (-Tag.G2.cartan g2ia j))
    (h1 : ∃ k : ℤ, c ^ k = fun j => c j * c g2ir ^ (-Tag.G2.cartan g2ir j)) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcart10 : (-Tag.G2.cartan g2ir g2ia) = ((3:ℕ):ℤ) := by decide
  have hcart11 : (-Tag.G2.cartan g2ir g2ir) = -2 := by decide
  have hcart01 : (-Tag.G2.cartan g2ia g2ir) = 1 := by decide
  have hu3 : c g2ia ^ 3 = 1 := by simpa using congrFun hc3 g2ia
  have hv3 : c g2ir ^ 3 = 1 := by simpa using congrFun hc3 g2ir
  obtain ⟨k1, hk1⟩ := h0
  obtain ⟨k2, hk2⟩ := h1
  have e1u : (c g2ia) ^ k2 = c g2ia := by
    have h := congrFun hk2 g2ia
    simp only [Pi.pow_apply] at h
    rw [hcart10, zpow_natCast, hv3, mul_one] at h
    exact h
  have e1v : (c g2ir) ^ k2 = (c g2ir) ^ (-1 : ℤ) := by
    have h := congrFun hk2 g2ir
    simp only [Pi.pow_apply] at h
    rw [hcart11] at h
    have hx : c g2ir * (c g2ir) ^ (-2 : ℤ) = (c g2ir) ^ (-1 : ℤ) := by
      have hsplit : c g2ir * (c g2ir) ^ (-2 : ℤ) = (c g2ir) ^ ((1 : ℤ) + (-2)) := by
        rw [zpow_add, zpow_one]
      rw [hsplit]
      norm_num
    rw [hx] at h
    exact h
  have huord : orderOf (c g2ia) = 3 := orderOf_eq_prime hu3 hia
  have hmod : k2 ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
    have h : (c g2ia) ^ k2 = (c g2ia) ^ (1 : ℤ) := by rw [e1u, zpow_one]
    have h2 := zpow_eq_zpow_iff_modEq.mp h
    rw [huord] at h2
    simpa using h2
  have h3dvd : (3 : ℤ) ∣ k2 - 1 := by
    obtain ⟨l, hl⟩ := Int.modEq_iff_dvd.mp hmod
    exact ⟨-l, by omega⟩
  obtain ⟨l, hl⟩ := h3dvd
  have hk2 : k2 = 3 * l + 1 := by omega
  have e2v : (c g2ir) ^ k2 = c g2ir := by
    rw [hk2]
    rw [show (3 * l + 1 : ℤ) = ((3:ℕ):ℤ) * l + 1 by push_cast; ring]
    rw [zpow_add, zpow_one]
    rw [show (c g2ir) ^ (((3:ℕ):ℤ) * l) = (c g2ir ^ ((3:ℕ):ℤ)) ^ l by rw [zpow_mul]]
    rw [zpow_natCast, hv3, one_zpow, one_mul]
  have hxinv : (c g2ir) ^ (-1 : ℤ) = c g2ir := by
    rw [← e1v, e2v]
  have hx2 : (c g2ir) ^ 2 = 1 := by
    rw [pow_two]
    have h := congrArg (fun y => y * c g2ir) hxinv
    rw [zpow_neg_one, inv_mul_cancel] at h
    exact h.symm
  have hv1 : c g2ir = 1 := by
    have h : c g2ir * (c g2ir) ^ 2 = 1 := by rw [← pow_succ', hv3]
    rwa [hx2, mul_one] at h
  have e0 : (c g2ir) ^ k1 = c g2ir * c g2ia := by
    have h := congrFun hk1 g2ir
    simp only [Pi.pow_apply] at h
    rw [hcart01, zpow_one] at h
    exact h
  have hcon : c g2ia = 1 := by
    have h := e0
    rw [hv1, one_zpow, one_mul] at h
    exact h.symm
  exact hia hcon

theorem ggNbrG2Off_torsion_moved
    {K : Type} [Field K] [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    (σ : K ≃+* K) {z : adjointGroup Tag.G2 K} (hz : (z : ModGL Tag.G2 K) ∈ torusTorsion K 3)
    (hz1 : z ≠ 1)
    (hC : Nat.card ↥(Subgroup.centralizer ({z} : Set (adjointGroup Tag.G2 K))) ≠
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :
    ∃ w : adjointGroup Tag.G2 K, g2FieldHom K σ w = w ∧
      (∀ y : adjointGroup Tag.G2 K, (y : ModGL Tag.G2 K) ∈ torusTorsion K 3 →
        ((w * y * w⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈ torusTorsion K 3) ∧
      w * z * w⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨c, hzc, hc3⟩ := torusTorsion_three_diag hz
  have hia : c g2ia ≠ 1 := not_diag_ia_eq_one h31 hzc hc3 hz1 hC
  let w0 : adjointGroup Tag.G2 K :=
    ⟨weylElt Tag.G2 K g2ia 1, weylElt_mem_adjointGroup g2ia 1⟩
  let w1 : adjointGroup Tag.G2 K :=
    ⟨weylElt Tag.G2 K g2ir 1, weylElt_mem_adjointGroup g2ir 1⟩
  by_cases hm0 : w0 * z * w0⁻¹ ∈ Subgroup.zpowers z
  · have hm1 : w1 * z * w1⁻¹ ∉ Subgroup.zpowers z := by
      intro hm1'
      apply finite_check c hc3 hia
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm0
        exact ⟨k, tuple_eq_of_zpow_eq_conj hzc g2ia hk⟩
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm1'
        exact ⟨k, tuple_eq_of_zpow_eq_conj hzc g2ir hk⟩
    exact ⟨w1, weylElt_fixed_g2FieldHom σ g2ir,
      fun y hy => weylElt_conj_mem_torusTorsion g2ir hy, hm1⟩
  · exact ⟨w0, weylElt_fixed_g2FieldHom σ g2ia,
      fun y hy => weylElt_conj_mem_torusTorsion g2ia hy, hm0⟩

end CFSG.StandardType

end
