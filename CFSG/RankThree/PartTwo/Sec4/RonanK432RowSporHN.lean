module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Cover
public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Sporadic.HNSchreier.AltCent
public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.Sporadic.HNSchreier (JH sJ sJ_mem thetaJ thetaJ_sJ iotaA iotaA_injective iotaA_theta
  iotaA_tri012 tri tripleNat tripleNat_one tri012A tri012A_val tri012_pow_three isThreeCycle_tri
  order_three_classes orderOf_sJ exists_even_conj_tripleNat hnEquivJ card_outer_HN)

theorem hnK432TriMem {a b c : Fin 12} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tri a b c ∈ alternatingGroup (Fin 12) :=
  (isThreeCycle_tri hab hac hbc).mem_alternatingGroup

theorem hnK432NotMem {x Y : alternatingGroup (Fin 12)} (hx3 : x ^ 3 = 1)
    (h1 : (Y : Equiv.Perm (Fin 12)) ≠ 1)
    (h2 : (Y : Equiv.Perm (Fin 12)) ≠ (x : Equiv.Perm (Fin 12)))
    (h3 : (Y : Equiv.Perm (Fin 12)) ≠ (x : Equiv.Perm (Fin 12))⁻¹) :
    Y ∉ Subgroup.zpowers x := by
  intro h
  rcases mem_zpowers_cases_of_pow_three hx3 h with rfl | rfl | rfl
  · exact h1 rfl
  · exact h2 rfl
  · exact h3 rfl

theorem hnK432IotaNotMem
    {x y : alternatingGroup (Fin 12)} (hy : y ∉ Subgroup.zpowers x) :
    iotaA y ∉ Subgroup.zpowers (iotaA x) := by
  intro h
  rw [← MonoidHom.map_zpowers] at h
  exact hy ((Subgroup.mem_map_iff_mem iotaA_injective).1 h)

theorem hnK432Cover
    (s : ↥JH) (hs : orderOf s = 3) :
    ∃ k c : ↥JH, c ∈ ({sJ 0, sJ 2} : Set ↥JH) ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      k * c ^ e * k⁻¹ = s := by
  rcases (order_three_classes s).1 hs with h | h
  · obtain ⟨k, hk⟩ := isConj_iff.1 h
    exact ⟨k, sJ 0, Set.mem_insert _ _, 1, Or.inl rfl, by rw [pow_one]; exact hk⟩
  · obtain ⟨k, hk⟩ := isConj_iff.1 h
    exact ⟨k, sJ 2, Set.mem_insert_of_mem _ (Set.mem_singleton _), 1, Or.inl rfl,
      by rw [pow_one]; exact hk⟩

theorem hnK432WitnessS1 :
    ∃ g : ↥JH, (g * sJ 0 * g⁻¹) * sJ 0 = sJ 0 * (g * sJ 0 * g⁻¹) ∧
      g * sJ 0 * g⁻¹ ∉ Subgroup.zpowers (sJ 0) := by
  obtain ⟨A, hA⟩ : ∃ A : alternatingGroup (Fin 12), (A : Equiv.Perm (Fin 12)) = tri 3 4 5 :=
    ⟨⟨tri 3 4 5, hnK432TriMem (by decide) (by decide) (by decide)⟩, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_even_conj_tripleNat (k := 1) (by norm_num) (by norm_num)
    (Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5)
  have hσ' : (σ : Equiv.Perm (Fin 12)) * tri 0 1 2 * (σ : Equiv.Perm (Fin 12))⁻¹ = tri 3 4 5 := by
    rw [← tripleNat_one]
    exact hσ.trans (by decide)
  have hσA : σ * tri012A * σ⁻¹ = A := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, tri012A_val, hA]
    exact hσ')
  have hcommA : A * tri012A = tri012A * A := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hA, tri012A_val]
    decide)
  have hpow : tri012A ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, tri012A_val]
    exact tri012_pow_three)
  have hA1 : (A : Equiv.Perm (Fin 12)) ≠ 1 := by
    rw [hA]
    decide
  have hA2 : (A : Equiv.Perm (Fin 12)) ≠ (tri012A : Equiv.Perm (Fin 12)) := by
    rw [hA, tri012A_val]
    decide
  have hA3 : (A : Equiv.Perm (Fin 12)) ≠ (tri012A : Equiv.Perm (Fin 12))⁻¹ := by
    rw [hA, tri012A_val]
    decide
  have hAnot : A ∉ Subgroup.zpowers tri012A := hnK432NotMem hpow hA1 hA2 hA3
  have hconj : iotaA σ * sJ 0 * (iotaA σ)⁻¹ = iotaA A := by
    rw [← iotaA_tri012, ← hσA, map_mul, map_mul, map_inv]
  refine ⟨iotaA σ, ?_, ?_⟩
  · rw [hconj, ← iotaA_tri012, ← map_mul iotaA, ← map_mul iotaA, hcommA]
  · rw [hconj, ← iotaA_tri012]
    exact hnK432IotaNotMem hAnot

theorem hnK432WitnessS3 :
    ∃ g : ↥JH, (g * sJ 2 * g⁻¹) * sJ 2 = sJ 2 * (g * sJ 2 * g⁻¹) ∧
      g * sJ 2 * g⁻¹ ∉ Subgroup.zpowers (sJ 2) := by
  obtain ⟨x3, hx3, hz2⟩ : ∃ x3 : alternatingGroup (Fin 12),
      (x3 : Equiv.Perm (Fin 12)) = tripleNat 3 ∧ iotaA x3 = sJ 2 :=
    ⟨thetaJ ⟨sJ 2, sJ_mem 2⟩, thetaJ_sJ (k := 2) (by norm_num), iotaA_theta ⟨sJ 2, sJ_mem 2⟩⟩
  obtain ⟨Y, hY⟩ : ∃ Y : alternatingGroup (Fin 12),
      (Y : Equiv.Perm (Fin 12)) = tri 0 1 2 * tri 3 4 5 * tri 9 10 11 :=
    ⟨⟨tri 0 1 2 * tri 3 4 5 * tri 9 10 11, mul_mem (mul_mem
      (hnK432TriMem (by decide) (by decide) (by decide))
      (hnK432TriMem (by decide) (by decide) (by decide)))
      (hnK432TriMem (by decide) (by decide) (by decide))⟩, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_even_conj_tripleNat (k := 3) (by norm_num) (by norm_num)
    (Equiv.swap 6 9 * Equiv.swap 7 10 * Equiv.swap 8 11)
  have hσ' : (σ : Equiv.Perm (Fin 12)) * tripleNat 3 * (σ : Equiv.Perm (Fin 12))⁻¹ =
      tri 0 1 2 * tri 3 4 5 * tri 9 10 11 := hσ.trans (by decide)
  have hσY : σ * x3 * σ⁻¹ = Y := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx3, hY]
    exact hσ')
  have hcomm : Y * x3 = x3 * Y := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx3, hY]
    decide)
  have hpow : x3 ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hx3]
    decide)
  have hY1 : (Y : Equiv.Perm (Fin 12)) ≠ 1 := by
    rw [hY]
    decide
  have hY2 : (Y : Equiv.Perm (Fin 12)) ≠ (x3 : Equiv.Perm (Fin 12)) := by
    rw [hY, hx3]
    decide
  have hY3 : (Y : Equiv.Perm (Fin 12)) ≠ (x3 : Equiv.Perm (Fin 12))⁻¹ := by
    rw [hY, hx3]
    decide
  have hYnot : Y ∉ Subgroup.zpowers x3 := hnK432NotMem hpow hY1 hY2 hY3
  have hconj : iotaA σ * sJ 2 * (iotaA σ)⁻¹ = iotaA Y := by
    rw [← hz2, ← hσY, map_mul, map_mul, map_inv]
  refine ⟨iotaA σ, ?_, ?_⟩
  · rw [hconj, ← hz2, ← map_mul iotaA, ← map_mul iotaA, hcomm]
  · rw [hconj, ← hz2]
    exact hnK432IotaNotMem hYnot

theorem hnK432ListJ
    [Finite ↥JH] : ListRow ↥JH := by
  refine listRow_of_cover ({sJ 0, sJ 2} : Set ↥JH) ?_ ?_ ?_
  · intro c hc
    rcases Set.mem_insert_iff.1 hc with rfl | h
    · exact orderOf_sJ (m := 0) (by norm_num)
    · rw [Set.mem_singleton_iff.1 h]
      exact orderOf_sJ (m := 2) (by norm_num)
  · intro s hs
    exact hnK432Cover s hs
  · intro c hc
    rcases Set.mem_insert_iff.1 hc with rfl | h
    · exact hnK432WitnessS1
    · rw [Set.mem_singleton_iff.1 h]
      exact hnK432WitnessS3

theorem listRow_hn :
    ListRow NativeSporadic.HN := by
  haveI : Finite ↥JH := Finite.of_equiv _ hnEquivJ.toEquiv
  exact @ListRow.of_mulEquiv ↥JH NativeSporadic.HN _ _ Units.instGroup _ hnEquivJ.symm hnK432ListJ

theorem outerRow_hn :
    OuterRow NativeSporadic.HN :=
  outerRow_of_not_three_dvd_outer (by rw [card_outer_HN]; norm_num)

theorem row_carrier_hn :
    RowOf (NativeSporadic.Carrier .HN) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.HN) e.symm ⟨listRow_hn, outerRow_hn⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
