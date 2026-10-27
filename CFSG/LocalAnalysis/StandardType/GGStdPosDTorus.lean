module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CliffordAlgebra

namespace StdPosD

theorem conj_longRoot_of_smul {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    {u : spinGroup Q} {a b : K} (ha : spinAction Q u (F.vec i s) = a • F.vec i s)
    (hb : spinAction Q u (F.vec j t) = b • F.vec j t) (c : K) :
    u * F.longRoot hij s t (.ofAdd c) * u⁻¹ = F.longRoot hij s t (.ofAdd (a * b * c)) := by
  apply Subtype.ext
  have h1 : (u : CliffordAlgebra Q) * ι Q (F.vec i s) * ↑u⁻¹ = a • ι Q (F.vec i s) := by
    rw [← ι_spinAction, ha, map_smul]
  have h2 : (u : CliffordAlgebra Q) * ι Q (F.vec j t) * ↑u⁻¹ = b • ι Q (F.vec j t) := by
    rw [← ι_spinAction, hb, map_smul]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, HypFrame.coe_longRoot, HypFrame.coe_longRoot]
  calc (u : CliffordAlgebra Q) * (1 + c • (ι Q (F.vec i s) * ι Q (F.vec j t))) * ↑u⁻¹
      = 1 + c • ((u * ι Q (F.vec i s) * ↑u⁻¹) * (u * ι Q (F.vec j t) * ↑u⁻¹)) := by
        simp only [mul_add, add_mul, mul_one, coe_mul_coe_inv, mul_smul_comm, smul_mul_assoc,
          mul_assoc, coe_inv_mul_coe_mul]
    _ = _ := by rw [h1, h2, smul_mul_smul_comm, smul_smul, mul_comm c]

theorem mem_ggTorus_of_lines {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {u : spinGroup (quadPlus n K)}
    (hu : ∀ k : Fin n ⊕ Fin n, ∃ c : K,
      spinAction (quadPlus n K) u (Pi.single k 1) = c • (Pi.single k 1 : Fin n ⊕ Fin n → K)) :
    u ∈ ggTorus (plusDatum n K hn) := by
  have hne : ∀ (k : Fin n ⊕ Fin n) (a : K), spinAction (quadPlus n K) u (Pi.single k 1) =
      a • (Pi.single k 1 : Fin n ⊕ Fin n → K) → a ≠ 0 := by
    rintro k a h rfl
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h
    simpa using congrFun h k
  have hvec : ∀ (i : Fin n) (s : Bool), ∃ a : K, a ≠ 0 ∧
      spinAction (quadPlus n K) u ((plusFrame n K hn).vec i s) =
        a • (plusFrame n K hn).vec i s := by
    intro i s
    cases s
    · obtain ⟨a, ha⟩ := hu (.inr i)
      exact ⟨a, hne _ a ha, ha⟩
    · obtain ⟨a, ha⟩ := hu (.inl i)
      exact ⟨a, hne _ a ha, ha⟩
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  obtain ⟨i, j, hij, s, t, -, hR⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  obtain ⟨a, ha0, ha⟩ := hvec i s
  obtain ⟨b, hb0, hb⟩ := hvec j t
  have hconj := conj_longRoot_of_smul (plusFrame n K hn) hij s t ha hb
  change u ∈ Subgroup.normalizer (plusRootGroup n K hn γ : Set (spinGroup (quadPlus n K)))
  rw [hR, Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨.ofAdd (a * b * c.toAdd), (hconj c.toAdd).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨.ofAdd ((a * b)⁻¹ * c.toAdd), ?_⟩
    have h1 := hconj ((a * b)⁻¹ * c.toAdd)
    rw [mul_inv_cancel_left₀ (mul_ne_zero ha0 hb0)] at h1
    exact mul_left_cancel (mul_right_cancel (h1.trans hc))

end StdPosD

end CFSG.StandardType

end
