module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTorusWeight
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpLabelOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums
import CFSG.Quasithin.Background.SmithB45U3Class

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis

private theorem spLB_corootChar_mul {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) (i : Fin n) (u v : Kˣ) :
    χ (corootSp i (u * v)) = χ (corootSp i u) * χ (corootSp i v) := by
  rw [map_mul]
  exact ht.chi_mul (corootSp_mem_H i u) (corootSp_mem_H i v)

private theorem spLB_corootChar_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) (i : Fin n) :
    χ (corootSp i 1) = 1 := by
  rw [map_one]
  exact ht.chi_one

private theorem spLB_card_units (K : Type) [Field K] [Finite K] : Nat.card Kˣ = Nat.card K - 1 :=
  Nat.card_units K

private theorem spLB_two_le_card (K : Type) [Field K] [Finite K] [CharP K 2] :
    2 ≤ Nat.card K :=
  Nat.succ_le_of_lt (Finite.one_lt_card (α := K))

private theorem spLB_pow_card_sub_one_eq_one {K : Type} [Field K] [Finite K] (u : Kˣ) :
    (u : K) ^ (Nat.card K - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero

private theorem spLB_algebraMap_pow_card_sub_one_eq_one {K k : Type} [Field K] [Finite K]
    [Field k] [Algebra K k] (u : Kˣ) :
    algebraMap K k (u : K) ^ (Nat.card K - 1) = 1 := by
  rw [← map_pow, spLB_pow_card_sub_one_eq_one u, map_one]

private theorem spLB_d'Scalar_eq_dScalar {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {χ : StatedSp n K → k} (i : Fin n) :
    (spCurtisDatum n K).d'Scalar χ i = (spCurtisDatum n K).dScalar χ i := by
  have hres := CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
    (D := rootDatum n K) (n := weylRep n K) (H := torus n K)
    (isCTGroupDatum n K) (steinbergExtras n K) CFSG.StandardType.GGRootSp.bruhatExtras 2
    (fun _ hγ => CFSG.StandardType.GGRootSp.isPGroup_rootGroup hγ) χ i
  simpa only [spCurtisDatum] using hres

private theorem spLB_dScalar_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {χ : StatedSp n K → k}
    (hχ : ∀ a ∈ (spCurtisDatum n K).H, ∀ b ∈ (spCurtisDatum n K).H, χ (a * b) = χ a * χ b)
    (i : Fin n) (h : ∃ u : Kˣ, χ (corootSp i u) ≠ 1) :
    (spCurtisDatum n K).dScalar χ i = 0 := by
  classical
  obtain ⟨u, hu⟩ := h
  have hχ' : ∀ a ∈ ⨆ j, torus n K j, ∀ b ∈ ⨆ j, torus n K j, χ (a * b) = χ a * χ b :=
    fun a ha b hb => hχ a ha b hb
  have ht_mem : corootSp i u ∈ ⨆ j, torus n K j := by
    rw [← spCurtisDatum_H]
    exact corootSp_mem_H i u
  have hconj : (weylRep n K i)⁻¹ * (corootSp i u)⁻¹ * weylRep n K i = corootSp i u := by
    have h := weylRep_conj_corootSp i u
    rw [map_inv] at h
    rw [← h]
    group
  have hχt : χ (corootSp i u) *
      χ ((weylRep n K i)⁻¹ * (corootSp i u)⁻¹ * weylRep n K i) ≠ 1 := by
    rw [hconj, ← sq]
    exact sq_ne_one_iff.mpr ⟨hu, by rwa [CharTwo.neg_eq]⟩
  have hres := CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_zero_of_conj
    (D := rootDatum n K) (n := weylRep n K) (H := torus n K)
    (isCTGroupDatum n K) (steinbergExtras n K) CFSG.StandardType.GGRootSp.bruhatExtras 2
    (fun _ hγ => CFSG.StandardType.GGRootSp.isPGroup_rootGroup hγ)
    χ hχ' i ht_mem hχt
  simpa only [spCurtisDatum] using hres

private theorem spLB_dScalar_eq_neg_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {χ : StatedSp n K → k}
    (i : Fin n) (h : ∀ u : Kˣ, χ (corootSp i u) = 1) :
    (spCurtisDatum n K).dScalar χ i = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hχi : ∀ x ∈ torus n K i, χ x = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_torus_iff.mp hx
    rw [hc]
    exact h c
  have hres := CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_neg_one
    (D := rootDatum n K) (n := weylRep n K) (H := torus n K)
    (isCTGroupDatum n K) (steinbergExtras n K) CFSG.StandardType.GGRootSp.bruhatExtras 2
    (fun _ hγ => CFSG.StandardType.GGRootSp.isPGroup_rootGroup hγ)
    χ i hχi
  simpa only [spCurtisDatum] using hres

private theorem spLB_label_nontrivial {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) (i : Fin n)
    (h : ∃ u : Kˣ, χ (corootSp i u) ≠ 1) :
    ∃ aᵢ : ℕ, aᵢ < Nat.card K ∧
      (0 < aᵢ ↔ μ i = (spCurtisDatum n K).dScalar χ i) ∧
      (aᵢ + 1 < Nat.card K → μ i = 0) ∧
      ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ aᵢ := by
  obtain ⟨u₀, hu₀⟩ := h
  obtain ⟨e, he_lt, he_val⟩ := CFSG.Quasithin.B45U3.exists_exponent k
    (fun u : Kˣ => χ (corootSp i u)) (spLB_corootChar_mul ht i) (spLB_corootChar_one ht i)
  have hd : (spCurtisDatum n K).dScalar χ i = 0 :=
    spLB_dScalar_eq_zero (fun a ha b hb => ht.chi_mul ha hb) i ⟨u₀, hu₀⟩
  have hμ : μ i = (spCurtisDatum n K).dScalar χ i := by
    rcases ht.mu_eq i with h0 | h1
    · rw [h0, hd]
    · rw [h1, spLB_d'Scalar_eq_dScalar i, hd]
  have he0 : e ≠ 0 := by
    intro h0
    exact hu₀ (by rw [he_val u₀, h0, pow_zero])
  rw [spLB_card_units K] at he_lt
  have hK2 : 2 ≤ Nat.card K := spLB_two_le_card K
  refine ⟨e, by omega, ?_, ?_, he_val⟩
  · constructor
    · intro _; exact hμ
    · intro _; exact Nat.pos_of_ne_zero he0
  · intro _; rw [hμ, hd]

private theorem spLB_label_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) (i : Fin n)
    (h : ∀ u : Kˣ, χ (corootSp i u) = 1) :
    ∃ aᵢ : ℕ, aᵢ < Nat.card K ∧
      (0 < aᵢ ↔ μ i = (spCurtisDatum n K).dScalar χ i) ∧
      (aᵢ + 1 < Nat.card K → μ i = 0) ∧
      ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ aᵢ := by
  have hK2 : 2 ≤ Nat.card K := spLB_two_le_card K
  have hd : (spCurtisDatum n K).dScalar χ i = -1 := spLB_dScalar_eq_neg_one i h
  have hd1 : (spCurtisDatum n K).dScalar χ i = 1 := by rw [hd, CharTwo.neg_eq]
  have hμ : μ i = 0 ∨ μ i = 1 := by
    rcases ht.mu_eq i with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by rw [h1, spLB_d'Scalar_eq_dScalar i, hd1])
  rcases hμ with hμ0 | hμ1
  · refine ⟨0, by omega, ?_, ?_, ?_⟩
    · constructor
      · intro hlt; exact absurd hlt (lt_irrefl 0)
      · intro heq; rw [hμ0, hd1] at heq; exact (zero_ne_one heq).elim
    · intro _; exact hμ0
    · intro u; rw [pow_zero]; exact h u
  · refine ⟨Nat.card K - 1, by omega, ?_, ?_, ?_⟩
    · constructor
      · intro _; rw [hμ1, hd1]
      · intro _; omega
    · intro hlt; omega
    · intro u
      rw [h u, spLB_algebraMap_pow_card_sub_one_eq_one u]

private theorem spLB_exists_label_at {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) (i : Fin n) :
    ∃ aᵢ : ℕ, aᵢ < Nat.card K ∧
      (0 < aᵢ ↔ μ i = (spCurtisDatum n K).dScalar χ i) ∧
      (aᵢ + 1 < Nat.card K → μ i = 0) ∧
      ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ aᵢ := by
  by_cases h : ∃ u : Kˣ, χ (corootSp i u) ≠ 1
  · exact spLB_label_nontrivial ht i h
  · push Not at h
    exact spLB_label_trivial ht i h

theorem exists_spLabel {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k]
    [CharP k 2] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) :
    ∃ a : Fin n → ℕ, (∀ i, a i < Nat.card K) ∧
      (∀ i, 0 < a i ↔ μ i = (spCurtisDatum n K).dScalar χ i) ∧
      (∀ i, a i + 1 < Nat.card K → μ i = 0) ∧
      ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i := by
  classical
  have hexp : ∀ i : Fin n, ∃ aᵢ : ℕ, aᵢ < Nat.card K ∧
      (0 < aᵢ ↔ μ i = (spCurtisDatum n K).dScalar χ i) ∧
      (aᵢ + 1 < Nat.card K → μ i = 0) ∧
      ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ aᵢ :=
    fun i => spLB_exists_label_at ht i
  choose a ha_lt ha_iff ha_zero ha_val using hexp
  exact ⟨a, ha_lt, ha_iff, ha_zero, ha_val⟩

private theorem spLB_spTorusChar_mulSingle {K k : Type} [Field K] [Field k] (ι : K →+* k)
    {n : ℕ} (e : Fin n → ℤ) (j : Fin n) (c : Kˣ) :
    ((spTorusChar ι e (Pi.mulSingle j c) : kˣ) : k) = ι (c : K) ^ e j := by
  rw [spTorusChar_apply]
  rw [Finset.prod_eq_single_of_mem j (Finset.mem_univ j) (fun b _ hbj => by
    rw [Pi.mulSingle_eq_of_ne hbj]; simp)]
  rw [Pi.mulSingle_eq_same]

private theorem spLB_spLabelVec_succ {n : ℕ} (a : Fin n → ℕ) (i : Fin n)
    (h : i.val + 1 < n) :
    spLabelVec a i = (a i : ℤ) + spLabelVec a ⟨i.val + 1, h⟩ := by
  rw [spLabelVec, spLabelVec]
  have hset : Finset.univ.filter (fun k : Fin n => i ≤ k) =
      insert i (Finset.univ.filter (fun k : Fin n => (⟨i.val + 1, h⟩ : Fin n) ≤ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rw [Fin.le_iff_val_le_val] at hk
      rcases Nat.eq_or_lt_of_le hk with hk' | hk'
      · exact Or.inl (Fin.ext hk').symm
      · exact Or.inr (by
          rw [Fin.le_iff_val_le_val]
          change i.val + 1 ≤ k.val
          omega)
    · rintro (rfl | hk)
      · exact le_rfl
      · rw [Fin.le_iff_val_le_val] at hk ⊢
        change i.val + 1 ≤ k.val at hk
        omega
  rw [hset, Finset.sum_insert]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.le_iff_val_le_val]
    change ¬ (i.val + 1 ≤ i.val)
    omega

private theorem spLB_spLabelVec_last {n : ℕ} (a : Fin n → ℕ) (i : Fin n)
    (h : i.val + 1 = n) : spLabelVec a i = (a i : ℤ) := by
  rw [spLabelVec]
  have hset : Finset.univ.filter (fun k : Fin n => i ≤ k) = {i} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      rw [Fin.le_iff_val_le_val] at hk
      exact Fin.ext (by omega)
    · rintro rfl
      exact le_rfl
  rw [hset, Finset.sum_singleton]

private theorem spLB_spTorusChar_corootVec {K k : Type} [Field K] [Field k] [Algebra K k]
    {n : ℕ} {a : Fin n → ℕ} (i : Fin n) (c : Kˣ) :
    ((spTorusChar (algebraMap K k) (spLabelVec a) (corootVec n K i c) : kˣ) : k) =
      algebraMap K k (c : K) ^ a i := by
  rw [← zpow_natCast (algebraMap K k (c : K)) (a i)]
  rw [corootVec_eq_mul, map_mul, Units.val_mul]
  by_cases h : i.val + 1 < n
  · rw [dif_pos h,
      spLB_spTorusChar_mulSingle (algebraMap K k) (spLabelVec a) i c,
      spLB_spTorusChar_mulSingle (algebraMap K k) (spLabelVec a) ⟨i.val + 1, h⟩ c⁻¹]
    have hx : algebraMap K k (c : K) ≠ 0 := by
      intro h0
      exact c.ne_zero ((algebraMap K k).injective (by rw [h0, map_zero]))
    rw [show algebraMap K k ((c⁻¹ : Kˣ) : K) = (algebraMap K k (c : K))⁻¹ by
      rw [Units.val_inv_eq_inv_val, map_inv₀]]
    rw [inv_zpow', ← zpow_add₀ hx]
    congr 1
    have := spLB_spLabelVec_succ a i h
    omega
  · rw [dif_neg h, map_one, Units.val_one, mul_one,
      spLB_spTorusChar_mulSingle (algebraMap K k) (spLabelVec a) i c]
    rw [spLB_spLabelVec_last a i (by have := i.isLt; omega)]

theorem chi_diagHom_eq_spTorusChar {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] [Algebra K k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {a : Fin n → ℕ}
    (ha : ∀ i (u : Kˣ), χ (corootSp i u) = algebraMap K k (u : K) ^ a i) (t : Fin n → Kˣ) :
    χ (diagHom n K t) = ((spTorusChar (algebraMap K k) (spLabelVec a) t : kˣ) : k) := by
  let F : (Fin n → Kˣ) →* k :=
    { toFun := fun s => χ (diagHom n K s)
      map_one' := by rw [map_one]; exact ht.chi_one
      map_mul' := fun s t => by
        rw [map_mul]
        exact ht.chi_mul (diagHom_mem_spCurtisDatum_H s) (diagHom_mem_spCurtisDatum_H t) }
  let G : (Fin n → Kˣ) →* k :=
    { toFun := fun s => ((spTorusChar (algebraMap K k) (spLabelVec a) s : kˣ) : k)
      map_one' := by rw [map_one, Units.val_one]
      map_mul' := fun s t => by rw [map_mul, Units.val_mul] }
  have hcoroot : ∀ (i : Fin n) (c : Kˣ), F (corootVec n K i c) = G (corootVec n K i c) := by
    intro i c
    have hF : F (corootVec n K i c) = algebraMap K k (c : K) ^ a i := by
      change χ (diagHom n K (corootVec n K i c)) = algebraMap K k (c : K) ^ a i
      rw [← corootSp_apply i c]
      exact ha i c
    have hG : G (corootVec n K i c) = algebraMap K k (c : K) ^ a i := by
      change ((spTorusChar (algebraMap K k) (spLabelVec a) (corootVec n K i c) : kˣ) : k) =
        algebraMap K k (c : K) ^ a i
      exact spLB_spTorusChar_corootVec i c
    rw [hF, hG]
  calc χ (diagHom n K t) = F t := rfl
    _ = F (∏ i, corootVec n K i (prefixProd i t)) := by rw [prod_corootVec_prefixProd]
    _ = ∏ i, F (corootVec n K i (prefixProd i t)) := map_prod F _ _
    _ = ∏ i, G (corootVec n K i (prefixProd i t)) :=
        Finset.prod_congr rfl fun i _ => hcoroot i (prefixProd i t)
    _ = G (∏ i, corootVec n K i (prefixProd i t)) := (map_prod G _ _).symm
    _ = G t := by rw [prod_corootVec_prefixProd]
    _ = ((spTorusChar (algebraMap K k) (spLabelVec a) t : kˣ) : k) := rfl

end CFSG.LocalAnalysis.WeakClosure81
