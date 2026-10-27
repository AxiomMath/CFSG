module

public import CFSG.RankThree.PartOne.KE6.E6LDescent
public import CFSG.RankThree.PartOne.KD4T.Normal

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

section Scalars

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L]

@[expose] def e6SetEquiv (τ : Tag) [E6Sub τ] : Fin Tag.E6.rank ≃ e6Set τ where
  toFun k := ⟨e6Idx k, e6Idx_mem_e6Set k⟩
  invFun j := ⟨j.1.val, e6Set_lt j.2⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

omit [M27Ok τ] in
theorem e6SetEquiv_apply (k : Fin Tag.E6.rank) :
    (e6SetEquiv τ k : Fin τ.rank) = e6Idx k := rfl

theorem adj_mul_entry {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (l k : Fin n) :
    ∑ k', C.adjugate l k' * C k' k = C.det * if l = k then 1 else 0 := by
  have := congrFun (congrFun (Matrix.adjugate_mul C) l) k
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this

omit [M27Ok τ] in
theorem exists_e6Params [IsAlgClosed L] (s : Fin Tag.E6.rank → Lˣ) :
    ∃ a : e6Set τ → Lˣ, ∀ k : Fin Tag.E6.rank,
      ∏ j : e6Set τ, a j ^ τ.cartan j (e6Idx k) = s k := by
  classical
  have hd := det_cartan_pos Tag.E6
  have hroot : ∀ j, ∃ u : Lˣ, u ^ Tag.E6.cartan.det = s j := by
    intro j
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (s j : L) (n := Tag.E6.cartan.det.toNat)
      (by omega)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz
      exact (s j).ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [← Int.toNat_of_nonneg hd.le, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  choose u hu using hroot
  refine ⟨fun j => ∏ l : Fin Tag.E6.rank, u l ^ Tag.E6.cartan.adjugate l ((e6SetEquiv τ).symm j),
    fun k => ?_⟩
  rw [← Equiv.prod_comp (e6SetEquiv τ)]
  have e1 : ∀ k' : Fin Tag.E6.rank,
      (∏ l : Fin Tag.E6.rank, u l ^ Tag.E6.cartan.adjugate l ((e6SetEquiv τ).symm (e6SetEquiv τ k'))) ^
        τ.cartan (e6SetEquiv τ k') (e6Idx k) =
      ∏ l : Fin Tag.E6.rank, u l ^ (Tag.E6.cartan.adjugate l k' * Tag.E6.cartan k' k) := fun k' => by
    rw [Equiv.symm_apply_apply, ← Finset.prod_zpow, e6SetEquiv_apply, cartan_e6Idx]
    exact Finset.prod_congr rfl fun l _ => by rw [← zpow_mul]
  simp only [e1]
  rw [Finset.prod_comm]
  have e2 : ∀ l : Fin Tag.E6.rank,
      ∏ k' : Fin Tag.E6.rank, u l ^ (Tag.E6.cartan.adjugate l k' * Tag.E6.cartan k' k) =
        u l ^ (Tag.E6.cartan.det * (if l = k then 1 else 0)) := fun l => by
    rw [prod_zpow_self, adj_mul_entry]
  simp only [e2]
  rw [Finset.prod_eq_single k]
  · simpa using hu k
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [M27Ok τ] in
theorem exists_e6TorusWord_scalars [IsAlgClosed L] (s : Fin Tag.E6.rank → Lˣ) :
    ∃ T : ModGL τ L, T ∈ supportedTorus τ L (e6Set τ) ∧ ∀ (k : Fin Tag.E6.rank) (c : L),
      T * xUnit τ L (e6Idx k) c * T⁻¹ = xUnit τ L (e6Idx k) (s k * c) ∧
      T * yUnit τ L (e6Idx k) c * T⁻¹ = yUnit τ L (e6Idx k) (((s k)⁻¹ : Lˣ) * c) := by
  obtain ⟨a, ha⟩ := exists_e6Params (τ := τ) (L := L) s
  have hTs : supportedTorusHom τ L (e6Set τ) a ∈ supportedTorus τ L (e6Set τ) :=
    supportedTorusHom_mem _ _
  have hT : supportedTorusHom τ L (e6Set τ) a ∈ torusGroup τ L :=
    supportedTorus_le_torusGroup _ hTs
  refine ⟨_, hTs, fun k c => ⟨?_, ?_⟩⟩
  · rw [← pinnedX_single, ← pinnedX_single, conj_pinnedX_of_mem_torusGroup hT (isRoot_single _ _),
      torusRootChar_supportedTorusHom _ a (isRoot_single _ _)]
    simp only [pair_single_eq]
    rw [ha k]
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single,
      conj_pinnedX_of_mem_torusGroup hT (isRoot_neg_single _ _),
      torusRootChar_supportedTorusHom _ a (isRoot_neg_single _ _)]
    have hn : ∀ j : Fin τ.rank, (∑ i, τ.cartan j i *
        (-Pi.single (e6Idx k) 1 : Fin τ.rank → ℤ) i) = -τ.cartan j (e6Idx k) := fun j => by
      simp [Pi.single_apply, Finset.sum_neg_distrib]
    simp only [hn, zpow_neg, Finset.prod_inv_distrib, ha k]

end Scalars

section Normal

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L]

omit [E6Sub τ] in
theorem exists_normalized [IsAlgClosed L] [E6Sub τ] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ)
    (hπ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (e6Set τ))
    (hact : ∀ j ∈ e6Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ q n₁ : ModGL τ L, q ∈ subsystemGroup τ L (e6Set τ) ∧ n₁ ∈ monomialSubgroup τ L ∧
      n = q * n₁ ∧ ∀ j ∈ e6Set τ, ∀ c : L,
        n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c := by
  exact KD4T.exists_normalized_of_word e6Idx e6Idx_mem_e6Set (fun _ hi => exists_e6Id_eq hi)
    (fun s => by
      obtain ⟨T, hTs, hT⟩ := exists_e6TorusWord_scalars (τ := τ) (L := L) s
      exact ⟨T, supportedTorus_le_subsystemGroup _ hTs, supportedTorus_le_torusGroup _ hTs, hT⟩)
    hn hπ hπ' hu hact

end Normal

section Lang

variable {τ : Tag} [E6Sub τ] {L : Type} [Field L]

omit [E6Sub τ] in
theorem mem_normalizer_subsystemGroup_of_conj {n₁ : ModGL τ L}
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ) (hπ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ)
    (h : ∀ j ∈ e6Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
      n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) :
    n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (e6Set τ) : Set (ModGL τ L)) := by
  exact KD4T.mem_normalizer_subsystemGroup_of_conj hπ hπ' h

theorem exists_conj_twistedFixed [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ)
    (hπ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (e6Set τ))
    (hact : ∀ j ∈ e6Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ n₁ h : ModGL τ L, n₁ ∈ monomialSubgroup τ L ∧ h ∈ subsystemGroup τ L (e6Set τ) ∧
      (∀ j ∈ e6Set τ, ∀ c : L, n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c) ∧
      ∀ g : ModGL τ L,
        n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
            h * g * h⁻¹ := by
  exact KD4T.exists_conj_twistedFixed_of_word e6Idx e6Idx_mem_e6Set
    (fun _ hi => exists_e6Id_eq hi) (fun s => by
      obtain ⟨T, hTs, hT⟩ := exists_e6TorusWord_scalars (τ := τ) (L := L) s
      exact ⟨T, supportedTorus_le_subsystemGroup _ hTs, supportedTorus_le_torusGroup _ hTs, hT⟩)
    hf hn hπ hπ' hu hact

end Lang

end CFSG.RankThree.PartOne.KE6
