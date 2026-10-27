module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem b15_relIndex_sup_eq_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B hB) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

private theorem b15_relIndex_sup_eq_card_of_disjoint {A B : Subgroup G}
    (hdisj : B ⊓ A = ⊥) (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    B.relIndex (A ⊔ B) = Nat.card A := by
  rw [b15_relIndex_sup_eq_of_le_normalizer hB]
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [hdisj, Subgroup.card_bot, mul_one] at h1
  exact h1

private theorem b15_not_dvd_card_of_isPGroup {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hpr : p ≠ r) {I : Subgroup G} (hI : IsPGroup r ↥I) : ¬ p ∣ Nat.card I := by
  obtain ⟨n, hn⟩ := hI.exists_card_eq
  have hn' : Nat.card I = r ^ n := hn
  rw [hn']
  intro hd
  exact hpr ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
    (Nat.Prime.dvd_of_dvd_pow Fact.out hd))

theorem exists_mul_of_comm_mem_of_coprime {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {Q I X : Subgroup G} (hX : IsPGroup p ↥X) (hI : IsPGroup r ↥I) (hIQ : I ≤ Q)
    (hXI : X ≤ normalizer (I : Set G)) (hQI : Q ≤ normalizer (I : Set G))
    (hcomm : ∀ x ∈ X, ∀ q ∈ Q, ⁅x, q⁆ ∈ I) {q : G} (hq : q ∈ Q) :
    ∃ c ∈ Q ⊓ centralizer (X : Set G), ∃ i ∈ I, q = c * i := by
  classical
  let J : Subgroup G := X ⊔ I
  have hXJ : X ≤ J := le_sup_left
  have hIJ : I ≤ J := le_sup_right
  have hdisjXI : X ⊓ I = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne p r hpr X I hX hI)
  have hnotdvdI : ¬ p ∣ Nat.card I := b15_not_dvd_card_of_isPGroup hpr hI
  have hrelX : X.relIndex J = Nat.card I := by
    rw [show J = I ⊔ X from sup_comm X I]
    exact b15_relIndex_sup_eq_card_of_disjoint (A := I) (B := X) hdisjXI hXI
  have hXJ_sylow : IsSylowIn p X J :=
    ⟨hXJ, hX, by rw [hrelX]; exact hnotdvdI⟩
  set X' : Subgroup G := MulAut.conj q⁻¹ • X with hX'def
  have hX'mem : ∀ y : G, y ∈ X' ↔ ∃ x ∈ X, q⁻¹ * x * q = y := by
    intro y
    rw [hX'def, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]⟩
  have hX'le : X' ≤ J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hX'mem y).mp hy
    have hkey : q⁻¹ * x * q = x * ⁅x⁻¹, q⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [hkey]
    exact J.mul_mem (hXJ hx) (hIJ (hcomm x⁻¹ (X.inv_mem hx) q⁻¹ (Q.inv_mem hq)))
  have hX'grp : IsPGroup p ↥X' := by
    rw [hX'def]
    exact hX.of_equiv (Subgroup.equivSMul (MulAut.conj q⁻¹) X)
  have hcardX' : Nat.card X' = Nat.card X := by
    rw [hX'def]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj q⁻¹) X).toEquiv).symm
  have hrelX' : X'.relIndex J = X.relIndex J := by
    have h1 := Subgroup.relIndex_mul_card (H := X') (K := J)
    have h2 := Subgroup.relIndex_mul_card (H := X) (K := J)
    rw [inf_eq_left.mpr hX'le, hcardX'] at h1
    rw [inf_eq_left.mpr hXJ] at h2
    exact mul_right_cancel₀ Nat.card_pos.ne' (h1.trans h2.symm)
  have hX'J_sylow : IsSylowIn p X' J :=
    ⟨hX'le, hX'grp, by rw [hrelX', hrelX]; exact hnotdvdI⟩
  let S : Sylow p ↥J := hXJ_sylow.toSylow
  let T : Sylow p ↥J := hX'J_sylow.toSylow
  haveI : Finite (Sylow p ↥J) := Sylow.finite_of_finiteIndex S
  obtain ⟨j, hj⟩ := MulAction.exists_smul_eq (M := ↥J) S T
  have hcoe : (MulAut.conj j) • (X.subgroupOf J) = X'.subgroupOf J := by
    have h1 : (↑(j • S) : Subgroup ↥J) = (T : Subgroup ↥J) :=
      congrArg (fun P : Sylow p ↥J => (P : Subgroup ↥J)) hj
    rw [Sylow.coe_subgroup_smul, IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow] at h1
    exact h1
  have hconj_le : MulAut.conj (j : G) • X ≤ X' := by
    intro y hy
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem0 : (MulAut.conj j) • (⟨x, hXJ hx⟩ : ↥J) ∈
        (MulAut.conj j) • (X.subgroupOf J) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [hcoe, Subgroup.mem_subgroupOf] at hmem0
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hmem0
  have hconjX : MulAut.conj (j : G) • X = X' := by
    have hbridge : (MulAut.conj (j : G) • X).subgroupOf J = X'.subgroupOf J := by
      rw [← Subgroup.conj_smul_subgroupOf hXJ j, hcoe]
    have h2 := Subgroup.subgroupOf_inj.mp hbridge
    rwa [inf_eq_left.mpr (hconj_le.trans hX'le), inf_eq_left.mpr hX'le] at h2
  have hqj_smul : MulAut.conj (q * j : G) • X = X := by
    have h := congrArg (fun H : Subgroup G => MulAut.conj q • H) hconjX
    rw [hX'def] at h
    rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, one_smul] at h
    exact h
  have hqjN : (q * j : G) ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    rw [← SetLike.ext_iff.mp hqj_smul h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_inv_apply, mul_assoc]
  obtain ⟨i₁, hi₁, x₁, hx₁, hix⟩ := by
    have hmem : (j : G) ∈ (I : Set G) * (X : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left I X hXI]
      exact sup_comm X I ▸ j.2
    exact Set.mem_mul.mp hmem
  have hqiN : (q * i₁ : G) ∈ Subgroup.normalizer (X : Set G) := by
    have h1 : q * i₁ = (q * j) * x₁⁻¹ := by rw [← hix]; group
    rw [h1]
    exact (Subgroup.normalizer (X : Set G)).mul_mem hqjN
      ((Subgroup.normalizer (X : Set G)).inv_mem (Subgroup.le_normalizer hx₁))
  have hcQ : (q * i₁ : G) ∈ Q := Q.mul_mem hq (hIQ hi₁)
  have hcC : (q * i₁ : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcx : x * (q * i₁) = (q * i₁) * x := by
      have hcom : ⁅x, q * i₁⁆ = 1 := by
        have hmemX : ⁅x, q * i₁⁆ ∈ X := by
          have hxN : (q * i₁) * x⁻¹ * (q * i₁)⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp hqiN x⁻¹).mp (X.inv_mem hx)
          simpa only [commutatorElement_def, mul_assoc] using X.mul_mem hx hxN
        have hmemI : ⁅x, q * i₁⁆ ∈ I := hcomm x hx (q * i₁) hcQ
        have hmem : ⁅x, q * i₁⁆ ∈ X ⊓ I := ⟨hmemX, hmemI⟩
        rw [hdisjXI] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hcom
    exact hcx
  exact ⟨q * i₁, ⟨hcQ, hcC⟩, i₁⁻¹, I.inv_mem hi₁, (mul_inv_cancel_right q i₁).symm⟩

theorem le_inf_centralizer_sup_of_comm_mem {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {Q I X : Subgroup G} (hX : IsPGroup p ↥X) (hI : IsPGroup r ↥I) (hIQ : I ≤ Q)
    (hXI : X ≤ normalizer (I : Set G)) (hQI : Q ≤ normalizer (I : Set G))
    (hcomm : ∀ x ∈ X, ∀ q ∈ Q, ⁅x, q⁆ ∈ I) : Q ≤ (Q ⊓ centralizer (X : Set G)) ⊔ I := by
  intro q hq
  obtain ⟨c, hc, i, hi, rfl⟩ := exists_mul_of_comm_mem_of_coprime hpr hX hI hIQ hXI hQI hcomm hq
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hi)

end CFSG.LocalAnalysis.WeakClosure81
