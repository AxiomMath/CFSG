module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

private theorem b15_W15ElevenSeven_conjSubgroup_eq_of_isSylowIn {p : ℕ} [Fact p.Prime]
    {A B H : Subgroup G} (hA : IsSylowIn p A H) (hB : IsSylowIn p B H) :
    ∃ h ∈ H, conjSubgroup A h⁻¹ = B := by
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (↥H) hA.toSylow hB.toSylow
  refine ⟨(q : G), q.2, ?_⟩
  have hq' : MulAut.conj q • (A.subgroupOf H) = B.subgroupOf H := by
    have h := congrArg (fun P : Sylow p ↥H => (P : Subgroup ↥H)) hq
    simpa [Sylow.coe_subgroup_smul, IsSylowIn.coe_toSylow] using h
  have hq'' : (MulAut.conj (q : G) • A).subgroupOf H = B.subgroupOf H := by
    rw [← Subgroup.conj_smul_subgroupOf hA.le q]
    exact hq'
  have hmap : MulAut.conj (q : G) • A = B := by
    have h := congrArg (Subgroup.map H.subtype) hq''
    rwa [Subgroup.map_subgroupOf_eq_of_le (Subgroup.conj_smul_le_of_le hA.le q),
      Subgroup.map_subgroupOf_eq_of_le hB.le] at h
  rw [← hmap]
  ext x
  rw [mem_conjSubgroup_iff]
  simp only [inv_inv]
  constructor
  · intro hx
    have h := Subgroup.smul_mem_pointwise_smul ((q : G)⁻¹ * x * (q : G))
      (MulAut.conj (q : G)) A hx
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h
  · intro hx
    rw [Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj (q : G)) A] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rw [← hxs]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs

theorem mem_qSub15_of_commutator_mem
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) {t : G}
    (ht : t ∈ tSub15 M V₀ V U P) (hK : ∀ k ∈ kHull15 V₀ H, ⁅k, t⁆ ∈ iHull15 V₀ U H) :
    t ∈ qSub15 M V₀ V U H P := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIN : H ≤ normalizer (iHull15 V₀ U H : Set G) :=
    Hyp1510.le_normalizer_iHull15 V₀ U H
  have hKH : kHull15 V₀ H ≤ H := c.hyp.kHull15_le
  have hXNI : X ≤ normalizer (iHull15 V₀ U H : Set G) :=
    hX.le_kHull15.trans (hKH.trans hIN)
  have hYQ : conjSubgroup X t⁻¹ ≤ Q₀ := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    simp only [inv_inv] at hy
    have hcomm : ⁅(t⁻¹ * y * t)⁻¹, t⁆ ∈ iHull15 V₀ U H :=
      hK _ (hX.le_kHull15 (X.inv_mem hy))
    have hy_eq : y = (t⁻¹ * y * t) * ⁅(t⁻¹ * y * t)⁻¹, t⁆ := by
      rw [commutatorElement_def]
      group
    rw [hy_eq, ← hX.sup_eq]
    exact Subgroup.mul_mem_sup hy hcomm
  have hXQ' : IsSylowIn p X Q₀ := by
    refine ⟨hX.le, hX.isPGroup, ?_⟩
    intro hdvd
    exact hX.sylow.not_dvd_relIndex (by
      rw [← Subgroup.relIndex_mul_relIndex X Q₀ (kHull15 V₀ H) hX.le c.odd.le_kHull,
        c.relIndex_Q₀_kHull15]
      exact dvd_mul_of_dvd_left hdvd 2)
  have hYcard : Nat.card (conjSubgroup X t⁻¹) = Nat.card X := by
    have h := Subgroup.card_map_of_injective (K := X) (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective
    simpa [conjSubgroup] using h
  have hYQ' : IsSylowIn p (conjSubgroup X t⁻¹) Q₀ :=
    isSylowIn_of_card_eq hYQ (by rw [hYcard, hXQ'.card_eq])
  obtain ⟨q, hqQ, hqconj⟩ := b15_W15ElevenSeven_conjSubgroup_eq_of_isSylowIn hXQ' hYQ'
  have hqIX : q ∈ (iHull15 V₀ U H ⊔ X : Subgroup G) := by
    rw [sup_comm, hX.sup_eq]
    exact hqQ
  have hIX : (↑(iHull15 V₀ U H ⊔ X) : Set G) = iHull15 V₀ U H * X :=
    Subgroup.coe_mul_of_right_le_normalizer_left (iHull15 V₀ U H) X hXNI
  have hqmul : q ∈ (iHull15 V₀ U H : Set G) * (X : Set G) := by
    rw [← hIX]
    exact hqIX
  obtain ⟨i, hi, x', hx', hqix⟩ := Set.mem_mul.1 hqmul
  let t' : G := i⁻¹ * t
  have ht'T : t' ∈ tSub15 M V₀ V U P :=
    (tSub15 M V₀ V U P).mul_mem
      ((tSub15 M V₀ V U P).inv_mem (c.iHull15_le_tSub15 hi)) ht
  have hu : q⁻¹ * t ∈ normalizer (X : Set G) := by
    have h1 : conjSubgroup X (q⁻¹ * t) = X := by
      have h := congrArg (fun S : Subgroup G => conjSubgroup S t) hqconj
      rwa [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel,
        conjSubgroup_one] at h
    exact conjSubgroup_eq_iff_mem_normalizer.1 h1
  have ht'norm : t' ∈ normalizer (X : Set G) := by
    have ht'eq : t' = x' * (q⁻¹ * t) := by
      rw [show q = i * x' from hqix.symm]
      show i⁻¹ * t = x' * ((i * x')⁻¹ * t)
      group
    rw [ht'eq]
    exact (normalizer (X : Set G)).mul_mem (X.le_normalizer hx') hu
  have hK' : ∀ k ∈ kHull15 V₀ H, ⁅k, t'⁆ ∈ iHull15 V₀ U H := by
    intro k hk
    have hkI : k * i⁻¹ * k⁻¹ ∈ iHull15 V₀ U H :=
      (Subgroup.mem_normalizer_iff.1 (hIN (hKH hk)) i⁻¹).1 ((iHull15 V₀ U H).inv_mem hi)
    have hid : ⁅k, t'⁆ = (k * i⁻¹ * k⁻¹) * ⁅k, t⁆ * i := by
      show ⁅k, i⁻¹ * t⁆ = (k * i⁻¹ * k⁻¹) * ⁅k, t⁆ * i
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hid]
    exact (iHull15 V₀ U H).mul_mem ((iHull15 V₀ U H).mul_mem hkI (hK k hk)) hi
  have ht'cent : t' ∈ centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcomm_mem : ⁅x, t'⁆ ∈ X := by
      have hxt : t' * x⁻¹ * t'⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 ht'norm x⁻¹).1 (X.inv_mem hx)
      rw [commutatorElement_def]
      simpa only [mul_assoc] using X.mul_mem hx hxt
    have hcommI : ⁅x, t'⁆ ∈ iHull15 V₀ U H := hK' x (hX.le_kHull15 hx)
    have hbot : ⁅x, t'⁆ ∈ X ⊓ iHull15 V₀ U H := ⟨hcomm_mem, hcommI⟩
    rw [hX.inf_eq] at hbot
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.1 hbot)
  have ht'C : t' ∈ cSub15 M V₀ V U H P := hX.tSub15_inf_centralizer_le c ⟨ht'T, ht'cent⟩
  have ht_eq : t = i * t' := by
    show t = i * (i⁻¹ * t)
    group
  rw [ht_eq, c.qSub15_eq_sup hX]
  exact Subgroup.mul_mem_sup hi ht'C

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
