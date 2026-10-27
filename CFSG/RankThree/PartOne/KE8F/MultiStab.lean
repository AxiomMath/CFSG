module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootSpace
open CFSG.RankThree.E6 (charVal charVal_add charVal_neg charVal_smul charVal_single)
open CFSG.RankThree.PartOne.KE

section Digits

theorem digits_eq_zero : ∀ {n : ℕ} (d : Fin n → ℤ) {N : ℤ}, 0 < N → (∀ i, 2 * |d i| < N) →
    ∑ i : Fin n, N ^ (i : ℕ) * d i = 0 → ∀ i, d i = 0 := by
  intro n
  induction n with
  | zero => intro d N _ _ _ i; exact i.elim0
  | succ n ih =>
    intro d N hN hd hs
    rw [Fin.sum_univ_succ] at hs
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ] at hs
    have hs' : d 0 + N * ∑ i : Fin n, N ^ (i : ℕ) * d i.succ = 0 := by
      rw [← hs, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hdvd : N ∣ d 0 := by
      have : d 0 = -(N * ∑ i : Fin n, N ^ (i : ℕ) * d i.succ) := by linarith
      rw [this]
      exact (dvd_neg).2 (dvd_mul_right _ _)
    have h0 : d 0 = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      have := hd 0
      omega
    have hsum : ∑ i : Fin n, N ^ (i : ℕ) * d i.succ = 0 := by
      rw [h0, zero_add] at hs'
      exact (mul_eq_zero.1 hs').resolve_left hN.ne'
    have ih' := ih (fun i => d i.succ) hN (fun i => hd i.succ) hsum
    intro i
    refine Fin.cases h0 (fun j => ih' j) i

end Digits

section Stab

variable {τ : Tag} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem charVal_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℤ) (r : ι → Fin τ.rank → ℤ)
    (x : Fin τ.rank → ℤ) :
    charVal (∑ i, c i • r i) x = ∑ i, c i * charVal (r i) x := by
  simp only [charVal_int_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem iInf_dualWeylStabilizer_le_of_card
    {ι : Type*} [Finite ι] (z : ι → Fin τ.rank → ZMod p)
    (hUp : ¬ p ∣ Nat.card (⨅ i, dualWeylStabilizer (z i) : Subgroup (WeylGroup τ))) :
    (⨅ i, dualWeylStabilizer (z i)) ≤ Subgroup.closure
      {s | ∃ α, IsRoot τ α ∧ (∀ i, charVal (z i) α = 0) ∧ s = rootReflection α} := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set U : Subgroup (WeylGroup τ) := ⨅ i, dualWeylStabilizer (z i) with hU
  have : Fintype U := Fintype.ofFinite _
  have hUle : ∀ i, U ≤ dualWeylStabilizer (z i) := fun i => iInf_le _ i
  set r : ι → Fin τ.rank → ℤ := fun i => avgColumn U (intLift (z i)) with hr
  have hcard : (Fintype.card U : ZMod p) ≠ 0 := by
    intro h0
    apply hUp
    rw [Nat.card_eq_fintype_card]
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  have hcast : ∀ i x, ((charVal (r i) x : ℤ) : ZMod p) =
      (Fintype.card U : ZMod p) * charVal (z i) x := fun i x =>
    charVal_avgColumn_cast (hUle i) x
  have hinv : ∀ i, ∀ w ∈ U, ∀ x, charVal (r i) (w • x) = charVal (r i) x := fun i w hw x =>
    charVal_avgColumn_smul (intLift (z i)) hw x
  have hker : ∀ α, IsRoot τ α → ((∀ i, charVal (r i) α = 0) ↔ ∀ i, charVal (z i) α = 0) := by
    intro α hα
    constructor
    · intro h i
      have := hcast i α
      rw [h i, Int.cast_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hcard
    · intro h i
      have hmem : rootReflection α ∈ U :=
        Subgroup.mem_iInf.2 fun j => rootReflection_mem_dualWeylStabilizer ⟨hα, h j⟩
      have h1 := hinv i _ hmem α
      rw [rootReflection_smul_self hα, charVal_neg] at h1
      omega
  have hrootfin : Finite {α : Fin τ.rank → ℤ // IsRoot τ α} := (finite_setOf_isRoot τ).to_subtype
  obtain ⟨M, hM⟩ := Finite.exists_le
    (fun x : {α : Fin τ.rank → ℤ // IsRoot τ α} × ι => (charVal (r x.2) x.1.1).natAbs)
  set N : ℤ := 2 * (M : ℤ) + 1 with hN
  have hNpos : 0 < N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set r' : Fin τ.rank → ℤ := ∑ i, N ^ ((e i : Fin (Fintype.card ι)) : ℕ) • r i with hr'
  have hr'val : ∀ x, charVal r' x = ∑ i, N ^ ((e i : Fin (Fintype.card ι)) : ℕ) * charVal (r i) x :=
    fun x => charVal_sum_smul _ _ x
  have hr'inv : ∀ w ∈ U, ∀ x, charVal r' (w • x) = charVal r' x := fun w hw x => by
    rw [hr'val, hr'val]
    exact Finset.sum_congr rfl fun i _ => by rw [hinv i w hw]
  have hr'ker : ∀ α, IsRoot τ α → (charVal r' α = 0 ↔ ∀ i, charVal (z i) α = 0) := by
    intro α hα
    rw [← hker α hα]
    constructor
    · intro h
      have hsum : ∑ k : Fin (Fintype.card ι), N ^ (k : ℕ) * charVal (r (e.symm k)) α = 0 := by
        rw [← h, hr'val]
        exact Fintype.sum_equiv e.symm _ _ fun k => by simp
      have hd := digits_eq_zero (fun k => charVal (r (e.symm k)) α) hNpos (fun k => by
        have := hM (⟨α, hα⟩, e.symm k)
        simp only at this ⊢
        rw [Int.abs_eq_natAbs]
        omega) hsum
      intro i
      have := hd (e i)
      simpa using this
    · intro h
      rw [hr'val]
      exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
  intro w hw
  have hfix : w ∈ weylStabilizer τ (dualVector r') :=
    weylAct_dualVector_eq fun v => hr'inv w⁻¹ (U.inv_mem hw) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (dualVector r')] at hfix
  convert hfix using 2
  ext s
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨α, hα, h0, rfl⟩
    refine ⟨α, hα, ?_, rfl⟩
    rw [inner_ofLattice_dualVector, (hr'ker α hα).2 h0, Int.cast_zero]
  · rintro ⟨α, hα, h0, rfl⟩
    rw [inner_ofLattice_dualVector, Int.cast_eq_zero] at h0
    exact ⟨α, hα, (hr'ker α hα).1 h0, rfl⟩

theorem iInf_dualWeylStabilizer_le
    (hord : ¬ p ∣ Nat.card (WeylGroup τ)) {ι : Type*} [Finite ι] (z : ι → Fin τ.rank → ZMod p) :
    (⨅ i, dualWeylStabilizer (z i)) ≤ Subgroup.closure
      {s | ∃ α, IsRoot τ α ∧ (∀ i, charVal (z i) α = 0) ∧ s = rootReflection α} :=
  iInf_dualWeylStabilizer_le_of_card z fun h =>
    hord (h.trans (Subgroup.card_subgroup_dvd_card _))

end Stab

end CFSG.RankThree.PartOne.KE8F
