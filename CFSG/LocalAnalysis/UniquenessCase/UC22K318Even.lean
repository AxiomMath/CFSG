module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Two
public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Flag
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87EngCC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.RepresentationTheory CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.RankThree.SubgroupLists (IsIrreducibleOn isIrreducibleOn_iff)
open scoped Matrix commutatorElement

variable {q : ℕ} [Fact q.Prime]

theorem card_quot_center_le_sixteen (hq2 : q ≠ 2) {N : Type} [Group N] [Finite N]
    (ι : N →* GL (Fin 4) (ZMod q))
    (hneg : ∀ t : N, t ∉ center N → ∃ s : N, ι (s * t * s⁻¹) = -ι t) :
    Nat.card (N ⧸ center N) ≤ 16 := by
  classical
  have hq : q.Prime := Fact.out
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 q).1 h0'))
  have h4 : ((4 : ℕ) : ZMod q) ≠ 0 := by
    intro h0
    have h22 : q ∣ 2 ^ 2 := (ZMod.natCast_eq_zero_iff 4 q).1 h0
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h22))
  have htr : ∀ t : N, t ∉ center N →
      Matrix.trace ((ι t : GL (Fin 4) (ZMod q)) : Matrix (Fin 4) (Fin 4) (ZMod q)) = 0 := by
    intro t ht
    obtain ⟨s, hs⟩ := hneg t ht
    have hconj : Matrix.trace ((ι (s * t * s⁻¹) : GL (Fin 4) (ZMod q)) :
        Matrix (Fin 4) (Fin 4) (ZMod q)) =
        Matrix.trace ((ι t : GL (Fin 4) (ZMod q)) : Matrix (Fin 4) (Fin 4) (ZMod q)) := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle,
        Units.inv_mul, one_mul]
    rw [hs, Units.val_neg, Matrix.trace_neg] at hconj
    have h2t : (2 : ZMod q) *
        Matrix.trace ((ι t : GL (Fin 4) (ZMod q)) : Matrix (Fin 4) (Fin 4) (ZMod q)) = 0 := by
      rw [two_mul]
      nth_rewrite 1 [← hconj]
      exact neg_add_cancel _
    exact (mul_eq_zero.1 h2t).resolve_left h2
  have : Fintype (N ⧸ center N) := Fintype.ofFinite _
  obtain ⟨r, hr⟩ := (QuotientGroup.mk_surjective (s := center N)).hasRightInverse
  obtain ⟨v, hv⟩ : ∃ v : N ⧸ center N → Matrix (Fin 4) (Fin 4) (ZMod q),
      ∀ a, v a = ((ι (r a) : GL (Fin 4) (ZMod q)) : Matrix (Fin 4) (Fin 4) (ZMod q)) :=
    ⟨_, fun _ => rfl⟩
  have hli : LinearIndependent (ZMod q) v := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod q) => Matrix.trace
      (M * (((ι (r j))⁻¹ : GL (Fin 4) (ZMod q)) : Matrix (Fin 4) (Fin 4) (ZMod q)))) hg
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      zero_mul, Matrix.trace_zero] at h
    rw [Finset.sum_eq_single j] at h
    · rw [hv j, Units.mul_inv, Matrix.trace_one, Fintype.card_fin] at h
      exact (mul_eq_zero.1 h).resolve_right h4
    · intro i _ hij
      have hnc : r i * (r j)⁻¹ ∉ center N := by
        intro hc
        apply hij
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          mul_inv_eq_one] at hc
        exact (hr i).symm.trans (hc.trans (hr j))
      have h0 := htr _ hnc
      rw [map_mul, map_inv, Units.val_mul] at h0
      rw [hv i, h0, mul_zero]
    · intro hj'
      exact absurd hj hj'
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

theorem le_center_of_normal_abelian_two (hq2 : q ≠ 2) {P : Subgroup (GL (Fin 4) (ZMod q))}
    [Group.IsPerfect P] (A : Subgroup P) (hA : A.Normal) (hA2 : IsPGroup 2 A)
    (hAc : IsMulCommutative A) : A ≤ center P := by
  have hq : q.Prime := Fact.out
  have hZ : ∀ x ∈ A.map P.subtype, ∀ y ∈ A.map P.subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (congrArg Subtype.val (hAc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hcop : Nat.Coprime (Nat.card (A.map P.subtype)) (ringChar (ZMod q)) := by
    obtain ⟨k, hk⟩ := (hA2.map P.subtype).exists_card_eq
    rw [hk, ZMod.ringChar_zmod_n]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hEN : ∀ e ∈ P, ∀ z ∈ A.map P.subtype, e * z * e⁻¹ ∈ A.map P.subtype := by
    rintro e he _ ⟨a, ha, rfl⟩
    exact ⟨⟨e, he⟩ * a * ⟨e, he⟩⁻¹, hA.conj_mem a ha _, rfl⟩
  have hcen := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.perfect_centralizes_coprime_abelian
    (le_of_eq (Fintype.card_fin 4)) (A.map P.subtype) P hZ hcop inferInstance hEN
  intro a ha
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (hcen g g.2 a ⟨a, ha, rfl⟩)

theorem eq_of_central_involutions {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    {P : Subgroup (GL σ K)} (hirr : IsIrreducibleOn P) :
    ∀ s ∈ center P, ∀ t ∈ center P, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s = t := by
  have key : ∀ s ∈ center P, s * s = 1 → s ≠ 1 → (s : GL σ K) = -1 := fun s hs hss hs1 =>
    eq_neg_one_of_commute hirr (fun g hg => congrArg Subtype.val (mem_center_iff.mp hs ⟨g, hg⟩))
      (congrArg Subtype.val hss) (fun h => hs1 (Subtype.ext h))
  intro s hs t ht hss htt hs1 ht1
  exact Subtype.ext ((key s hs hss hs1).trans (key t ht htt ht1).symm)

theorem alt_of_twoSubgroup (hq2 : q ≠ 2) {P : Subgroup (GL (Fin 4) (ZMod q))} [Group.IsPerfect P]
    (hirr : IsIrreducibleOn P) {R : Subgroup P} [R.Normal] (hRs : Group.IsSolvable R)
    (hs : IsSimpleGroup (P ⧸ R)) {T : Subgroup P} [T.Normal] (hT2 : IsPGroup 2 T)
    (hTZ : ¬ T ≤ center P) :
    Nonempty (P ⧸ R ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (P ⧸ R ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨z, h, hZX, w, hw1, hcard⟩ := exists_commData hT2 hTZ
    (fun A hA hA2 hAc => le_center_of_normal_abelian_two hq2 A hA hA2 hAc)
    (eq_of_central_involutions hirr)
  have hz : ((z : P) : GL (Fin 4) (ZMod q)) = -1 := by
    have hzc := hZX z h.mem_center
    exact eq_neg_one_of_commute hirr
      (fun g hg => congrArg Subtype.val (mem_center_iff.mp hzc ⟨g, hg⟩))
      (congrArg (fun x : T => ((x : P) : GL (Fin 4) (ZMod q))) h.sq_eq_one)
      (fun h1 => h.ne_one (Subtype.ext (Subtype.ext h1)))
  have hneg : ∀ t : T, t ∉ center T → ∃ s : T,
      (P.subtype.comp T.subtype) (s * t * s⁻¹) = -(P.subtype.comp T.subtype) t := by
    intro t ht
    rw [mem_center_iff] at ht
    push_neg at ht
    obtain ⟨s, hst⟩ := ht
    refine ⟨s, ?_⟩
    have hc : ⁅s, t⁆ = z := by
      rcases h.mem_zpowers_iff.mp (h.comm_mem s t) with h1 | h1
      · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hst
      · exact h1
    have he : s * t * s⁻¹ = z * t := by
      rw [← hc, commutatorElement_def]
      group
    rw [he, map_mul]
    change ((z : P) : GL (Fin 4) (ZMod q)) * ((t : P) : GL (Fin 4) (ZMod q)) =
      -((t : P) : GL (Fin 4) (ZMod q))
    rw [hz, neg_one_mul]
  have h16 := card_quot_center_le_sixteen hq2 (P.subtype.comp T.subtype) hneg
  rw [hcard] at h16
  have hw : w ≤ 2 := by
    by_contra hw
    have h64 : 2 ^ 6 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := h64.trans h16
    norm_num at this
  refine alt_of_commData hRs hs hTZ hZX h ?_
  rw [hcard]
  interval_cases w <;> norm_num

theorem alt_of_not_twoCore_le (hq2 : q ≠ 2) {P : Subgroup (GL (Fin 4) (ZMod q))}
    [Group.IsPerfect P] (hirr : IsIrreducibleMatrixRep P.subtype) (R : Subgroup P) [R.Normal]
    (hRs : Group.IsSolvable R) (hs : IsSimpleGroup (P ⧸ R))
    (h2 : ¬ (CFSG.pCore 2 R).map R.subtype ≤ center P) :
    Nonempty (P ⧸ R ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (P ⧸ R ≃* alternatingGroup (Fin 6)) :=
  alt_of_twoSubgroup hq2 (isIrreducibleOn_iff.2 hirr) hRs hs
    ((CFSG.pCore_isPGroup (p := 2) (G := R)).map R.subtype) h2

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
