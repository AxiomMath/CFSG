module

public import CFSG.Quasithin.Background.A1bBasic


public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj

open CFSG.Quasithin Subgroup

variable {Q : Type} [Group Q] [Finite Q]

private lemma card_sup_mul_card_inf_of_comm_Tor5 {H K : Subgroup Q}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  let f : ↥H × ↥K →* Q :=
    MonoidHom.noncommCoprod H.subtype K.subtype
      fun a b => (commute_iff_eq (H.subtype a) (K.subtype b)).mpr (hcomm a.1 a.2 b.1 b.2)
  have hrange : f.range = H ⊔ K := by
    simp only [f]
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card ↥f.ker = Nat.card ↥(H ⊓ K) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun z => ⟨(z.1.1 : Q), z.1.1.2, ?_⟩
        invFun := fun z =>
          ⟨(⟨z.1, (Subgroup.mem_inf.mp z.2).1⟩,
              ⟨z.1⁻¹, K.inv_mem (Subgroup.mem_inf.mp z.2).2⟩), ?_⟩
        left_inv := fun z => ?_
        right_inv := fun z => ?_ }
    · have hz : (z.1.1 : Q) * (z.1.2 : Q) = 1 := by
        have h := z.2
        rw [MonoidHom.mem_ker] at h
        simp only [f, MonoidHom.noncommCoprod_apply] at h
        simpa using h
      rw [show (z.1.1 : Q) = (z.1.2 : Q)⁻¹ by rw [eq_inv_of_mul_eq_one_right hz, inv_inv]]
      exact K.inv_mem z.1.2.2
    · rw [MonoidHom.mem_ker]
      simp only [f, MonoidHom.noncommCoprod_apply]
      simp
    · apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        have hz : (z.1.1 : Q) * (z.1.2 : Q) = 1 := by
          have h := z.2
          rw [MonoidHom.mem_ker] at h
          simp only [f, MonoidHom.noncommCoprod_apply] at h
          simpa using h
        show (z.1.1 : Q)⁻¹ = (z.1.2 : Q)
        rw [eq_inv_of_mul_eq_one_right hz]
    · apply Subtype.ext
      rfl
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_prod] at hcard
  exact (mul_comm _ _).trans hcard

private lemma sup_le_normalizer_left_Tor5 {X X' : Subgroup Q}
    (hcomm : ∀ x ∈ X, ∀ y ∈ X', x * y = y * x) :
    X ⊔ X' ≤ normalizer (X : Set Q) := by
  refine sup_le le_normalizer ?_
  intro y hy
  exact Subgroup.centralizer_le_normalizer (X : Set Q)
    (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy)

theorem isSylowIn_inf_left {X X' S : Subgroup Q} (hcomm : ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (hS : IsSylowIn 2 S (X ⊔ X')) : IsSylowIn 2 (S ⊓ X) X := by
  refine hS.inf_normal (N := X) le_sup_left ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le_normalizer_left_Tor5 hcomm

theorem inf_sup_inf_eq {X X' S : Subgroup Q} (hcomm : ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (hS : IsSylowIn 2 S (X ⊔ X')) : (S ⊓ X) ⊔ (S ⊓ X') = S := by
  have hcomm' : ∀ y ∈ X', ∀ x ∈ X, y * x = x * y := fun y hy x hx => (hcomm x hx y hy).symm
  have hSX : IsSylowIn 2 (S ⊓ X) X := isSylowIn_inf_left hcomm hS
  have hSX' : IsSylowIn 2 (S ⊓ X') X' := isSylowIn_inf_left hcomm' (by rwa [sup_comm])
  have hleN : X ⊔ X' ≤ normalizer (X : Set Q) := sup_le_normalizer_left_Tor5 hcomm
  have hleN' : X ⊔ X' ≤ normalizer (X' : Set Q) := by
    rw [sup_comm]
    exact sup_le_normalizer_left_Tor5 hcomm'
  have hN : ((X ⊓ X').subgroupOf (X ⊔ X')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans le_sup_left)).mpr
      (le_trans (le_inf hleN hleN') Subgroup.inf_normalizer_le_normalizer_inf)
  have hSinf : IsSylowIn 2 (S ⊓ (X ⊓ X')) (X ⊓ X') :=
    hS.inf_normal (inf_le_left.trans le_sup_left) hN
  have hZeq : ((S ⊓ X) ⊓ (S ⊓ X') : Subgroup Q) = S ⊓ (X ⊓ X') := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hcard₁ : Nat.card ↥((S ⊓ X) ⊔ (S ⊓ X')) * Nat.card ↥(S ⊓ (X ⊓ X')) =
      Nat.card ↥(S ⊓ X) * Nat.card ↥(S ⊓ X') := by
    rw [← hZeq]
    exact card_sup_mul_card_inf_of_comm_Tor5 fun a ha b hb => hcomm a ha.2 b hb.2
  have hcard₂ : Nat.card ↥(X ⊔ X') * Nat.card ↥(X ⊓ X') = Nat.card ↥X * Nat.card ↥X' :=
    card_sup_mul_card_inf_of_comm_Tor5 hcomm
  have hexp : (Nat.card ↥(X ⊔ X')).factorization 2 + (Nat.card ↥(X ⊓ X')).factorization 2 =
      (Nat.card ↥X).factorization 2 + (Nat.card ↥X').factorization 2 := by
    have h := congrArg (fun n : ℕ => n.factorization 2) hcard₂
    simpa only [Nat.factorization_mul (Nat.card_pos (α := ↥(X ⊔ X'))).ne'
        (Nat.card_pos (α := ↥(X ⊓ X'))).ne',
      Nat.factorization_mul (Nat.card_pos (α := ↥X)).ne' (Nat.card_pos (α := ↥X')).ne',
      Finsupp.add_apply] using h
  have hTcard : Nat.card ↥((S ⊓ X) ⊔ (S ⊓ X')) = Nat.card ↥S := by
    refine Nat.mul_right_cancel (Nat.card_pos (α := ↥(S ⊓ (X ⊓ X')))) ?_
    rw [hcard₁, hSX.card_eq, hSX'.card_eq, hSinf.card_eq, hS.card_eq, ← pow_add, ← pow_add, hexp]
  exact Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (le_of_eq hTcard.symm)

theorem inf_normalizer_le_normalizer {X X' S : Subgroup Q}
    (hcomm : ∀ x ∈ X, ∀ y ∈ X', x * y = y * x) (hS : IsSylowIn 2 S (X ⊔ X')) :
    X ⊓ normalizer ((S ⊓ X : Subgroup Q) : Set Q) ≤ normalizer (S : Set Q) := by
  have hdec : (S ⊓ X) ⊔ (S ⊓ X') = S := inf_sup_inf_eq hcomm hS
  have hXnorm : X ≤ normalizer ((S ⊓ X' : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb s hs
    rw [hcomm b hb s hs.2]
    simpa using hs
  have hmain := Subgroup.inf_normalizer_le_normalizer_sup (S ⊓ X) (S ⊓ X')
  rw [hdec] at hmain
  intro b hb
  exact hmain ⟨hb.2, hXnorm hb.1⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj
