module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
import Mathlib.GroupTheory.FiniteAbelian.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 1
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped IsMulCommutative

universe u

private theorem lemma1_finite_A
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) (A : Subgroup P) :
    Finite A := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  infer_instance

private theorem lemma1_involutions_of_A_transitive
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} {x y : A} (hx : IsInvolution x) (hy : IsInvolution y) :
    ∃ k : X, (y : P) = k • (x : P) := by
  apply hXtrans x
  · exact ⟨fun h => hx.ne_one (Subtype.ext h), by
      simpa using congrArg Subtype.val hx.sq_eq_one⟩
  · exact ⟨fun h => hy.ne_one (Subtype.ext h), by
      simpa using congrArg Subtype.val hy.sq_eq_one⟩

private theorem lemma1_abelian_two_group_decomposition
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) (hA_abelian : IsMulCommutative A) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ),
      (∀ i, 0 < e i) ∧
        Nonempty (A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e i)))) := by
  letI : Finite A := inferInstance
  letI : IsMulCommutative A := hA_abelian
  letI : CommGroup A := IsMulCommutative.instCommGroup
  obtain ⟨ι, hι, n, hn, ⟨f⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI : Fintype ι := hι
  obtain ⟨m, hm⟩ := hP.to_subgroup A |>.exists_card_eq
  have hcard : Nat.card A = ∏ i, n i := by
    rw [Nat.card_congr f.toEquiv, Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod (n i))
  have hpow : ∀ i, ∃ k ≤ m, n i = 2 ^ k := by
    intro i
    apply (Nat.dvd_prime_pow Nat.prime_two).mp
    rw [← hm, hcard]
    exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  choose e he_le heq using hpow
  have he_pos : ∀ i, 0 < e i := by
    intro i
    apply Nat.pos_of_ne_zero
    intro hei
    have hni : n i = 1 := by simp [heq i, hei]
    exact (ne_of_gt (hn i)) hni
  have hn_eq : n = fun i => 2 ^ e i := funext heq
  subst n
  exact ⟨ι, hι, e, he_pos, ⟨f⟩⟩

private def lemma1_invariantMulEquiv
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {A : Subgroup P} (hA : IsXInvariantSubgroup X A) (x : X) : A ≃* A where
  toFun a := ⟨x • (a : P), (hA x a).mp a.property⟩
  invFun a := ⟨x⁻¹ • (a : P), (hA x⁻¹ a).mp a.property⟩
  left_inv a := by
    apply Subtype.ext
    exact inv_smul_smul x (a : P)
  right_inv a := by
    apply Subtype.ext
    exact smul_inv_smul x (a : P)
  map_mul' a b := by
    apply Subtype.ext
    exact smul_mul' x (a : P) (b : P)

private theorem lemma1_coordValue_pow_eq_one {e : ℕ} (z : ZMod (2 ^ e)) :
    (Multiplicative.ofAdd z) ^ (2 ^ e) = 1 := by
  rw [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]
  rfl

private theorem lemma1_coordValue_ne_one {e : ℕ} (he : 0 < e) :
    Multiplicative.ofAdd ((2 ^ (e - 1) : ℕ) : ZMod (2 ^ e)) ≠ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  intro h
  change ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) = 0 at h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact (Nat.not_succ_le_self k) ((Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp h)

private theorem lemma1_coordValue_sq_eq_one {e : ℕ} (he : 0 < e) :
    (Multiplicative.ofAdd ((2 ^ (e - 1) : ℕ) : ZMod (2 ^ e))) ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  change Multiplicative.ofAdd ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ^ 2 =
    Multiplicative.ofAdd 0
  rw [← ofAdd_nsmul]
  congr 1
  rw [two_nsmul, ← Nat.cast_add]
  convert ZMod.natCast_self (2 ^ (k + 1)) using 1
  simp [pow_succ, mul_two]

private theorem lemma1_coordValue_root_pow {a b : ℕ} (h : a < b) :
    (Multiplicative.ofAdd
      ((2 ^ (b - a - 1) : ℕ) : ZMod (2 ^ b))) ^ (2 ^ a) =
      Multiplicative.ofAdd ((2 ^ (b - 1) : ℕ) : ZMod (2 ^ b)) := by
  rw [← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  have hn : 2 ^ a * 2 ^ (b - a - 1) = 2 ^ (b - 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    ((2 ^ a : ℕ) : ZMod (2 ^ b)) *
        ((2 ^ (b - a - 1) : ℕ) : ZMod (2 ^ b)) =
        (((2 ^ a * 2 ^ (b - a - 1) : ℕ) : ZMod (2 ^ b))) := by
          push_cast
          rfl
    _ = ((2 ^ (b - 1) : ℕ) : ZMod (2 ^ b)) :=
      congrArg (fun n : ℕ => (n : ZMod (2 ^ b))) hn

private def lemma1_coordInvolution
    {ι : Type} [DecidableEq ι] (e : ι → ℕ) (i : ι) :
    (j : ι) → Multiplicative (ZMod (2 ^ e j)) :=
  Pi.mulSingle i (Multiplicative.ofAdd ((2 ^ (e i - 1) : ℕ) : ZMod (2 ^ e i)))

private def lemma1_coordRoot
    {ι : Type} [DecidableEq ι] (e : ι → ℕ) (i : ι) (s : ℕ) :
    (j : ι) → Multiplicative (ZMod (2 ^ e j)) :=
  Pi.mulSingle i
    (Multiplicative.ofAdd ((2 ^ (e i - s - 1) : ℕ) : ZMod (2 ^ e i)))

private theorem lemma1_coordInvolution_isInvolution
    {ι : Type} [DecidableEq ι] (e : ι → ℕ) (he : ∀ i, 0 < e i) (i : ι) :
    IsInvolution (lemma1_coordInvolution e i) := by
  constructor
  · intro h
    have hi := congrFun h i
    simp only [lemma1_coordInvolution, Pi.mulSingle_eq_same, Pi.one_apply] at hi
    exact lemma1_coordValue_ne_one (he i) hi
  · ext j
    by_cases hji : j = i
    · subst j
      simp only [lemma1_coordInvolution, Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply]
      exact lemma1_coordValue_sq_eq_one (he i)
    · simp [lemma1_coordInvolution, Pi.mulSingle_eq_of_ne hji]

private theorem lemma1_coordRoot_pow
    {ι : Type} [DecidableEq ι] (e : ι → ℕ) {i j : ι} (h : e i < e j) :
    (lemma1_coordRoot e j (e i)) ^ (2 ^ e i) = lemma1_coordInvolution e j := by
  unfold lemma1_coordRoot lemma1_coordInvolution
  rw [← Pi.mulSingle_pow]
  exact congrArg (Pi.mulSingle j) (lemma1_coordValue_root_pow h)

private theorem lemma1_equal_cyclic_orders
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_X : IsXInvariantSubgroup X A)
    {ι : Type} [Fintype ι] (e : ι → ℕ) (he : ∀ i, 0 < e i)
    (f : A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e i)))) :
    ∃ e0 : ℕ, 0 < e0 ∧ ∀ i, e i = e0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      exact ⟨1, by omega, fun i => isEmptyElim i⟩
  | inr hι =>
      let i0 : ι := Classical.choice hι
      have hnotlt : ∀ i j : ι, ¬ e i < e j := by
        intro i j hij
        let ai : A := f.symm (lemma1_coordInvolution e i)
        let aj : A := f.symm (lemma1_coordInvolution e j)
        have hai : IsInvolution ai := by
          have hci := lemma1_coordInvolution_isInvolution e he i
          constructor
          · intro hai1
            apply hci.ne_one
            simpa [ai] using congrArg f hai1
          · apply f.injective
            simpa [ai] using hci.sq_eq_one
        have haj : IsInvolution aj := by
          have hcj := lemma1_coordInvolution_isInvolution e he j
          constructor
          · intro haj1
            apply hcj.ne_one
            simpa [aj] using congrArg f haj1
          · apply f.injective
            simpa [aj] using hcj.sq_eq_one
        obtain ⟨x, hx⟩ := hXtrans ai
          ⟨fun h => hai.ne_one (Subtype.ext h), by
            simpa using congrArg Subtype.val hai.sq_eq_one⟩ aj
          ⟨fun h => haj.ne_one (Subtype.ext h), by
            simpa using congrArg Subtype.val haj.sq_eq_one⟩
        let phi : A ≃* A := lemma1_invariantMulEquiv hA_X x
        have haj_phi : aj = phi ai := Subtype.ext hx
        let bj : A := f.symm (lemma1_coordRoot e j (e i))
        have hbj : bj ^ (2 ^ e i) = aj := by
          apply f.injective
          simpa [bj, aj] using lemma1_coordRoot_pow e hij
        have hroot_ai : (phi.symm bj) ^ (2 ^ e i) = ai := by
          apply phi.injective
          simpa only [map_pow, phi.apply_symm_apply] using hbj.trans haj_phi
        have hno_root_ai : ¬ ∃ b : A, b ^ (2 ^ e i) = ai := by
          rintro ⟨b, hb⟩
          have hb' : (f b) ^ (2 ^ e i) = lemma1_coordInvolution e i := by
            simpa [ai] using congrArg f hb
          have hbi := congrFun hb' i
          simp only [Pi.pow_apply, lemma1_coordInvolution, Pi.mulSingle_eq_same] at hbi
          exact lemma1_coordValue_ne_one (he i)
            (hbi.symm.trans (lemma1_coordValue_pow_eq_one (f b i)))
        exact hno_root_ai ⟨phi.symm bj, hroot_ai⟩
      refine ⟨e i0, he i0, fun i => ?_⟩
      exact le_antisymm (le_of_not_gt (hnotlt i0 i))
        (le_of_not_gt (hnotlt i i0))
private theorem lemma1_homocyclic_decomposition
    {X P : Type u} [Group X] [Group P] [Finite P]
    [MulDistribMulAction X P]
    (hP : IsPGroup 2 P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A)
    (hA_X : IsXInvariantSubgroup X A) :
    ∃ e r : ℕ, 0 < e ∧
      Nonempty (A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) := by
  obtain ⟨ι, hι, e, he, ⟨f⟩⟩ :=
    lemma1_abelian_two_group_decomposition hP A hA_abelian
  letI : Fintype ι := hι
  obtain ⟨e0, he0, heq⟩ :=
    lemma1_equal_cyclic_orders hXtrans hA_X e he f
  have he_fun : e = fun _ => e0 := funext heq
  subst e
  let r := Fintype.card ι
  let reindex :
      ((i : ι) → Multiplicative (ZMod (2 ^ e0))) ≃*
        (Fin r → Multiplicative (ZMod (2 ^ e0))) :=
    MulEquiv.arrowCongr (Fintype.equivFin ι) (MulEquiv.refl _)
  let untag :
      (Fin r → Multiplicative (ZMod (2 ^ e0))) ≃*
        Multiplicative (Fin r → ZMod (2 ^ e0)) :=
    (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod (2 ^ e0))).symm
  exact ⟨e0, r, he0, ⟨f.trans (reindex.trans untag)⟩⟩
/-- A finite abelian `2`-group on whose involutions a group acts transitively
is homocyclic.  The Suzuki hypotheses are only needed by the later invariant-subgroup part. -/
public theorem homocyclic_of_abelian_twoGroup_of_involutions_transitive
    {X P : Type u} [Group X] [Group P] [Finite P]
    [MulDistribMulAction X P]
    (hP : IsPGroup 2 P) (hP_abelian : IsMulCommutative P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x) :
    ∃ e r : ℕ, 0 < e ∧
      Nonempty (P ≃* Multiplicative (Fin r → ZMod (2 ^ e))) := by
  letI : IsMulCommutative P := hP_abelian
  letI : IsMulCommutative (⊤ : Subgroup P) := inferInstance
  obtain ⟨e, r, he, ⟨f⟩⟩ :=
    lemma1_homocyclic_decomposition hP hXtrans
      (A := (⊤ : Subgroup P)) inferInstance (by intro x a; simp)
  exact ⟨e, r, he, ⟨Subgroup.topEquiv.symm.trans f⟩⟩

public theorem lemma1_involutions_mem_of_nontrivial_invariant
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {B : Subgroup P} (hB_X : IsXInvariantSubgroup X B) (hB_ne : B ≠ ⊥) :
    ∀ a : P, IsInvolution a → a ∈ B := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite B := inferInstance
  haveI : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB_ne
  obtain ⟨m, hm⟩ :=
    (isPGroup_of_isSuzukiTwoGroup hP).to_subgroup B |>.exists_card_eq
  have hm_ne : m ≠ 0 := by
    intro hm0
    have hcard_one : Nat.card B = 1 := by simpa [hm0] using hm
    exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
      (Nat.card_eq_one_iff_unique.mp hcard_one).1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  have htwo_dvd : 2 ∣ Nat.card B := by
    rw [hm, pow_succ]
    rw [mul_comm]
    exact dvd_mul_right 2 (2 ^ k)
  obtain ⟨b, hb_order⟩ := exists_prime_orderOf_dvd_card' 2 htwo_dvd
  have hb : IsInvolution b := (orderOf_eq_prime_iff.mp hb_order).symm
  intro a ha
  obtain ⟨x, hx⟩ := hXtrans b
    ⟨fun h => hb.ne_one (Subtype.ext h), by
      simpa using congrArg Subtype.val hb.sq_eq_one⟩ a
    ⟨ha.ne_one, ha.sq_eq_one⟩
  rw [hx]
  exact (hB_X x b).mp b.property
private theorem lemma1_coord_twoTorsion_card {e : ℕ} (he : 0 < e) :
    Nat.card {x : Multiplicative (ZMod (2 ^ e)) // x ^ 2 = 1} = 2 := by
  classical
  let phi : {x : Multiplicative (ZMod (2 ^ e)) // x ^ 2 = 1} ≃
      ((powMonoidHom 2 :
        Multiplicative (ZMod (2 ^ e)) →* Multiplicative (ZMod (2 ^ e))).ker) := by
    refine
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  calc
    Nat.card {x : Multiplicative (ZMod (2 ^ e)) // x ^ 2 = 1} =
        Nat.card ((powMonoidHom 2 :
          Multiplicative (ZMod (2 ^ e)) →* Multiplicative (ZMod (2 ^ e))).ker) :=
      Nat.card_congr phi
    _ = Nat.gcd (Nat.card (Multiplicative (ZMod (2 ^ e)))) 2 :=
      IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod (2 ^ e))) 2
    _ = Nat.gcd (2 ^ e) 2 := by
      congr 1
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr
        (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ e)) ≃ ZMod (2 ^ e))
        |>.trans (by simp [ZMod.card])
    _ = 2 := Nat.gcd_eq_right (by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
      rw [pow_succ]
      exact dvd_mul_left 2 (2 ^ k))

public theorem lemma1_twoTorsion_card_of_homocyclic
    {G : Type u} [Group G] {e r : ℕ} (he : 0 < e)
    (f : G ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    Nat.card {x : G // x ^ 2 = 1} = 2 ^ r := by
  let g : G ≃* (Fin r → Multiplicative (ZMod (2 ^ e))) :=
    f.trans (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod (2 ^ e)))
  let split : {x : G // x ^ 2 = 1} ≃
      (Fin r → {z : Multiplicative (ZMod (2 ^ e)) // z ^ 2 = 1}) := by
    refine
      { toFun := fun x i => ⟨g x.1 i, ?_⟩
        invFun := fun x => ⟨g.symm (fun i => (x i).1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx := congrArg g x.2
      exact congrFun (by simpa using hx) i
    · apply g.injective
      simp only [map_pow, map_one, g.apply_symm_apply]
      funext i
      exact (x i).2
    · intro x
      apply Subtype.ext
      exact g.symm_apply_apply x.1
    · intro x
      funext i
      apply Subtype.ext
      exact congrFun (g.apply_symm_apply (fun j => (x j).1)) i
  calc
    Nat.card {x : G // x ^ 2 = 1} =
        Nat.card (Fin r → {z : Multiplicative (ZMod (2 ^ e)) // z ^ 2 = 1}) :=
      Nat.card_congr split
    _ = ∏ _i : Fin r,
        Nat.card {z : Multiplicative (ZMod (2 ^ e)) // z ^ 2 = 1} := Nat.card_pi
    _ = ∏ _i : Fin r, 2 := by
      congr
      ext i
      exact lemma1_coord_twoTorsion_card he
    _ = 2 ^ r := by simp

private def lemma1_twoTorsionEquiv
    {P : Type u} [Group P] {A B : Subgroup P} (hBA : B ≤ A)
    (hall : ∀ a : P, IsInvolution a → a ∈ B) :
    {x : B // x ^ 2 = 1} ≃ {x : A // x ^ 2 = 1} := by
  refine
    { toFun := fun x => ⟨⟨x.1, hBA x.1.property⟩, ?_⟩
      invFun := fun x => ⟨⟨x.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    simpa using congrArg Subtype.val x.2
  · by_cases hx1 : (x.1 : P) = 1
    · simp [hx1]
    · apply hall x.1
      exact ⟨hx1, by simpa using congrArg Subtype.val x.2⟩
  · apply Subtype.ext
    simpa using congrArg Subtype.val x.2
  · intro _
    rfl
  · intro _
    rfl

private theorem lemma1_homocyclic_rank_eq
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A B : Subgroup P} (hBA : B ≤ A)
    (hB_X : IsXInvariantSubgroup X B) (hB_ne : B ≠ ⊥)
    {e r f q : ℕ} (he : 0 < e) (hf : 0 < f)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (hB : B ≃* Multiplicative (Fin q → ZMod (2 ^ f))) :
    q = r := by
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  calc
    2 ^ q = Nat.card {x : B // x ^ 2 = 1} :=
      (lemma1_twoTorsion_card_of_homocyclic hf hB).symm
    _ = Nat.card {x : A // x ^ 2 = 1} := Nat.card_congr
      (lemma1_twoTorsionEquiv hBA
        (lemma1_involutions_mem_of_nontrivial_invariant hP hXtrans hB_X hB_ne))
    _ = 2 ^ r := lemma1_twoTorsion_card_of_homocyclic he hA
public theorem lemma1_pow_eq_one_of_homocyclic
    {G : Type u} [Group G] {e r : ℕ}
    (f : G ≃* Multiplicative (Fin r → ZMod (2 ^ e))) (x : G) :
    x ^ (2 ^ e) = 1 := by
  apply f.injective
  rw [map_pow, map_one]
  change Multiplicative.ofAdd (f x).toAdd ^ (2 ^ e) = Multiplicative.ofAdd 0
  rw [← ofAdd_nsmul]
  congr 1
  funext i
  exact ZModModule.char_nsmul_eq_zero (2 ^ e) ((f x).toAdd i)

private theorem lemma1_rank_pos_of_nontrivial_homocyclic
    {G : Type u} [Group G] [Nontrivial G] {e r : ℕ}
    (f : G ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hr
  subst r
  have htarget : Nontrivial (Multiplicative (Fin 0 → ZMod (2 ^ e))) :=
    (Equiv.nontrivial_congr f.toEquiv).mp inferInstance
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) htarget

private theorem lemma1_homocyclic_exponent_le
    {P : Type u} [Group P] {A B : Subgroup P} (hBA : B ≤ A)
    {e r f : ℕ} (hr : 0 < r)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (hB : B ≃* Multiplicative (Fin r → ZMod (2 ^ f))) :
    f ≤ e := by
  let i0 : Fin r := ⟨0, hr⟩
  let basis : Fin r → ZMod (2 ^ f) := Pi.single i0 (1 : ZMod (2 ^ f))
  let genB : B := hB.symm (Multiplicative.ofAdd basis)
  let genA : A := ⟨genB.1, hBA genB.2⟩
  have hkillA : genA ^ (2 ^ e) = 1 :=
    lemma1_pow_eq_one_of_homocyclic hA genA
  have hkillB : genB ^ (2 ^ e) = 1 := by
    apply Subtype.ext
    simpa [genA] using congrArg Subtype.val hkillA
  have htarget : (Multiplicative.ofAdd basis) ^ (2 ^ e) = 1 := by
    simpa [genB] using congrArg hB hkillB
  have hi := congrArg
    (fun z : Multiplicative (Fin r → ZMod (2 ^ f)) => z.toAdd i0) htarget
  have hcast : ((2 ^ e : ℕ) : ZMod (2 ^ f)) = 0 := by
    simpa [basis, Pi.single_eq_same, nsmul_eq_mul] using hi
  have hdvd : 2 ^ f ∣ 2 ^ e :=
    (ZMod.natCast_eq_zero_iff (2 ^ e) (2 ^ f)).mp hcast
  exact (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mp hdvd

private theorem lemma1_coord_pow_ker_eq_range {e f : ℕ} (hf : f ≤ e) :
    (powMonoidHom (2 ^ f) :
      Multiplicative (ZMod (2 ^ e)) →* Multiplicative (ZMod (2 ^ e))).ker =
    (powMonoidHom (2 ^ (e - f)) :
      Multiplicative (ZMod (2 ^ e)) →* Multiplicative (ZMod (2 ^ e))).range := by
  let M := Multiplicative (ZMod (2 ^ e))
  let kill : M →* M := powMonoidHom (2 ^ f)
  let root : M →* M := powMonoidHom (2 ^ (e - f))
  have hle : root.range ≤ kill.ker := by
    rintro _ ⟨y, rfl⟩
    change (y ^ (2 ^ (e - f))) ^ (2 ^ f) = 1
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hf]
    exact lemma1_coordValue_pow_eq_one y.toAdd
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have hcardM : Nat.card M = 2 ^ e := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      (Multiplicative.toAdd : M ≃ ZMod (2 ^ e))
      |>.trans (by simp [ZMod.card])
  rw [show root = powMonoidHom (2 ^ (e - f)) by rfl,
    show kill = powMonoidHom (2 ^ f) by rfl,
    IsCyclic.card_powMonoidHom_range,
    IsCyclic.card_powMonoidHom_ker, hcardM]
  have hdvd_f : 2 ^ f ∣ 2 ^ e :=
    (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mpr hf
  have hdvd_sub : 2 ^ (e - f) ∣ 2 ^ e :=
    (Nat.pow_dvd_pow_iff_le_right' (b := 0)).mpr (Nat.sub_le e f)
  rw [Nat.gcd_eq_right hdvd_f, Nat.gcd_eq_right hdvd_sub,
    Nat.pow_div (Nat.sub_le e f) (by omega)]
  have hsub : e - (e - f) = f := by omega
  rw [hsub]

public theorem lemma1_exists_power_root_of_homocyclic
    {G : Type u} [Group G] {e r f : ℕ} (hf : f ≤ e)
    (hG : G ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    {x : G} (hx : x ^ (2 ^ f) = 1) :
    ∃ y : G, y ^ (2 ^ (e - f)) = x := by
  let g : G ≃* (Fin r → Multiplicative (ZMod (2 ^ e))) :=
    hG.trans (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod (2 ^ e)))
  have hxg : (g x) ^ (2 ^ f) = 1 := by
    simpa using congrArg g hx
  have hcoord : ∀ i, g x i ∈
      (powMonoidHom (2 ^ (e - f)) :
        Multiplicative (ZMod (2 ^ e)) →*
          Multiplicative (ZMod (2 ^ e))).range := by
    intro i
    rw [← lemma1_coord_pow_ker_eq_range hf]
    exact congrFun hxg i
  choose y hy using fun i => MonoidHom.mem_range.mp (hcoord i)
  refine ⟨g.symm y, ?_⟩
  apply g.injective
  rw [map_pow, g.apply_symm_apply]
  funext i
  exact hy i

private theorem lemma1_coord_powKernel_card {e f : ℕ} (hf : f ≤ e) :
    Nat.card {x : Multiplicative (ZMod (2 ^ e)) // x ^ (2 ^ f) = 1} =
      2 ^ f := by
  classical
  let phi : {x : Multiplicative (ZMod (2 ^ e)) // x ^ (2 ^ f) = 1} ≃
      ((powMonoidHom (2 ^ f) :
        Multiplicative (ZMod (2 ^ e)) →* Multiplicative (ZMod (2 ^ e))).ker) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card {x : Multiplicative (ZMod (2 ^ e)) // x ^ (2 ^ f) = 1} =
        Nat.card ((powMonoidHom (2 ^ f) :
          Multiplicative (ZMod (2 ^ e)) →* Multiplicative (ZMod (2 ^ e))).ker) :=
      Nat.card_congr phi
    _ = Nat.gcd (Nat.card (Multiplicative (ZMod (2 ^ e)))) (2 ^ f) :=
      IsCyclic.card_powMonoidHom_ker
        (G := Multiplicative (ZMod (2 ^ e))) (2 ^ f)
    _ = Nat.gcd (2 ^ e) (2 ^ f) := by
      congr 1
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr
        (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ e)) ≃ ZMod (2 ^ e))
        |>.trans (by simp [ZMod.card])
    _ = 2 ^ f := Nat.gcd_eq_right
      ((Nat.pow_dvd_pow_iff_le_right' (b := 0)).mpr hf)

public theorem lemma1_powKernel_card_of_homocyclic
    {G : Type u} [Group G] {e r f : ℕ} (hf : f ≤ e)
    (hG : G ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    Nat.card {x : G // x ^ (2 ^ f) = 1} = (2 ^ f) ^ r := by
  let g : G ≃* (Fin r → Multiplicative (ZMod (2 ^ e))) :=
    hG.trans (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod (2 ^ e)))
  let split : {x : G // x ^ (2 ^ f) = 1} ≃
      (Fin r → {z : Multiplicative (ZMod (2 ^ e)) // z ^ (2 ^ f) = 1}) := by
    refine
      { toFun := fun x i => ⟨g x.1 i, ?_⟩
        invFun := fun x => ⟨g.symm (fun i => (x i).1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx := congrArg g x.2
      exact congrFun (by simpa using hx) i
    · apply g.injective
      simp only [map_pow, map_one, g.apply_symm_apply]
      funext i
      exact (x i).2
    · intro x
      apply Subtype.ext
      exact g.symm_apply_apply x.1
    · intro x
      funext i
      apply Subtype.ext
      exact congrFun (g.apply_symm_apply (fun j => (x j).1)) i
  calc
    Nat.card {x : G // x ^ (2 ^ f) = 1} =
        Nat.card (Fin r →
          {z : Multiplicative (ZMod (2 ^ e)) // z ^ (2 ^ f) = 1}) :=
      Nat.card_congr split
    _ = ∏ _i : Fin r,
        Nat.card {z : Multiplicative (ZMod (2 ^ e)) // z ^ (2 ^ f) = 1} :=
      Nat.card_pi
    _ = ∏ _i : Fin r, 2 ^ f := by
      congr
      ext i
      exact lemma1_coord_powKernel_card hf
    _ = (2 ^ f) ^ r := by simp

private theorem lemma1_pow_ker_eq_range_of_homocyclic
    {G : Type u} [CommGroup G] {e r f : ℕ} (hf : f ≤ e)
    (hG : G ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    (powMonoidHom (2 ^ f) : G →* G).ker =
      (powMonoidHom (2 ^ (e - f)) : G →* G).range := by
  apply le_antisymm
  · intro x hx
    exact MonoidHom.mem_range.mpr
      (lemma1_exists_power_root_of_homocyclic hf hG hx)
  · rintro _ ⟨y, rfl⟩
    change (y ^ (2 ^ (e - f))) ^ (2 ^ f) = 1
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hf]
    exact lemma1_pow_eq_one_of_homocyclic hG y

private theorem lemma1_homocyclic_card
    {G : Type u} [Group G] {e r : ℕ}
    (f : G ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    Nat.card G = (2 ^ e) ^ r := by
  calc
    Nat.card G = Nat.card (Multiplicative (Fin r → ZMod (2 ^ e))) :=
      Nat.card_congr f.toEquiv
    _ = Nat.card (Fin r → ZMod (2 ^ e)) := Nat.card_congr Multiplicative.toAdd
    _ = ∏ _i : Fin r, Nat.card (ZMod (2 ^ e)) := Nat.card_pi
    _ = ∏ _i : Fin r, 2 ^ e := by simp
    _ = (2 ^ e) ^ r := by simp

public theorem lemma1_power_closure_card
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_abelian : IsMulCommutative A)
    {e r f : ℕ} (hf : f ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    Nat.card (Subgroup.closure
      {x : P | ∃ a : A, (a : P) ^ (2 ^ (e - f)) = x}) = (2 ^ f) ^ r := by
  letI : IsMulCommutative A := hA_abelian
  letI : CommGroup A := IsMulCommutative.instCommGroup
  let power : A →* A := powMonoidHom (2 ^ (e - f))
  have hclosure : Subgroup.closure
      {x : P | ∃ a : A, (a : P) ^ (2 ^ (e - f)) = x} =
      power.range.map A.subtype := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨a, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨a ^ (2 ^ (e - f)), MonoidHom.mem_range.mpr ⟨a, rfl⟩, rfl⟩
    · rintro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
      exact Subgroup.subset_closure ⟨a, rfl⟩
  rw [hclosure, Subgroup.card_map_of_injective A.subtype_injective]
  have hrange : power.range = (powMonoidHom (2 ^ f) : A →* A).ker :=
    (lemma1_pow_ker_eq_range_of_homocyclic hf hA).symm
  rw [hrange]
  exact lemma1_powKernel_card_of_homocyclic hf hA
private theorem lemma1_invariant_subgroup_eq_power
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A)
    {e r : ℕ} (he : 0 < e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (B : Subgroup P) (hBA : B ≤ A) (hB_X : IsXInvariantSubgroup X B) :
    ∃ s : ℕ, s ≤ e ∧
      B = Subgroup.closure {x : P | ∃ a : A, (a : P) ^ (2 ^ s) = x} := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  by_cases hB_bot : B = ⊥
  · subst B
    refine ⟨e, le_rfl, ?_⟩
    apply le_antisymm bot_le
    rw [Subgroup.closure_le]
    rintro x ⟨a, rfl⟩
    exact Subgroup.mem_bot.mpr (by
      simpa using congrArg Subtype.val (lemma1_pow_eq_one_of_homocyclic hA a))
  · have hB_abelian : IsMulCommutative B := by
      letI : IsMulCommutative A := hA_abelian
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val
        (mul_comm (⟨x, hBA x.property⟩ : A) (⟨y, hBA y.property⟩ : A))
    obtain ⟨f, q, hf, ⟨hB⟩⟩ :=
      lemma1_homocyclic_decomposition
        (isPGroup_of_isSuzukiTwoGroup hP) hXtrans hB_abelian hB_X
    have hq : q = r :=
      lemma1_homocyclic_rank_eq hP hXtrans hBA hB_X hB_bot he hf hA hB
    subst q
    haveI : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB_bot
    have hr : 0 < r := lemma1_rank_pos_of_nontrivial_homocyclic hB
    have hfe : f ≤ e := lemma1_homocyclic_exponent_le hBA hr hA hB
    let C : Subgroup P := Subgroup.closure
      {x : P | ∃ a : A, (a : P) ^ (2 ^ (e - f)) = x}
    have hBC : B ≤ C := by
      intro b hb
      let bB : B := ⟨b, hb⟩
      have hkillB : bB ^ (2 ^ f) = 1 :=
        lemma1_pow_eq_one_of_homocyclic hB bB
      let bA : A := ⟨b, hBA hb⟩
      have hkillA : bA ^ (2 ^ f) = 1 := by
        apply Subtype.ext
        simpa [bA, bB] using congrArg Subtype.val hkillB
      obtain ⟨a, ha⟩ :=
        lemma1_exists_power_root_of_homocyclic hfe hA hkillA
      exact Subgroup.subset_closure ⟨a, by
        simpa [bA] using congrArg Subtype.val ha⟩
    have hcardB : Nat.card B = (2 ^ f) ^ r := lemma1_homocyclic_card hB
    have hcardC : Nat.card C = (2 ^ f) ^ r := by
      simpa [C] using lemma1_power_closure_card hA_abelian hfe hA
    have hBC_eq : B = C :=
      Subgroup.eq_of_le_of_card_ge hBC (by rw [hcardB, hcardC])
    exact ⟨e - f, Nat.sub_le e f, hBC_eq⟩
/-- Higman Lemma 1: abelian `X`-subgroups are homocyclic, and their
`X`-subgroups are exactly the power subgroups. -/
public theorem lemma1_abelian_invariant_homocyclic
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A)
    (hA_X : IsXInvariantSubgroup X A) :
    ∃ e r : ℕ,
      Nonempty (A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) ∧
      ∀ B : Subgroup P, B ≤ A → IsXInvariantSubgroup X B →
        ∃ s : ℕ, s ≤ e ∧
          B = Subgroup.closure {x : P | ∃ a : A, (a : P) ^ (2 ^ s) = x} := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  obtain ⟨e, r, he, ⟨hA⟩⟩ :=
    lemma1_homocyclic_decomposition
      (isPGroup_of_isSuzukiTwoGroup hP) hXtrans hA_abelian hA_X
  refine ⟨e, r, ⟨hA⟩, ?_⟩
  exact lemma1_invariant_subgroup_eq_power hP hXtrans hA_abelian he hA
end Higman
end External
end CFSG.BenderSuzuki
