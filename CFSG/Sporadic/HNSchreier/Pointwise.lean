module

public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Sporadic.HNSchreier.PointwiseCheck
public import Certificates.Certificate2096
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open Equiv

local notation "hwA" => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) PointwiseData.hw
local notation "k1A" => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) PointwiseData.k1
local notation "k2A" => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) PointwiseData.k2
local notation "c1A" => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) PointwiseData.c1
local notation "PA" => natArr PointwiseData.natP
local notation "QA" => natArr PointwiseData.natQ
local notation "P2A" => natArr PointwiseData.natP2

theorem pointwise_parts :
    (∀ l ∈ PointwiseData.g0, l = 1 ∨ l = 2) ∧ plettersOK 17 PointwiseData.hw = true ∧
    plettersOK 17 PointwiseData.k1 = true ∧ plettersOK 17 PointwiseData.k2 = true ∧
    plettersOK 17 PointwiseData.c1 = true ∧
    pisInv hnsData.n hwA (pinvs hnsData.n #[hwA])[0]! = true ∧
    seedWordIdx a0Arr a1Arr PointwiseData.g0 hwA[0]! = 88 ∧
    seedWordIdx a0Arr a1Arr PointwiseData.g0 hwA[88]! = 0 ∧
    (∀ x < hnsData.n, (k1A[x]! = x ∧ k2A[x]! = x) ↔ (x = 0 ∨ x = 88)) ∧
    (∀ b ∈ Data.baseList, seedWordIdx a0Arr a1Arr PointwiseData.g0
      hwA[k1A[((pinvs hnsData.n #[hwA])[0]!)[seedWordInvIdx (pinvs hnsData.n #[a0Arr, a1Arr])[0]!
        (pinvs hnsData.n #[a0Arr, a1Arr])[1]! PointwiseData.g0 b]!]!]! = c1A[b]!) ∧
    peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) PointwiseData.k1) PA = true ∧
    peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) PointwiseData.k2) QA = true ∧
    peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) PointwiseData.c1) P2A = true ∧
    (∀ j < 12, (boolWordArr PA QA PointwiseData.ufix)[j]! = j ↔ j = 0) ∧
    (∀ b < 12, (boolWordArr PA QA PointwiseData.tw[b]!)[0]! = b) ∧
    PA[7]! = 7 ∧ ∀ j < 12, P2A[j]! ≠ j := by
  have h := pointwise_cert
  unfold pointwiseChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← natStrongArr_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, -⟩, h20⟩, h21⟩, h22⟩ := h
  refine ⟨fun l hl => ?_, h5, h6, h7, h8, h10, h11, h12, fun x hx => ?_, fun b hb => ?_, h15,
    h16, h17, fun j hj => ?_, fun b hb => ?_, h21, fun j hj => ?_⟩
  · have := List.all_eq_true.1 h4 l hl
    simpa using this
  · have := allBelowN_spec h13 hx
    rw [beq_iff_eq, Bool.eq_iff_iff] at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · have := List.all_eq_true.1 h14 b hb
    simpa using this
  · have := allBelowN_spec h18 hj
    rw [beq_iff_eq, Bool.eq_iff_iff] at this
    simp only [beq_iff_eq] at this
    exact this
  · have := allBelowN_spec h20 hb
    simpa using this
  · have := allBelowN_spec h22 hj
    simpa using this

@[expose] def s0J : JH := seedWordJ PointwiseData.g0 * hWordJ PointwiseData.hw

@[expose] def k1J : JH := hWordJ PointwiseData.k1

@[expose] def k2J : JH := hWordJ PointwiseData.k2

@[expose] def ck1J : JH := hWordJ PointwiseData.c1

abbrev y88 : X := ⟨88, by decide⟩

theorem s0J_smul_val
    (y : X) :
    ((s0J • y : X) : ℕ) = seedWordIdx a0Arr a1Arr PointwiseData.g0 hwA[y.val]! := by
  rw [prep_apply (prep_hWord pointwise_parts.2.1) y, permJ_apply,
    seedWordIdx_val _ pointwise_parts.1, s0J, mul_smul]

theorem s0J_inv_smul_val
    (y : X) :
    ((s0J⁻¹ • y : X) : ℕ) = ((pinvs hnsData.n #[hwA])[0]!)[seedWordInvIdx
      (pinvs hnsData.n #[a0Arr, a1Arr])[0]! (pinvs hnsData.n #[a0Arr, a1Arr])[1]!
      PointwiseData.g0 y.val]! := by
  have hinv := prep_inv_of_pisInv (prep_hWord pointwise_parts.2.1) pointwise_parts.2.2.2.2.2.1
  rw [seedWordInvIdx_val _ pointwise_parts.1, prep_apply hinv, ← map_inv, permJ_apply, s0J,
    mul_inv_rev, mul_smul]

theorem s0J_x0 :
    s0J • x0 = y88 :=
  Fin.ext (by rw [s0J_smul_val]; exact pointwise_parts.2.2.2.2.2.2.1)

theorem s0J_y88 :
    s0J • y88 = x0 :=
  Fin.ext (by rw [s0J_smul_val]; exact pointwise_parts.2.2.2.2.2.2.2.1)

theorem x0_ne_y88 : x0 ≠ y88 := fun h => by
  have := congrArg Fin.val h
  simp at this

theorem k1J_smul_val
    (z : X) : ((k1J • z : X) : ℕ) = k1A[z.val]! := by
  rw [prep_apply (prep_hWord pointwise_parts.2.2.1) z, permJ_apply]
  rfl

theorem k2J_smul_val
    (z : X) : ((k2J • z : X) : ℕ) = k2A[z.val]! := by
  rw [prep_apply (prep_hWord pointwise_parts.2.2.2.1) z, permJ_apply]
  rfl

theorem ck1J_smul_val
    (z : X) : ((ck1J • z : X) : ℕ) = c1A[z.val]! := by
  rw [prep_apply (prep_hWord pointwise_parts.2.2.2.2.1) z, permJ_apply]
  rfl

theorem fix_k12
    (x : X) : (k1J • x = x ∧ k2J • x = x) ↔ (x = x0 ∨ x = y88) := by
  have h := pointwise_parts.2.2.2.2.2.2.2.2.1 x.val x.isLt
  rw [← k1J_smul_val, ← k2J_smul_val] at h
  simp only [Fin.ext_iff]
  exact h

theorem s0J_conj_k1 :
    s0J * k1J * s0J⁻¹ = ck1J := by
  apply eq_of_base
  intro k
  apply Fin.ext
  have := pointwise_parts.2.2.2.2.2.2.2.2.2.1 _ (baseX_mem k)
  rw [mul_smul, mul_smul, s0J_smul_val, k1J_smul_val, s0J_inv_smul_val, ck1J_smul_val]
  exact this

@[expose] def wordPQ (P Q : Perm (Fin 12)) : List Bool → Perm (Fin 12)
  | [] => 1
  | b :: w => (if b then P else Q) * wordPQ P Q w

theorem prep_boolWordArr {A B : Array ℕ} {P Q : Perm (Fin 12)} (hA : PRep 12 A P)
    (hB : PRep 12 B Q) : ∀ w, PRep 12 (boolWordArr A B w) (wordPQ P Q w)
  | [] => prep_pid
  | b :: w => by
    cases b
    · exact prep_pcomp hB (prep_boolWordArr hA hB w)
    · exact prep_pcomp hA (prep_boolWordArr hA hB w)

theorem comm_wordPQ {m P Q : Perm (Fin 12)} (hP : m * P = P * m) (hQ : m * Q = Q * m) :
    ∀ w, m * wordPQ P Q w = wordPQ P Q w * m
  | [] => by rw [wordPQ, mul_one, one_mul]
  | b :: w => by
    have hb : m * (if b then P else Q) = (if b then P else Q) * m := by
      cases b
      · exact hQ
      · exact hP
    rw [wordPQ, ← mul_assoc, hb, mul_assoc, comm_wordPQ hP hQ w, mul_assoc]

theorem k1J_mem : k1J ∈ HJ := hWordJ_mem _

theorem k2J_mem : k2J ∈ HJ := hWordJ_mem _

theorem ck1J_mem : ck1J ∈ HJ := hWordJ_mem _

theorem theta_k1 :
    PRep 12 PA (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12)) := by
  have e : (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12)) = natWord PointwiseData.k1 := thetaJ_hWord _
  rw [e]
  exact prep_of_peq_left pointwise_parts.2.2.2.2.2.2.2.2.2.2.1 (prep_natWord pointwise_parts.2.2.1)

theorem theta_k2 :
    PRep 12 QA (thetaJ ⟨k2J, k2J_mem⟩ : Perm (Fin 12)) := by
  have e : (thetaJ ⟨k2J, k2J_mem⟩ : Perm (Fin 12)) = natWord PointwiseData.k2 := thetaJ_hWord _
  rw [e]
  exact prep_of_peq_left pointwise_parts.2.2.2.2.2.2.2.2.2.2.2.1
    (prep_natWord pointwise_parts.2.2.2.1)

theorem theta_ck1 :
    PRep 12 P2A (thetaJ ⟨ck1J, ck1J_mem⟩ : Perm (Fin 12)) := by
  have e : (thetaJ ⟨ck1J, ck1J_mem⟩ : Perm (Fin 12)) = natWord PointwiseData.c1 := thetaJ_hWord _
  rw [e]
  exact prep_of_peq_left pointwise_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
    (prep_natWord pointwise_parts.2.2.2.2.1)

theorem eq_one_of_comm_k12
    {m : Perm (Fin 12)}
    (hP : m * (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12)) =
      (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12)) * m)
    (hQ : m * (thetaJ ⟨k2J, k2J_mem⟩ : Perm (Fin 12)) =
      (thetaJ ⟨k2J, k2J_mem⟩ : Perm (Fin 12)) * m) :
    m = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hu, htw, -⟩ := pointwise_parts
  have hrep := prep_boolWordArr theta_k1 theta_k2
  have hUfix : ∀ j : Fin 12, wordPQ (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12))
      (thetaJ ⟨k2J, k2J_mem⟩ : Perm (Fin 12)) PointwiseData.ufix j = j ↔ j = 0 := fun j => by
    have := hu j.val j.isLt
    rw [hrep PointwiseData.ufix j] at this
    simp only [Fin.ext_iff, Fin.val_zero]
    exact this
  have hU := comm_wordPQ hP hQ PointwiseData.ufix
  have h0 : m 0 = 0 := by
    apply (hUfix (m 0)).1
    have := congrArg (fun f : Perm (Fin 12) => f 0) hU
    simp only [Perm.mul_apply] at this
    rw [← this, (hUfix 0).2 rfl]
  ext b
  have hW := comm_wordPQ hP hQ (PointwiseData.tw[b.val]!)
  have hb : wordPQ (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12)) (thetaJ ⟨k2J, k2J_mem⟩ : Perm (Fin 12))
      PointwiseData.tw[b.val]! 0 = b := by
    apply Fin.ext
    rw [← hrep _ 0]
    exact htw b.val b.isLt
  have := congrArg (fun f : Perm (Fin 12) => f 0) hW
  simp only [Perm.mul_apply, h0, hb] at this
  rw [this, Perm.one_apply]

theorem jh_preprimitive :
    MulAction.IsPreprimitive JH X := by
  let f : X →ₑ[(jEquivP : JH → PH)] X := ⟨id, fun g x => (jEquivP_apply g x).symm⟩
  exact (MulAction.isPreprimitive_congr jEquivP.surjective (f := f) Function.bijective_id).2
    ph_preprimitive

theorem HJ_coatom :
    IsCoatom HJ := by
  have : Nontrivial X := ⟨⟨x0, y88, x0_ne_y88⟩⟩
  have := jh_preprimitive
  have h := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := JH) x0
  have e : MulAction.stabilizer JH x0 = HJ := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_HJ_iff_fix]
  rwa [e] at h

@[expose] def fixAutSub (α : MulAut JH) : Subgroup JH where
  carrier := {g | α g = g}
  mul_mem' {a b} ha hb := by
    have ha' : α a = a := ha
    have hb' : α b = b := hb
    show α (a * b) = a * b
    rw [map_mul, ha', hb']
  one_mem' := map_one α
  inv_mem' {a} ha := by
    have ha' : α a = a := ha
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha']

theorem eq_one_of_fix_HJ
    (α : MulAut JH) (hα : ∀ h ∈ HJ, α h = h) : α = 1 := by
  set z := α s0J * s0J⁻¹ with hz
  have hconj : ∀ k : JH, k ∈ HJ → k • y88 = y88 → z * k = k * z := by
    intro k hkH hky
    have hm : s0J⁻¹ * k * s0J ∈ HJ := by
      rw [mem_HJ_iff_fix, mul_smul, mul_smul, s0J_x0, hky, ← s0J_x0, inv_smul_smul]
    have e := hα _ hm
    rw [map_mul α, map_mul α, map_inv α, hα k hkH] at e
    calc z * k = α s0J * (s0J⁻¹ * k * s0J) * s0J⁻¹ := by rw [hz]; group
      _ = α s0J * ((α s0J)⁻¹ * k * α s0J) * s0J⁻¹ := by rw [e]
      _ = k * z := by rw [hz]; group
  have hk1y : k1J • y88 = y88 := ((fix_k12 y88).2 (Or.inr rfl)).1
  have hk2y : k2J • y88 = y88 := ((fix_k12 y88).2 (Or.inr rfl)).2
  have hz1 := hconj k1J k1J_mem hk1y
  have hz2 := hconj k2J k2J_mem hk2y
  have hfixz : ∀ x : X, (k1J • x = x ∧ k2J • x = x) →
      (k1J • (z • x) = z • x ∧ k2J • (z • x) = z • x) := by
    rintro x ⟨h1, h2⟩
    constructor
    · rw [← mul_smul, ← hz1, mul_smul, h1]
    · rw [← mul_smul, ← hz2, mul_smul, h2]
  have hz1' : z = 1 := by
    rcases (fix_k12 _).1 (hfixz x0 ((fix_k12 x0).2 (Or.inl rfl))) with h | h
    · have hzH : z ∈ HJ := (mem_HJ_iff_fix z).2 h
      have hcomm : ∀ k (hk : k ∈ HJ), z * k = k * z →
          (thetaJ ⟨z, hzH⟩ : Perm (Fin 12)) * (thetaJ ⟨k, hk⟩ : Perm (Fin 12)) =
            (thetaJ ⟨k, hk⟩ : Perm (Fin 12)) * (thetaJ ⟨z, hzH⟩ : Perm (Fin 12)) := by
        intro k hk hzk
        have : (⟨z, hzH⟩ : HJ) * ⟨k, hk⟩ = ⟨k, hk⟩ * ⟨z, hzH⟩ := Subtype.ext hzk
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul thetaJ, ← map_mul thetaJ, this]
      have h1 := eq_one_of_comm_k12 (hcomm k1J k1J_mem hz1) (hcomm k2J k2J_mem hz2)
      have h2 : thetaJ ⟨z, hzH⟩ = 1 := Subtype.ext h1
      have h3 : (⟨z, hzH⟩ : HJ) = 1 := thetaJ.injective (h2.trans (map_one thetaJ).symm)
      simpa using congrArg Subtype.val h3
    · exfalso
      have hzy : z • y88 = x0 := by
        rcases (fix_k12 _).1 (hfixz y88 ((fix_k12 y88).2 (Or.inr rfl))) with h' | h'
        · exact h'
        · exact absurd (smul_left_cancel z (h.trans h'.symm)) x0_ne_y88
      have hs0inv : s0J⁻¹ • x0 = y88 := by rw [← s0J_y88, inv_smul_smul]
      have hhH : z * s0J⁻¹ ∈ HJ := by
        rw [mem_HJ_iff_fix, mul_smul, hs0inv, hzy]
      have hc : ck1J = (z * s0J⁻¹)⁻¹ * k1J * (z * s0J⁻¹) := by
        rw [← s0J_conj_k1]
        have : k1J * z = z * k1J := hz1.symm
        calc s0J * k1J * s0J⁻¹ = s0J * (z⁻¹ * (z * k1J)) * s0J⁻¹ := by group
          _ = s0J * (z⁻¹ * (k1J * z)) * s0J⁻¹ := by rw [this]
          _ = (z * s0J⁻¹)⁻¹ * k1J * (z * s0J⁻¹) := by group
      have hcH : (⟨ck1J, ck1J_mem⟩ : HJ) =
          (⟨z * s0J⁻¹, hhH⟩ : HJ)⁻¹ * ⟨k1J, k1J_mem⟩ * ⟨z * s0J⁻¹, hhH⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hc
      have hθ : thetaJ ⟨ck1J, ck1J_mem⟩ =
          (thetaJ ⟨z * s0J⁻¹, hhH⟩)⁻¹ * thetaJ ⟨k1J, k1J_mem⟩ * thetaJ ⟨z * s0J⁻¹, hhH⟩ := by
        rw [hcH, map_mul thetaJ, map_mul thetaJ, map_inv thetaJ]
      set t := (thetaJ ⟨z * s0J⁻¹, hhH⟩ : Perm (Fin 12)) with ht
      have h7 : (thetaJ ⟨k1J, k1J_mem⟩ : Perm (Fin 12)) 7 = 7 := by
        apply Fin.ext
        rw [← theta_k1 7]
        exact pointwise_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hfix : (thetaJ ⟨ck1J, ck1J_mem⟩ : Perm (Fin 12)) (t⁻¹ 7) = t⁻¹ 7 := by
        rw [hθ]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, ← ht]
        rw [show t (t⁻¹ 7) = 7 from Equiv.apply_symm_apply t 7, h7]
      have hno := pointwise_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (t⁻¹ 7).val (t⁻¹ 7).isLt
      apply hno
      rw [theta_ck1 (t⁻¹ 7), hfix]
  have hs0 : α s0J = s0J := by
    have := hz1'
    rw [hz, mul_inv_eq_one] at this
    exact this
  have htop : fixAutSub α = ⊤ := by
    refine HJ_coatom.2 _ (lt_of_le_of_ne (fun h hh => hα h hh) fun he => ?_)
    have : s0J ∈ HJ := by rw [he]; exact hs0
    rw [mem_HJ_iff_fix, s0J_x0] at this
    exact x0_ne_y88 this.symm
  refine MulEquiv.ext fun g => ?_
  have : g ∈ fixAutSub α := by rw [htop]; trivial
  exact this


theorem ctuc_hn_alternating_stabilizer_pointwise_automorphism_centralizer_trivial :
    ∀ α : MulAut JH, (∀ h ∈ HJ, α h = h) → α = 1 :=
  eq_one_of_fix_HJ

end CFSG.Sporadic.HNSchreier
