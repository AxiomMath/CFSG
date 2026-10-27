module

public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import Certificates.Certificate8124
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Monster.B.Fischer.Fi22Order

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer
open scoped commutatorElement

theorem fi22FiveKeyPts_lt : ∀ p ∈ fi22FiveKeyPts, p < 3510 := by decide

theorem mem_fi22P_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hG : Rep 3510 g G)
    (h : siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 g = true) :
    G ∈ fi22P :=
  (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1 hG).1 h

theorem not_mem_fi22P_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hG : Rep 3510 g G)
    (h : siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 g = false) :
    G ∉ fi22P := fun hG' => by
  have := (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1 hG).2 hG'
  rw [h] at this
  exact Bool.false_ne_true this

theorem fi22FiveQ_le_P : fi22FiveQ ≤ fi22P :=
  Certificates.certificate8124.1.1.1

instance fi22FiveQ_isElementaryAbelian :
    IsElementaryAbelian 5 fi22FiveQ :=
  Certificates.certificate8124.1.1.2.1

theorem card_fi22FiveQ : Nat.card fi22FiveQ = 25 :=
  Certificates.certificate8124.1.1.2.2.1

theorem factorization_card_fi22P_five : (Nat.card fi22P).factorization 5 = 2 := by
  rw [card_fi22P, show (64561751654400 : ℕ) = 5 ^ 2 * 2582470066176 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem fi22FiveQ_sylow :
    ∃ S : Sylow 5 fi22P, (S : Subgroup fi22P) = fi22FiveQ.subgroupOf fi22P :=
  Certificates.certificate8124.1.1.2.2.2

theorem fi22FiveQ_lines :
    {H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i)) :=
  Certificates.certificate8124.1.2.1

theorem fi22FiveLine_zpowers (i : Fin 6) :
    Subgroup.zpowers (fi22FiveLine i) ≤ fi22FiveQ ∧
      Nat.card (Subgroup.zpowers (fi22FiveLine i)) = 5 := by
  have h : Subgroup.zpowers (fi22FiveLine i) ∈
      {H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} := by
    rw [fi22FiveQ_lines.1]
    exact ⟨i, rfl⟩
  exact h

theorem fi22FiveLine_mem_Q (i : Fin 6) : fi22FiveLine i ∈ fi22FiveQ :=
  (fi22FiveLine_zpowers i).1 (Subgroup.mem_zpowers _)

theorem orderOf_fi22FiveLine (i : Fin 6) : orderOf (fi22FiveLine i) = 5 := by
  rw [← Nat.card_zpowers]
  exact (fi22FiveLine_zpowers i).2

theorem fi22FiveLine_ne_one (i : Fin 6) : fi22FiveLine i ≠ 1 := fun h => by
  have := orderOf_fi22FiveLine i
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem fi22FiveLine_pow_five (i : Fin 6) : fi22FiveLine i ^ 5 = 1 := by
  rw [← orderOf_fi22FiveLine i]
  exact pow_orderOf_eq_one _

theorem fi22FiveLine_mem_P (i : Fin 6) : fi22FiveLine i ∈ fi22P :=
  fi22FiveQ_le_P (fi22FiveLine_mem_Q i)

theorem rep_qgen {k : ℕ} (hk : k < fi22FiveQGenArrs.size) :
    Rep 3510 fi22FiveQGenArrs[k]! (permOfArr 3510 fi22FiveQGenArrs[k]!) :=
  Certificates.certificate8124.2.2.1 k hk

theorem valid_qgen {k : ℕ} (hk : k < fi22FiveQGenArrs.size) :
    validA 3510 fi22FiveQGenArrs[k]! = true :=
  F2.validA_of_rep (rep_qgen hk)

theorem fi22FiveW_mem_R : fi22FiveW ∈ fi22R :=
  Certificates.certificate8124.1.2.2.1.1

theorem fi22FiveW_not_mem_P : fi22FiveW ∉ fi22P :=
  Certificates.certificate8124.1.2.2.1.2.1

theorem orderOf_fi22FiveW : orderOf fi22FiveW = 2 :=
  Certificates.certificate8124.1.2.2.1.2.2

theorem fi22FiveW_pow_two : fi22FiveW ^ 2 = 1 := by
  rw [← orderOf_fi22FiveW]
  exact pow_orderOf_eq_one _

theorem fi22FiveW_mul_self : fi22FiveW * fi22FiveW = 1 := by
  rw [← pow_two]
  exact fi22FiveW_pow_two

theorem fi22FiveW_ne_one : fi22FiveW ≠ 1 := fun h => by
  have := orderOf_fi22FiveW
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem fi22Five_mem_zpowers_sup_iff {G : Type*} [Group G] {x w : G} (hc : Commute x w)
    (hx : x ^ 5 = 1) (hw : w ^ 2 = 1) (g : G) :
    g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers w ↔ ∃ e < 5, ∃ f < 2, g = x ^ e * w ^ f := by
  have hmul : ∀ a b c d : ℕ, x ^ a * w ^ b * (x ^ c * w ^ d) = x ^ (a + c) * w ^ (b + d) :=
    fun a b c d => by
      rw [pow_add, pow_add, mul_assoc, ← mul_assoc (w ^ b), (hc.pow_pow c b).eq.symm]
      simp only [mul_assoc]
  have hred : ∀ a b : ℕ, x ^ a * w ^ b = x ^ (a % 5) * w ^ (b % 2) := fun a b => by
    conv_lhs => rw [← Nat.mod_add_div a 5, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul,
      pow_mul, hx, hw, one_pow, one_pow, mul_one, mul_one]
  constructor
  · intro hg
    suffices h : ∃ a b : ℕ, g = x ^ a * w ^ b by
      obtain ⟨a, b, rfl⟩ := h
      exact ⟨a % 5, Nat.mod_lt _ (by norm_num), b % 2, Nat.mod_lt _ (by norm_num), hred a b⟩
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨1, 0, by rw [Set.mem_singleton_iff.1 hy]; simp⟩
      · exact ⟨0, 1, by rw [Set.mem_singleton_iff.1 hy]; simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, b, rfl⟩ := hy
      obtain ⟨c, d, rfl⟩ := hz
      exact ⟨a + c, b + d, hmul a b c d⟩
    | inv y _ hy =>
      obtain ⟨a, b, rfl⟩ := hy
      refine ⟨4 * a, b, inv_eq_of_mul_eq_one_right ?_⟩
      have e1 : a + 4 * a = 5 * a := by ring
      have e2 : b + b = 2 * b := by ring
      rw [hmul, e1, e2, pow_mul, pow_mul, hx, hw, one_pow, one_pow, one_mul]
  · rintro ⟨e, -, f, -, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers _ e))
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers _ f))

theorem fi22FiveLineArr_zero : fi22FiveLineArr 0 = fi22FiveQ1Arr := by
  rw [fi22FiveLineArr, ite_eq_left (rfl : (0 : ℕ) = 0)]

theorem fi22FiveCGenArrs_zero (j : ℕ) : (fi22FiveCGenArrs j)[0]! = fi22FiveLineArr j := by
  simp [fi22FiveCGenArrs]

theorem fi22FiveCGenArrs_three (j : ℕ) : (fi22FiveCGenArrs j)[3]! = fi22FiveWArr := by
  simp [fi22FiveCGenArrs]

theorem fi22FiveDGenArrs_zero (j : ℕ) :
    (fi22FiveDGenArrs j)[0]! =
      commutatorA 3510 (fi22FiveCGenArrs j)[1]! (fi22FiveCGenArrs j)[2]! := by
  rw [fi22FiveDGenArrs]
  simp

theorem fi22FiveDGenArrs_size (j : ℕ) : (fi22FiveDGenArrs j).size = 2 := by
  simp [fi22FiveDGenArrs]

theorem fi22FiveDGenArrs_one (j : ℕ) : (fi22FiveDGenArrs j)[1]! = (fi22FiveCGenArrs j)[2]! := by
  rw [fi22FiveDGenArrs]
  simp

section Record

variable (i : Fin 6)

theorem rep_cgen {k : ℕ} (hk : k < 4) :
    Rep 3510 (fi22FiveCGenArrs i)[k]! (permOfArr 3510 (fi22FiveCGenArrs i)[k]!) :=
  (Certificates.certificate8124.2.2.2 i).1 k hk

theorem valid_cgen {k : ℕ} (hk : k < 4) : validA 3510 (fi22FiveCGenArrs i)[k]! = true :=
  F2.validA_of_rep (rep_cgen i hk)

theorem valid_dgen {l : ℕ} (hl : l < 2) : validA 3510 (fi22FiveDGenArrs i)[l]! = true := by
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · rw [fi22FiveDGenArrs_zero]
    exact F2.validA_of_rep
      (rep_commutatorA (valid_cgen i (by norm_num)) (valid_cgen i (by norm_num)))
  · rw [fi22FiveDGenArrs_one]
    exact valid_cgen i (by norm_num)

theorem rep_dgen {l : ℕ} (hl : l < 2) :
    Rep 3510 (fi22FiveDGenArrs i)[l]! (permOfArr 3510 (fi22FiveDGenArrs i)[l]!) :=
  rep_of_validA (valid_dgen i hl)

theorem rep_fi22FiveLine : Rep 3510 (fi22FiveLineArr i) (fi22FiveLine i) := by
  have h := rep_cgen i (k := 0) (by norm_num)
  rw [fi22FiveCGenArrs_zero] at h
  exact h

theorem rep_fi22FiveW : Rep 3510 fi22FiveWArr fi22FiveW := by
  have h := rep_cgen 0 (k := 3) (by norm_num)
  rw [fi22FiveCGenArrs_three] at h
  exact h

theorem cgen_zero : permOfArr 3510 (fi22FiveCGenArrs i)[0]! = fi22FiveLine i := by
  rw [fi22FiveCGenArrs_zero]
  rfl

theorem cgen_three : permOfArr 3510 (fi22FiveCGenArrs i)[3]! = fi22FiveW := by
  rw [fi22FiveCGenArrs_three]
  rfl

theorem cgen_mem {k : ℕ} (hk : k < 4) : permOfArr 3510 (fi22FiveCGenArrs i)[k]! ∈ fi22FiveC i :=
  Subgroup.subset_closure (mem_permsA hk)

theorem fi22FiveLine_mem_C : fi22FiveLine i ∈ fi22FiveC i := by
  rw [← cgen_zero i]
  exact cgen_mem i (by norm_num)

theorem fi22FiveW_mem_C : fi22FiveW ∈ fi22FiveC i := by
  rw [← cgen_three i]
  exact cgen_mem i (by norm_num)

theorem cgen_mem_P {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 3) :
    permOfArr 3510 (fi22FiveCGenArrs i)[k]! ∈ fi22P :=
  (Certificates.certificate8124.2.2.2 i).2.1 k hk1 hk

theorem fi22FiveC_eq : fi22FiveC i = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22R :=
  (Certificates.certificate8124.1.2.2.2 i).1

theorem card_fi22FiveC : Nat.card (fi22FiveC i) = 1200 :=
  (Certificates.certificate8124.1.2.2.2 i).2.1

theorem fi22FiveC_inf_P :
    fi22FiveC i ⊓ fi22P = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22P :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.1

theorem card_fi22FiveC_inf_P : Nat.card (fi22FiveC i ⊓ fi22P : Subgroup _) = 600 :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.1

theorem fi22FiveD_le_P : fi22FiveD i ≤ fi22P :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.1

theorem fi22FiveD_isSimpleGroup : IsSimpleGroup (fi22FiveD i) :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.1

theorem fi22FiveD_nonabelian : ∃ g ∈ fi22FiveD i, ∃ h ∈ fi22FiveD i, g * h ≠ h * g :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.1

theorem card_fi22FiveD : Nat.card (fi22FiveD i) = 60 :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.1

theorem fi22FiveW_mem_center :
    fi22FiveW ∈ (Subgroup.center (fi22FiveC i)).map (fi22FiveC i).subtype :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.2.1

theorem fi22FiveCentD_eq :
    Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i =
      Subgroup.zpowers (fi22FiveLine i) ⊔ Subgroup.zpowers fi22FiveW :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.2.2.1

theorem fi22FiveLine_inf_W :
    Subgroup.zpowers (fi22FiveLine i) ⊓ Subgroup.zpowers fi22FiveW = ⊥ :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.2.2.2.1

theorem fi22FiveLine_commute_W : Commute (fi22FiveLine i) fi22FiveW :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.2.2.2.2.1

theorem card_fi22FiveCentD :
    Nat.card (Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i :
      Subgroup (Equiv.Perm (Fin 3510))) = 10 :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fi22FiveCentDP_eq :
    Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ (fi22FiveC i ⊓ fi22P) =
      Subgroup.zpowers (fi22FiveLine i) :=
  (Certificates.certificate8124.1.2.2.2 i).2.2.2.2.2.2.2.2.2.2.2.2.2

theorem fi22FiveD_eq : fi22FiveD i = Subgroup.closure (permsA 3510 (fi22FiveDGenArrs i)) :=
  (Certificates.certificate8124.2.2.2 i).2.2

theorem fi22FiveH_mem_P : permOfArr 3510 (fi22FiveHArr i) ∈ fi22P :=
  (Certificates.certificate8124.2.1 i).1

theorem fi22FiveH_conj :
    permOfArr 3510 (fi22FiveHArr i) * fi22FiveLine i * (permOfArr 3510 (fi22FiveHArr i))⁻¹ =
      fi22FiveLine 0 :=
  (Certificates.certificate8124.2.1 i).2

theorem card_centralizer_fi22FiveLine_le :
    Nat.card (Subgroup.centralizer {fi22FiveLine i} ⊓ fi22P : Subgroup _) ≤ 600 := by
  rw [← fi22FiveC_inf_P i, card_fi22FiveC_inf_P i]

theorem fi22FiveC_le : fi22FiveC i ≤ Subgroup.centralizer {fi22FiveLine i} ⊓ fi22R :=
  (fi22FiveC_eq i).le

theorem cgen_mem_R {k : ℕ} (hk : k < 4) : permOfArr 3510 (fi22FiveCGenArrs i)[k]! ∈ fi22R :=
  (Subgroup.mem_inf.1 (fi22FiveC_le i (cgen_mem i hk))).2

theorem fi22FiveC_le_centralizer_line : fi22FiveC i ≤ Subgroup.centralizer {fi22FiveLine i} :=
  fun _ hg => (Subgroup.mem_inf.1 (fi22FiveC_le i hg)).1

theorem fi22FiveC_le_centralizer_W : fi22FiveC i ≤ Subgroup.centralizer {fi22FiveW} := by
  intro g hg
  obtain ⟨z, hz, hzw⟩ := fi22FiveW_mem_center i
  rw [Subgroup.mem_centralizer_singleton_iff, ← hzw]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)

theorem fi22FiveW_comm_line : fi22FiveW * fi22FiveLine i = fi22FiveLine i * fi22FiveW :=
  (fi22FiveLine_commute_W i).eq.symm

theorem dgen_zero : permOfArr 3510 (fi22FiveDGenArrs i)[0]! =
    ⁅permOfArr 3510 (fi22FiveCGenArrs i)[1]!, permOfArr 3510 (fi22FiveCGenArrs i)[2]!⁆ := by
  rw [fi22FiveDGenArrs_zero]
  exact permOfArr_eq_of_rep (rep_commutatorA (valid_cgen i (by norm_num))
    (valid_cgen i (by norm_num)))

theorem dgen_one : permOfArr 3510 (fi22FiveDGenArrs i)[1]! =
    permOfArr 3510 (fi22FiveCGenArrs i)[2]! := by
  rw [fi22FiveDGenArrs_one]

theorem fi22FiveD_le_C : fi22FiveD i ≤ fi22FiveC i := by
  rw [fi22FiveD, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact (fi22FiveC i).mul_mem ((fi22FiveC i).mul_mem ((fi22FiveC i).mul_mem ha hb)
    ((fi22FiveC i).inv_mem ha)) ((fi22FiveC i).inv_mem hb)

theorem mem_centralizer_fi22FiveD_iff (g : Equiv.Perm (Fin 3510)) :
    g ∈ Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i ↔
      ∃ e < 5, ∃ f < 2, g = fi22FiveLine i ^ e * fi22FiveW ^ f := by
  rw [fi22FiveCentD_eq i]
  exact fi22Five_mem_zpowers_sup_iff (fi22FiveLine_commute_W i) (fi22FiveLine_pow_five i)
    fi22FiveW_pow_two g

end Record

theorem R3E_Fi22_full_five_centralizers_common_outer_involution :
    (fi22FiveQ ≤ fi22P ∧ IsElementaryAbelian 5 fi22FiveQ ∧ Nat.card fi22FiveQ = 25 ∧
      ∃ S : Sylow 5 fi22P, (S : Subgroup fi22P) = fi22FiveQ.subgroupOf fi22P) ∧
    ({H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i))) ∧
    (fi22FiveW ∈ fi22R ∧ fi22FiveW ∉ fi22P ∧ orderOf fi22FiveW = 2) ∧
    ∀ i : Fin 6,
      fi22FiveC i = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22R ∧
      Nat.card (fi22FiveC i) = 1200 ∧
      fi22FiveC i ⊓ fi22P = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22P ∧
      Nat.card (fi22FiveC i ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) = 600 ∧
      fi22FiveD i ≤ fi22P ∧ IsSimpleGroup (fi22FiveD i) ∧
      (∃ g ∈ fi22FiveD i, ∃ h ∈ fi22FiveD i, g * h ≠ h * g) ∧ Nat.card (fi22FiveD i) = 60 ∧
      fi22FiveW ∈ (Subgroup.center (fi22FiveC i)).map (fi22FiveC i).subtype ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i =
        Subgroup.zpowers (fi22FiveLine i) ⊔ Subgroup.zpowers fi22FiveW ∧
      Subgroup.zpowers (fi22FiveLine i) ⊓ Subgroup.zpowers fi22FiveW = ⊥ ∧
      Commute (fi22FiveLine i) fi22FiveW ∧
      Nat.card (Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i :
        Subgroup (Equiv.Perm (Fin 3510))) = 10 ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ (fi22FiveC i ⊓ fi22P) =
        Subgroup.zpowers (fi22FiveLine i) :=
  Certificates.certificate8124.1

end CFSG.RankThree.Native
