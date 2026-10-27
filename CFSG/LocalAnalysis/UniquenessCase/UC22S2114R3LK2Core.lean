module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LTFullSigmaCore
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofL4
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLTools
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Syl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUPerm
public import CFSG.Goldschmidt.Steps.Sec87b
import all CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
public import CFSG.RankThree.PartOne.KFOUT3.CycUnits
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.RankThree.PartOne.SRC.ModelL4Two
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.Blueprint Matrix Module
open CFSG.RankThree.PartTwo.Sec4

section TracePair

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_trace_one_pair_of_elemAbelian_sl_four
    (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    (E : Subgroup (SpecialLinearGroup (Fin 4) K))
    (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    ∃ a ∈ E, ∃ b ∈ E, orderOf a = 3 ∧ orderOf b = 3 ∧
      b ∉ zpowers a ∧ E = zpowers a ⊔ zpowers b ∧
      ∀ x ∈ E, trace (x : Matrix (Fin 4) (Fin 4) K) = 1 ↔
        x = a ∨ x = a⁻¹ ∨ x = b ∨ x = b⁻¹ := by
  classical
  let ρ : SpecialLinearGroup (Fin 4) K → (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    fun g => (SpecialLinearGroup.toLin' g).toLinearMap
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := by
    intro g h
    ext v
    simp [ρ, map_mul, Module.End.mul_apply]
  have hone : ρ 1 = 1 := by ext v; simp [ρ]
  have hinj : ∀ g, ρ g = 1 → g = 1 := by
    intro g h
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    simpa [ρ] using congrArg (fun f : Module.End K (Fin 4 → K) => f v) h
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, ha, b, hb, u, w, hAA, hAw, hABw, hBu, hBAu, hBB, hli⟩ :=
    Item424Res5.exists_blockBasis_sl (by simp) (by
      rw [show (3 : K) = 2 + 1 by ring, CharTwo.two_eq_zero, zero_add]
      exact one_ne_zero)
      hK ρ hmul hone hinj hcomm hEe.2 hEc
  let bs := Item424Res5.blockBasis hli (by simp)
  have hbs : ∀ i, bs i = ![u, ρ a u, w, ρ b w] i := by
    intro i
    exact congrFun (Item424Res5.coe_blockBasis hli (by simp)) i
  have hAA' : ρ a (ρ a u) = -u - ρ a u := by
    rw [← sub_eq_zero]
    rw [← hAA]
    abel
  have hBB' : ρ b (ρ b w) = -w - ρ b w := by
    rw [← sub_eq_zero]
    rw [← hBB]
    abel
  have hu : bs.repr u = Finsupp.single 0 1 := by
    have h := bs.repr_self 0
    rwa [hbs] at h
  have hau : bs.repr (ρ a u) = Finsupp.single 1 1 := by
    have h := bs.repr_self 1
    rwa [hbs] at h
  have hw : bs.repr w = Finsupp.single 2 1 := by
    have h := bs.repr_self 2
    rwa [hbs] at h
  have hbw : bs.repr (ρ b w) = Finsupp.single 3 1 := by
    have h := bs.repr_self 3
    rwa [hbs] at h
  let A : Matrix (Fin 4) (Fin 4) K :=
    !![0, -1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  let B : Matrix (Fin 4) (Fin 4) K :=
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, -1]
  have hA : LinearMap.toMatrix bs bs (ρ a) = A := by
    ext i j
    rw [LinearMap.toMatrix_apply, hbs]
    fin_cases j
    · change (bs.repr (ρ a u)) i = A i 0
      rw [hau]
      fin_cases i <;> simp [A]
    · change (bs.repr (ρ a (ρ a u))) i = A i 1
      rw [hAA', map_sub, map_neg, hu, hau]
      fin_cases i <;> simp [A]
    · change (bs.repr (ρ a w)) i = A i 2
      rw [hAw, hw]
      fin_cases i <;> simp [A]
    · change (bs.repr (ρ a (ρ b w))) i = A i 3
      rw [hABw, hbw]
      fin_cases i <;> simp [A]
  have hB : LinearMap.toMatrix bs bs (ρ b) = B := by
    ext i j
    rw [LinearMap.toMatrix_apply, hbs]
    fin_cases j
    · change (bs.repr (ρ b u)) i = B i 0
      rw [hBu, hu]
      fin_cases i <;> simp [B]
    · change (bs.repr (ρ b (ρ a u))) i = B i 1
      rw [hBAu, hau]
      fin_cases i <;> simp [B]
    · change (bs.repr (ρ b w)) i = B i 2
      rw [hbw]
      fin_cases i <;> simp [B]
    · change (bs.repr (ρ b (ρ b w))) i = B i 3
      rw [hBB', map_sub, map_neg, hw, hbw]
      fin_cases i <;> simp [B]
  have hpairTrace : ∀ i j : Fin 3,
      trace ((a ^ (i : ℕ) * b ^ (j : ℕ) : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 ↔
      (i ≠ 0 ∧ j = 0) ∨ (i = 0 ∧ j ≠ 0) := by
    intro i j
    have htr : trace ((a ^ (i : ℕ) * b ^ (j : ℕ) : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = trace (A ^ (i : ℕ) * B ^ (j : ℕ)) := by
      rw [← Matrix.trace_toLin'_eq]
      change LinearMap.trace K (Fin 4 → K) (ρ (a ^ (i : ℕ) * b ^ (j : ℕ))) = _
      rw [LinearMap.trace_eq_matrix_trace K bs, hmul]
      have hpow : ∀ g k, ρ (g ^ k) = (ρ g) ^ k := by
        intro g k
        induction k with
        | zero => exact hone
        | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
      rw [hpow, hpow, LinearMap.toMatrix_mul, ← LinearMap.toMatrix_pow,
        ← LinearMap.toMatrix_pow, hA, hB]
    rw [htr]
    have h4 : (4 : K) = 0 := by linear_combination 2 * CharTwo.two_eq_zero (R := K)
    fin_cases i <;> fin_cases j <;>
      simp [A, B, trace, Fin.sum_univ_four, pow_two,
        CharTwo.neg_eq, CharTwo.add_self_eq_zero, h4]
  have ha1 : a ≠ 1 := by
    intro h
    have htr := (hpairTrace 1 0).mpr (Or.inl ⟨by decide, rfl⟩)
    have h4 : (4 : K) = 0 := by linear_combination 2 * CharTwo.two_eq_zero (R := K)
    simp [h, trace, h4] at htr
  have hb1 : b ≠ 1 := by
    intro h
    have htr := (hpairTrace 0 1).mpr (Or.inr ⟨rfl, by decide⟩)
    have h4 : (4 : K) = 0 := by linear_combination 2 * CharTwo.two_eq_zero (R := K)
    simp [h, trace, h4] at htr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haord : orderOf a = 3 := orderOf_eq_prime (hEe.2 a ha) ha1
  have hbord : orderOf b = 3 := orderOf_eq_prime (hEe.2 b hb) hb1
  have hnot : b ∉ zpowers a := by
    intro h
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp h)
    rw [Finset.mem_range] at hk
    rw [haord] at hk
    have hk2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk2 with rfl | rfl | rfl
    · simp at heq
      exact hb1 heq.symm
    · simp only [pow_one] at heq
      have tr := (hpairTrace 1 1).not.mpr (by simp)
      rw [heq, ← pow_two] at tr
      exact tr (by simpa using (hpairTrace 0 2).mpr (by simp))
    · have hfix : ρ b u = u := hBu
      rw [← heq] at hfix
      have hpow2 : ρ (a ^ 2) u = ρ a (ρ a u) := by rw [pow_two, hmul]; rfl
      rw [hpow2] at hfix
      have h0 : u + ρ a u + u = 0 := by rwa [hfix] at hAA
      have hau0 : ρ a u = 0 := by
        have hz : u + u = 0 := CharTwo.add_self_eq_zero u
        linear_combination (norm := module) h0 - hz
      exact (hli.ne_zero 1) hau0
  obtain ⟨-, hjoinCard⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair
    Nat.prime_three haord hbord hnot (hcomm a ha b hb)
  have hjoin : E = zpowers a ⊔ zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb))
      (by rw [hEc, hjoinCard]; norm_num)).symm
  refine ⟨a, ha, b, hb, haord, hbord, hnot, hjoin, ?_⟩
  intro x hx
  have hnorm : zpowers b ≤ normalizer (zpowers a : Set _) := by
    have hc : zpowers b ≤ centralizer (zpowers a : Set _) := by
      rw [zpowers_le, mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hcomm a ha b hb) k).eq
    exact hc.trans (centralizer_le_normalizer _)
  rw [hjoin] at hx
  change x ∈ ((zpowers a ⊔ zpowers b : Subgroup (SpecialLinearGroup (Fin 4) K)) : Set _) at hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx1)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx2)
  rw [Finset.mem_range] at hi hj
  rw [haord] at hi
  rw [hbord] at hj
  have h3a := hEe.2 a ha
  have h3b := hEe.2 b hb
  have hia : a ^ 2 = a⁻¹ := by apply mul_right_cancel (b := a); rw [← pow_succ, h3a, inv_mul_cancel]
  have hib : b ^ 2 = b⁻¹ := by apply mul_right_cancel (b := b); rw [← pow_succ, h3b, inv_mul_cancel]
  constructor
  · intro ht
    rcases (hpairTrace ⟨i, hi⟩ ⟨j, hj⟩).mp ht with ⟨hi0, hj0⟩ | ⟨hi0, hj0⟩
    · have hj' : j = 0 := congrArg Fin.val hj0
      subst j
      have hi' : i = 1 ∨ i = 2 := by
        have hi0' : i ≠ 0 := by intro h; apply hi0; exact Fin.ext h
        omega
      rcases hi' with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (by simp [hia]))
    · have hi' : i = 0 := congrArg Fin.val hi0
      subst i
      have hj' : j = 1 ∨ j = 2 := by
        have hj0' : j ≠ 0 := by intro h; apply hj0; exact Fin.ext h
        omega
      rcases hj' with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by simp)))
      · exact Or.inr (Or.inr (Or.inr (by simp [hib])))
  · rintro (h | h | h | h)
    · rw [h]
      simpa using (hpairTrace 1 0).mpr (by simp)
    · rw [h]
      simpa [hia] using (hpairTrace 2 0).mpr (by simp)
    · rw [h]
      simpa using (hpairTrace 0 1).mpr (by simp)
    · rw [h]
      simpa [hib] using (hpairTrace 0 2).mpr (by simp)

end TracePair

section PairAction

variable {X : Type} [Group X]

theorem fixes_pair_of_odd_order_of_inverse_pair
    (α : MulAut X) {a b : X} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hnot : b ∉ zpowers a) (hα : Odd (orderOf α))
    (hA : α a = a ∨ α a = a⁻¹ ∨ α a = b ∨ α a = b⁻¹)
    (hB : α b = a ∨ α b = a⁻¹ ∨ α b = b ∨ α b = b⁻¹) :
    α a = a ∧ α b = b := by
  classical
  let f : Fin 4 → X := ![a, a⁻¹, b, b⁻¹]
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; omega
  have haInv : a ≠ a⁻¹ := by
    intro h
    have h2 : a ^ 2 = 1 := by
      calc a ^ 2 = a * a := pow_two a
        _ = a * a⁻¹ := congrArg (fun x => a * x) h
        _ = 1 := mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h2
    rw [ha] at this
    norm_num at this
  have hbInv : b ≠ b⁻¹ := by
    intro h
    have h2 : b ^ 2 = 1 := by
      calc b ^ 2 = b * b := pow_two b
        _ = b * b⁻¹ := congrArg (fun x => b * x) h
        _ = 1 := mul_inv_cancel b
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hb] at this
    norm_num at this
  have hbA : b ≠ a := fun h => hnot (h ▸ mem_zpowers a)
  have hbAi : b ≠ a⁻¹ := fun h => hnot (h ▸ (zpowers a).inv_mem (mem_zpowers a))
  have hbiA : b⁻¹ ≠ a := fun h => hbAi (by rw [← inv_inv b, h])
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;>
      first | exact haInv h | exact haInv h.symm | exact hbInv h | exact hbInv h.symm |
        exact hbA h | exact hbA h.symm | exact hbAi h | exact hbAi h.symm |
        exact hbiA h | exact hbiA h.symm
  have hmem : ∀ i : Fin 4, ∃ j : Fin 4, α (f i) = f j := by
    intro i
    fin_cases i
    · rcases hA with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    · rcases hA with h | h | h | h
      · exact ⟨1, by simpa [f] using congrArg Inv.inv h⟩
      · exact ⟨0, by simpa [f] using congrArg Inv.inv h⟩
      · exact ⟨3, by simpa [f] using congrArg Inv.inv h⟩
      · exact ⟨2, by simpa [f] using congrArg Inv.inv h⟩
    · rcases hB with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    · rcases hB with h | h | h | h
      · exact ⟨1, by simpa [f] using congrArg Inv.inv h⟩
      · exact ⟨0, by simpa [f] using congrArg Inv.inv h⟩
      · exact ⟨3, by simpa [f] using congrArg Inv.inv h⟩
      · exact ⟨2, by simpa [f] using congrArg Inv.inv h⟩
  choose g hg using hmem
  have hgInj : Function.Injective g := by
    intro i j h
    apply hf
    apply α.injective
    rw [hg, hg, h]
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective g
    ⟨hgInj, Finite.surjective_of_injective hgInj⟩
  have hσ : ∀ i, α (f i) = f (σ i) := hg
  let τ := CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore.fourRep
  have hτ : ∀ i : Fin 4, f (τ i) = (f i)⁻¹ := by
    intro i
    fin_cases i <;>
      simp [τ, CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore.fourRep, f,
        Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  have hcomm : σ * τ = τ * σ := by
    apply Equiv.ext
    intro i
    apply hf
    change f (σ (τ i)) = f (τ (σ i))
    rw [← hσ, hτ, map_inv, hσ, hτ]
  have hσ4 : σ ^ 4 = 1 :=
    CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore.perm4_pow_four_of_commute σ hcomm
  have hα4 : ∀ i, (α ^ 4) (f i) = f i := by
    have hpow : ∀ n : ℕ, ∀ i, (α ^ n) (f i) = f ((σ ^ n) i) := by
      intro n
      induction n with
      | zero => intro i; rfl
      | succ n ih => intro i; rw [pow_succ, MulAut.mul_apply, hσ, ih, pow_succ, Equiv.Perm.mul_apply]
    intro i
    rw [hpow, hσ4]
    rfl
  have hfix : ∀ i, α (f i) = f i := by
    intro i
    have hm : Function.IsPeriodicPt α 4 (f i) := by
      have hpow : ∀ n : ℕ, ∀ x, α^[n] x = (α ^ n) x := by
        intro n
        induction n with
        | zero => intro x; rfl
        | succ n ih => intro x; rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
      change α^[4] (f i) = f i
      rw [hpow]
      exact hα4 i
    have hn : Function.IsPeriodicPt α (orderOf α) (f i) := by
      have hpow : ∀ n : ℕ, ∀ x, α^[n] x = (α ^ n) x := by
        intro n
        induction n with
        | zero => intro x; rfl
        | succ n ih => intro x; rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]
      change α^[orderOf α] (f i) = f i
      rw [hpow, pow_orderOf_eq_one]
      rfl
    have hd := hm.gcd hn
    have hcop : Nat.Coprime 4 (orderOf α) := by
      rw [show 4 = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
      exact Nat.coprime_two_left.mpr hα
    rw [hcop.gcd_eq_one] at hd
    change α^[1] (f i) = f i at hd
    simpa using hd
  exact ⟨hfix 0, hfix 2⟩

end PairAction

section OddNormalizer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_trace_transport_of_odd_sl_four
    (α : MulAut (SpecialLinearGroup (Fin 4) K)) (hα : Odd (orderOf α)) :
    ∃ σ : K ≃+* K, ∀ x : SpecialLinearGroup (Fin 4) K,
      trace (α x : Matrix (Fin 4) (Fin 4) K) = σ (trace (x : Matrix (Fin 4) (Fin 4) K)) := by
  let e : SpecialLinearGroup (Fin 4) K ≃* ProjectiveSpecialLinearGroup (Fin 4) K :=
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.RankThree.PartOne.center_SL4_eq_bot (F := K))).trans QuotientGroup.quotientBot).symm
  let β := MulAut.congr e α
  have hβ : Odd (orderOf β) := by
    rwa [show orderOf β = orderOf α from (MulAut.congr e).orderOf_eq α]
  obtain ⟨A, σ, hβeq⟩ :=
    CFSG.ComponentClassification.Foote5.OddLieCore.exists_semilinear_of_odd
      (n := 4) (by norm_num) hβ
  refine ⟨σ, fun x => ?_⟩
  have hx : α x =
      CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction 4 K A σ x := by
    apply e.injective
    have h := congrArg (fun f : MulAut (ProjectiveSpecialLinearGroup (Fin 4) K) => f (e x)) hβeq
    have hβx : β (e x) = e (α x) := by
      change e (α (e.symm (e x))) = _
      rw [e.symm_apply_apply]
    change β (e x) = _ at h
    rw [hβx] at h
    have hmk : e x = QuotientGroup.mk' (center (SpecialLinearGroup (Fin 4) K)) x := by
      change QuotientGroup.mk x = _
      rfl
    rw [hmk] at h
    rw [CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction_mk] at h
    change QuotientGroup.mk' (center (SpecialLinearGroup (Fin 4) K)) (α x) = _ at h
    exact h
  rw [hx, CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction_matrix,
    Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  simp [trace, map_sum]

theorem fixes_elemAbelian_nine_of_odd_sl_four
    (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    {E : Subgroup (SpecialLinearGroup (Fin 4) K)}
    (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (α : MulAut (SpecialLinearGroup (Fin 4) K)) (hα : Odd (orderOf α))
    (hαE : ∀ x ∈ E, α x ∈ E) : ∀ x ∈ E, α x = x := by
  obtain ⟨a, ha, b, hb, haord, hbord, hnot, hjoin, htrace⟩ :=
    exists_trace_one_pair_of_elemAbelian_sl_four hK E hEe hEc
  obtain ⟨σ, hσ⟩ := exists_trace_transport_of_odd_sl_four α hα
  have hA := (htrace (α a) (hαE a ha)).mp (by
    rw [hσ, (htrace a ha).mpr (Or.inl rfl), map_one])
  have hB := (htrace (α b) (hαE b hb)).mp (by
    rw [hσ, (htrace b hb).mpr (Or.inr (Or.inr (Or.inl rfl))), map_one])
  obtain ⟨hfa, hfb⟩ := fixes_pair_of_odd_order_of_inverse_pair α haord hbord hnot hα hA hB
  let C : Subgroup (SpecialLinearGroup (Fin 4) K) :=
    { carrier := {x | α x = x}
      one_mem' := map_one α
      mul_mem' := fun {x y} hx hy => by
        change α (x * y) = x * y
        rw [map_mul, hx, hy]
      inv_mem' := fun {x} hx => by
        change α x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have hle : E ≤ C := by
    rw [hjoin]
    exact sup_le (zpowers_le.mpr hfa) (zpowers_le.mpr hfb)
  exact fun x hx => hle hx

end OddNormalizer

section LieTransport

theorem fixes_elemAbelian_nine_of_odd_lieModel_psl_four
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : LieModel X .PSL 4 2 f) (hf : Odd f)
    {E : Subgroup X} (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (α : MulAut X) (hα : Odd (orderOf α)) (hαE : ∀ x ∈ E, α x ∈ E) :
    ∀ x ∈ E, α x = x := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let eSL : X ≃* SpecialLinearGroup (Fin 4) K := e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.RankThree.PartOne.center_SL4_eq_bot (F := K))).trans QuotientGroup.quotientBot))
  let β := MulAut.congr eSL α
  have hβ : Odd (orderOf β) := by rwa [(MulAut.congr eSL).orderOf_eq α]
  have hmapCard : Nat.card (E.map eSL.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective eSL.injective, hEc]
  have hβE : ∀ x ∈ E.map eSL.toMonoidHom, β x ∈ E.map eSL.toMonoidHom := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨α x, hαE x hx, ?_⟩
    change eSL (α x) = eSL (α (eSL.symm (eSL x)))
    rw [eSL.symm_apply_apply]
  have hno : ∀ c : K, c ^ 2 + c + 1 ≠ 0 :=
    CFSG.RankThree.PartOne.KFOUT3.quad_ne_zero (by
      have hmod : Nat.card K % 3 = 2 := by rw [hK]; exact CFSG.two_pow_mod_three_of_odd hf
      omega)
  have hfix := fixes_elemAbelian_nine_of_odd_sl_four hno (hEe.map eSL.toMonoidHom)
    hmapCard β hβ hβE
  intro x hx
  apply eSL.injective
  have h := hfix (eSL x) (Subgroup.mem_map_of_mem _ hx)
  change eSL (α (eSL.symm (eSL x))) = eSL x at h
  rwa [eSL.symm_apply_apply] at h

end LieTransport

section SylowPlane

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {G : Type} [Group G] [Finite G]

theorem commute_of_isPGroup_lieModel_psl_four_odd
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : LieModel X .PSL 4 2 f) (hf : Odd f)
    {P : Subgroup X} (hP : IsPGroup 3 P) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let eSL : X ≃* SpecialLinearGroup (Fin 4) K := e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.RankThree.PartOne.center_SL4_eq_bot (F := K))).trans QuotientGroup.quotientBot))
  let ψ := SpecialLinearGroup.toGL.comp eSL.toMonoidHom
  have hinj : Function.Injective ψ := SpecialLinearGroup.toGL_injective.comp eSL.injective
  have hcomm := CFSG.RankThree.PartTwo.Sec4.Ronan148L.comm_of_isPGroup_GL4
    (by rw [hK]; exact CFSG.two_pow_mod_three_of_odd hf) (P.map ψ) (hP.map ψ)
  intro a ha b hb
  apply hinj
  rw [map_mul, map_mul]
  exact hcomm _ (Subgroup.mem_map_of_mem _ ha) _ (Subgroup.mem_map_of_mem _ hb)

theorem exists_central_elemAbelian_nine_of_sylow_intersection
    {M L R : Subgroup G} (_hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ L) L)
    {f : ℕ} (hX : LieModel (Bar2 L) .PSL 4 2 f) (hf : Odd f)
    (hRank : CFSG.Open.pRank 3 L = 2) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q := R ⊓ L
  let π : L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 L)
  have hQL : Q ≤ L := inf_le_right
  have hQr : IsPGroup 3 Q := hQ.isPGroup
  have hOr : ¬ 3 ∣ Nat.card (CFSG.pCore 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup Nat.prime_three (by norm_num)
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
    (N := CFSG.pCore 2 L) hOr hQr.comap_subtype
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    let aL : L := ⟨a, hQL ha⟩
    let bL : L := ⟨b, hQL hb⟩
    have hmap := commute_of_isPGroup_lieModel_psl_four_odd hX hf
      (hQr.comap_subtype.map π) (π aL) (Subgroup.mem_map_of_mem π ha)
      (π bL) (Subgroup.mem_map_of_mem π hb)
    have h1 : (⟨aL, ha⟩ : Q.subgroupOf L) * ⟨bL, hb⟩ =
        (⟨bL, hb⟩ : Q.subgroupOf L) * ⟨aL, ha⟩ := by
      apply hinj
      change π (aL * bL) = π (bL * aL)
      rwa [map_mul, map_mul]
    exact congrArg (fun x : Q.subgroupOf L => (x : G)) h1
  have hQrank : CFSG.Open.pRank 3 Q = 2 :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.pRank_eq_of_isSylowOf hQ).trans hRank
  obtain ⟨E, hEQ, hEcomm, hEpow, hEc, hmax⟩ :=
    CFSG.Goldschmidt.Sec8.exists_omega1 Nat.prime_three hQcomm hQrank
  have hEe : IsElemAbelian 3 E := ⟨hEcomm, hEpow⟩
  have hEL : E ≤ L := hEQ.trans hQL
  have hER : E ≤ R := hEQ.trans inf_le_left
  have hRE : R ≤ normalizer (E : Set G) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hconR : r * x * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr (hER hx)) (R.inv_mem hr)
      have hconL : r * x * r⁻¹ ∈ L :=
        (mem_normalizer_iff.mp (hML (hR.le hr)) x).mp (hEL hx)
      apply hmax _ ⟨hconR, hconL⟩
      have hp := congrArg (MulAut.conj r) (hEpow x hx)
      simpa [MulAut.conj_apply, map_pow] using hp
    · intro hx
      have hrL : r⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem (hML (hR.le hr))
      have hconR : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ ∈ R :=
        R.mul_mem (R.mul_mem (R.inv_mem hr) (hER hx)) (by simpa using hr)
      have hconL : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ ∈ L :=
        (mem_normalizer_iff.mp hrL _).mp (hEL hx)
      have heq : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ = x := by group
      apply hmax
      · rw [heq] at hconR hconL
        exact ⟨hconR, hconL⟩
      · have hp := congrArg (MulAut.conj r⁻¹) (hEpow _ hx)
        rw [show MulAut.conj r⁻¹ ((r * x * r⁻¹) ^ 3) =
          (MulAut.conj r⁻¹ (r * x * r⁻¹)) ^ 3 from map_pow _ _ _] at hp
        have heq' : MulAut.conj r⁻¹ (r * x * r⁻¹) = x := by
          rw [MulAut.conj_apply]
          group
        rw [heq'] at hp
        simpa using hp
  let Ebar := (E.subgroupOf L).map π
  have hEbare : IsElemAbelian 3 Ebar := (hEe.comap L.subtype_injective).map π
  have hEbarc : Nat.card Ebar = 9 := by
    have hi : Function.Injective (π.comp (E.subgroupOf L).subtype) := by
      intro x y h
      have heq := hinj (show π.comp (Q.subgroupOf L).subtype ⟨x, hEQ x.2⟩ =
        π.comp (Q.subgroupOf L).subtype ⟨y, hEQ y.2⟩ from h)
      apply Subtype.ext
      have heq' : (x : L) = (y : L) := congrArg (fun x : Q.subgroupOf L => (x : L)) heq
      exact heq'
    have hrange : Ebar = (π.comp (E.subgroupOf L).subtype).range := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [hrange,
      ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hEc]
    norm_num
  have hEC : E ≤ centralizer (R : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro r hr
    let α := rhoL L ⟨r, hML (hR.le hr)⟩
    have hα : Odd (orderOf α) := by
      obtain ⟨k, hk⟩ := hR.isPGroup ⟨r, hr⟩
      have hpow : α ^ 3 ^ k = 1 := by
        have hrpow : (⟨r, hML (hR.le hr)⟩ : normalizer (L : Set G)) ^ 3 ^ k = 1 := by
          apply Subtype.ext
          simpa using congrArg (fun x : R => (x : G)) hk
        rw [← map_pow, hrpow, map_one]
      exact Odd.of_dvd_nat ((by decide : Odd 3).pow) (orderOf_dvd_of_pow_eq_one hpow)
    have hαE : ∀ y ∈ Ebar, α y ∈ Ebar := by
      rintro _ ⟨y, hy, rfl⟩
      have hcon : r * (y : G) * r⁻¹ ∈ E := (mem_normalizer_iff.mp (hRE hr) _).mp hy
      refine ⟨⟨r * (y : G) * r⁻¹, hEL hcon⟩, hcon, ?_⟩
      rfl
    have hfix := fixes_elemAbelian_nine_of_odd_lieModel_psl_four hX hf hEbare hEbarc α hα hαE
      (π ⟨x, hEL hx⟩) (Subgroup.mem_map_of_mem π hx)
    have hcon : r * x * r⁻¹ ∈ E := (mem_normalizer_iff.mp (hRE hr) x).mp hx
    have hqeq : (⟨⟨r * x * r⁻¹, hEL hcon⟩, hEQ hcon⟩ : Q.subgroupOf L) =
        ⟨⟨x, hEL hx⟩, hEQ hx⟩ := by
      apply hinj
      exact hfix
    have heq : r * x * r⁻¹ = x := congrArg (fun y : Q.subgroupOf L => (y : G)) hqeq
    calc r * x = r * x * r⁻¹ * r := by group
      _ = x * r := by rw [heq]
  exact ⟨E, hEL, le_inf hER hEC, hEe, by simpa using hEc⟩

end SylowPlane

section SplitPrime

open CFSG.ClassicalGroups.SpecialLinear

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_prime_order_centralizer_elemAbelian_nine_sl_four
    (hK : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ Nat.card K - 1)
    (E : Subgroup (SpecialLinearGroup (Fin 4) K))
    (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    ∃ y : SpecialLinearGroup (Fin 4) K, orderOf y = p ∧ y ∈ centralizer (E : Set _) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let ρ : SpecialLinearGroup (Fin 4) K → (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    fun g => (SpecialLinearGroup.toLin' g).toLinearMap
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := by intro g h; ext v; simp [ρ, map_mul, Module.End.mul_apply]
  have hone : ρ 1 = 1 := by ext v; simp [ρ]
  have hinj : ∀ g, ρ g = 1 → g = 1 := by
    intro g h
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    simpa [ρ] using congrArg (fun f : Module.End K (Fin 4 → K) => f v) h
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, ha, b, hb, u, w, hAA, hAw, hABw, hBu, hBAu, hBB, hli⟩ :=
    Item424Res5.exists_blockBasis_sl (by simp) (by
      rw [show (3 : K) = 2 + 1 by ring, CharTwo.two_eq_zero, zero_add]
      exact one_ne_zero) hK ρ hmul hone hinj hcomm hEe.2 hEc
  let bs := Item424Res5.blockBasis hli (by simp)
  have hbs : ∀ i, bs i = ![u, ρ a u, w, ρ b w] i := fun i =>
    congrFun (Item424Res5.coe_blockBasis hli (by simp)) i
  obtain ⟨mu, hmu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  let d : (prodHom 4 K).ker :=
    ⟨![mu, mu, mu⁻¹, mu⁻¹], by
      change prodHom 4 K ![mu, mu, mu⁻¹, mu⁻¹] = 1
      simp [prodHom, Fin.prod_univ_four, mul_assoc]⟩
  let y0 := diagSLHom 4 K d
  let e : SpecialLinearGroup (Fin 4) K ≃* SpecialLinearGroup (Fin 4) K :=
    (SpecialLinearGroup.toLin'_equiv).trans (SpecialLinearGroup.toLin_equiv bs).symm
  let y := e.symm y0
  have hY : ρ y = Matrix.toLin bs bs (y0 : Matrix (Fin 4) (Fin 4) K) := by
    have h : SpecialLinearGroup.toLin'_equiv y = SpecialLinearGroup.toLin_equiv bs y0 := by
      change SpecialLinearGroup.toLin'_equiv
        ((SpecialLinearGroup.toLin'_equiv).symm ((SpecialLinearGroup.toLin_equiv bs) y0)) = _
      rw [MulEquiv.apply_symm_apply]
    have hm := congrArg (fun z : _root_.SpecialLinearGroup K (Fin 4 → K) =>
      (z : Module.End K (Fin 4 → K))) h
    have hm' : ((SpecialLinearGroup.toLin'_equiv y :
        _root_.SpecialLinearGroup K (Fin 4 → K)) : Module.End K (Fin 4 → K)) = ρ y := by
      ext v
      rfl
    rw [hm'] at hm
    simpa only [SpecialLinearGroup.toLin_equiv.toLinearMap_eq] using hm
  have hyBasis : ∀ i, ρ y (bs i) =
      (if i = 0 ∨ i = 1 then (mu : K) else ((mu⁻¹ : Kˣ) : K)) • bs i := by
    intro i
    rw [hY, coe_diagSLHom]
    rw [Matrix.toLin_self]
    fin_cases i <;> simp [d, Fin.sum_univ_four]
  have hyu : ρ y u = (mu : K) • u := by have h := hyBasis 0; simpa [hbs] using h
  have hyau : ρ y (ρ a u) = (mu : K) • ρ a u := by have h := hyBasis 1; simpa [hbs] using h
  have hyw : ρ y w = ((mu⁻¹ : Kˣ) : K) • w := by have h := hyBasis 2; simpa [hbs] using h
  have hybw : ρ y (ρ b w) = ((mu⁻¹ : Kˣ) : K) • ρ b w := by have h := hyBasis 3; simpa [hbs] using h
  have hyA : y * a = a * y := by
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    change ρ (y * a) = ρ (a * y)
    rw [hmul, hmul]
    apply bs.ext
    intro i
    rw [hbs]
    have hAA' : ρ a (ρ a u) = -u - ρ a u := by rw [← sub_eq_zero, ← hAA]; abel
    fin_cases i <;>
      simp [Module.End.mul_apply, hyu, hyau, hyw, hybw, hAA', hAw, hABw, smul_sub, smul_neg]
  have hyB : y * b = b * y := by
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    change ρ (y * b) = ρ (b * y)
    rw [hmul, hmul]
    apply bs.ext
    intro i
    rw [hbs]
    have hBB' : ρ b (ρ b w) = -w - ρ b w := by rw [← sub_eq_zero, ← hBB]; abel
    fin_cases i <;>
      simp [Module.End.mul_apply, hyu, hyau, hyw, hybw, hBB', hBu, hBAu, smul_sub, smul_neg]
  have ha1 : a ≠ 1 := by
    intro h
    have hau : ρ a u = u := by rw [h, hone]; rfl
    exact (hli.injective.ne (by decide : (0 : Fin 4) ≠ 1)) hau.symm
  have hb1 : b ≠ 1 := by
    intro h
    have hbw : ρ b w = w := by rw [h, hone]; rfl
    exact (hli.injective.ne (by decide : (2 : Fin 4) ≠ 3)) hbw.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haord : orderOf a = 3 := orderOf_eq_prime (hEe.2 a ha) ha1
  have hbord : orderOf b = 3 := orderOf_eq_prime (hEe.2 b hb) hb1
  have hnot : b ∉ zpowers a := by
    intro hbA
    let C : Subgroup (SpecialLinearGroup (Fin 4) K) :=
      { carrier := {x | ρ x w = w}
        one_mem' := by change ρ 1 w = w; rw [hone]; rfl
        mul_mem' := fun {x y} hx hy => by
          change ρ (x * y) w = w
          rw [hmul, Module.End.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          change ρ x⁻¹ w = w
          have h : ρ x⁻¹ (ρ x w) = w := by
            rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]; rfl
          rwa [hx] at h }
    have hC : zpowers a ≤ C := zpowers_le.mpr hAw
    have hbw : ρ b w = w := hC hbA
    exact (hli.injective.ne (by decide : (2 : Fin 4) ≠ 3)) hbw.symm
  obtain ⟨-, hc⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair
    Nat.prime_three haord hbord hnot (hcomm a ha b hb)
  have hjoin : E = zpowers a ⊔ zpowers b :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb))
      (by rw [hEc, hc]; norm_num)).symm
  have hyE : y ∈ centralizer (E : Set _) := by
    have hle : E ≤ centralizer ({y} : Set _) := by
      rw [hjoin]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;>
        rw [mem_centralizer_iff] <;> rintro _ rfl
      · exact hyA
      · exact hyB
    rw [mem_centralizer_iff]
    intro x hx
    exact ((mem_centralizer_iff.mp (hle hx)) y (by simp)).symm
  have hyord : orderOf y = p := by
    have h0 : orderOf y0 = p := by
      have hinjd : Function.Injective (diagSLHom 4 K) := by
        intro a b h
        apply Subtype.ext
        funext i
        apply Units.ext
        have hentry := congrArg (fun z : SpecialLinearGroup (Fin 4) K =>
          (z : Matrix (Fin 4) (Fin 4) K) i i) h
        simpa using hentry
      have hdord : orderOf d = p := by
        have hpow : d ^ p = 1 := by
          apply Subtype.ext
          funext i
          have hmup : mu ^ p = 1 := by rw [← hmu]; exact pow_orderOf_eq_one mu
          fin_cases i <;> simp [d, Pi.pow_apply, hmup, inv_pow]
        have hdvd := orderOf_dvd_of_pow_eq_one hpow
        have hentry : p ∣ orderOf d := by
          rw [← hmu]
          let ev : (prodHom 4 K).ker →* Kˣ :=
            { toFun := fun x => x.1 0
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          exact orderOf_map_dvd ev d
        exact Nat.dvd_antisymm hdvd hentry
      exact (orderOf_injective (diagSLHom 4 K) hinjd d).trans hdord
    exact (e.symm.orderOf_eq y0).trans h0
  exact ⟨y, hyord, hyE⟩

end SplitPrime

section ModelSplitPrime

theorem exists_prime_order_centralizer_elemAbelian_nine_lieModel_psl_four
    {X : Type} [Group X] [Finite X] {f p : ℕ}
    (hX : LieModel X .PSL 4 2 f) (hf : Odd f)
    (hp : p.Prime) (hpdvd : p ∣ 2 ^ f - 1)
    {E : Subgroup X} (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    ∃ y : X, orderOf y = p ∧ y ∈ centralizer (E : Set X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let eSL : X ≃* SpecialLinearGroup (Fin 4) K := e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.RankThree.PartOne.center_SL4_eq_bot (F := K))).trans QuotientGroup.quotientBot))
  have hno : ∀ c : K, c ^ 2 + c + 1 ≠ 0 :=
    CFSG.RankThree.PartOne.KFOUT3.quad_ne_zero (by
      have hmod : Nat.card K % 3 = 2 := by rw [hK]; exact CFSG.two_pow_mod_three_of_odd hf
      omega)
  obtain ⟨y, hy, hyE⟩ := exists_prime_order_centralizer_elemAbelian_nine_sl_four
    hno hp (by rwa [hK]) (E.map eSL.toMonoidHom) (hEe.map _)
    (by rw [Subgroup.card_map_of_injective eSL.injective, hEc])
  refine ⟨eSL.symm y, (eSL.symm.orderOf_eq y).trans hy, ?_⟩
  rw [mem_centralizer_iff]
  intro x hx
  apply eSL.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact (mem_centralizer_iff.mp hyE) (eSL x) (mem_map_of_mem _ hx)

end ModelSplitPrime

section NonsplitPrime

open CFSG.RankThree.PartOne.SRC

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_elemAbelian_plane_centralizer_nine_sl_four_of_dvd_add_one
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq : Nat.card K % 3 = 2) (hpdvd : p ∣ Nat.card K + 1)
    (E : Subgroup (SpecialLinearGroup (Fin 4) K))
    (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    ∃ U : Subgroup (SpecialLinearGroup (Fin 4) K),
      U ≤ centralizer (E : Set _) ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 := by
  classical
  have h3 : (3 : K) ≠ 0 := by
    rw [show (3 : K) = 2 + 1 by ring, CharTwo.two_eq_zero, zero_add]
    exact one_ne_zero
  have hno : ∀ c : K, c ^ 2 + c + 1 ≠ 0 :=
    CFSG.RankThree.PartOne.KFOUT3.quad_ne_zero (by omega)
  let ρ : SpecialLinearGroup (Fin 4) K → (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    fun g => (SpecialLinearGroup.toLin' g).toLinearMap
  have hmul : ∀ g h, ρ (g * h) = ρ g * ρ h := by
    intro g h
    ext v
    simp [ρ, map_mul, Module.End.mul_apply]
  have hone : ρ 1 = 1 := by ext v; simp [ρ]
  have hinj : ∀ g, ρ g = 1 → g = 1 := by
    intro g h
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    simpa [ρ] using congrArg (fun f : Module.End K (Fin 4 → K) => f v) h
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, ha, b, hb, u, w, hAA, hAw, hABw, hBu, hBAu, hBB, hli⟩ :=
    Item424Res5.exists_blockBasis_sl (by simp) h3 hno ρ hmul hone hinj hcomm hEe.2 hEc
  let bs := Item424Res5.blockBasis hli (by simp)
  have hbs : ∀ i, bs i = ![u, ρ a u, w, ρ b w] i := fun i =>
    congrFun (Item424Res5.coe_blockBasis hli (by simp)) i
  let j : SpecialLinearGroup (Fin 2) K := CFSG.LinearAlgebra.cubeRootBlock K
  have hAA' : ρ a (ρ a u) = -u - ρ a u := by
    rw [← sub_eq_zero, ← hAA]
    abel
  have hBB' : ρ b (ρ b w) = -w - ρ b w := by
    rw [← sub_eq_zero, ← hBB]
    abel
  have hA : ρ a = Matrix.toLin bs bs
      (diagHom4 (j, 1) : Matrix (Fin 4) (Fin 4) K) := by
    apply bs.ext
    intro i
    rw [Matrix.toLin_self, hbs]
    fin_cases i <;>
      simp [j, coe_diagHom4, diagMat4, CFSG.LinearAlgebra.cubeRootBlock,
        Fin.sum_univ_four, hbs, hAA', hAw, hABw, sub_eq_add_neg, CharTwo.neg_eq]
  have hB : ρ b = Matrix.toLin bs bs
      (diagHom4 (1, j) : Matrix (Fin 4) (Fin 4) K) := by
    apply bs.ext
    intro i
    rw [Matrix.toLin_self, hbs]
    fin_cases i <;>
      simp [j, coe_diagHom4, diagMat4, CFSG.LinearAlgebra.cubeRootBlock,
        Fin.sum_univ_four, hbs, hBB', hBu, hBAu, sub_eq_add_neg, CharTwo.neg_eq]
  let e : SpecialLinearGroup (Fin 4) K ≃* SpecialLinearGroup (Fin 4) K :=
    SpecialLinearGroup.toLin'_equiv.trans (SpecialLinearGroup.toLin_equiv bs).symm
  let Φ := e.symm.toMonoidHom.comp (diagHom4 (F := K))
  have hΦ : ∀ x, ρ (Φ x) = Matrix.toLin bs bs
      (diagHom4 x : Matrix (Fin 4) (Fin 4) K) := by
    intro x
    have h : SpecialLinearGroup.toLin'_equiv (Φ x) =
        SpecialLinearGroup.toLin_equiv bs (diagHom4 x) := by
      change SpecialLinearGroup.toLin'_equiv
        (SpecialLinearGroup.toLin'_equiv.symm (SpecialLinearGroup.toLin_equiv bs
          (diagHom4 x))) = _
      rw [MulEquiv.apply_symm_apply]
    have hm := congrArg (fun z : _root_.SpecialLinearGroup K (Fin 4 → K) =>
      (z : Module.End K (Fin 4 → K))) h
    have hm' : ((SpecialLinearGroup.toLin'_equiv (Φ x) :
        _root_.SpecialLinearGroup K (Fin 4 → K)) : Module.End K (Fin 4 → K)) =
        ρ (Φ x) := by ext v; rfl
    rw [hm'] at hm
    simpa only [SpecialLinearGroup.toLin_equiv.toLinearMap_eq] using hm
  have hdi : Function.Injective (diagHom4 (F := K)) := by
    intro x y h
    apply Prod.ext
    · ext i k
      have hh := congrArg (fun g : SpecialLinearGroup (Fin 4) K =>
        (g : Matrix (Fin 4) (Fin 4) K)
          (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.castSucc k))) h
      fin_cases i <;> fin_cases k <;> simpa [coe_diagHom4, diagMat4] using hh
    · ext i k
      have hh := congrArg (fun g : SpecialLinearGroup (Fin 4) K =>
        (g : Matrix (Fin 4) (Fin 4) K) (Fin.natAdd 2 i) (Fin.natAdd 2 k)) h
      fin_cases i <;> fin_cases k <;> simpa [coe_diagHom4, diagMat4] using hh
  have hΦi : Function.Injective Φ := e.symm.injective.comp hdi
  have hja : Φ (j, 1) = a := by
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    change ρ (Φ (j, 1)) = ρ a
    exact (hΦ _).trans hA.symm
  have hjb : Φ (1, j) = b := by
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.toLinearMap_injective
    change ρ (Φ (1, j)) = ρ b
    exact (hΦ _).trans hB.symm
  have hj1 : j ≠ 1 := (CFSG.LinearAlgebra.isCubeRootBlock_cubeRootBlock h3).ne_one
  have ha1 : a ≠ 1 := by
    intro h
    have hh : (j, (1 : SpecialLinearGroup (Fin 2) K)) = 1 :=
      hΦi (by rw [hja, h, map_one])
    exact hj1 (congrArg Prod.fst hh)
  have hba : b ∉ zpowers a := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    rw [← hja, ← hjb, ← map_zpow] at hk
    have hh := congrArg Prod.snd (hΦi hk)
    exact hj1 (by simpa using hh.symm)
  have hE : closure ({a, b} : Set (SpecialLinearGroup (Fin 4) K)) = E :=
    Item424Res5.closure_pair_eq hEe.2 hEc ha hb ha1 hba
  have hc : ∀ x y : SpecialLinearGroup (Fin 2) K,
      x * j = j * x → y * j = j * y → Φ (x, y) ∈ centralizer (E : Set _) := by
    intro x y hx hy
    have hca : Φ (x, y) * a = a * Φ (x, y) := by
      rw [← hja, ← map_mul, ← map_mul]
      apply congrArg Φ
      exact Prod.ext hx (by simp)
    have hcb : Φ (x, y) * b = b * Φ (x, y) := by
      rw [← hjb, ← map_mul, ← map_mul]
      apply congrArg Φ
      exact Prod.ext (by simp) hy
    have hle : E ≤ centralizer ({Φ (x, y)} : Set _) := by
      rw [← hE, closure_le]
      intro t ht
      rcases ht with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr hca.symm
      · exact mem_centralizer_singleton_iff.mpr hcb.symm
    rw [mem_centralizer_iff]
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hle ht)
  have hp5 : 5 ≤ p := by
    have hp1 := hp.two_le
    have hp4 : p ≠ 4 := by intro h; subst p; norm_num at hp
    omega
  obtain ⟨z, hz, hzord⟩ := CFSG.LinearAlgebra.exists_commute_orderOf_eq_cubeRootBlock
    h3 (by omega) hp hp5 hpdvd
  have hzj : z * j = j * z := Subtype.ext hz.eq
  have hz1 : z ≠ 1 := by intro h; rw [h, orderOf_one] at hzord; exact hp.ne_one hzord.symm
  let x := Φ (z, 1)
  let y := Φ (1, z)
  have hxord : orderOf x = p := by
    rw [orderOf_injective Φ hΦi]
    simp [Prod.orderOf_mk, hzord]
  have hyord : orderOf y = p := by
    rw [orderOf_injective Φ hΦi]
    simp [Prod.orderOf_mk, hzord]
  have hyx : y ∉ zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    change Φ (z, 1) ^ k = Φ (1, z) at hk
    rw [← map_zpow] at hk
    have hh := congrArg Prod.snd (hΦi hk)
    exact hz1 (by simpa using hh.symm)
  have hxy : x * y = y * x := by
    change Φ (z, 1) * Φ (1, z) = Φ (1, z) * Φ (z, 1)
    rw [← map_mul, ← map_mul]
    congr 1
    simp
  obtain ⟨hUe, hUc⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.elemAbelian_pair
    hp hxord hyord hyx hxy
  exact ⟨zpowers x ⊔ zpowers y,
    sup_le (zpowers_le.mpr (hc z 1 hzj (by simp)))
      (zpowers_le.mpr (hc 1 z (by simp) hzj)), hUe, hUc⟩

end NonsplitPrime

section ModelNonsplitPrime

theorem two_le_pRank_centralizer_nine_lieModel_psl_four_of_dvd_add_one
    {X : Type} [Group X] [Finite X] {f p : ℕ}
    (hX : LieModel X .PSL 4 2 f) (hf : Odd f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpdvd : p ∣ 2 ^ f + 1)
    {E : Subgroup X} (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    2 ≤ CFSG.Open.pRank p (centralizer (E : Set X)) := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let eSL : X ≃* SpecialLinearGroup (Fin 4) K := e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.RankThree.PartOne.center_SL4_eq_bot (F := K))).trans QuotientGroup.quotientBot))
  obtain ⟨U, hUE, hUe, hUc⟩ :=
    exists_elemAbelian_plane_centralizer_nine_sl_four_of_dvd_add_one hp hp2 hp3
      (by rw [hK]; exact CFSG.two_pow_mod_three_of_odd hf) (by rwa [hK])
      (E.map eSL.toMonoidHom) (hEe.map _)
      (by rw [Subgroup.card_map_of_injective eSL.injective, hEc])
  let V := U.map eSL.symm.toMonoidHom
  have hVe : IsElemAbelian p V := hUe.map _
  have hVc : Nat.card V = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eSL.symm.injective, hUc]
  have hVE : V ≤ centralizer (E : Set X) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    apply eSL.injective
    rw [map_mul, map_mul]
    change eSL x * eSL (eSL.symm u) = eSL (eSL.symm u) * eSL x
    rw [MulEquiv.apply_symm_apply]
    exact (mem_centralizer_iff.mp (hUE hu)) (eSL x) (mem_map_of_mem _ hx)
  have hVr : CFSG.Open.pRank p V = 2 :=
    Nat.pow_right_injective hp.two_le
      ((CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hVe).symm.trans hVc)
  exact hVr ▸ CFSG.SectionRank.pRank_mono hp.one_lt hVE

end ModelNonsplitPrime

section NonsplitPlaneLift

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846

theorem two_le_pRank_inf_centralizer_nine_of_dvd_add_one
    {G : Type} [Group G] [Finite G] {L E : Subgroup G} {f p : ℕ}
    (hX : LieModel (Bar2 L) .PSL 4 2 f) (hf : Odd f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpdvd : p ∣ 2 ^ f + 1)
    (hEL : E ≤ L) (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    2 ≤ CFSG.Open.pRank p (L ⊓ centralizer (E : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let π : L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 L)
  let Ebar := (E.subgroupOf L).map π
  have hOr : ¬ 3 ∣ Nat.card (CFSG.pCore 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup Nat.prime_three (by norm_num)
  have hi : Function.Injective (π.comp (E.subgroupOf L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hOr hEe.isPGroup.comap_subtype
  have hEbarc : Nat.card Ebar = 9 := by
    have hrange : Ebar = (π.comp (E.subgroupOf L).subtype).range := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hEc]
  have hbar := two_le_pRank_centralizer_nine_lieModel_psl_four_of_dvd_add_one
    hX hf hp hp2 hp3 hpdvd ((hEe.comap L.subtype_injective).map π) hEbarc
  let C : Subgroup L := centralizer ((E.subgroupOf L) : Set L)
  have hmapC : C.map π = centralizer (Ebar : Set (Bar2 L)) :=
    CFSG.Holt.H78.lemma_1_8_centralizer (p := 3) (CFSG.pCore 2 L) hOr
      (P := E.subgroupOf L) hEe.isPGroup.comap_subtype
  have hOp : ¬ p ∣ Nat.card (CFSG.pCore 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup hp hp2
  have hrank := CFSG.pRank_map_eq_of_not_dvd_card_ker π
    (QuotientGroup.mk'_surjective _) hp (by simpa [π] using hOp) C
  have hC : 2 ≤ CFSG.Open.pRank p C := by
    rw [hmapC] at hrank
    change 2 ≤ CFSG.Open.pRank p (centralizer (Ebar : Set (Bar2 L))) at hbar
    omega
  have hrank' := CFSG.SectionRank.pRank_le_map hp.one_lt L.subtype L.subtype_injective C
  have hmap : C.map L.subtype = L ⊓ centralizer (E : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, mem_centralizer_iff.mpr ?_⟩
      intro a ha
      exact congrArg L.subtype ((mem_centralizer_iff.mp hy) ⟨a, hEL ha⟩ ha)
    · rintro ⟨hxL, hxC⟩
      refine ⟨⟨x, hxL⟩, mem_centralizer_iff.mpr ?_, rfl⟩
      intro a ha
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hxC) a ha
  rw [hmap] at hrank'
  exact hC.trans hrank'

end NonsplitPlaneLift

section SpecificPlaneLift

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_centralizer_of_specific_section_element
    {M L E : Subgroup G} (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hZ : center (Bar2 L) = ⊥) {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hEL : E ≤ L) (hEr : IsPGroup r E)
    (hCp : p ∣ Nat.card (F08.CentOverO2 M L))
    {y : Bar2 L} (hy : orderOf y = p)
    (hyE : y ∈ centralizer (((E.subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 L))) : Set (Bar2 L))) :
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  let π : L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 L)
  have hOr : ¬ r ∣ Nat.card (CFSG.pCore 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup hr hr2
  have hOp : ¬ p ∣ Nat.card (CFSG.pCore 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup hp hp2
  have hmapC := CFSG.Holt.H78.lemma_1_8_centralizer
    (p := r) (CFSG.pCore 2 L) hOr (P := E.subgroupOf L) hEr.comap_subtype
  have hyMap : y ∈ (centralizer ((E.subgroupOf L) : Set L)).map π := by
    rw [hmapC]
    exact hyE
  obtain ⟨x, hxC, hxπ⟩ := hyMap
  have hxp : x ^ p ∈ CFSG.pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (x ^ p) = 1
    rw [map_pow, hxπ, ← hy]
    exact pow_orderOf_eq_one y
  have hpow : (x ^ p) ^ Nat.card (CFSG.pCore 2 L) = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := CFSG.pCore 2 L) (x := ⟨x ^ p, hxp⟩))
  obtain ⟨k, -, hk⟩ := exists_pow_orderOf_eq_of_coprime_map (φ := π) (x := x) hp
    (by rwa [hxπ]) hpow (hp.coprime_iff_not_dvd.mpr hOp).symm
  let yL : L := x ^ k
  have hyLC : yL ∈ centralizer ((E.subgroupOf L) : Set L) :=
    (centralizer ((E.subgroupOf L) : Set L)).pow_mem hxC k
  have hyGC : (yL : G) ∈ centralizer (E : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact congrArg L.subtype ((mem_centralizer_iff.mp hyLC) ⟨a, hEL ha⟩ ha)
  obtain ⟨z, hzC, hzord, hzE⟩ := exists_prime_order_centOverO2_inf_centralizer
    hLM hML hp hp2 hr hr2 hEL hEr hCp
  exact two_le_pRank_of_centralizing_mod_pCore hp hp2 hZ (inf_le_left.trans hML)
    ⟨hLM yL.2, hyGC⟩ ⟨(mem_centOverO2_iff.mp hzC).1, hzE⟩ yL.2
    ((Subgroup.orderOf_coe yL).trans hk) hzord (mem_centOverO2_iff.mp hzC).2

end SpecificPlaneLift

section Core

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

section GenericSigma


theorem two_le_pRank_centralizer_nine_of_sigma_rank_gap
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hGA : GriessAllModelsStatement) (hSg : UC6S846.SigmaStd D)
    {L E : Subgroup G} (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G))
    {f p : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) (hmodel : LieModel (BarInf L) .PSL 4 2 f)
    (hpσ : p ∈ D.sig) (hp3 : p ≠ 3)
    (hgap : CFSG.Open.pRank p L < CFSG.Open.pRank p D.M)
    (hEL : E ≤ L) (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) := by
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hshape : LieModel (BarInf L) .PSL 4 2 f ∨
      LieModel (BarInf L) .PSp 3 2 f ∨ IsOmega8m (BarInf L) f := Or.inl hmodel
  have hZ : center (Bar2 L) = ⊥ :=
    Subgroup.card_eq_one.mp (uc22s2114r3l_card_center_eq_one hGA hL hshape)
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have hmodelK : LieModel (Bar2 L) .PSL 4 2 f := LieModel.of_mulEquiv e hmodel
  have hOp : F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hpσ)
  have hbound := pRank_le_add_centOverO2_of_rank_three_model hL hML hshape hZ hp hp2 hOp
  have hpM : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpσ
  by_cases hpL : CFSG.Open.pRank p L ≤ 1
  · have hkernel : 2 ≤ CFSG.Open.pRank p (F08.CentOverO2 D.M L) := by omega
    have hle := pRank_centOverO2_le_pRank_inf_centralizer hL.1.le hML hp hp2
      Nat.prime_three (by norm_num) (Ne.symm hp3) hEL hEe.isPGroup
    omega
  · have hd := (pRank_le_three_and_dvd_sq_sub_one_of_rank_three_model hGA hL
      (by omega) hshape hp hp2).2 (by omega)
    rw [show (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ f) 1] at hd
    rcases hp.dvd_mul.mp hd with hpq | hpq
    · have hCp : p ∣ Nat.card (F08.CentOverO2 D.M L) :=
        CFSG.GroupTheory.dvd_card_of_one_le_pRank hp (by omega)
      let Ebar := (E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L))
      have hEbare : IsElemAbelian 3 Ebar := (hEe.comap L.subtype_injective).map _
      have hEbarc : Nat.card Ebar = 9 := by
        have hi : Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp
            (E.subgroupOf L).subtype) :=
          CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
            (N := CFSG.pCore 2 L)
            (CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup
              Nat.prime_three (by norm_num)) hEe.isPGroup.comap_subtype
        have hrange : Ebar = ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp
            (E.subgroupOf L).subtype).range := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨⟨y, hy⟩, rfl⟩
          · rintro ⟨y, rfl⟩
            exact ⟨y, y.2, rfl⟩
        rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hEc]
      obtain ⟨y, hy, hyE⟩ :=
        exists_prime_order_centralizer_elemAbelian_nine_lieModel_psl_four
          hmodelK hf hp hpq hEbare hEbarc
      exact two_le_pRank_centralizer_of_specific_section_element hL.1.le hML
        hZ hp hp2 Nat.prime_three (by norm_num) hEL hEe.isPGroup hCp hy hyE
    · exact (two_le_pRank_inf_centralizer_nine_of_dvd_add_one hmodelK hf
        hp hp2 hp3 hpq hEL hEe hEc).trans
        (CFSG.SectionRank.pRank_mono hp.one_lt (inf_le_inf_right _ hL.1.le))

theorem pRank_inf_centralizer_nine_eq_two_of_dvd_add_one
    {G : Type} [Group G] [Finite G] {M L E : Subgroup G}
    (hGA : GriessAllModelsStatement) (hL : L ∈ calC M)
    {f p : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) (hmodel : LieModel (BarInf L) .PSL 4 2 f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ 2 ^ f + 1)
    (hEL : E ≤ L) (hEe : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    CFSG.Open.pRank p (L ⊓ centralizer (E : Set G)) = 2 := by
  have hshape : LieModel (BarInf L) .PSL 4 2 f ∨
      LieModel (BarInf L) .PSp 3 2 f ∨ IsOmega8m (BarInf L) f := Or.inl hmodel
  have hZ : center (Bar2 L) = ⊥ :=
    Subgroup.card_eq_one.mp (uc22s2114r3l_card_center_eq_one hGA hL hshape)
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have hmodelK : LieModel (Bar2 L) .PSL 4 2 f := LieModel.of_mulEquiv e hmodel
  have hlo := two_le_pRank_inf_centralizer_nine_of_dvd_add_one hmodelK hf
    hp hp2 hp3 hpq hEL hEe hEc
  have hpq' : ¬ p ∣ 2 ^ f - 1 := by
    intro hd
    have h2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hd
      have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have hdiff : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by omega
      rwa [hdiff] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have he : eP (2 ^ f) p ≠ 1 := fun he =>
    hpq' ((eP_eq_one_iff Nat.one_le_two_pow).mp he)
  have htab := uc22s2114r3l_pRank_eq_rkLin hGA hL (by omega) hmodel hp hp2
  simp only [rkLin, ↓reduceIte, if_neg he] at htab
  have hle := uc22s218_u4_div_le_two he
  have hmono := CFSG.SectionRank.pRank_mono hp.one_lt
    (inf_le_left : L ⊓ centralizer (E : Set G) ≤ L)
  omega

end GenericSigma


theorem s21_14R3LK2_of_rank_four_sigma
    {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) :
    S21_14R3LK2 D Ch := by
  intro hH c L hL hX hpow f hf hf3 hmodel hk hn3 hBL hfaith hML hM3 h3sig hcent
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hshape : LieModel (BarInf L) .PSL 4 2 f ∨
      LieModel (BarInf L) .PSp 3 2 f ∨ IsOmega8m (BarInf L) f := Or.inl hmodel
  have hZ : center (Bar2 L) = ⊥ :=
    Subgroup.card_eq_one.mp (uc22s2114r3l_card_center_eq_one hGA hL hshape)
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have hmodelK : LieModel (Bar2 L) .PSL 4 2 f := LieModel.of_mulEquiv e hmodel
  have hRank3 : CFSG.Open.pRank 3 L = 2 := by
    rw [uc22s2114r3l_pRank_eq_rkLin hGA hL (by omega) hmodel Nat.prime_three (by norm_num)]
    have he : eP (2 ^ f) 3 = 2 := by
      rw [eP_two_pow_three, if_neg (Nat.not_even_iff_odd.mpr hf)]
    simp [rkLin, he]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  have hQ := hR.inf_of_le_normalizer hL.1.le hML
  obtain ⟨E, hEL, hER, hEe, hEc⟩ :=
    exists_central_elemAbelian_nine_of_sylow_intersection hL.1.le hML hR hQ
      hmodelK hf hRank3
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hp3 : p ≠ 3 := fun h => h3sig (h ▸ hpσ)
  have hOp : F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hpσ)
  have hpM := hfour p hpσ
  have hple := (pRank_le_three_and_dvd_sq_sub_one_of_rank_three_model hGA hL
    (by omega) hshape hp hp2).1
  have hgap : CFSG.Open.pRank p L < CFSG.Open.pRank p D.M := by omega
  have htwo := two_le_pRank_centralizer_nine_of_sigma_rank_gap hGA hSg hL hML
    hf hf3 hmodel hpσ hp3 hgap hEL hEe hEc
  have hcontr := hcent p hpσ R E hR hER hEe hEc
  omega

theorem s21_14R3LK2_core
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (_hMS : S.InMSigma) (_hPart : PartIAt S.M) :
    S21_14R3LK2 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
  s21_14R3LK2_of_rank_four_sigma
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (fun _p hp => UC6.four_le_pRank_of_sigma hp)

end Core

end CFSG.LocalAnalysis.UniquenessCase.UC22
