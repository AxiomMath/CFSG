module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Coord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

@[expose] def S16C11AltEqv {n : ℕ} (x y : Fin n → ZMod 2) : Prop :=
  y = x ∨ y = fun i => x i + 1

instance {n : ℕ} (x y : Fin n → ZMod 2) : Decidable (S16C11AltEqv x y) := by
  unfold S16C11AltEqv
  infer_instance

theorem s16c11_alt_eqv_comm {n : ℕ} (x y : Fin n → ZMod 2) :
    S16C11AltEqv x y ↔ S16C11AltEqv y x := by
  have key : ∀ a b : ZMod 2, b = a + 1 → a = b + 1 := by decide
  constructor <;> rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr (funext fun i => key _ _ (congrFun h i))
  · exact Or.inl h.symm
  · exact Or.inr (funext fun i => key _ _ (congrFun h i))

@[expose] def S16C11AltPact {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  fun i => x (g⁻¹ i)

@[expose] def S16C11AltBits (n k : ℕ) : Fin n → ZMod 2 :=
  fun i => if (k / 2 ^ (i : ℕ)) % 2 = 1 then 1 else 0

private lemma s16c11_altvec_bits_cons (n k : ℕ) :
    S16C11AltBits (n + 1) k =
      Fin.cons (if k % 2 = 1 then (1 : ZMod 2) else 0) (S16C11AltBits n (k / 2)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [S16C11AltBits]
  · intro j
    simp only [S16C11AltBits, Fin.cons_succ]
    have hdiv : k / 2 ^ (j.succ : ℕ) = k / 2 / 2 ^ (j : ℕ) := by
      rw [Fin.val_succ, pow_succ, mul_comm (2 ^ (j : ℕ)) 2, ← Nat.div_div_eq_div_mul]
    exact congrArg (fun t => if t % 2 = 1 then (1 : ZMod 2) else 0) hdiv

@[expose] def S16C11AltWt {n : ℕ} (x : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i = 1).card

@[expose] noncomputable def S16C11AltCls (n : ℕ) (x : Fin n → ZMod 2) : (FFModel.altDn n).Mod :=
  if h : ∑ i, x i = 0 then s16c11AltVec n x h else 1

theorem s16c11_alt_cls_of_even {n : ℕ} {x : Fin n → ZMod 2} (h : ∑ i, x i = 0) :
    S16C11AltCls n x = s16c11AltVec n x h := by
  unfold S16C11AltCls
  rw [dif_pos h]

theorem s16c11_alt_cls_surjective (n : ℕ) (q : (FFModel.altDn n).Mod) :
    ∃ x : Fin n → ZMod 2, ∑ i, x i = 0 ∧ q = S16C11AltCls n x := by
  obtain ⟨x, hx, rfl⟩ := s16c11AltVec_surjective n q
  exact ⟨x, hx, (s16c11_alt_cls_of_even hx).symm⟩

private lemma s16c11_altvec_toAdd_allOnes_zpow (n : ℕ) (k : ℤ) (i : Fin n) :
    Multiplicative.toAdd (G6.allOnes n ^ k) i = k • (1 : ZMod 2) := by
  rw [toAdd_zpow, Pi.smul_apply, G6.allOnes, toAdd_ofAdd]

private lemma s16c11_altvec_toAdd_mul_inv (n : ℕ) (x y : Fin n → ZMod 2) (i : Fin n) :
    Multiplicative.toAdd ((Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y) i =
      - x i + y i := by
  rw [toAdd_mul, Pi.add_apply, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, Pi.neg_apply]

theorem s16c11_alt_cls_eq_iff {n : ℕ} {x y : Fin n → ZMod 2} (hx : ∑ i, x i = 0)
    (hy : ∑ i, y i = 0) : S16C11AltCls n x = S16C11AltCls n y ↔ S16C11AltEqv x y := by
  rw [s16c11_alt_cls_of_even hx, s16c11_alt_cls_of_even hy]
  constructor
  · intro h
    have hmem : ((⟨Multiplicative.ofAdd x, hx⟩ : ↥(G6.coreMod n))⁻¹ *
        ⟨Multiplicative.ofAdd y, hy⟩) ∈
        (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) :=
      QuotientGroup.eq.mp h
    obtain ⟨hzp, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have hk' : ∀ i : Fin n, k • (1 : ZMod 2) = - x i + y i := by
      intro i
      rw [← s16c11_altvec_toAdd_allOnes_zpow n k i,
        ← s16c11_altvec_toAdd_mul_inv n x y i]
      exact congrFun (congrArg Multiplicative.toAdd hk) i
    have hyx : ∀ i : Fin n, y i = x i + k • (1 : ZMod 2) := by
      intro i
      exact (by decide : ∀ a b c : ZMod 2, c = -a + b → b = a + c)
        (x i) (y i) (k • (1 : ZMod 2)) (hk' i)
    have hk_eq : k • (1 : ZMod 2) = (k : ZMod 2) := by
      rw [zsmul_eq_mul, mul_one]
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (k : ZMod 2) with h0 | h1
    · left
      funext i
      rw [hyx i, hk_eq, h0, add_zero]
    · right
      funext i
      rw [hyx i, hk_eq, h1]
  · rintro (rfl | h)
    · rfl
    · have hxA : Multiplicative.ofAdd x ∈ G6.coreMod n := hx
      have hyA : Multiplicative.ofAdd y ∈ G6.coreMod n := hy
      have hmem : ((⟨Multiplicative.ofAdd x, hxA⟩ : ↥(G6.coreMod n))⁻¹ *
          ⟨Multiplicative.ofAdd y, hyA⟩) ∈
          (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) := by
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · refine Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩
          apply Multiplicative.toAdd.injective
          funext i
          rw [show (↑((⟨Multiplicative.ofAdd x, hxA⟩ : ↥(G6.coreMod n))⁻¹ *
              ⟨Multiplicative.ofAdd y, hyA⟩) : G6.PermMod n) =
              (Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y from rfl]
          rw [s16c11_altvec_toAdd_allOnes_zpow n 1 i,
            s16c11_altvec_toAdd_mul_inv n x y i, h, one_zsmul]
          exact (by decide : ∀ a : ZMod 2, (1 : ZMod 2) = -a + (a + 1)) (x i)
        · exact ((⟨Multiplicative.ofAdd x, hxA⟩ : ↥(G6.coreMod n))⁻¹ *
            ⟨Multiplicative.ofAdd y, hyA⟩).2
      exact (QuotientGroup.eq).mpr hmem

theorem s16c11_alt_exists_bits {n : ℕ} (x : Fin n → ZMod 2) :
    ∃ k : ℕ, k < 2 ^ n ∧ x = S16C11AltBits n k := by
  induction n with
  | zero =>
      refine ⟨0, by norm_num, ?_⟩
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨k', hk'lt, hk'⟩ := ih (Fin.tail x)
      have hval : (x 0).val < 2 := ZMod.val_lt (x 0)
      refine ⟨(x 0).val + 2 * k', ?_, ?_⟩
      · calc (x 0).val + 2 * k' < 2 + 2 * k' := by omega
          _ = 2 * (k' + 1) := by ring
          _ ≤ 2 * 2 ^ n := by gcongr; omega
          _ = 2 ^ (n + 1) := by rw [pow_succ, mul_comm]
      · have hk2 : ((x 0).val + 2 * k') / 2 = k' := by
          rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2),
            Nat.div_eq_of_lt hval, zero_add]
        have hkmod : ((x 0).val + 2 * k') % 2 = (x 0).val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hval]
        have hbit0 : (if ((x 0).val + 2 * k') % 2 = 1 then (1 : ZMod 2) else 0) = x 0 := by
          rw [hkmod]
          rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x 0) with h | h <;>
            rw [h] <;> decide
        have hbits : S16C11AltBits (n + 1) ((x 0).val + 2 * k') =
            Fin.cons (x 0) (S16C11AltBits n k') := by
          rw [s16c11_altvec_bits_cons, hk2, hbit0]
        calc x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
          _ = Fin.cons (x 0) (S16C11AltBits n k') := by rw [hk']
          _ = S16C11AltBits (n + 1) ((x 0).val + 2 * k') := hbits.symm

theorem s16c11_alt_wt_pact {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    S16C11AltWt (S16C11AltPact g x) = S16C11AltWt x := by
  unfold S16C11AltWt S16C11AltPact
  refine Finset.card_nbij' (fun i => g⁻¹ i) (fun j => g j) ?_ ?_ ?_ ?_
  · intro a ha
    simpa using ha
  · intro b hb
    simpa using hb
  · intro a _
    simp
  · intro b _
    simp

theorem s16c11_alt_sum_pact {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    ∑ i, S16C11AltPact g x i = ∑ i, x i :=
  Equiv.sum_comp g⁻¹ x

theorem s16c11_alt_cls_zero (n : ℕ) : S16C11AltCls n (0 : Fin n → ZMod 2) = 1 := by
  rw [s16c11_alt_cls_of_even (by simp)]
  rw [s16c11AltVec]
  rfl

theorem s16c11_alt_cls_one_iff {n : ℕ} {x : Fin n → ZMod 2} (hx : ∑ i, x i = 0) :
    S16C11AltCls n x = 1 ↔ S16C11AltEqv 0 x := by
  have h0 : ∑ i, (0 : Fin n → ZMod 2) i = 0 := by simp
  rw [← s16c11_alt_cls_zero n, s16c11_alt_cls_eq_iff hx h0]
  exact s16c11_alt_eqv_comm x 0

theorem s16c11_alt_act_cls {n : ℕ} (g : ↥(alternatingGroup (Fin n))) {x : Fin n → ZMod 2}
    (hx : ∑ i, x i = 0) :
    S16C11AltAct n g (S16C11AltCls n x) =
      S16C11AltCls n (S16C11AltPact (g : Equiv.Perm (Fin n)) x) := by
  have hx' : ∑ i, S16C11AltPact (g : Equiv.Perm (Fin n)) x i = 0 := by
    rw [s16c11_alt_sum_pact]
    exact hx
  rw [s16c11_alt_cls_of_even hx, s16c11_alt_cls_of_even hx']
  exact s16c11AltAct_vec n g

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
