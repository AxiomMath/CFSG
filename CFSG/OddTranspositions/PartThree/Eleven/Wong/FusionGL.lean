module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionMat
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Matrix Subgroup

@[expose] def fusionQ (a b c d e f g h : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![f + h, 0, f, 0;
     a, b, c, d;
     f + h + b + d, 0, b + f, 0;
     e, f, g, h]

theorem eq_fusionQ_of_commute {Q : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : Q * fusionA = fusionA * Q) :
    Q = fusionQ (Q 1 0) (Q 1 1) (Q 1 2) (Q 1 3) (Q 3 0) (Q 3 1) (Q 3 2) (Q 3 3) := by
  have e : ∀ i j, (Q * fusionA) i j = (fusionA * Q) i j := fun i j => by rw [h]
  have e00 := e 0 0; have e02 := e 0 2; have e22 := e 2 2; have e20 := e 2 0
  have e30 := e 3 0; have e32 := e 3 2; have e10 := e 1 0; have e12 := e 1 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, fusionA] at e00 e02 e22 e20 e30 e32 e10 e12
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fusionQ]
  all_goals grind

theorem fusionWord_fusionQ : ∀ a b c d e f g h : ZMod 2,
    fusionQ a b c d e f g h ≠ 1 → fusionQ a b c d e f g h ^ 3 = 1 →
    fusionB * fusionQ a b c d e f g h * fusionB * fusionQ a b c d e f g h = 1 →
    fusionWord (fusionQ a b c d e f g h) = fusionR := by
  decide +kernel

theorem fusionWord_eq_fusionR {Q : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hQ1 : Q ≠ 1)
    (hQ3 : Q ^ 3 = 1) (hQA : Q * fusionA = fusionA * Q) (hBQ : fusionB * Q * fusionB * Q = 1) :
    fusionWord Q = fusionR := by
  obtain ⟨a, b, c, d, e, f, g, h, rfl⟩ : ∃ a b c d e f g h, Q = fusionQ a b c d e f g h :=
    ⟨_, _, _, _, _, _, _, _, eq_fusionQ_of_commute hQA⟩
  exact fusionWord_fusionQ a b c d e f g h hQ1 hQ3 hBQ

private theorem eight_dvd_card_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {H K L : Subgroup G} (hK : IsPGroup 2 K) (hL : IsPGroup 2 L) (hKH : K ≤ H) (hLH : L ≤ H)
    (hLK : L ≤ normalizer (K : Set G)) (hLK' : ¬ L ≤ K) (h4 : Nat.card K = 4) :
    8 ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := (hK.to_sup_of_normal_left' hL hLK).exists_card_eq
  have hlt : Nat.card K < Nat.card (K ⊔ L : Subgroup G) :=
    card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hLK' (h ▸ le_sup_right))
  rw [hn, h4] at hlt
  have h3 : 3 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> norm_num at hlt
  have h8 : 8 ∣ Nat.card (K ⊔ L : Subgroup G) := by
    rw [hn]
    simpa using Nat.pow_dvd_pow 2 h3
  exact h8.trans (card_dvd_of_le (sup_le hKH hLH))

private def FusionOcto (y b : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  y ^ 4 = 1 ∧ y ^ 2 ≠ 1 ∧ b * b = 1 ∧ (b * y * b = y ∨ b * y * b = y ^ 3) ∧
    b ≠ 1 ∧ b ≠ y ∧ b ≠ y ^ 2 ∧ b ≠ y ^ 3

private instance (y b : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Decidable (FusionOcto y b) := by
  unfold FusionOcto
  infer_instance

private theorem eight_dvd_card_of_fusionOcto {H : Subgroup (GL (Fin 4) (ZMod 2))}
    {y b : GL (Fin 4) (ZMod 2)} (hy : y ∈ H) (hb : b ∈ H)
    (h : FusionOcto (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) b) : 8 ∣ Nat.card H := by
  unfold FusionOcto at h
  obtain ⟨h4, h2, hbb, hby, hb1, hby1, hby2, hby3⟩ := h
  have hy4 : y ^ 2 ^ (1 + 1) = 1 := Units.ext (by simpa using h4)
  have hy2 : ¬ y ^ 2 ^ 1 = 1 := fun e => h2 (by simpa using congrArg Units.val e)
  have hord : orderOf y = 4 := orderOf_eq_prime_pow hy2 hy4
  have hbb' : b * b = 1 := Units.ext (by simpa using hbb)
  have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hbb').symm
  have hb2 : orderOf b ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by simp [sq, hbb'])
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hb2
  refine eight_dvd_card_of_le_normalizer (K := zpowers y) (L := zpowers b)
    (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord]; norm_num))
    (IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm]))
    (zpowers_le.2 hy) (zpowers_le.2 hb) ?_ ?_ (by rw [Nat.card_zpowers, hord])
  · rw [zpowers_le]
    refine mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [← conj_zpow, hbinv]
    refine zpow_mem ?_ k
    rcases hby with e | e
    · rw [show b * y * b = y from Units.ext (by simpa using e)]
      exact mem_zpowers y
    · rw [show b * y * b = y ^ 3 from Units.ext (by simpa using e)]
      exact pow_mem (mem_zpowers y) 3
  · rw [zpowers_le]
    intro hmem
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
    obtain ⟨k, hk, e⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_range] at hk
    interval_cases k
    · exact hb1 (by rw [← e]; simp)
    · exact hby1 (by rw [← e]; simp)
    · exact hby2 (by rw [← e]; simp)
    · exact hby3 (by rw [← e]; simp)

private theorem val_mem_of_mem_closure {g : GL (Fin 4) (ZMod 2)}
    (hg : g ∈ closure {fusionUnitA, fusionUnitB}) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 ∨ (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionA ∨
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionB ∨
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionA * fusionB := by
  induction hg using closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl <;> simp
  | one => simp
  | mul g g' _ _ hg hg' =>
    rw [Units.val_mul]
    rcases hg with h | h | h | h <;> rcases hg' with h' | h' | h' | h' <;> rw [h, h'] <;> decide
  | inv g _ hg =>
    have hgg : g * g = 1 := Units.ext (by
      rw [Units.val_mul, Units.val_one]
      rcases hg with h | h | h | h <;> rw [h] <;> decide)
    rwa [show g⁻¹ = g from (eq_inv_of_mul_eq_one_left hgg).symm]

private theorem card_closure_fusionUnitA_fusionUnitB :
    Nat.card (closure {fusionUnitA, fusionUnitB} : Subgroup (GL (Fin 4) (ZMod 2))) = 4 := by
  have hle : Nat.card (closure {fusionUnitA, fusionUnitB} : Subgroup (GL (Fin 4) (ZMod 2))) ≤ 4 := by
    have := Nat.card_le_card_of_injective
      (β := (({1, fusionA, fusionB, fusionA * fusionB} :
        Finset (Matrix (Fin 4) (Fin 4) (ZMod 2))) : Set (Matrix (Fin 4) (Fin 4) (ZMod 2))))
      (fun g : (closure {fusionUnitA, fusionUnitB} : Subgroup (GL (Fin 4) (ZMod 2))) =>
        ⟨((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)),
          by simpa using val_mem_of_mem_closure g.2⟩)
      (fun g g' e => Subtype.ext (Units.ext (congrArg Subtype.val e)))
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at this
    exact this.trans Finset.card_le_four
  have hA2 : orderOf fusionUnitA = 2 :=
    orderOf_eq_prime (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; decide))
      (fun e => absurd (congrArg Units.val e) (by decide))
  have hB : fusionUnitB ∉ zpowers fusionUnitA := by
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hA2]
    intro h
    obtain ⟨k, hk, e⟩ := Finset.mem_image.1 h
    rw [Finset.mem_range] at hk
    interval_cases k
    · exact absurd (congrArg Units.val e) (by decide)
    · exact absurd (congrArg Units.val e) (by decide)
  have hAS : zpowers fusionUnitA ≤ closure {fusionUnitA, fusionUnitB} :=
    zpowers_le.2 (subset_closure (by simp))
  have hlt := card_lt_of_lt (lt_of_le_of_ne hAS fun h => hB (h ▸ subset_closure (by simp)))
  have hdvd := card_dvd_of_le hAS
  rw [Nat.card_zpowers, hA2] at hlt hdvd
  omega

private def FusionCases (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  (x * fusionB = fusionB * x ∨ x * fusionB = fusionA * fusionB * x) ∨
    FusionOcto (fusionB * x) fusionB ∨ FusionOcto x fusionA ∨
    ((fusionB * x) ^ 4 ≠ 1 ∧ ((fusionB * x) ^ 4) ^ 3 = 1 ∧
      fusionB * (fusionB * x) ^ 4 * fusionB * (fusionB * x) ^ 4 = 1 ∧
      (fusionB * x) ^ 4 * fusionA = fusionA * (fusionB * x) ^ 4)

private instance (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Decidable (FusionCases x) := by
  unfold FusionCases
  infer_instance

private def FusionCheck (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  x ^ 4 = 1 → x ≠ 1 → x ≠ fusionA → x ≠ fusionB → x ≠ fusionA * fusionB → FusionCases x

private instance (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Decidable (FusionCheck x) := by
  unfold FusionCheck
  infer_instance

private theorem fusionCheck_fusionQ :
    ∀ a b c d e f g h : ZMod 2, FusionCheck (fusionQ a b c d e f g h) := by
  decide +kernel

theorem eq_closure_fusionUnitA_fusionUnitB {H : Subgroup (GL (Fin 4) (ZMod 2))}
    (hA : fusionUnitA ∈ H) (hB : fusionUnitB ∈ H) (hF : fusionUnitF ∈ H)
    (h8 : ¬ 8 ∣ Nat.card H) {P : Subgroup (GL (Fin 4) (ZMod 2))} (hPH : P ≤ H)
    (hAP : fusionUnitA ∈ P) (hP : Nat.card P = 4) :
    P = closure {fusionUnitA, fusionUnitB} := by
  have hSH : closure {fusionUnitA, fusionUnitB} ≤ H :=
    (closure_le _).2 (Set.insert_subset_iff.2 ⟨hA, Set.singleton_subset_iff.2 hB⟩)
  have hS4 := card_closure_fusionUnitA_fusionUnitB
  by_contra hne
  obtain ⟨x, hxP, hxS⟩ : ∃ x ∈ P, x ∉ closure {fusionUnitA, fusionUnitB} := by
    by_contra h
    push Not at h
    exact hne (eq_of_le_of_card_ge h (by rw [hP, hS4]))
  have hxH : x ∈ H := hPH hxP
  have hx4 : x ^ 4 = 1 := by
    have : (⟨x, hxP⟩ : P) ^ Nat.card P = 1 := pow_card_eq_one'
    rw [hP] at this
    simpa using congrArg Subtype.val this
  have hxA : x * fusionUnitA = fusionUnitA * x := by
    have := IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (by rw [hP]; norm_num) (⟨x, hxP⟩ : P)
      ⟨_, hAP⟩
    simpa using congrArg Subtype.val this
  have hcases : FusionCases (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    have hxA' : (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) * fusionA = fusionA * x :=
      congrArg Units.val hxA
    obtain ⟨a, b, c, d, e, f, g, h, hq⟩ : ∃ a b c d e f g h,
        (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionQ a b c d e f g h :=
      ⟨_, _, _, _, _, _, _, _, eq_fusionQ_of_commute hxA'⟩
    rw [hq]
    refine fusionCheck_fusionQ a b c d e f g h ?_ ?_ ?_ ?_ ?_ <;> rw [← hq]
    · simpa using congrArg Units.val hx4
    · exact fun e => hxS (by rw [show x = 1 from Units.ext e]; exact one_mem _)
    · exact fun e => hxS (by rw [show x = fusionUnitA from Units.ext e]; exact subset_closure (by simp))
    · exact fun e => hxS (by rw [show x = fusionUnitB from Units.ext e]; exact subset_closure (by simp))
    · exact fun e => hxS (by
        rw [show x = fusionUnitA * fusionUnitB from Units.ext e]
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
  apply h8
  unfold FusionCases at hcases
  rcases hcases with hN | hO | hO | ⟨hQ1, hQ3, hBQ, hQA⟩
  ·
    have hx2 : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hx4)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hx2
    refine eight_dvd_card_of_le_normalizer (IsPGroup.of_card (n := 2) (by rw [hS4]; norm_num))
      (IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])) hSH (zpowers_le.2 hxH) ?_
      (fun h => hxS (zpowers_le.1 h)) hS4
    rw [zpowers_le]
    refine mem_normalizer_fintype fun n hn => ?_
    induction hn using closure_induction with
    | mem n hn =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with rfl | rfl
      · rw [hxA, mul_inv_cancel_right]
        exact subset_closure (by simp)
      · rcases hN with e | e
        · rw [show x * fusionUnitB = fusionUnitB * x from Units.ext e, mul_inv_cancel_right]
          exact subset_closure (by simp)
        · rw [show x * fusionUnitB = fusionUnitA * fusionUnitB * x from Units.ext e,
            mul_inv_cancel_right]
          exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    | one => simp
    | mul n n' _ _ hn hn' => simpa [mul_assoc] using mul_mem hn hn'
    | inv n _ hn => simpa [mul_assoc] using inv_mem hn
  · exact eight_dvd_card_of_fusionOcto (mul_mem hB hxH) hB (by rw [Units.val_mul]; exact hO)
  · exact eight_dvd_card_of_fusionOcto hxH hA hO
  ·
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = (fusionUnitB * x) ^ 4 := ⟨_, rfl⟩
    have hQH : Q ∈ H := hQ ▸ pow_mem (mul_mem hB hxH) 4
    have hQv : (Q : Matrix (Fin 4) (Fin 4) (ZMod 2)) = (fusionB * x) ^ 4 := by simp [hQ]
    have hW := fusionWord_eq_fusionR (Q := (Q : Matrix (Fin 4) (Fin 4) (ZMod 2)))
      (by rw [hQv]; exact hQ1) (by rw [hQv]; exact hQ3) (by rw [hQv]; exact hQA)
      (by rw [hQv]; exact hBQ)
    have hF2 : fusionUnitF ^ 2 ∈ H := pow_mem hF 2
    have hRH : fusionUnitB * fusionUnitF * Q * fusionUnitF ^ 2 * Q * fusionUnitF * Q *
        fusionUnitF ^ 2 * Q * fusionUnitF * Q ∈ H :=
      mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
        (mul_mem hB hF) hQH) hF2) hQH) hF) hQH) hF2) hQH) hF) hQH
    refine eight_dvd_card_of_fusionOcto hRH hB ?_
    have hRv : ((fusionUnitB * fusionUnitF * Q * fusionUnitF ^ 2 * Q * fusionUnitF * Q *
        fusionUnitF ^ 2 * Q * fusionUnitF * Q : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = fusionR := by
      rw [← hW]
      simp [fusionWord]
    rw [hRv]
    decide

private def fusionStab : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := {g | ∀ p ∈ fusionPplus, p ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionPplus}
  mul_mem' {g g'} hg hg' := by
    simp only [Set.mem_setOf_eq] at hg hg' ⊢
    intro p hp
    rw [Units.val_mul, ← vecMul_vecMul]
    exact hg' _ (hg p hp)
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro p hp
    simpa using hp
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.surj_on_of_inj_on_of_card_le (s := fusionPplus)
      (t := fusionPplus) (fun q _ => q ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) hg
      (fun q q' _ _ e => by
        simpa [vecMul_vecMul] using
          congrArg (· ᵥ* ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) e)
      le_rfl p hp
    simpa [vecMul_vecMul] using hq

private theorem mem_fusionStab {g : GL (Fin 4) (ZMod 2)} :
    g ∈ fusionStab ↔
      ∀ p ∈ fusionPplus, p ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionPplus :=
  Iff.rfl

private theorem eq_of_vecMul_fusionPplus {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ p ∈ fusionPplus, p ᵥ* M = p ᵥ* N) : M = N := by
  have h0 := h ![1, 0, 0, 0] (by decide)
  have h1 := h ![1, 1, 0, 0] (by decide)
  have h2 := h ![0, 1, 1, 0] (by decide)
  have h3 := h ![0, 1, 0, 1] (by decide)
  ext i j
  have e0 := congrFun h0 j
  have e1 := congrFun h1 j
  have e2 := congrFun h2 j
  have e3 := congrFun h3 j
  simp [vecMul, dotProduct, Fin.sum_univ_four] at e0 e1 e2 e3
  fin_cases i <;> simp <;> grind

private theorem card_fusionStab_le : Nat.card fusionStab ≤ 120 := by
  let φ : fusionStab → Equiv.Perm fusionPplus := fun g =>
    Equiv.ofBijective
      (fun p => ⟨p.1 ᵥ* ((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)),
        mem_fusionStab.1 g.2 p.1 p.2⟩)
      (Finite.injective_iff_bijective.1 fun p p' e => Subtype.ext (by
        simpa [vecMul_vecMul] using congrArg (fun v : fusionPplus => v.1 ᵥ*
          (((g : GL (Fin 4) (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2))) e))
  have hφ : Function.Injective φ := fun g g' e => Subtype.ext (Units.ext
    (eq_of_vecMul_fusionPplus fun p hp => by
      simpa [φ] using congrArg (fun σ : Equiv.Perm fusionPplus => (σ ⟨p, hp⟩ : Fin 4 → ZMod 2)) e))
  calc Nat.card fusionStab ≤ Nat.card (Equiv.Perm fusionPplus) :=
        Nat.card_le_card_of_injective φ hφ
    _ = 120 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]
        decide

theorem fusionUnitZ_mem {H : Subgroup (GL (Fin 4) (ZMod 2))}
    (hH : ∀ h ∈ H, ∀ p ∈ fusionPplus, p ᵥ* (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionPplus)
    (h60 : Nat.card H = 60) : fusionUnitZ ∈ H := by
  have hHS : H ≤ fusionStab := fun g hg => mem_fusionStab.2 (hH g hg)
  have hY : fusionUnitY ∈ fusionStab := by
    rw [mem_fusionStab, val_fusionUnitY]
    decide
  have hZ : fusionUnitZ = fusionUnitY * fusionUnitY := Units.ext (by
    rw [Units.val_mul, val_fusionUnitZ, val_fusionUnitY]
    decide)
  rw [hZ]
  have hidx := (H.subgroupOf fusionStab).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hHS).toEquiv, h60] at hidx
  have hle := card_fusionStab_le
  have h0 : (H.subgroupOf fusionStab).index ≠ 0 := index_ne_zero_of_finite
  have h12 : (H.subgroupOf fusionStab).index = 1 ∨ (H.subgroupOf fusionStab).index = 2 := by
    omega
  rcases h12 with h1 | h2
  · rw [index_eq_one] at h1
    have hYH : fusionUnitY ∈ H :=
      mem_subgroupOf.1 (h1 ▸ mem_top (⟨fusionUnitY, hY⟩ : fusionStab))
    exact mul_mem hYH hYH
  · exact mem_subgroupOf.1 (mul_self_mem_of_index_two h2 ⟨fusionUnitY, hY⟩)

private def fusionStabT : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := {g | ![1, 0, 0, 0] ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = ![1, 0, 0, 0]}
  mul_mem' {g g'} hg hg' := by
    simp only [Set.mem_setOf_eq] at hg hg' ⊢
    rw [Units.val_mul, ← vecMul_vecMul, hg, hg']
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    calc ![1, 0, 0, 0] ᵥ* ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
        = (![1, 0, 0, 0] ᵥ* (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) ᵥ*
            ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by rw [hg]
      _ = ![1, 0, 0, 0] := by rw [vecMul_vecMul, Units.mul_inv, vecMul_one]

private def fusionPerm : fusionStab →* Equiv.Perm fusionPplus where
  toFun g :=
    { toFun := fun p => ⟨p.1 ᵥ* (((g⁻¹ : fusionStab) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)), mem_fusionStab.1 (g⁻¹).2 p.1 p.2⟩
      invFun := fun p => ⟨p.1 ᵥ* ((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)),
        mem_fusionStab.1 g.2 p.1 p.2⟩
      left_inv := fun p => Subtype.ext (by
        change p.1 ᵥ* (((g : GL (Fin 4) (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) ᵥ* ((g : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) = p.1
        rw [vecMul_vecMul, Units.inv_mul, vecMul_one])
      right_inv := fun p => Subtype.ext (by
        change p.1 ᵥ* ((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ᵥ*
          (((g : GL (Fin 4) (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) = p.1
        rw [vecMul_vecMul, Units.mul_inv, vecMul_one]) }
  map_one' := Equiv.ext fun p => Subtype.ext (by
    change p.1 ᵥ* (((1 : GL (Fin 4) (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) = p.1
    simp)
  map_mul' g g' := Equiv.ext fun p => Subtype.ext (by
    change p.1 ᵥ* ((((g : GL (Fin 4) (ZMod 2)) * g')⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      p.1 ᵥ* (((g' : GL (Fin 4) (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) ᵥ* (((g : GL (Fin 4) (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2))
    rw [vecMul_vecMul, _root_.mul_inv_rev, Units.val_mul])

private theorem fusionPerm_injective : Function.Injective fusionPerm := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hinv : ((g⁻¹ : fusionStab) : GL (Fin 4) (ZMod 2)) = 1 :=
    Units.ext (eq_of_vecMul_fusionPplus fun p hp => by
      have := congrArg (fun σ : Equiv.Perm fusionPplus => (σ ⟨p, hp⟩ : Fin 4 → ZMod 2)) hg
      simpa [fusionPerm] using this)
  have : (g⁻¹ : fusionStab) = 1 := Subtype.ext hinv
  simpa using this

theorem card_eq_sixty_of_fusionPplus {H : Subgroup (GL (Fin 4) (ZMod 2))}
    (hA : fusionUnitA ∈ H) (hB : fusionUnitB ∈ H) (hF : fusionUnitF ∈ H) (h8 : ¬ 8 ∣ Nat.card H)
    (hH : ∀ h ∈ H, ∀ p ∈ fusionPplus, p ᵥ* (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionPplus)
    (hmove : ∃ h ∈ H, ![1, 0, 0, 0] ᵥ* (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ ![1, 0, 0, 0]) :
    Nat.card H = 60 := by
  have hHS : H ≤ fusionStab := fun g hg => mem_fusionStab.2 (hH g hg)
  have h120 : Nat.card H ∣ 120 := by
    have hcard : Nat.card ((H.subgroupOf fusionStab).map fusionPerm) = Nat.card H := by
      rw [card_map_of_injective fusionPerm_injective]
      exact Nat.card_congr (subgroupOfEquivOfLe hHS).toEquiv
    have h5 : Nat.card fusionPplus = 5 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      decide
    have hdvd := card_subgroup_dvd_card ((H.subgroupOf fusionStab).map fusionPerm)
    rw [hcard, Nat.card_perm, h5] at hdvd
    exact hdvd
  have hAT : fusionUnitA ∈ fusionStabT := by
    change ![1, 0, 0, 0] ᵥ* fusionA = ![1, 0, 0, 0]
    decide
  have hBT : fusionUnitB ∈ fusionStabT := by
    change ![1, 0, 0, 0] ᵥ* fusionB = ![1, 0, 0, 0]
    decide
  have hFT : fusionUnitF ∈ fusionStabT := by
    change ![1, 0, 0, 0] ᵥ* fusionF = ![1, 0, 0, 0]
    decide
  have h4 : 4 ∣ Nat.card (H ⊓ fusionStabT : Subgroup (GL (Fin 4) (ZMod 2))) := by
    have := card_dvd_of_le ((closure_le (H ⊓ fusionStabT)).2
      (Set.insert_subset_iff.2 ⟨⟨hA, hAT⟩, Set.singleton_subset_iff.2 ⟨hB, hBT⟩⟩))
    rwa [card_closure_fusionUnitA_fusionUnitB] at this
  have hF3 : orderOf fusionUnitF = 3 :=
    orderOf_eq_prime (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; decide))
      (fun e => absurd (congrArg Units.val e) (by decide))
  have h3 : 3 ∣ Nat.card (H ⊓ fusionStabT : Subgroup (GL (Fin 4) (ZMod 2))) := by
    have := card_dvd_of_le (zpowers_le.2 (show fusionUnitF ∈ H ⊓ fusionStabT from ⟨hF, hFT⟩))
    rwa [Nat.card_zpowers, hF3] at this
  have h12 : 12 ∣ Nat.card (H ⊓ fusionStabT : Subgroup (GL (Fin 4) (ZMod 2))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hlt : Nat.card (H ⊓ fusionStabT : Subgroup (GL (Fin 4) (ZMod 2))) < Nat.card H := by
    refine card_lt_of_lt (lt_of_le_of_ne inf_le_left fun e => ?_)
    obtain ⟨h, hh, hne⟩ := hmove
    have hh' : h ∈ H ⊓ fusionStabT := by
      rw [e]
      exact hh
    exact hne hh'.2
  have hpos : 0 < Nat.card (H ⊓ fusionStabT : Subgroup (GL (Fin 4) (ZMod 2))) := Nat.card_pos
  obtain ⟨k, hk⟩ := card_dvd_of_le (inf_le_left : H ⊓ fusionStabT ≤ H)
  have h12' : 12 ∣ Nat.card H := hk ▸ h12.mul_right k
  have hm12 : 12 ≤ Nat.card (H ⊓ fusionStabT : Subgroup (GL (Fin 4) (ZMod 2))) :=
    Nat.le_of_dvd hpos h12
  have h24 : 24 ≤ Nat.card H := by
    rcases k with _ | _ | k
    · rw [hk] at hlt
      omega
    · rw [hk] at hlt
      omega
    · rw [hk]
      nlinarith
  have hle : Nat.card H ≤ 120 := Nat.le_of_dvd (by norm_num) h120
  interval_cases h : Nat.card H <;> omega

@[expose] def fusionJ3 : Finset (Fin 4 → ZMod 2) :=
  {![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![1, 0, 1, 0], ![1, 0, 0, 1], ![1, 0, 1, 1]}

private def FusionJ3Check (x y z : Fin 4 → ZMod 2) : Prop :=
  y ∈ fusionJ3 → z ∈ fusionJ3 → y + z ∈ fusionJ3 → x + y ∈ fusionJ3 → x + z ∈ fusionJ3 →
    x + y + z ∈ fusionJ3 → x ≠ 0 → x = ![1, 0, 0, 0]

private instance (x y z : Fin 4 → ZMod 2) : Decidable (FusionJ3Check x y z) := by
  unfold FusionJ3Check
  infer_instance

private theorem fusionJ3Check : ∀ x y z : Fin 4 → ZMod 2, FusionJ3Check x y z := by
  decide +kernel

theorem eq_of_mem_fusionJ3 {x y z : Fin 4 → ZMod 2} (hy : y ∈ fusionJ3) (hz : z ∈ fusionJ3)
    (hyz : y + z ∈ fusionJ3) (hxy : x + y ∈ fusionJ3) (hxz : x + z ∈ fusionJ3)
    (hxyz : x + y + z ∈ fusionJ3) (hx : x ≠ 0) : x = ![1, 0, 0, 0] :=
  fusionJ3Check x y z hy hz hyz hxy hxz hxyz hx

end CFSG.OddTranspositions.PartThree.Wong
