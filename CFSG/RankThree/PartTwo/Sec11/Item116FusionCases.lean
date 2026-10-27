module

public import CFSG.RankThree.PartTwo.Sec11.RFactsK

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Item116Fusion

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_three_mem {W C : Subgroup G}
    (h3 : ∀ w ∈ W, (∃ k : ℕ, w ^ 3 ^ k = 1) → w ∈ C) {y : G} (hy : y ∈ W) (hy3 : y ^ 3 ∈ C) :
    y ∈ C := by
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  have hym : y ^ m ∈ C := h3 _ (W.pow_mem hy m) ⟨e, by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]⟩
  have hcop : Nat.Coprime m 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hy' : y = (y ^ m) ^ u * (y ^ 3) ^ v := by
    rw [← zpow_natCast y m, ← zpow_natCast y 3, ← zpow_mul, ← zpow_mul, ← zpow_add]
    conv_lhs => rw [← zpow_one y]
    congr 1
    linear_combination -huv
  rw [hy']
  exact C.mul_mem (C.zpow_mem hym u) (C.zpow_mem hy3 v)

omit [Finite G] in
theorem mem_centralizer_iff_conj {B : Subgroup G} {w : G} :
    w ∈ Subgroup.centralizer (B : Set G) ↔ ∀ b ∈ B, w * b * w⁻¹ = b := by
  rw [Subgroup.mem_centralizer_iff]
  refine ⟨fun h b hb => ?_, fun h b hb => ?_⟩
  · rw [← h b hb, mul_inv_cancel_right]
  · calc b * w = w * b * w⁻¹ * w := by rw [h b hb]
      _ = w * b := by group

omit [Finite G] in
theorem conj_mem_of_closure {A B : Subgroup G} (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) {S : Set G}
    (hSA : Subgroup.closure S = A) (hS : ∀ s ∈ S, s⁻¹ * (w⁻¹ * s * w) ∈ B) :
    ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ B := by
  have hconj : ∀ x ∈ A, w⁻¹ * x * w ∈ A := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) x).mp hx
    rwa [inv_inv] at this
  intro x hx
  rw [← hSA] at hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxA : x ∈ A := hSA ▸ hx
    have hyA : y ∈ A := hSA ▸ hy
    have e : (x * y)⁻¹ * (w⁻¹ * (x * y) * w) =
        (x⁻¹ * (w⁻¹ * x * w)) * (y⁻¹ * (w⁻¹ * y * w)) := by
      have h1 : (x * y)⁻¹ * (w⁻¹ * (x * y) * w) =
          y⁻¹ * (x⁻¹ * (w⁻¹ * x * w)) * (w⁻¹ * y * w) := by group
      rw [h1, hcomm _ (A.inv_mem hyA) _ (A.mul_mem (A.inv_mem hxA) (hconj x hxA)), mul_assoc]
    rw [e]
    exact B.mul_mem ihx ihy
  | inv x hx ihx =>
    have hxA : x ∈ A := hSA ▸ hx
    have e : x⁻¹⁻¹ * (w⁻¹ * x⁻¹ * w) = (x⁻¹ * (w⁻¹ * x * w))⁻¹ := by
      have h1 : x⁻¹⁻¹ * (w⁻¹ * x⁻¹ * w) = x * (w⁻¹ * x * w)⁻¹ := by group
      rw [h1, hcomm x hxA _ (A.inv_mem (hconj x hxA))]
      group
    rw [e]
    exact B.inv_mem ihx

theorem card_closure_pair_eq_nine {A : Subgroup G} (hexp : ∀ u ∈ A, u ^ 3 = 1)
    (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) {c d : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (hc1 : c ≠ 1) (hdc : d ∉ Subgroup.zpowers c) :
    Nat.card (Subgroup.closure ({c, d} : Set G)) = 9 := by
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  have hle : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcA
    · exact hdA
  have h1 : Subgroup.zpowers c ≤ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have h9 := Sec9.three_mul_card_le_of_le_of_ne hA3 hle h1 (fun h => hdc (by
    rw [h]
    exact Subgroup.subset_closure (by simp)))
  rw [Nat.card_zpowers, hco] at h9
  have h2 := Sec10.card_closure_pair_le (hcomm c hcA d hdA) (hexp c hcA) (hexp d hdA)
  omega

omit [Finite G] in
theorem conj_eq_of_mem_closure_pair {c d g : G} (hc : g * c * g⁻¹ = c)
    (hd : g * d * g⁻¹ = d) : ∀ b ∈ Subgroup.closure ({c, d} : Set G), g * b * g⁻¹ = b := by
  have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with hy | hy <;> rw [hy]
    · exact mul_comm_of_conj_eq hc
    · exact mul_comm_of_conj_eq hd
  intro b hb
  rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hb), mul_inv_cancel_right]

omit [Finite G] in
theorem coordMat_apply_of_conj {A : Subgroup G} {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    {w : Subgroup.normalizer (A : Set G)} {j : Fin 3} {u : Fin 3 → ZMod 3}
    (h : (w : G) * (f (Multiplicative.ofAdd (Pi.single j 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd u) : G)) (i : Fin 3) : coordMat f w i j = u i := by
  rw [coordMat, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, wAction_eq_of_conj h]

omit [Finite G] in
theorem conj_eq_coordMat {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (w : Subgroup.normalizer (A : Set G)) (j : Fin 3) :
    (w : G) * (f (Multiplicative.ofAdd (Pi.single j 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (fun i => coordMat f w i j)) : G) := by
  have e : (fun i => coordMat f w i j) = Sec12.wAction f w (Pi.single j 1) := by
    funext i
    rw [coordMat, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  rw [e, Sec12.wAction_apply]

omit [Finite G] in
theorem pow_val_two_mul {x : G} (hx : x ^ 3 = 1) (q : ZMod 3) :
    x ^ (2 * q).val = x⁻¹ ^ q.val := by
  have hx2 : x⁻¹ = x ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hx
  rw [hx2, ← pow_mul, ZMod.val_mul, show (2 : ZMod 3).val = 2 from rfl,
    ← pow_eq_pow_mod_three hx]

end General

section Matrices

open Matrix

abbrev Mat22 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

@[expose] def blk (M : KFacts.Mat33) : Mat22 :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem blk_mul {M N : KFacts.Mat33} (hN0 : N 2 0 = 0) (hN1 : N 2 1 = 0) :
    blk (M * N) = blk M * blk N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hN0, hN1]

theorem sd16_cases : ∀ p q s t p' q' s' t' : ZMod 3,
    p * p' + q * s' = 1 → p * q' + q * t' = 0 → s * p' + t * s' = 0 → s * q' + t * t' = 1 →
    (s = 0 ∧ q = 0) ∨ (p = 0 ∧ t = 0) ∨ (s = p ∧ t = 2 * q) ∨ (s = 2 * p ∧ t = q) ∨
    ((!![1, 0; 0, 2] * !![p, q; s, t] * !![1, 0; 0, 2] * !![p', q'; s', t'] : Mat22) ^ 2 ≠ 1 ∧
      ((!![1, 0; 0, 2] * !![p, q; s, t] * !![1, 0; 0, 2] * !![p', q'; s', t'] : Mat22) ^ 2) ^ 3 =
        1) := by
  decide +kernel

end Matrices

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem closure_le_innerPreimage (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) :
    Subgroup.closure ({c, d} : Set G) ≤ innerPreimage L := by
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hdLL : d ∈ L := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).2
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy <;> rw [hy]
  · have hcCL : c ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun l hl => (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
    have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.centralizer_le_normalizer _ hcCL
    refine mem_innerPreimage_iff.mpr ⟨hcN, ⟨1, ?_⟩⟩
    have h1 : Sec4.compAction L ⟨c, hcN⟩ = 1 := by
      ext x
      rw [Sec4.compAction, Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply,
        ← (Subgroup.mem_centralizer_iff.mp hcCL x x.2), mul_inv_cancel_right]
    rw [h1, map_one, map_one]
  · refine mem_innerPreimage_iff.mpr ⟨Subgroup.le_normalizer hdLL, ?_⟩
    rw [thetaQuotMulAut_compAction_of_mem L hdLL]
    exact ⟨_, rfl⟩

theorem not_mem_innerPreimage (h : Sec11Std G A c L a R Y) : a ∉ innerPreimage L := by
  intro ha
  obtain ⟨haN, hinn⟩ := mem_innerPreimage_iff.mp ha
  obtain ⟨haN', hout⟩ := h.toHyp81.inducesOuterTheta
  exact hout hinn

theorem closure_cda_eq (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    Subgroup.closure ({c, d, a} : Set G) = A := by
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  exact closure_triple_eq h.mem_partTwoF.1.2 h.card_eq h.mem_A hdA h.a_mem h.ne_one hdc
    (fun ha => not_mem_innerPreimage h (closure_le_innerPreimage h hdL ha))

theorem le_normalizer_L (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    A ≤ Subgroup.normalizer (L : Set G) := by
  have hdL' : d ∈ L := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).2
  rw [← closure_cda_eq h hdL hdc, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy <;> rw [hy]
  · have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  · exact Subgroup.le_normalizer hdL'
  · exact h.toHyp81.a_mem_normalizer

theorem inf_le_normalizer_L (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  exact Sec10.le_normalizer_of_mem_inf h.toHyp81 (le_normalizer_L h hdL hdc) hdAL.1 hdAL.2 hdc

theorem conj_mem_zpowers_d (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {w : G}
    (hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hwW : w ∈ Subgroup.normalizer (A : Set G)) : w * d * w⁻¹ ∈ Subgroup.zpowers d := by
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  have hwL := inf_le_normalizer_L h hdL hdc ⟨hwH, hwW⟩
  rw [← hdL]
  exact ⟨(Subgroup.mem_normalizer_iff.mp hwW d).mp hdAL.1,
    (Subgroup.mem_normalizer_iff.mp hwL d).mp hdAL.2⟩

theorem exists_coords_cda (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) = c ∧
      (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) = d ∧
      (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) = a ∧
      ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
        c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val := by
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  obtain ⟨f, hfc, hfd, hfa, hfv⟩ := exists_coords_triple hcomm hAe.2 h.card_eq h.mem_A hdA
    h.a_mem (closure_cda_eq h hdL hdc)
  exact ⟨f, congrArg Subtype.val hfc, congrArg Subtype.val hfd, congrArg Subtype.val hfa, hfv⟩

theorem exists_mem_closure_mul_pow (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {x : G} (hx : x ∈ A) :
    ∃ b ∈ Subgroup.closure ({c, d} : Set G), ∃ k : ℕ, k < 3 ∧ x = b * a ^ k := by
  obtain ⟨f, -, -, -, hfv⟩ := exists_coords_cda h hdL hdc
  set v := Multiplicative.toAdd (f.symm ⟨x, hx⟩) with hv
  have hx' : x = (f (Multiplicative.ofAdd v) : G) := by
    rw [hv, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rw [hfv] at hx'
  refine ⟨c ^ (v 0).val * d ^ (v 1).val, Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _), (v 2).val, ZMod.val_lt _, hx'⟩

theorem threeElement_centralizes (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d}))) :
    ∀ w ∈ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) →
      ∀ b ∈ Subgroup.closure ({c, d} : Set G), w * b * w⁻¹ = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  by_cases hdc : d ∈ Subgroup.zpowers c
  ·
    have hBc : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.zpowers c := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact Subgroup.mem_zpowers c
      · exact hdc
    rintro w hwW ⟨k, hk⟩ b hb
    have hwc : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
      hBc ((Subgroup.mem_normalizer_iff.mp (hWB hwW) c).mp hcB)
    have hwc' : Commute w c := Sec12.commute_of_conj_mem_zpowers hco hwc hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hBc hb)
    rw [(hwc'.zpow_right j).eq, mul_inv_cancel_right]
  · have hdA := hdAL.1
    have hBA : Subgroup.closure ({c, d} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact hcA
      · exact hdA
    have hB9 := card_closure_pair_eq_nine hexp hcomm hcA hdA hc1 hdc
    have hBe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c, d} : Set G)) :=
      ⟨⟨⟨fun x y => Subtype.ext (hcomm _ (hBA x.2) _ (hBA y.2))⟩⟩, fun x hx => hexp x (hBA hx)⟩
    have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
    have hdo : orderOf d = 3 := orderOf_eq_prime (hexp d hdA) hd1
    obtain ⟨S, hSW, hSc⟩ := exists_isSylowOf_le_normalizer hBe hB9 hWB hirr hcB hc1
    have hSB : ∀ s ∈ S, ∀ b ∈ Subgroup.closure ({c, d} : Set G), s * b * s⁻¹ = b := by
      intro s hs
      obtain ⟨k, hk⟩ := hSW.isPGroup ⟨s, hs⟩
      have hk' : s ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hsc : s * c * s⁻¹ ∈ Subgroup.zpowers c :=
        (Subgroup.mem_normalizer_iff.mp (hSc hs) c).mp (Subgroup.mem_zpowers c)
      have hsd := conj_mem_zpowers_d h hdL hdc (hSc hs) (hSW.le hs)
      have h1 : s * c = c * s := Sec12.commute_of_conj_mem_zpowers hco hsc hk'
      have h2 : s * d = d * s := Sec12.commute_of_conj_mem_zpowers hdo hsd hk'
      have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rcases hy with hy | hy <;> rw [hy]
        · exact h1.symm
        · exact h2.symm
      intro b hb
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hb), mul_inv_cancel_right]
    rintro w hwW ⟨k, hk⟩ b hb
    have hP : IsPGroup 3 (Subgroup.zpowers w) := by
      rintro ⟨g, hg⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    obtain ⟨S', hS', hwS'⟩ := exists_isSylowOf_ge hP (Subgroup.zpowers_le.mpr hwW)
    obtain ⟨g, hgW, hg⟩ := hSW.exists_mem_conj hS'
    have hgw : g⁻¹ * w * g ∈ S := (hg w).mp (hwS' (Subgroup.mem_zpowers w))
    have hgb : g⁻¹ * b * g ∈ Subgroup.closure ({c, d} : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (hWB (Subgroup.inv_mem _ hgW)) b).mp hb
      rwa [inv_inv] at this
    have h1 := hSB _ hgw _ hgb
    calc w * b * w⁻¹ = g * ((g⁻¹ * w * g) * (g⁻¹ * b * g) * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * b * g) * g⁻¹ := by rw [h1]
      _ = b := by group

theorem conj_mem_of_mem_normalizer_zpowers (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {w : G}
    (hwW : w ∈ Subgroup.normalizer (A : Set G))
    (hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA := h.a_mem
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hwH' : w⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := Subgroup.inv_mem _ hwH
  have hwW' : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hwW
  have hconj : ∀ x ∈ A, w⁻¹ * x * w ∈ A := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp hwW' x).mp hx
    rwa [inv_inv] at this
  apply conj_mem_of_closure hcomm hwW (closure_cda_eq h hdL hdc)
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with hs | hs | hs <;> rw [hs]
  · have h1 : w⁻¹ * c * w ∈ Subgroup.zpowers c := by
      have := (Subgroup.mem_normalizer_iff.mp hwH' c).mp (Subgroup.mem_zpowers c)
      rwa [inv_inv] at this
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcB) (Subgroup.zpowers_le.mpr hcB h1)
  · have h1 : w⁻¹ * d * w ∈ Subgroup.zpowers d := by
      have := conj_mem_zpowers_d h hdL hdc hwH' hwW'
      rwa [inv_inv] at this
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hdB) (Subgroup.zpowers_le.mpr hdB h1)
  ·
    have hwL : w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      inf_le_normalizer_L h hdL hdc ⟨hwH', hwW'⟩
    have haL : a⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.inv_mem _ h.toHyp81.a_mem_normalizer
    have hU := commutator_mem_innerPreimage outAbelian1016 h.isList1016 haL hwL
    rw [inv_inv, inv_inv] at hU
    obtain ⟨b, hb, k, hk3, hbk⟩ := exists_mem_closure_mul_pow h hdL hdc
      (A.mul_mem (A.inv_mem haA) (hconj a haA))
    have hak : a ^ k ∈ innerPreimage L := by
      have e : a ^ k = b⁻¹ * (a⁻¹ * w⁻¹ * a * w) := by
        rw [show a⁻¹ * w⁻¹ * a * w = a⁻¹ * (w⁻¹ * a * w) by group, hbk]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (closure_le_innerPreimage h hdL hb)) hU
    have hk0 : k = 0 := by
      by_contra hk0
      apply not_mem_innerPreimage h
      rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
      · rwa [pow_one] at hak
      · have h2 := Subgroup.pow_mem _ hak 2
        rwa [← pow_mul, show a ^ (2 * 2) = a by
          rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, hexp a haA, one_mul]] at h2
    rw [hbk, hk0, pow_zero, mul_one]
    exact hb

open CFSG.GorensteinWalter in
theorem exists_inverting (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hexp d hdAL.1) hd1
  have hA : A = Subgroup.closure {c, a, d} := by
    rw [← closure_cda_eq h hdL hdc, Set.pair_comm d a]
  have hsc : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  have key : ∀ {K : Type} [Field K] [Finite K], (3 : K) ≠ 0 →
      (L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) →
      ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), l * d * l⁻¹ = d⁻¹ := by
    intro K _ _ h3K e
    have hout : Sec4.InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
    have ha := KFacts.inducesKind_field_of_pow_three L (hexp a h.a_mem) hout e
    exact KFacts.exists_inverting_of_inducesKindPSL2 h3K hAe h.mem_A h.a_mem hdAL.1 hA hsc.2
      hdAL.2 hd1 e ha
  rcases h.isList1016 with ⟨p, e, _, hp, -, ⟨eq⟩⟩ | ⟨n, -, ⟨eq⟩⟩ | ⟨n, hn, hL⟩
  · exact key (KFacts.three_ne_zero_galoisField (by omega) _)
      (eq.trans (Sec4.projSLEquivPSL _))
  · exact key (KFacts.three_ne_zero_galoisField (by norm_num) _)
      (eq.trans (Sec4.projSLEquivPSL _))
  · have haN := h.toHyp81.a_mem_normalizer
    set τ₀ := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hτ₀
    have hτ3 : τ₀ ^ 3 = 1 := h.toHyp81.induced_pow_three
    have hτout : ¬ KFacts.IsInnerAut τ₀ := h.toHyp81.not_isInnerAut_induced
    set db : L ⧸ aschbacherSolvableCore 3 L :=
      ((⟨d, hdAL.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) with hdb
    have hτd : τ₀ db = db := by
      rw [hdb, hτ₀, Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      show a * d * a⁻¹ = d
      rw [hcomm a h.a_mem d hdAL.1, mul_inv_cancel_right]
    have hdb3 : db ^ 3 = 1 := by
      rw [hdb, ← QuotientGroup.mk_pow]
      have : (⟨d, hdAL.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hexp d hdAL.1)
      rw [this, QuotientGroup.mk_one]
    have hdb1 : db ≠ 1 := by
      intro h1
      rw [hdb, QuotientGroup.eq_one_iff] at h1
      have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
      have h2 := Subgroup.orderOf_dvd_natCard _ h1
      rw [Subgroup.orderOf_mk, hd3] at h2
      exact hθ3 h2
    obtain ⟨yb, hybτ, hybd⟩ := lThreeMinusPiInverting _ n hn hL τ₀ hτ3 hτout db hdb3 hdb1 hτd
    exact KFacts.exists_inverting_of_bar hAe h.mem_A h.a_mem hdAL.1 hA hsc.2 hdAL.2 haN yb
      hybτ hybd

theorem mem_sd16 (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d}))) :
    ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have hco : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  have hdA := hdAL.1
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  by_cases hdc : d ∈ Subgroup.zpowers c
  ·
    intro w hwW
    left
    have hBc : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.zpowers c := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · exact Subgroup.mem_zpowers c
      · exact hdc
    refine ⟨hBc ((Subgroup.mem_normalizer_iff.mp (hWB hwW) c).mp hcB), ?_⟩
    by_cases hd1 : d = 1
    · rw [hd1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hdo : orderOf d = 3 := orderOf_eq_prime (hexp d hdA) hd1
      have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc) (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hco, hdo])
      rw [heq]
      exact hBc ((Subgroup.mem_normalizer_iff.mp (hWB hwW) d).mp hdB)
  obtain ⟨f, hfc, hfd, hfa, hfv⟩ := exists_coords_cda h hdL hdc
  obtain ⟨l₁, ⟨hl₁L, hl₁W⟩, hl₁d⟩ := exists_inverting h hdL hdc
  have hl₁c := conj_eq_of_mem_inf_normalizer h.toHyp91 hl₁L hl₁W
  have h3 := threeElement_centralizes h hdL hWB hirr
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) :=
    fun ha => not_mem_innerPreimage h (closure_le_innerPreimage h hdL ha)
  have hd3 : d ^ 3 = 1 := hexp d hdA
  have hvB : ∀ v : Fin 3 → ZMod 3,
      (f (Multiplicative.ofAdd v) : G) ∈ Subgroup.closure ({c, d} : Set G) → v 2 = 0 := by
    intro v hv
    rw [hfv] at hv
    have h1 : a ^ (v 2).val ∈ Subgroup.closure ({c, d} : Set G) := by
      have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ hcB (v 0).val) (Subgroup.pow_mem _ hdB (v 1).val))) hv
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
    by_contra hv2
    apply haB
    have hlt := ZMod.val_lt (v 2)
    have hne : (v 2).val ≠ 0 := fun h0 => hv2 ((ZMod.val_eq_zero _).mp h0)
    rcases (by omega : (v 2).val = 1 ∨ (v 2).val = 2) with h2 | h2
    · rwa [h2, pow_one] at h1
    · rw [h2] at h1
      have h4 := Subgroup.pow_mem _ h1 2
      rwa [← pow_mul, show a ^ (2 * 2) = a by
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, hexp a h.a_mem, one_mul]] at h4
  have hzero : ∀ y : Subgroup.normalizer (A : Set G),
      coordMat f y 2 0 = 0 ∧ coordMat f y 2 1 = 0 := by
    intro y
    have hyB := hWB y.2
    constructor
    · refine hvB (fun i => coordMat f y i 0) ?_
      rw [← conj_eq_coordMat, hfc]
      exact (Subgroup.mem_normalizer_iff.mp hyB c).mp hcB
    · refine hvB (fun i => coordMat f y i 1) ?_
      rw [← conj_eq_coordMat, hfd]
      exact (Subgroup.mem_normalizer_iff.mp hyB d).mp hdB
  have hbm : ∀ y z : Subgroup.normalizer (A : Set G),
      blk (coordMat f (y * z)) = blk (coordMat f y) * blk (coordMat f z) := fun y z => by
    rw [coordMat_mul, blk_mul (hzero z).1 (hzero z).2]
  have hb1 : ∀ y : Subgroup.normalizer (A : Set G), blk (coordMat f y) = 1 ↔
      ((y : G) * c * (y : G)⁻¹ = c ∧ (y : G) * d * (y : G)⁻¹ = d) := by
    intro y
    constructor
    · intro hy
      have e : ∀ i j : Fin 2, blk (coordMat f y) i j = (1 : Mat22) i j := fun i j => by rw [hy]
      have e00 : coordMat f y 0 0 = 1 := by simpa [blk] using e 0 0
      have e01 : coordMat f y 0 1 = 0 := by simpa [blk] using e 0 1
      have e10 : coordMat f y 1 0 = 0 := by simpa [blk] using e 1 0
      have e11 : coordMat f y 1 1 = 1 := by simpa [blk] using e 1 1
      have col0 : (fun i => coordMat f y i 0) = Pi.single 0 1 := by
        funext i
        fin_cases i <;> simp [e00, e10, (hzero y).1]
      have col1 : (fun i => coordMat f y i 1) = Pi.single 1 1 := by
        funext i
        fin_cases i <;> simp [e01, e11, (hzero y).2]
      constructor
      · have h0 := conj_eq_coordMat f y 0
        rw [col0, hfc] at h0
        exact h0
      · have h1 := conj_eq_coordMat f y 1
        rw [col1, hfd] at h1
        exact h1
    · rintro ⟨h0, h1⟩
      have c0 := coordMat_apply_of_conj (w := y) (j := 0) (u := Pi.single 0 1)
        (by rw [hfc]; exact h0)
      have c1 := coordMat_apply_of_conj (w := y) (j := 1) (u := Pi.single 1 1)
        (by rw [hfd]; exact h1)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blk, c0, c1]
  have hE2 : ∀ y : Subgroup.normalizer (A : Set G),
      blk (coordMat f y) ^ 3 = 1 → blk (coordMat f y) = 1 := by
    intro y hy3
    have h1 : blk (coordMat f (y ^ 3)) = 1 := by
      rw [pow_succ, pow_two, hbm, hbm]
      rw [pow_succ, pow_two] at hy3
      exact hy3
    obtain ⟨hc3, hd3'⟩ := (hb1 _).mp h1
    have hyC : (y : G) ∈ Subgroup.centralizer
        ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G) := by
      refine mem_of_pow_three_mem (W := Subgroup.normalizer (A : Set G))
        (fun w hw hk => mem_centralizer_iff_conj.mpr (h3 w hw hk)) y.2 ?_
      rw [mem_centralizer_iff_conj]
      push_cast at hc3 hd3'
      exact conj_eq_of_mem_closure_pair hc3 hd3'
    rw [mem_centralizer_iff_conj] at hyC
    exact (hb1 y).mpr ⟨hyC c hcB, hyC d hdB⟩
  set l' : Subgroup.normalizer (A : Set G) := ⟨l₁, hl₁W⟩ with hl'
  have hd2 : l₁ * d * l₁⁻¹ = d ^ 2 := by
    rw [hl₁d, inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hd3
  have hr : blk (coordMat f l') = !![1, 0; 0, 2] := by
    have c0 := coordMat_apply_of_conj (w := l') (j := 0) (u := Pi.single 0 1)
      (by rw [hfc]; exact hl₁c)
    have c1 := coordMat_apply_of_conj (w := l') (j := 1) (u := ![0, 2, 0]) (by
      rw [hfd, hfv]
      show l₁ * d * l₁⁻¹ = _
      rw [hd2]
      simp
      rfl)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk, c0, c1]
  intro w hwW
  set w' : Subgroup.normalizer (A : Set G) := ⟨w, hwW⟩ with hw'
  have hPQ : blk (coordMat f w') * blk (coordMat f w'⁻¹) = 1 := by
    rw [← hbm, mul_inv_cancel]
    exact (hb1 1).mpr ⟨by simp, by simp⟩
  have hcw : w * c * w⁻¹ = (f (Multiplicative.ofAdd (fun i => coordMat f w' i 0)) : G) := by
    rw [← conj_eq_coordMat, hfc]
  have hdw : w * d * w⁻¹ = (f (Multiplicative.ofAdd (fun i => coordMat f w' i 1)) : G) := by
    rw [← conj_eq_coordMat, hfd]
  have hcd : Commute c d := hcomm c hcA d hdA
  rw [hcw, hdw, hfv, hfv]
  simp only [(hzero w').1, (hzero w').2, ZMod.val_zero, pow_zero, mul_one]
  have hPQ' : ∀ i j : Fin 2,
      (blk (coordMat f w') * blk (coordMat f w'⁻¹)) i j = (1 : Mat22) i j := fun i j => by
    rw [hPQ]
  have e00 := hPQ' 0 0
  have e01 := hPQ' 0 1
  have e10 := hPQ' 1 0
  have e11 := hPQ' 1 1
  simp only [blk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11
  rcases sd16_cases (coordMat f w' 0 0) (coordMat f w' 0 1) (coordMat f w' 1 0)
      (coordMat f w' 1 1) (coordMat f w'⁻¹ 0 0) (coordMat f w'⁻¹ 0 1) (coordMat f w'⁻¹ 1 0)
      (coordMat f w'⁻¹ 1 1) e00 e01 e10 e11 with
    ⟨hs, hq⟩ | ⟨hp, ht⟩ | ⟨hs, ht⟩ | ⟨hs, ht⟩ | ⟨hz1, hz3⟩
  · left
    rw [hs, hq, ZMod.val_zero, pow_zero, pow_zero, mul_one, one_mul]
    exact ⟨Subgroup.npow_mem_zpowers _ _, Subgroup.npow_mem_zpowers _ _⟩
  · right; left
    rw [hp, ht, ZMod.val_zero, pow_zero, pow_zero, mul_one, one_mul]
    exact ⟨Subgroup.npow_mem_zpowers _ _, Subgroup.npow_mem_zpowers _ _⟩
  · right; right; left
    rw [hs, ht, pow_val_two_mul hd3, ← hcd.mul_pow, ← (hcd.inv_right).mul_pow]
    exact ⟨Subgroup.npow_mem_zpowers _ _, Subgroup.npow_mem_zpowers _ _⟩
  · right; right; right
    rw [hs, ht, pow_val_two_mul hd3, ← hcd.mul_pow, ← (hcd.inv_right).mul_pow]
    exact ⟨Subgroup.npow_mem_zpowers _ _, Subgroup.npow_mem_zpowers _ _⟩
  ·
    exfalso
    set x := l' * w' * l' * w'⁻¹ with hx
    have hbx : blk (coordMat f x) = !![1, 0; 0, 2] * blk (coordMat f w') * !![1, 0; 0, 2] *
        blk (coordMat f w'⁻¹) := by
      rw [hx, hbm, hbm, hbm, hr]
    have hbx2 : blk (coordMat f (x ^ 2)) = blk (coordMat f x) ^ 2 := by
      rw [pow_two, pow_two, hbm]
    apply hz1
    have h1 := hE2 (x ^ 2) (by rw [hbx2, hbx]; exact hz3)
    rw [hbx2, hbx] at h1
    exact h1

open CFSG.GorensteinWalter in
theorem exists_transvection (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
      ∃ x ∈ A, l * x * l⁻¹ ≠ x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hA : A = Subgroup.closure {c, a, d} := by
    rw [← closure_cda_eq h hdL hdc, Set.pair_comm d a]
  have hsc : c ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    rw [h.sectionCentralizer_eq]
    exact Subgroup.mem_zpowers c
  have key : ∀ {K : Type} [Field K] [Finite K], (3 : K) ≠ 0 →
      (L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 K) →
      ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ 3 ^ k = 1) ∧
        ∃ x ∈ A, l * x * l⁻¹ ≠ x := by
    intro K _ _ h3K e
    have hout : Sec4.InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
    have ha := KFacts.inducesKind_field_of_pow_three L (hexp a h.a_mem) hout e
    exact KFacts.exists_threeElement_moving_of_inducesKindPSL2 h3K hAe h.mem_A h.a_mem hdAL.1 hA
      hsc.2 hdAL.2 hd1 e ha
  rcases h.isList1016 with ⟨p, e, _, hp, -, ⟨eq⟩⟩ | ⟨n, -, ⟨eq⟩⟩ | ⟨n, hn, hL⟩
  · exact key (KFacts.three_ne_zero_galoisField (by omega) _)
      (eq.trans (Sec4.projSLEquivPSL _))
  · exact key (KFacts.three_ne_zero_galoisField (by norm_num) _)
      (eq.trans (Sec4.projSLEquivPSL _))
  · have hAN : A ≤ Subgroup.normalizer (L : Set G) := le_normalizer_L h hdL hdc
    have hΩ : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, y * x = x * y) → x ∈ A := fun x hx3 hx =>
      Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3 fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hx y hy)
    have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
    have hcyc := KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi hn hL
    have hab : ∀ Q : Sylow 3 L, ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L),
        x * y = y * x := by
      intro Q x hx y hy
      have hinj : ∀ z ∈ (Q : Subgroup L), π z = 1 → z = 1 := by
        intro z hz hz1
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
        obtain ⟨k, hk⟩ := Q.isPGroup' ⟨z, hz⟩
        have hk' : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have h1 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
        have h2 : orderOf z ∣ Nat.card (aschbacherSolvableCore 3 L) :=
          Subgroup.orderOf_dvd_natCard _ hz1
        have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
          Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
      obtain ⟨S, hS⟩ := (Q.isPGroup'.map π).exists_le_sylow
      have := hcyc S
      have hc : π x * π y = π y * π x := by
        have h1 := (IsCyclic.commGroup (α := S)).mul_comm ⟨π x, hS ⟨x, hx, rfl⟩⟩
          ⟨π y, hS ⟨y, hy, rfl⟩⟩
        exact congrArg Subtype.val h1
      have h2 : π (x * y * (y * x)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
      have h3 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hx hy)
        ((Q : Subgroup L).inv_mem ((Q : Subgroup L).mul_mem hy hx))) h2
      exact mul_inv_eq_one.mp h3
    have haN := h.toHyp81.a_mem_normalizer
    set τ₀ := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hτ₀
    have hτ3 : τ₀ ^ 3 = 1 := h.toHyp81.induced_pow_three
    have hτout : ¬ KFacts.IsInnerAut τ₀ := h.toHyp81.not_isInnerAut_induced
    have hQ : ∀ Q : Sylow 3 L, ¬ ∀ y ∈ (Q : Subgroup L), a * (y : G) = y * a := by
      intro Q hQa
      obtain ⟨y, hy, hy'⟩ := lThreeMinusPiNoFixedSylow _ n hn hL τ₀ hτ3 hτout
        (Q.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L)))
      apply hy'
      rw [Sylow.coe_mapSurjective] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [QuotientGroup.mk'_apply, hτ₀, Sec4.thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      show a * z * a⁻¹ = z
      rw [hQa z hz, mul_inv_cancel_right]
    exact KFacts.exists_moving_of_not_centralizes_sylow hcomm hexp hΩ hAN h.a_mem hab hQ

theorem exists_transvection_eq (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) :
    ∀ b ∈ Subgroup.closure ({c, d} : Set G), ∃ w ∈ Subgroup.normalizer (A : Set G),
      (∀ y ∈ Subgroup.closure ({c, d} : Set G), w * y * w⁻¹ = y) ∧ w * a * w⁻¹ = a * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA := h.a_mem
  have hdAL : d ∈ A ⊓ L := by rw [hdL]; exact Subgroup.mem_zpowers d
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hdo : orderOf d = 3 := orderOf_eq_prime (hexp d hdAL.1) hd1
  set B := Subgroup.closure ({c, d} : Set G) with hB
  set W := Subgroup.normalizer (A : Set G) with hW
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy]
    · exact h.mem_A
    · exact hdAL.1
  have haB : a ∉ B := fun ha => not_mem_innerPreimage h (closure_le_innerPreimage h hdL ha)
  have hconjB : ∀ g ∈ W, ∀ y ∈ B, g * y * g⁻¹ ∈ B := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hWB hg) y).mp hy
  have hconjA : ∀ g ∈ W, ∀ y ∈ A, g * y * g⁻¹ ∈ A := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  let T : Subgroup G :=
    { carrier := {b | b ∈ B ∧ ∃ w ∈ W, (∀ y ∈ B, w * y * w⁻¹ = y) ∧ w * a * w⁻¹ = a * b}
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁, w₁, hw₁, hc₁, ha₁⟩ ⟨hb₂, w₂, hw₂, hc₂, ha₂⟩
        refine ⟨B.mul_mem hb₁ hb₂, w₁ * w₂, W.mul_mem hw₁ hw₂, fun y hy => ?_, ?_⟩
        · calc w₁ * w₂ * y * (w₁ * w₂)⁻¹ = w₁ * (w₂ * y * w₂⁻¹) * w₁⁻¹ := by group
            _ = y := by rw [hc₂ y hy, hc₁ y hy]
        · calc w₁ * w₂ * a * (w₁ * w₂)⁻¹ = w₁ * (w₂ * a * w₂⁻¹) * w₁⁻¹ := by group
            _ = (w₁ * a * w₁⁻¹) * (w₁ * b₂ * w₁⁻¹) := by rw [ha₂]; group
            _ = a * (b₁ * b₂) := by rw [ha₁, hc₁ b₂ hb₂, mul_assoc]
      one_mem' := ⟨B.one_mem, 1, W.one_mem, fun y _ => by group, by group⟩
      inv_mem' := by
        rintro b ⟨hb, w, hw, hc, ha⟩
        refine ⟨B.inv_mem hb, w⁻¹, W.inv_mem hw, fun y hy => ?_, ?_⟩
        · rw [inv_inv]
          calc w⁻¹ * y * w = w⁻¹ * (w * y * w⁻¹) * w := by rw [hc y hy]
            _ = y := by group
        · have h1 : w⁻¹ * b * w = b := by
            calc w⁻¹ * b * w = w⁻¹ * (w * b * w⁻¹) * w := by rw [hc b hb]
              _ = b := by group
          have h2 : a = (w⁻¹ * a * w) * (w⁻¹ * b * w) := by
            calc a = w⁻¹ * (w * a * w⁻¹) * w := by group
              _ = w⁻¹ * (a * b) * w := by rw [ha]
              _ = (w⁻¹ * a * w) * (w⁻¹ * b * w) := by group
          rw [h1] at h2
          rw [inv_inv]
          calc w⁻¹ * a * w = (w⁻¹ * a * w) * b * b⁻¹ := by group
            _ = a * b⁻¹ := by rw [← h2] }
  have hTB : T ≤ B := fun b hb => hb.1
  have hTW : ∀ g ∈ W, ∀ b ∈ T, g * b * g⁻¹ ∈ T := by
    rintro g hg b ⟨hb, w, hw, hc, ha⟩
    have hg' : g⁻¹ ∈ W := W.inv_mem hg
    have hgaA : g⁻¹ * a * g ∈ A := by
      have := hconjA _ hg' a haA
      rwa [inv_inv] at this
    obtain ⟨b'', hb'', j, hj3, hj⟩ := exists_mem_closure_mul_pow h hdL hdc hgaA
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply haB
      rw [pow_zero, mul_one] at hj
      have := hconjB g hg _ (hj ▸ hb'')
      rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at this
    have hgb : g * b * g⁻¹ ∈ B := hconjB g hg b hb
    have hc' : ∀ y ∈ B, g * w * g⁻¹ * y * (g * w * g⁻¹)⁻¹ = y := by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ B := by
        have := hconjB _ hg' y hy
        rwa [inv_inv] at this
      calc g * w * g⁻¹ * y * (g * w * g⁻¹)⁻¹ = g * (w * (g⁻¹ * y * g) * w⁻¹) * g⁻¹ := by group
        _ = y := by rw [hc _ hy']; group
    have hwaj : w * a ^ j * w⁻¹ = (a * b) ^ j := by
      rw [← conj_pow, ha]
    have ha' : g * w * g⁻¹ * a * (g * w * g⁻¹)⁻¹ = a * (g * b * g⁻¹) ^ j := by
      have hbA := hBA hb
      have hb''A := hBA hb''
      have hga : a = g * (b'' * a ^ j) * g⁻¹ := by rw [← hj]; group
      calc g * w * g⁻¹ * a * (g * w * g⁻¹)⁻¹ = g * (w * (g⁻¹ * a * g) * w⁻¹) * g⁻¹ := by group
        _ = g * ((w * b'' * w⁻¹) * (w * a ^ j * w⁻¹)) * g⁻¹ := by rw [hj]; group
        _ = g * (b'' * (a * b) ^ j) * g⁻¹ := by rw [hc b'' hb'', hwaj]
        _ = g * (b'' * a ^ j * b ^ j) * g⁻¹ := by
            rw [Commute.mul_pow (hcomm a haA b hbA) j]
            simp only [mul_assoc]
        _ = g * (b'' * a ^ j) * g⁻¹ * (g * b * g⁻¹) ^ j := by rw [conj_pow]; group
        _ = a * (g * b * g⁻¹) ^ j := by rw [← hga]
    have hTj : (g * b * g⁻¹) ^ j ∈ T :=
      ⟨B.pow_mem hgb j, g * w * g⁻¹, W.mul_mem (W.mul_mem hg hw) hg', hc', ha'⟩
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · rwa [pow_one] at hTj
    · have h2 := T.pow_mem hTj 2
      rwa [← pow_mul, show (g * b * g⁻¹) ^ (2 * 2) = g * b * g⁻¹ by
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, hexp _ (hBA hgb), one_mul]] at h2
  have hTN : ∀ g ∈ W, g ∈ Subgroup.normalizer (B : Set G) →
      g ∈ Subgroup.normalizer (T : Set G) := by
    intro g hg _
    apply mem_normalizer_of_forall_conj_mem
    intro u hu
    have := hTW g⁻¹ (W.inv_mem hg) u hu
    rwa [inv_inv] at this
  obtain ⟨l₀, ⟨hl₀L, hl₀W⟩, ⟨k, hk⟩, x₀, hx₀A, hx₀⟩ := exists_transvection h hdL hdc
  have hl₀c := conj_eq_of_mem_inf_normalizer h.toHyp91 hl₀L hl₀W
  have hl₀d : l₀ * d * l₀⁻¹ = d := by
    have h1 : l₀ * d * l₀⁻¹ ∈ Subgroup.zpowers d := by
      rw [← hdL]
      exact ⟨hconjA _ hl₀W d hdAL.1, L.mul_mem (L.mul_mem hl₀L hdAL.2) (L.inv_mem hl₀L)⟩
    rw [Sec12.commute_of_conj_mem_zpowers hdo h1 hk, mul_inv_cancel_right]
  have hl₀B := conj_eq_of_mem_closure_pair hl₀c hl₀d
  set b₀ := a⁻¹ * (l₀ * a * l₀⁻¹) with hb₀
  have hb₀B : b₀ ∈ B := by
    have h1 : b₀ ∈ A ⊓ L := by
      refine ⟨A.mul_mem (A.inv_mem haA) (hconjA _ hl₀W a haA), ?_⟩
      have haN := h.toHyp81.a_mem_normalizer
      have h2 : a⁻¹ * l₀ * a ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) l₀).mp hl₀L
        rwa [inv_inv] at this
      rw [show b₀ = (a⁻¹ * l₀ * a) * l₀⁻¹ by rw [hb₀]; group]
      exact L.mul_mem h2 (L.inv_mem hl₀L)
    rw [hdL] at h1
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp) : d ∈ B) h1
  have hb₀T : b₀ ∈ T := ⟨hb₀B, l₀, hl₀W, hl₀B, by rw [hb₀]; group⟩
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    apply hx₀
    have hla : l₀ * a * l₀⁻¹ = a := by
      rw [hb₀, inv_mul_eq_one] at h1
      exact h1.symm
    have hle : Subgroup.closure ({c, d, a} : Set G) ≤ Subgroup.centralizer ({l₀} : Set G) := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with hy | hy | hy <;> rw [hy]
      · exact mul_comm_of_conj_eq hl₀c
      · exact mul_comm_of_conj_eq hl₀d
      · exact mul_comm_of_conj_eq hla
    rw [← closure_cda_eq h hdL hdc] at hx₀A
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hx₀A), mul_inv_cancel_right]
  rcases eq_bot_or_eq_of_isIrreducibleOn hirr hTB hTN with hT | hT
  · exact absurd (by rw [← Subgroup.mem_bot, ← hT]; exact hb₀T) hb₀1
  · intro b hb
    rw [← hT] at hb
    obtain ⟨-, w, hw, hc, ha⟩ := hb
    exact ⟨w, hw, hc, ha⟩

theorem not_mem_zpowers_of_item45 (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) : d ∉ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hdc
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.mem_A h.ne_one L
      h.mem_thetaComponentsAt
  have h3L : 3 ∣ Nat.card L :=
    (three_dvd_card_of_isList1016 h.isList1016).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨u, ⟨huL, huA'⟩, hu3⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hAN h3L
  have hu3' : u ^ 3 = 1 := by
    rw [← hu3]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  have huA : u ∈ A := Sec15.mem_of_mem_partTwoF h.mem_partTwoF hu3' fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huA' y hy)
  have huc : u ∈ Subgroup.zpowers c := by
    have hu : u ∈ A ⊓ L := ⟨huA, huL⟩
    rw [hdL] at hu
    exact Subgroup.zpowers_le.mpr hdc hu
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun l hl => (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)))
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
    have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
    rw [show l⁻¹ * (c * l * c⁻¹) = 1 by rw [← hlc]; group]
    exact Subgroup.one_mem _
  have huC : u ∈ Sec4.thetaQuotCentralizer L := Subgroup.zpowers_le.mpr hcC huc
  have h1 := mem_theta_of_mem_thetaQuotCentralizer (center_eq_bot_of_isList1016 h.isList1016)
    huL huC
  have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (Subtype.ext (by simpa using hu3'))
  exact hu1 (congrArg Subtype.val h2)

end Certified

end Item116Fusion

section Main

@[expose] def Item116FusionE9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
        Sec21.IsIrreducibleOn
            (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) →
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ →
          (∀ w ∈ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) →
            ∀ b ∈ Subgroup.closure ({c, d} : Set G), w * b * w⁻¹ = b) →
          (∀ w ∈ Subgroup.normalizer (A : Set G),
            (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧
              w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧
              w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))) →
          (d ∉ Subgroup.zpowers c →
            Subgroup.closure ({c, d, a} : Set G) = A ∧
            (∀ b ∈ Subgroup.closure ({c, d} : Set G), ∃ w ∈ Subgroup.normalizer (A : Set G),
              (∀ y ∈ Subgroup.closure ({c, d} : Set G), w * y * w⁻¹ = y) ∧
                w * a * w⁻¹ = a * b) ∧
            ∀ w ∈ Subgroup.normalizer (A : Set G),
              w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
                ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G)) →
            ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ A,
              x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure {c, d}

theorem item116Fusion_of (hE9 : Item116FusionE9) : Item116Fusion := by
  intro G _ _ A c L a R Y h d hdL hWB hirr hRG
  exact hE9 G A c L a R Y h d hdL hWB hirr hRG
    (Item116Fusion.threeElement_centralizes h hdL hWB hirr)
    (Item116Fusion.mem_sd16 h hdL hWB hirr)
    (fun hdc => ⟨Item116Fusion.closure_cda_eq h hdL hdc,
      Item116Fusion.exists_transvection_eq h hdL hWB hirr hdc,
      fun w hwW hwH => Item116Fusion.conj_mem_of_mem_normalizer_zpowers h hdL hdc hwW hwH⟩)

end Main

end CFSG.RankThree.PartTwo.Sec11
