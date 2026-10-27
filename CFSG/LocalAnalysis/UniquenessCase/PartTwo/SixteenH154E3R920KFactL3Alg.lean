module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3BT
public import CFSG.RankThree.PartOne.MB3.FieldLmThree
public import CFSG.Quasithin.Vol2.KGFactC31LieSylGL
public import CFSG.RankThree.PartOne.N143.JTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix Subgroup Module

private lemma r920kl3a_one_le_card {K : Type} [Field K] [Finite K] : 1 ≤ Nat.card K := by
  haveI : Nonempty K := ⟨0⟩
  have := Nat.card_pos (α := K)
  omega

private lemma r920kl3a_zmod7_eq_one_iff {m : ℕ} (hm : 1 ≤ m) :
    (m : ZMod 7) = 1 ↔ 7 ∣ m - 1 := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' hm]

private lemma r920kl3a_seven_dvd_pow_three_sub_one {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : 7 ∣ Nat.card K ^ 3 - 1 := by
  have h23 : (2 : ZMod 7) ^ 3 = 1 := by decide
  rw [← r920kl3a_zmod7_eq_one_iff (m := Nat.card K ^ 3)
    (Nat.one_le_pow 3 _ (by haveI : Nonempty K := ⟨0⟩; exact Nat.card_pos)), Nat.cast_pow]
  have hcast : ((Nat.card K : ZMod 7)) = (2 : ZMod 7) ^ f := by
    rw [hK]; push_cast; rfl
  rw [hcast]
  calc ((2 : ZMod 7) ^ f) ^ 3 = (2 : ZMod 7) ^ (f * 3) := (pow_mul _ _ _).symm
    _ = (2 : ZMod 7) ^ (3 * f) := by rw [mul_comm]
    _ = ((2 : ZMod 7) ^ 3) ^ f := pow_mul _ _ _
    _ = 1 := by rw [h23, one_pow]

private lemma r920kl3a_pow_three_eq_pow_of_order_three {M : Type*} [Monoid M] {u : M}
    (h3 : u ^ 3 = 1) (h1 : u ≠ 1) {e : ℕ} (he : e ≤ 3) (h : u ^ 3 = u ^ e) :
    e = 0 ∨ e = 3 := by
  have hx : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, h3⟩
  have hord : orderOf u = 3 := by
    have hdvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) (orderOf u) hdvd with
      h' | h'
    · exfalso
      rw [orderOf_eq_one_iff] at h'
      exact h1 h'
    · exact h'
  have hm := hx.pow_eq_pow_iff_modEq.mp h
  rw [hord, Nat.ModEq, show 3 % 3 = 0 by norm_num] at hm
  interval_cases e
  · exact Or.inl rfl
  · exfalso; revert hm; norm_num
  · exfalso; revert hm; norm_num
  · exact Or.inr rfl

private def r920kl3a_fixV (K : Type) [Field K]
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ b : B, ((b : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
  add_mem' := by
    intro x y hx hy b
    rw [mulVec_add, hx b, hy b]
  zero_mem' := by
    intro b
    exact mulVec_zero _
  smul_mem' := by
    intro c x hx b
    rw [mulVec_smul, hx b]

private lemma r920kl3a_fixedPoints_eq_fixV (K : Type) [Field K]
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
    (MulAction.fixedPoints B (Fin 3 → K)) = (r920kl3a_fixV K B : Set (Fin 3 → K)) := by
  ext v
  rfl

private lemma r920kl3a_eigenvalue_eq_one {K : Type} [Field K] [Finite K]
    (h7 : ¬ 7 ∣ Nat.card K - 1)
    {M : Matrix (Fin 3) (Fin 3) K} (hM7 : M ^ 7 = 1)
    {v : Fin 3 → K} (hv : v ≠ 0) {μ : K} (hMv : M *ᵥ v = μ • v) : μ = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]
  have h7' := hpow 7
  rw [hM7, Matrix.one_mulVec] at h7'
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => by simpa using not_exists.mp h i)
  have hμ7 : μ ^ 7 = 1 := by
    have := congrFun h7' i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_left_eq_self₀.mp this.symm).resolve_right hi
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ7
  have hμcard : μ ^ (Nat.card K - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card] at this
  have hcop : Nat.Coprime 7 (Nat.card K - 1) :=
    (show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr h7
  have := pow_gcd_eq_one.mpr ⟨hμ7, hμcard⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

private lemma r920kl3a_Tor_pow_seven {K : Type} [Field K]
    {t : Matrix.SpecialLinearGroup (Fin 3) K}
    (ht : t ∈ CFSG.RankThree.PartOne.KFOUT3.Tor 7 K) : t ^ 7 = 1 := by
  obtain ⟨v, hv1, hv, rfl⟩ := CFSG.RankThree.PartOne.KFOUT3.mem_Tor_iff.mp ht
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, CFSG.RankThree.PartOne.KFOUT3.coe_diagSL,
    Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
  rw [show (fun i => (v i : K)) ^ 7 = (fun _ => (1 : K)) by
    funext i
    rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, hv1 i]
    rfl, Matrix.diagonal_one]

theorem sl3_irreducible_of_not_seven_dvd {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (h7 : ¬ 7 ∣ Nat.card K - 1)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hB7 : Nat.card B = 7)
    (Z : Submodule K (Fin 3 → K))
    (hZ : ∀ s ∈ B, ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) : Z = ⊥ ∨ Z = ⊤ := by
  classical
  by_cases hZbot : Z = ⊥
  · exact Or.inl hZbot
  right
  by_contra hZtop
  haveI : Fintype K := Fintype.ofFinite K
  have hBpg : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by rw [hB7, pow_one])
  have h3u : ((Nat.card K : ZMod 7)) ^ 3 = 1 := by
    have h := r920kl3a_seven_dvd_pow_three_sub_one hK
    have h' : (((Nat.card K ^ 3 : ℕ)) : ZMod 7) = 1 :=
      (r920kl3a_zmod7_eq_one_iff (m := Nat.card K ^ 3)
        (Nat.one_le_pow 3 _ (by haveI : Nonempty K := ⟨0⟩; exact Nat.card_pos))).mpr h
    simpa [Nat.cast_pow] using h'
  have h1u : ((Nat.card K : ZMod 7)) ≠ 1 := fun h =>
    h7 ((r920kl3a_zmod7_eq_one_iff (m := Nat.card K) (r920kl3a_one_le_card)).mp h)
  have hcardV := hBpg.card_modEq_card_fixedPoints (Fin 3 → K)
  rw [r920kl3a_fixedPoints_eq_fixV] at hcardV
  have hmodV : (Nat.card K) ^ (finrank K (Fin 3 → K)) ≡
      (Nat.card K) ^ (finrank K (r920kl3a_fixV K B)) [MOD 7] := by
    rw [← Module.natCard_eq_pow_finrank (K := K) (V := Fin 3 → K),
      ← Module.natCard_eq_pow_finrank (K := K) (V := r920kl3a_fixV K B)]
    exact hcardV
  have hzmodV : ((Nat.card K : ZMod 7)) ^ (finrank K (Fin 3 → K)) =
      ((Nat.card K : ZMod 7)) ^ (finrank K (r920kl3a_fixV K B)) := by
    have h : (((Nat.card K ^ finrank K (Fin 3 → K) : ℕ)) : ZMod 7) =
        (((Nat.card K ^ finrank K (r920kl3a_fixV K B) : ℕ)) : ZMod 7) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hmodV
    simpa [Nat.cast_pow] using h
  have hfixVne : r920kl3a_fixV K B ≠ ⊥ := by
    have hBne : B ≠ ⊥ := by
      intro h
      rw [h] at hB7
      simp at hB7
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hb7 : b ^ 7 = 1 := by
      have hdvd : orderOf b ∣ 7 := by rw [← hB7]; exact orderOf_dvd_natCard b
      rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7) (orderOf b) hdvd with
        h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hb1
      · rw [← h]; exact pow_orderOf_eq_one b
    have hb7' : (b : Matrix.SpecialLinearGroup (Fin 3) K) ^ 7 = 1 := by
      have h := congrArg (fun x : ↥B => (x : Matrix.SpecialLinearGroup (Fin 3) K)) hb7
      simpa using h
    have hordb : orderOf (b : Matrix.SpecialLinearGroup (Fin 3) K) = 7 := by
      have hdvd : orderOf (b : Matrix.SpecialLinearGroup (Fin 3) K) ∣ 7 :=
        orderOf_dvd_of_pow_eq_one hb7'
      rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7)
        (orderOf (b : Matrix.SpecialLinearGroup (Fin 3) K)) hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) (fun hh => hb1 (Subtype.ext hh))
      · exact h
    have hgen : Subgroup.zpowers (b : Matrix.SpecialLinearGroup (Fin 3) K) = B := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr b.2)
      rw [Nat.card_zpowers, hordb, hB7]
    have hM7 : (((b : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) ^ 7 = 1 := by
      have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) K =>
        (x : Matrix (Fin 3) (Fin 3) K)) hb7'
      simpa [Matrix.SpecialLinearGroup.coe_pow] using h
    obtain ⟨x, hx0, μ, hxμ⟩ :=
      CFSG.RankThree.PartOne.MB3.exists_eigenvector_of_invariant (M :=
        ((b : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        hZbot hZtop (fun w hw => hZ (b : Matrix.SpecialLinearGroup (Fin 3) K) b.2 w hw)
    have hμ1 : μ = 1 := r920kl3a_eigenvalue_eq_one h7 hM7 hx0 hxμ
    rw [hμ1, one_smul] at hxμ
    have hxfix : x ∈ r920kl3a_fixV K B := by
      have hbstab : (b : Matrix.SpecialLinearGroup (Fin 3) K) ∈
          MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 3) K) x := by
        rw [MulAction.mem_stabilizer_iff, Matrix.SpecialLinearGroup.smul_def]
        exact hxμ
      have hle : Subgroup.zpowers (b : Matrix.SpecialLinearGroup (Fin 3) K) ≤
          MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 3) K) x :=
        Subgroup.zpowers_le.mpr hbstab
      intro g
      have hgb : (g : Matrix.SpecialLinearGroup (Fin 3) K) ∈
          Subgroup.zpowers (b : Matrix.SpecialLinearGroup (Fin 3) K) := by
        rw [hgen]
        exact g.2
      have hgstab := hle hgb
      rw [MulAction.mem_stabilizer_iff, Matrix.SpecialLinearGroup.smul_def] at hgstab
      exact hgstab
    intro hbot
    rw [hbot] at hxfix
    exact hx0 ((Submodule.mem_bot K).mp hxfix)
  have heV : finrank K (r920kl3a_fixV K B) ≤ finrank K (Fin 3 → K) :=
    Submodule.finrank_le _
  have hfixVeq : finrank K (r920kl3a_fixV K B) = finrank K (Fin 3 → K) := by
    have heV3 : finrank K (r920kl3a_fixV K B) ≤ 3 := by
      simpa [Module.finrank_fin_fun] using heV
    have hzmodV3 : ((Nat.card K : ZMod 7)) ^ 3 =
        ((Nat.card K : ZMod 7)) ^ (finrank K (r920kl3a_fixV K B)) := by
      simpa [Module.finrank_fin_fun] using hzmodV
    rcases r920kl3a_pow_three_eq_pow_of_order_three h3u h1u heV3 hzmodV3 with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) hfixVne
    · rw [h, Module.finrank_fin_fun]
  have hfixVtop : r920kl3a_fixV K B = ⊤ := Submodule.eq_top_of_finrank_eq hfixVeq
  have hBbot : B = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    have hfix : ∀ v : Fin 3 → K,
        ((b : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
      intro v
      have hv : v ∈ r920kl3a_fixV K B := by rw [hfixVtop]; trivial
      exact hv ⟨b, hb⟩
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have h1 := congrFun (hfix (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h1
    simpa [Matrix.one_apply, Pi.single_apply] using h1
  have h1 : Nat.card (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofSubsingleton _
  rw [hBbot] at hB7
  omega

private lemma r920kl3a_zeta_ne {K : Type} [Field K] {ζ : Kˣ}
    (hζ : CFSG.RankThree.PartOne.KFOUT3.IsZeta 7 ζ) :
    ζ ≠ ζ ^ 2 ∧ ζ ≠ ζ ^ 4 ∧ ζ ^ 2 ≠ ζ ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : ζ = 1 := by
      have hh := congrArg (fun x => ζ⁻¹ * x) h
      simpa [pow_two, mul_assoc] using hh.symm
    exact hζ.sq (by rw [h1, one_pow])
  · intro h
    have h1 : ζ ^ 3 = 1 := by
      calc ζ ^ 3 = ζ ^ 4 * ζ⁻¹ := by group
        _ = ζ * ζ⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel ζ
    exact hζ.cube h1
  · intro h
    have h1 : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ ^ 4 * (ζ ^ 2)⁻¹ := by group
        _ = ζ ^ 2 * (ζ ^ 2)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel _
    exact hζ.sq h1

theorem sl3_irreducible_of_seven_dvd {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (h7 : 7 ∣ Nat.card K - 1)
    {W B : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hBW : B ≤ W) (hB7 : Nat.card B = 7)
    (hN : ∀ P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), IsPGroup 7 ↥P → B ≤ P →
      normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ W)
    (Z : Submodule K (Fin 3 → K))
    (hZ : ∀ s ∈ W, ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) : Z = ⊥ ∨ Z = ⊤ := by
  classical
  by_cases hZbot : Z = ⊥
  · exact Or.inl hZbot
  right
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := CFSG.RankThree.PartOne.N143.charP_two_of_card hK
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.N143.exists_isZeta (p := 7)
    (by norm_num) (by norm_num) h7
  have hB7pow : ∀ b ∈ B, b ^ 7 = 1 := by
    intro b hb
    have hdvd : orderOf (⟨b, hb⟩ : ↥B) ∣ 7 := by
      rw [← hB7]; exact orderOf_dvd_natCard _
    have h7' : (⟨b, hb⟩ : ↥B) ^ 7 = 1 := by
      rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 7)
        (orderOf (⟨b, hb⟩ : ↥B)) hdvd with h | h
      · rw [orderOf_eq_one_iff.mp h, one_pow]
      · rw [← h]; exact pow_orderOf_eq_one _
    simpa using congrArg Subtype.val h7'
  let R : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K) :=
    B.map (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := K))
  have hR : IsPGroup 7 ↥R := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp x.2
    apply Subtype.ext
    change (x : Matrix.GeneralLinearGroup (Fin 3) K) ^ 7 = 1
    rw [← hbx, ← map_pow, hB7pow b hb, map_one]
  obtain ⟨g, hg⟩ := CFSG.Quasithin.KGC31.exists_conj_le_diagTorusA (ι := Fin 3) (K := K)
    (ℓ := 7) (by decide) (by rw [Fintype.card_eq_nat_card]; exact h7) hR
  let α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K g
  have hαTor : ∀ b ∈ B, α b ∈ CFSG.RankThree.PartOne.KFOUT3.Tor 7 K := by
    intro b hb
    have hmem : Matrix.SpecialLinearGroup.toGL (α b) ∈
        CFSG.Quasithin.KGC31.diagTorusA (Fin 3) K := by
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
      exact hg (Matrix.SpecialLinearGroup.toGL b) (Subgroup.mem_map_of_mem _ hb)
    obtain ⟨a, ha⟩ := hmem
    have hmat : ((α b : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (fun i => (a i : K)) := by
      have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 3) K =>
        (x : Matrix (Fin 3) (Fin 3) K)) ha
      simpa [CFSG.Quasithin.KGC31.coe_diagHomA] using h.symm
    have hαb7 : (α b) ^ 7 = 1 := by rw [← map_pow, hB7pow b hb, map_one]
    have ha7 : ∀ i, a i ^ 7 = 1 := by
      intro i
      apply Units.ext
      have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) K =>
        (x : Matrix (Fin 3) (Fin 3) K)) hαb7
      rw [Matrix.SpecialLinearGroup.coe_pow, hmat, Matrix.diagonal_pow,
        Matrix.SpecialLinearGroup.coe_one] at h1
      have h2 := congrFun (congrFun h1 i) i
      simpa [Pi.pow_apply] using h2
    have hprod : ∏ i, a i = 1 := by
      apply Units.ext
      have hdet := (α b).2
      rw [hmat, Matrix.det_diagonal] at hdet
      simpa using hdet
    exact CFSG.RankThree.PartOne.KFOUT3.mem_Tor_iff.mpr ⟨a, ha7, hprod, by
      apply Subtype.ext
      rw [CFSG.RankThree.PartOne.KFOUT3.coe_diagSL, hmat]⟩
  let P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
    (CFSG.RankThree.PartOne.KFOUT3.Tor 7 K).comap α
  have hBP : B ≤ P := fun b hb => hαTor b hb
  have hP : IsPGroup 7 ↥P := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx : α (x : Matrix.SpecialLinearGroup (Fin 3) K) ∈
        CFSG.RankThree.PartOne.KFOUT3.Tor 7 K := x.2
    have hxt : (α (x : Matrix.SpecialLinearGroup (Fin 3) K)) ^ 7 = 1 :=
      r920kl3a_Tor_pow_seven hx
    apply Subtype.ext
    change (x : Matrix.SpecialLinearGroup (Fin 3) K) ^ 7 = 1
    apply α.injective
    rw [map_pow, hxt, map_one]
  have hnormP : normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ W := hN P hP hBP
  let v : Fin 3 → Kˣ := ![ζ, ζ ^ 2, ζ ^ 4]
  have hv0 : v 0 = ζ := rfl
  have hv1 : v 1 = ζ ^ 2 := rfl
  have hv2 : v 2 = ζ ^ 4 := rfl
  have hv_prod : ∏ i, v i = 1 := by
    rw [Fin.prod_univ_three, hv0, hv1, hv2]
    rw [show ζ * ζ ^ 2 * ζ ^ 4 = ζ ^ 7 by group]
    exact hζ.pow
  have hv_pow : ∀ i, v i ^ 7 = 1 := by
    intro i
    fin_cases i
    · change v 0 ^ 7 = 1
      rw [hv0]; exact hζ.pow
    · change v 1 ^ 7 = 1
      rw [hv1, ← pow_mul, show 2 * 7 = 7 * 2 by norm_num, pow_mul, hζ.pow, one_pow]
    · change v 2 ^ 7 = 1
      rw [hv2, ← pow_mul, show 4 * 7 = 7 * 4 by norm_num, pow_mul, hζ.pow, one_pow]
  let d : Matrix.SpecialLinearGroup (Fin 3) K := CFSG.RankThree.PartOne.KFOUT3.diagSL v hv_prod
  have hdTor : d ∈ CFSG.RankThree.PartOne.KFOUT3.Tor 7 K :=
    CFSG.RankThree.PartOne.KFOUT3.diagSL_mem_Tor v hv_pow hv_prod
  have hdP : α.symm d ∈ P := by
    change α (α.symm d) ∈ CFSG.RankThree.PartOne.KFOUT3.Tor 7 K
    rw [α.apply_symm_apply]
    exact hdTor
  have hdW : α.symm d ∈ W := hnormP (Subgroup.le_normalizer hdP)
  let y : Matrix.SpecialLinearGroup (Fin 3) K := CFSG.RankThree.PartOne.KFOUT3.permSL (finRotate 3)
  have hyN : α.symm y ∈ normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    change α h ∈ CFSG.RankThree.PartOne.KFOUT3.Tor 7 K ↔
      α (α.symm y * h * (α.symm y)⁻¹) ∈ CFSG.RankThree.PartOne.KFOUT3.Tor 7 K
    rw [show α (α.symm y * h * (α.symm y)⁻¹) = y * α h * y⁻¹ by
      simp only [map_mul, map_inv, α.apply_symm_apply]]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.RankThree.PartOne.N143.permSL_mem_normalizer_Tor (finRotate 3)) (α h))
  have hyW : α.symm y ∈ W := hnormP hyN
  let gM : Matrix (Fin 3) (Fin 3) K := g
  let Z' : Submodule K (Fin 3 → K) := Z.map gM.mulVecLin
  have hgg : (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * gM = 1 := by
    rw [show gM = (g : Matrix (Fin 3) (Fin 3) K) from rfl]
    have h := congrArg (fun u : (Matrix (Fin 3) (Fin 3) K)ˣ =>
      (u : Matrix (Fin 3) (Fin 3) K)) (inv_mul_cancel g)
    simpa [Units.val_mul] using h
  have hgg' : gM * (g⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [show gM = (g : Matrix (Fin 3) (Fin 3) K) from rfl]
    have h := congrArg (fun u : (Matrix (Fin 3) (Fin 3) K)ˣ =>
      (u : Matrix (Fin 3) (Fin 3) K)) (mul_inv_cancel g)
    simpa [Units.val_mul] using h
  have hβd : ((α.symm d : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * (d : Matrix (Fin 3) (Fin 3) K) * gM := by
    change ((α.symm d : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * (d : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K)
    have h := CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation 3 K g
      (α.symm d)
    rw [show CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K g
      (α.symm d) = α (α.symm d) from rfl, α.apply_symm_apply] at h
    have h' : Matrix.SpecialLinearGroup.toGL (α.symm d) =
        g⁻¹ * Matrix.SpecialLinearGroup.toGL d * g := by
      rw [h]; group
    have h'' := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K)) h'
    rw [Units.val_mul, Units.val_mul] at h''
    simpa using h''
  have hβy : ((α.symm y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) * gM := by
    change ((α.symm y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g⁻¹ : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K)
    have h := CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation 3 K g
      (α.symm y)
    rw [show CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K g
      (α.symm y) = α (α.symm y) from rfl, α.apply_symm_apply] at h
    have h' : Matrix.SpecialLinearGroup.toGL (α.symm y) =
        g⁻¹ * Matrix.SpecialLinearGroup.toGL y * g := by
      rw [h]; group
    have h'' := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K)) h'
    rw [Units.val_mul, Units.val_mul] at h''
    simpa using h''
  have hdv : (d : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (fun i => (v i : K)) :=
    CFSG.RankThree.PartOne.KFOUT3.coe_diagSL v hv_prod
  have hycyc : (y : Matrix (Fin 3) (Fin 3) K) =
      CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat := by
    rw [show y = CFSG.RankThree.PartOne.KFOUT3.permSL (finRotate 3) from rfl,
      CFSG.RankThree.PartOne.KFOUT3.coe_permSL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_some_iff] <;>
      (first | rfl | exact one_ne_zero)
  have hinvD : ∀ w ∈ Z', Matrix.diagonal (fun i => (v i : K)) *ᵥ w ∈ Z' := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    have hMg : Matrix.diagonal (fun i => (v i : K)) * gM =
        gM * ((α.symm d : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hβd, hdv]
      rw [show gM * ((g⁻¹ : Matrix (Fin 3) (Fin 3) K) *
            Matrix.diagonal (fun i => (v i : K)) * gM)
          = (gM * (g⁻¹ : Matrix (Fin 3) (Fin 3) K)) *
              Matrix.diagonal (fun i => (v i : K)) * gM by noncomm_ring, hgg', one_mul]
    refine ⟨((α.symm d : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z,
      hZ _ hdW _ hz, ?_⟩
    calc gM *ᵥ (((α.symm d : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ z)
        = (gM * ((α.symm d : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)) *ᵥ z := Matrix.mulVec_mulVec z gM _
      _ = (Matrix.diagonal (fun i => (v i : K)) * gM) *ᵥ z := by rw [← hMg]
      _ = Matrix.diagonal (fun i => (v i : K)) *ᵥ (gM *ᵥ z) :=
            (Matrix.mulVec_mulVec z (Matrix.diagonal fun i => (v i : K)) gM).symm
  have hinvC : ∀ w ∈ Z',
      CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat *ᵥ w ∈ Z' := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    have hCy : CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat * gM =
        gM * ((α.symm y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hβy, hycyc]
      rw [show gM * ((g⁻¹ : Matrix (Fin 3) (Fin 3) K) *
            CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat * gM)
          = (gM * (g⁻¹ : Matrix (Fin 3) (Fin 3) K)) *
              CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat * gM by
            noncomm_ring, hgg', one_mul]
    refine ⟨((α.symm y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z,
      hZ _ hyW _ hz, ?_⟩
    calc gM *ᵥ (((α.symm y : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ z)
        = (gM * ((α.symm y : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)) *ᵥ z := Matrix.mulVec_mulVec z gM _
      _ = (CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat * gM) *ᵥ z := by
            rw [← hCy]
      _ = CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat *ᵥ (gM *ᵥ z) :=
            (Matrix.mulVec_mulVec z
              CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat gM).symm
  have hZ'ne : Z' ≠ ⊥ := by
    intro hbot
    apply hZbot
    rw [eq_bot_iff]
    intro w hw
    have hmem : gM *ᵥ w ∈ Z' := ⟨w, hw, rfl⟩
    rw [hbot] at hmem
    have hgw : gM *ᵥ w = 0 := (Submodule.mem_bot K).mp hmem
    calc w = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ w := by rw [Matrix.one_mulVec]
      _ = ((g⁻¹ : Matrix (Fin 3) (Fin 3) K) * gM) *ᵥ w := by rw [hgg]
      _ = (g⁻¹ : Matrix (Fin 3) (Fin 3) K) *ᵥ (gM *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = (g⁻¹ : Matrix (Fin 3) (Fin 3) K) *ᵥ 0 := by rw [hgw]
      _ = 0 := by rw [mulVec_zero]
  have hZ'top : Z' = ⊤ := by
    refine CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3BT.eq_top_of_invariant
      (d := fun i => (v i : K)) (c := fun _ => 1) ?_ ?_ hZ'ne ?_ ?_
    · intro i j hij
      obtain ⟨h01, h02, h12⟩ := r920kl3a_zeta_ne hζ
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        have hh : v 0 = v 1 := Units.ext hij
        rw [hv0, hv1] at hh
        exact h01 hh
      · exfalso
        have hh : v 0 = v 2 := Units.ext hij
        rw [hv0, hv2] at hh
        exact h02 hh
      · exfalso
        have hh : v 1 = v 0 := Units.ext hij
        rw [hv1, hv0] at hh
        exact h01 hh.symm
      · rfl
      · exfalso
        have hh : v 1 = v 2 := Units.ext hij
        rw [hv1, hv2] at hh
        exact h12 hh
      · exfalso
        have hh : v 2 = v 0 := Units.ext hij
        rw [hv2, hv0] at hh
        exact h02 hh.symm
      · exfalso
        have hh : v 2 = v 1 := Units.ext hij
        rw [hv2, hv1] at hh
        exact h12 hh.symm
      · rfl
    · intro i; exact one_ne_zero
    · intro w hw; exact hinvD w hw
    · intro w hw
      rw [show CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat *
          Matrix.diagonal (fun _ : Fin 3 => (1 : K)) =
          CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat.cycMat by
        rw [Matrix.diagonal_one, mul_one]]
      exact hinvC w hw
  have hZtop : Z = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hmem : gM *ᵥ w ∈ Z' := by rw [hZ'top]; trivial
    obtain ⟨z, hz, hz_eq⟩ := Submodule.mem_map.mp hmem
    have hz_eq' : gM *ᵥ z = gM *ᵥ w := by
      simpa [Matrix.mulVecLin_apply] using hz_eq
    have hzw : z = w := by
      have h := congrArg (fun x => (g⁻¹ : Matrix (Fin 3) (Fin 3) K) *ᵥ x) hz_eq'
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec,
        Matrix.one_mulVec] at h
    rwa [← hzw]
  exact hZtop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
