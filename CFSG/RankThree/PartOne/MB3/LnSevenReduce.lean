module

public import CFSG.RankThree.PartOne.MB3.LnSevenGood
public import CFSG.RankThree.PartOne.MB3.LnSevenOne
public import CFSG.RankThree.PartOne.MB3.LnSevenGLTwo
public import CFSG.RankThree.PartOne.MB3.LnSevenReindex
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Subgroup

@[expose] def Good (J : Type) [Fintype J] [DecidableEq J] {X : Type} [Group X] (y : X) : Prop :=
  CompModel (SpecialLinearGroup J (ZMod 2)) (SpecialLinearGroup (Fin 2) F8)
    ↥(Subgroup.centralizer ({y} : Set X))

section Good

variable {J : Type} [Fintype J] [DecidableEq J]

theorem Good.of_mulEquiv {X X' : Type} [Group X] [Group X'] (φ : X ≃* X') {y : X}
    (h : Good J (φ y)) : Good J y :=
  CompModel.centralizer_of_mulEquiv φ h

theorem Good.of_pow {X : Type} [Group X] {y : X} (h7 : y ^ 7 = 1) {k : ℕ} (hk : Nat.Coprime k 7)
    (h : Good J (y ^ k)) : Good J y :=
  CompModel.centralizer_of_pow h7 hk h

theorem good_β₁ (hJ : IsSimpleGroup (SpecialLinearGroup J (ZMod 2))) :
    Good J (β₁ : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) :=
  compModel_of_sub fun _ hE hcomp => Or.inl (nonempty_mulEquiv_of_isComponent hJ hE hcomp)

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem good_β₂ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1) : Good J (β₂ κ) :=
  compModel_of_sub fun _ hE hcomp => Or.inr (nonempty_mulEquiv_of_isComponent_T₂ hκ hE hcomp)

theorem good_β₃ (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1) : Good J (β₃ κ) :=
  compModel_of_sub fun _ _ hcomp => absurd hcomp (not_isComponent_T₃ hκ)

end Good

section Reduce

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem reindex_D2_one :
    slReEquiv (Equiv.sumAssoc (Fin 3) (Fin 3) κ) (D2 (cSL, 1)) =
      (β₁ : SpecialLinearGroup (Fin 3 ⊕ (Fin 3 ⊕ κ)) (ZMod 2)) := by
  refine Subtype.ext ?_
  rw [coe_slReEquiv, coe_D2, coe_β₁]
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, bd2, cSL, Matrix.one_apply,
      Matrix.fromBlocks]

theorem reindex_D2_two :
    slReEquiv ((Equiv.sumCongr (Equiv.sumComm (Fin 3) (Fin 3)) (Equiv.refl κ)).trans
      (Equiv.sumAssoc (Fin 3) (Fin 3) κ)) (D2 (1, cSL)) =
      (β₁ : SpecialLinearGroup (Fin 3 ⊕ (Fin 3 ⊕ κ)) (ZMod 2)) := by
  refine Subtype.ext ?_
  rw [coe_slReEquiv, coe_D2, coe_β₁]
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, bd2, cSL, Matrix.one_apply,
      Matrix.fromBlocks]

@[expose] def dd (a b : ZMod 7) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) :=
  D2 (cSL ^ a.val, cSL ^ b.val)

theorem cSL_pow_val_eq {n : ℕ} {a : ZMod 7} (h : (n : ZMod 7) = a) : cSL ^ a.val = cSL ^ n := by
  have h1 := pow_mod_orderOf cSL n
  rw [orderOf_cSL] at h1
  rw [← h, ZMod.val_natCast, h1]

theorem cSL_zpow_eq (i : ℤ) : cSL ^ i = cSL ^ (i : ZMod 7).val := by
  have h1 := zpow_mod_orderOf cSL i
  rw [orderOf_cSL] at h1
  rw [← h1, ← zpow_natCast]
  congr 1
  rw [ZMod.val_intCast]

theorem fSL_conj_pow (m : ℕ) : fSL * cSL ^ m * fSL⁻¹ = cSL ^ (2 * m) := by
  have h : fSL * cSL ^ m = cSL ^ (2 * m) * fSL := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, fSL_mul_cSL, ← mul_assoc, ← pow_add]
      congr 2
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem dd_zero_zero : (dd 0 0 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = 1 := by
  rw [dd, ZMod.val_zero, pow_zero]
  exact map_one D2

theorem conj_dd_fst (a b : ZMod 7) :
    (MulAut.conj (D2 (fSL, 1) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) (dd a b) =
      dd (2 * a) b := by
  unfold dd
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ ?_
  · show fSL * cSL ^ a.val * fSL⁻¹ = cSL ^ (2 * a).val
    rw [fSL_conj_pow]
    refine (cSL_pow_val_eq ?_).symm
    simp
  · simp

theorem conj_dd_snd (a b : ZMod 7) :
    (MulAut.conj (D2 (1, fSL) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) (dd a b) =
      dd a (2 * b) := by
  unfold dd
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ ?_
  · simp
  · show fSL * cSL ^ b.val * fSL⁻¹ = cSL ^ (2 * b).val
    rw [fSL_conj_pow]
    refine (cSL_pow_val_eq ?_).symm
    simp

theorem dd_pow_seven (a b : ZMod 7) :
    (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) ^ 7 = 1 := by
  unfold dd
  rw [← map_pow]
  have h1 : (cSL ^ a.val) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, cSL_pow_seven, one_pow]
  have h2 : (cSL ^ b.val) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, cSL_pow_seven, one_pow]
  rw [Prod.pow_mk, h1, h2]
  exact map_one _

theorem dd_pow (a b k : ZMod 7) :
    (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) ^ k.val = dd (k * a) (k * b) := by
  unfold dd
  rw [← map_pow, Prod.pow_mk, ← pow_mul, ← pow_mul]
  congr 2
  · exact (cSL_pow_val_eq (n := a.val * k.val) (by simp [mul_comm])).symm
  · exact (cSL_pow_val_eq (n := b.val * k.val) (by simp [mul_comm])).symm

theorem val_one_seven : (1 : ZMod 7).val = 1 := by decide

theorem val_three_seven : (3 : ZMod 7).val = 3 := by decide

theorem good_dd_one_zero (hJ : IsSimpleGroup (SpecialLinearGroup (Fin 3 ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd 1 0 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  refine Good.of_mulEquiv (slReEquiv (Equiv.sumAssoc (Fin 3) (Fin 3) κ)) ?_
  have h : (dd 1 0 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = D2 (cSL, 1) := by
    rw [dd, val_one_seven, ZMod.val_zero, pow_one, pow_zero]
  rw [h, reindex_D2_one]
  exact good_β₁ hJ

theorem good_dd_zero_one (hJ : IsSimpleGroup (SpecialLinearGroup (Fin 3 ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd 0 1 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  refine Good.of_mulEquiv (slReEquiv ((Equiv.sumCongr (Equiv.sumComm (Fin 3) (Fin 3))
    (Equiv.refl κ)).trans (Equiv.sumAssoc (Fin 3) (Fin 3) κ))) ?_
  have h : (dd 0 1 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = D2 (1, cSL) := by
    rw [dd, val_one_seven, ZMod.val_zero, pow_one, pow_zero]
  rw [h, reindex_D2_two]
  exact good_β₁ hJ

theorem good_dd_one_one (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1) :
    Good (Fin 3 ⊕ κ) (dd 1 1 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  have h : (dd 1 1 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = β₂ κ := by
    refine Subtype.ext ?_
    rw [dd, coe_D2, coe_β₂, val_one_seven, pow_one]
    rfl
  rw [h]
  exact good_β₂ hκ

theorem good_dd_one_three (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1) :
    Good (Fin 3 ⊕ κ) (dd 1 3 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  have h : (dd 1 3 : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) = β₃ κ := by
    refine Subtype.ext ?_
    rw [dd, coe_D2, coe_β₃, val_one_seven, val_three_seven, pow_one, coe_cSL_pow]
    rfl
  rw [h]
  exact good_β₃ hκ

theorem good_dd_fst {a b : ZMod 7}
    (h : Good (Fin 3 ⊕ κ) (dd (2 * a) b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :=
  Good.of_mulEquiv (MulAut.conj (D2 (fSL, 1) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))
    (by rw [conj_dd_fst]; exact h)

theorem good_dd_snd {a b : ZMod 7}
    (h : Good (Fin 3 ⊕ κ) (dd a (2 * b) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :=
  Good.of_mulEquiv (MulAut.conj (D2 (1, fSL) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))
    (by rw [conj_dd_snd]; exact h)

theorem good_dd_fst_pow (n : ℕ) {a b : ZMod 7}
    (h : Good (Fin 3 ⊕ κ) (dd (2 ^ n * a) b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    refine good_dd_fst (ih ?_)
    rwa [show (2 : ZMod 7) ^ n * (2 * a) = 2 ^ (n + 1) * a by ring]

theorem good_dd_snd_pow (n : ℕ) {a b : ZMod 7}
    (h : Good (Fin 3 ⊕ κ) (dd a (2 ^ n * b) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  induction n generalizing b with
  | zero => simpa using h
  | succ n ih =>
    refine good_dd_snd (ih ?_)
    rwa [show (2 : ZMod 7) ^ n * (2 * b) = 2 ^ (n + 1) * b by ring]

theorem good_dd_scale {a b k : ZMod 7} (hk : k ≠ 0)
    (h : Good (Fin 3 ⊕ κ)
      (dd (k * a) (k * b) : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) :
    Good (Fin 3 ⊕ κ) (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  have hcop : ∀ k : ZMod 7, k ≠ 0 → Nat.Coprime k.val 7 := by decide
  exact Good.of_pow (dd_pow_seven a b) (hcop k hk) (by rw [dd_pow]; exact h)

theorem cover_zmod7 : ∀ a b : ZMod 7, (a, b) ≠ (0, 0) →
    ∃ (s t : Fin 3) (k : ZMod 7), k ≠ 0 ∧
      ((2 ^ (s : ℕ) * (k * a), 2 ^ (t : ℕ) * (k * b)) : ZMod 7 × ZMod 7) ∈
        ({(1, 0), (0, 1), (1, 1), (1, 3)} : Finset (ZMod 7 × ZMod 7)) := by
  decide +kernel

theorem good_dd_of_ne (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    (hJ : IsSimpleGroup (SpecialLinearGroup (Fin 3 ⊕ κ) (ZMod 2))) {a b : ZMod 7}
    (hab : (a, b) ≠ (0, 0)) :
    Good (Fin 3 ⊕ κ) (dd a b : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  obtain ⟨s, t, k, hk, hmem⟩ := cover_zmod7 a b hab
  have hbase : Good (Fin 3 ⊕ κ) (dd (2 ^ (s : ℕ) * (k * a)) (2 ^ (t : ℕ) * (k * b)) :
      SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact good_dd_one_zero hJ
    · rw [h1, h2]; exact good_dd_zero_one hJ
    · rw [h1, h2]; exact good_dd_one_one hκ
    · rw [h1, h2]; exact good_dd_one_three hκ
  exact good_dd_scale hk (good_dd_snd_pow (t : ℕ) (good_dd_fst_pow (s : ℕ) hbase))

@[expose] def B₀ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :=
  ((Subgroup.zpowers cSL).prod (Subgroup.zpowers cSL)).map D2

theorem card_B₀ : Nat.card (B₀ (κ := κ)) = 49 := by
  unfold B₀
  rw [Subgroup.card_map_of_injective D2_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers,
    orderOf_cSL]

theorem exists_dd_of_mem_B₀ {z : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)}
    (hz : z ∈ B₀) : ∃ a b : ZMod 7, z = dd a b := by
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp huv).1
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp huv).2
  refine ⟨i, j, ?_⟩
  simp only [dd]
  rw [cSL_zpow_eq i, cSL_zpow_eq j]

theorem exists_conj_mem_B₀
    (hM : ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))
    {y : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} (hy : orderOf y = 7) :
    ∃ g : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2), g⁻¹ * y * g ∈ B₀ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.RankThree.PartOne.Sec109.exists_sylow_of_card_forty_nine hM B₀ card_B₀
  have hp : IsPGroup 7 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
  obtain ⟨P₁, hP₁⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) P₀ P₁
  have hyP : y ∈ (P₁ : Subgroup (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2))) :=
    hP₁ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, hP₀, Subgroup.pointwise_smul_def] at hyP
  obtain ⟨z, hz, hzy⟩ := hyP
  have hz' : z = g⁻¹ * y * g := by
    rw [← hzy]
    simp [mul_assoc]
  exact ⟨g, hz' ▸ hz⟩

theorem good_of_orderOf_seven (hκ : ∀ T : Matrix κ κ (ZMod 2), T.det = 1 → T = 1)
    (hJ : IsSimpleGroup (SpecialLinearGroup (Fin 3 ⊕ κ) (ZMod 2)))
    (hM : ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)))
    {y : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)} (hy : orderOf y = 7) :
    Good (Fin 3 ⊕ κ) y := by
  obtain ⟨g, hg⟩ := exists_conj_mem_B₀ hM hy
  obtain ⟨a, b, hab⟩ := exists_dd_of_mem_B₀ hg
  have hne : (a, b) ≠ (0, 0) := by
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [dd_zero_zero] at hab
    have hy1 : y = 1 := by
      have := congrArg (fun w => g * w * g⁻¹) hab
      simpa [mul_assoc] using this
    rw [hy1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  refine Good.of_mulEquiv (MulAut.conj g⁻¹) ?_
  rw [MulAut.conj_apply, inv_inv, hab]
  exact good_dd_of_ne hκ hJ hne

end Reduce

end CFSG.RankThree.PartOne.MB3
