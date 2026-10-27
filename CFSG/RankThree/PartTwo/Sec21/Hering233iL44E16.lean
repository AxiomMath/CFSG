module

public import CFSG.RankThree.PartTwo.Sec21.Item233RootsL44
public import CFSG.RankThree.PartTwo.Sec21.Hering233iE16Groups
import CFSG.RankThree.PartTwo.Sec6.Item63

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

section Model

open CFSG.RankThree.PartTwo.Sec21.TablesL44 CFSG.RankThree.PartTwo.KFacts.KS21.L44
  CFSG.RankThree.PartTwo.Sec21.Tables

@[expose] noncomputable def uMat (a b c d : Fin 4) (s t : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  1 + Matrix.single a b s + Matrix.single c d t

theorem uMat_mul {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a) (hcd : c ≠ d)
    (s t s' t' : F4) :
    uMat a b c d s t * uMat a b c d s' t' = uMat a b c d (s + s') (t + t') := by
  have h1 : Matrix.single a b s * Matrix.single a b s' = 0 :=
    Matrix.single_mul_single_of_ne s a b a hab.symm s'
  have h2 : Matrix.single a b s * Matrix.single c d t' = 0 :=
    Matrix.single_mul_single_of_ne s a b c hbc t'
  have h3 : Matrix.single c d t * Matrix.single a b s' = 0 :=
    Matrix.single_mul_single_of_ne t c d a hda s'
  have h4 : Matrix.single c d t * Matrix.single c d t' = 0 :=
    Matrix.single_mul_single_of_ne t c d c hcd.symm t'
  simp only [uMat, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, h1, h2, h3, h4,
    add_zero, Matrix.single_add]
  abel

theorem det_uMat {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (s t : F4) :
    (uMat a b c d s t).det = 1 := by
  have h2 : Matrix.single a b s * Matrix.single c d t = 0 :=
    Matrix.single_mul_single_of_ne s a b c hbc t
  have : uMat a b c d s t = Matrix.transvection a b s * Matrix.transvection c d t := by
    simp only [uMat, Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_one, h2, add_zero]
  rw [this, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hab,
    Matrix.det_transvection_of_ne _ _ hcd, one_mul]

@[expose] noncomputable def uHom {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a)
    (hcd : c ≠ d) : Multiplicative (F4 × F4) →* M where
  toFun x := ⟨uMat a b c d (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2,
    det_uMat hab hbc hcd _ _⟩
  map_one' := Subtype.ext (by
    change uMat a b c d 0 0 = 1
    simp [uMat])
  map_mul' x y := Subtype.ext (by
    change uMat a b c d ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1)
      ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2) = _
    rw [← uMat_mul hab hbc hda hcd]
    rfl)

theorem coe_uHom {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a) (hcd : c ≠ d)
    (x : Multiplicative (F4 × F4)) :
    ((uHom hab hbc hda hcd x : M) : Matrix (Fin 4) (Fin 4) F4) =
      uMat a b c d (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 := rfl

theorem uHom_injective {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a)
    (hcd : c ≠ d) (hne : a ≠ c ∨ b ≠ d) : Function.Injective (uHom hab hbc hda hcd) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h : uMat a b c d (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 = 1 :=
    congrArg Subtype.val hx
  have e1 := congrFun₂ h a b
  have e2 := congrFun₂ h c d
  have hne' : ¬ (c = a ∧ d = b) := fun ⟨h1, h2⟩ => by
    rcases hne with h3 | h3
    · exact h3 h1.symm
    · exact h3 h2.symm
  have hne'' : ¬ (a = c ∧ b = d) := fun ⟨h1, h2⟩ => by
    rcases hne with h3 | h3
    · exact h3 h1
    · exact h3 h2
  simp only [uMat, Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, and_self,
    if_true, hne', if_false, add_zero, Matrix.one_apply_ne hcd, zero_add, hne''] at e1 e2
  apply Multiplicative.toAdd.injective
  exact Prod.ext e1 e2

theorem isElemAbelian_range_uHom {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a)
    (hcd : c ≠ d) : IsElemAbelian 2 (uHom hab hbc hda hcd).range := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    apply Subtype.ext
    change uHom hab hbc hda hcd x * uHom hab hbc hda hcd y =
      uHom hab hbc hda hcd y * uHom hab hbc hda hcd x
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have h : x ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, two_nsmul, toAdd_one]
      exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)
    rw [h, map_one]

theorem card_range_uHom {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a)
    (hcd : c ≠ d) (hne : a ≠ c ∨ b ≠ d) : Nat.card (uHom hab hbc hda hcd).range = 2 ^ 4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (uHom_injective hab hbc hda hcd hne)).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (F4 × F4) ≃ F4 × F4), Nat.card_prod,
    card_F4]
  norm_num

theorem range_uHom_le_centralizer {a b c d : Fin 4} (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a)
    (hcd : c ≠ d) {v : Fin 3 → ZMod 3} (hv₁ : ext v a = ext v b) (hv₂ : ext v c = ext v d) :
    (uHom hab hbc hda hcd).range ≤
      Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) := by
  rintro _ ⟨x, rfl⟩
  apply mem_centralizer_of_isBlockDiag
  rw [coe_uHom]
  intro i j hij
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  have h1 : ¬ (a = i ∧ b = j) := by
    rintro ⟨rfl, rfl⟩
    exact hij hv₁
  have h2 : ¬ (c = i ∧ d = j) := by
    rintro ⟨rfl, rfl⟩
    exact hij hv₂
  simp [uMat, Matrix.single_apply, Matrix.one_apply_ne hij', h1, h2]

theorem exists_E16_std (i : Fin 3) (hi : i ≠ 0) :
    ∃ E₀ : Subgroup M, IsElemAbelian 2 E₀ ∧ Nat.card E₀ = 2 ^ 4 ∧
      E₀ ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd (std i))} : Set M) := by
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨(uHom (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) (by decide)
      (by decide)).range, isElemAbelian_range_uHom _ _ _ _,
      card_range_uHom _ _ _ _ (Or.inl (by decide)),
      range_uHom_le_centralizer _ _ _ _ (by decide) (by decide)⟩
  · exact ⟨(uHom (a := 0) (b := 1) (c := 0) (d := 2) (by decide) (by decide) (by decide)
      (by decide)).range, isElemAbelian_range_uHom _ _ _ _,
      card_range_uHom _ _ _ _ (Or.inr (by decide)),
      range_uHom_le_centralizer _ _ _ _ (by decide) (by decide)⟩

theorem isComponent_normal_cv {v : Fin 3 → ZMod 3} (hv : v ≠ 0)
    {Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M))}
    (hY : CFSG.IsComponent Y) : Y.Normal := by
  have hmem : Y ∈ {K : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) |
      CFSG.IsComponent K} := hY
  rw [components_big hv] at hmem
  obtain ⟨κ, rfl⟩ := hmem
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (blockSub_le_cv v κ.1)).mpr
    (block_normal (v := v) (κ := κ.1) (S := blockSub {i : Fin 4 | ext v i = κ.1})
      (fun x => mem_blockSub)).2

theorem components_std0 :
    ∃ Y₀ : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set M)),
      Nat.card Y₀ = 60 ∧ ∀ Y, CFSG.IsComponent Y → Y = Y₀ := by
  have hv : std 0 ≠ 0 := by decide
  have key : ∀ κ : ZMod 3, (∃ i j : Fin 4, i ≠ j ∧ ext (std 0) i = κ ∧ ext (std 0) j = κ) →
      κ = 0 := by decide
  refine ⟨(blockSub {i : Fin 4 | ext (std 0) i = 0}).subgroupOf _, ?_, ?_⟩
  · have hbs : blockSub {i : Fin 4 | ext (std 0) i = 0} = ι23.range := by
      ext x
      rw [mem_blockSub, fib0_0, mem_range_ι23_iff]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockSub_le_cv (std 0) 0)).toEquiv, hbs,
      ← Nat.card_congr (MonoidHom.ofInjective ι23_injective).toEquiv]
    exact card_SL2
  · intro Y hY
    have hmem : Y ∈ {K | CFSG.IsComponent K} := hY
    rw [components_big hv] at hmem
    obtain ⟨κ, rfl⟩ := hmem
    show (blockSub {i : Fin 4 | ext (std 0) i = κ.1}).subgroupOf _ = _
    rw [key κ.1 κ.2]

variable {G : Type} [Group G]

theorem exists_E16_of_model {I H : Subgroup G} (Φ : I ≃* M) {C : Subgroup M}
    (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) {E₀ : Subgroup M} (hE₀ : IsElemAbelian 2 E₀)
    (hcard : Nat.card E₀ = 2 ^ 4) (hEC : E₀ ≤ C) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 := by
  refine ⟨(E₀.map Φ.symm.toMonoidHom).map I.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, ⟨e, he, rfl⟩, rfl⟩
    have hy : Φ.toMonoidHom (Φ.symm e) ∈ (H.subgroupOf I).map Φ.toMonoidHom := by
      rw [hΦH]
      simpa using hEC he
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective).mp hy)
  · exact CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map
      (CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map hE₀ _) _
  · rw [Subgroup.card_map_of_injective I.subtype_injective,
      Subgroup.card_map_of_injective Φ.symm.injective, hcard]

theorem exists_std_pos {I A : Subgroup G} (hAI : A ≤ I) (Φ₁ : I ≃* M)
    (hΦ₁A : (A.subgroupOf I).map Φ₁.toMonoidHom = A0) (hAe : IsElemAbelian 3 A) {b : G}
    (hbA : b ∈ A) (hb1 : b ≠ 1) :
    ∃ (Φ : I ≃* M) (i : Fin 3) (b₀ : G) (hb₀I : b₀ ∈ I),
      Subgroup.zpowers b₀ = Subgroup.zpowers b ∧
        Φ ⟨b₀, hb₀I⟩ = δ (Multiplicative.ofAdd (std i)) ∧
          (A.subgroupOf I).map Φ.toMonoidHom = A0 := by
  have hbI : b ∈ I := hAI hbA
  have ha1 : (⟨b, hbA⟩ : A) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨v, hv⟩ := exists_v_of_thetaA hAI Φ₁ hΦ₁A ⟨b, hbA⟩
  have hv0 : v ≠ 0 := ne_zero_of_thetaA hAI Φ₁ hΦ₁A ha1 hv
  have hΦb : Φ₁ ⟨b, hbI⟩ = δ (Multiplicative.ofAdd v) :=
    (coe_thetaA hAI Φ₁ hΦ₁A ⟨b, hbA⟩).symm.trans hv
  obtain ⟨σ, i, hσ⟩ := exists_perm_std v hv0
  have hΦσ : (Φ₁.trans (reindexSL σ)) ⟨b, hbI⟩ =
      δ (Multiplicative.ofAdd (res (ext v ∘ σ))) := by
    rw [MulEquiv.trans_apply, hΦb, reindexSL_δ]
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hΦA : (A.subgroupOf I).map (Φ₁.trans (reindexSL σ)).toMonoidHom = A0 := by
    have : (Φ₁.trans (reindexSL σ)).toMonoidHom =
        (reindexSL σ).toMonoidHom.comp Φ₁.toMonoidHom := rfl
    rw [this, ← Subgroup.map_map, hΦ₁A, map_reindexSL_A0]
  rcases hσ with h | h
  · refine ⟨Φ₁.trans (reindexSL σ), i, b, hbI, rfl, ?_, hΦA⟩
    rw [hΦσ, h, res_ext]
  · refine ⟨Φ₁.trans (reindexSL σ), i, b ^ 2, Subgroup.pow_mem I hbI 2, zpowers_sq hb3, ?_,
      hΦA⟩
    have hsq : (⟨b ^ 2, Subgroup.pow_mem I hbI 2⟩ : I) = ⟨b, hbI⟩ ^ 2 := rfl
    rw [hsq, map_pow, hΦσ, h, res_ext, δ_two_smul, ← pow_mul]
    calc δ (Multiplicative.ofAdd (std i)) ^ (2 * 2)
        = δ (Multiplicative.ofAdd (std i)) ^ 3 * δ (Multiplicative.ofAdd (std i)) := by
          rw [← pow_succ]
      _ = δ (Multiplicative.ofAdd (std i)) := by rw [δ_pow_three, one_mul]

theorem terminalE16L44 : TerminalE16L44 := by
  intro G _ _ I A hAI hAe hT B hBA hB3 X hX
  obtain ⟨⟨e⟩, hA⟩ := hT
  obtain ⟨Φ₁, hΦ₁A⟩ := exists_Phi hAI hAe e hA
  obtain ⟨b, hbB, hb1, hBb⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA hbB
  obtain ⟨Φ, i, b₀, hb₀I, hzp, hΦb₀, -⟩ := exists_std_pos hAI Φ₁ hΦ₁A hAe hbA hb1
  have hBb₀ : B = Subgroup.zpowers b₀ := hBb.trans hzp.symm
  subst hBb₀
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hΦH : ((I ⊓ Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup G) : Set G)).subgroupOf
      I).map Φ.toMonoidHom =
      Subgroup.centralizer ({δ (Multiplicative.ofAdd (std i))} : Set M) := by
    rw [map_inf_centralizer_zpowers Φ hb₀I, hΦb₀]
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (thetaC hHI Φ hΦH) hX
  have hv0 : ∀ j : Fin 3, std j ≠ 0 := by decide
  by_cases hi : i = 0
  · subst hi
    right
    obtain ⟨Y₀, hcard, huniq⟩ := components_std0
    have hXY : X.map (thetaC hHI Φ hΦH).toMonoidHom = Y₀ := huniq _ hY
    refine ⟨fun X' hX' => ?_, ?_⟩
    · have hY' := CFSG.LocalCores.isComponent_map_mulEquiv (thetaC hHI Φ hΦH) hX'
      exact Subgroup.map_injective (thetaC hHI Φ hΦH).injective ((huniq _ hY').trans hXY.symm)
    · have hinj : Function.Injective (thetaC hHI Φ hΦH).toMonoidHom :=
        (thetaC hHI Φ hΦH).injective
      rw [← Subgroup.card_map_of_injective hinj, hXY]
      exact hcard
  · left
    obtain ⟨E₀, hE₀, hcardE₀, hE₀C⟩ := exists_E16_std i hi
    obtain ⟨E, hEH, hEab, hEcard⟩ := exists_E16_of_model Φ hΦH hE₀ hcardE₀ hE₀C
    have hYn : (X.map (thetaC hHI Φ hΦH).toMonoidHom).Normal := isComponent_normal_cv (hv0 i) hY
    haveI hXN : X.Normal := by
      have := hYn.comap (thetaC hHI Φ hΦH).toMonoidHom
      rwa [Subgroup.comap_map_eq_self_of_injective (thetaC hHI Φ hΦH).injective] at this
    exact ⟨E, fun g hg => (hEH hg).1, hEab, hEcard,
      fun g hg => Subgroup.centralizer_le_normalizer _ (hEH hg).2,
      fun g hg => Sec6.le_normalizer_map_subtype X (hEH hg)⟩

end Model

end CFSG.RankThree.PartTwo.Sec21
