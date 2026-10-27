module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4
namespace Item434SmallTwoOther

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL)
open Item434Kit
open Matrix
open scoped MatrixGroups commutatorElement

section Cross

variable {n : ℕ}

noncomputable def crossA {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d) :
    SL(n, GaloisField 2 1) :=
  SpecialLinearGroup.transvection hac 1 * SpecialLinearGroup.transvection hbd 1

theorem crossA_smul_of_ne {a b c d k : Fin n} (hac : a ≠ c) (hbd : b ≠ d) (hkc : k ≠ c)
    (hkd : k ≠ d) :
    crossA hac hbd • (Pi.single k 1 : Fin n → GaloisField 2 1) = Pi.single k 1 := by
  rw [crossA, mul_smul, transvection_smul_single_of_ne hbd hkd,
    transvection_smul_single_of_ne hac hkc]

theorem crossA_smul_c {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    crossA hac hbd • (Pi.single c 1 : Fin n → GaloisField 2 1) =
      Pi.single c 1 + Pi.single a 1 := by
  rw [crossA, mul_smul, transvection_smul_single_of_ne hbd hcd, transvection_smul_single_snd' hac]

theorem crossA_smul_d {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d) (hdc : d ≠ c)
    (hbc : b ≠ c) :
    crossA hac hbd • (Pi.single d 1 : Fin n → GaloisField 2 1) =
      Pi.single d 1 + Pi.single b 1 := by
  rw [crossA, mul_smul, transvection_smul_single_snd' hbd, smul_add,
    transvection_smul_single_of_ne hac hdc, transvection_smul_single_of_ne hac hbc]

theorem commute_crossA {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : Commute (crossA hac hbd) (blk hab * blk hcd) := by
  show crossA hac hbd * (blk hab * blk hcd) = blk hab * blk hcd * crossA hac hbd
  apply SL_ext_smul
  intro k
  simp only [mul_smul]
  by_cases hka : k = a
  · rw [hka]
    simp only [blk_smul_of_ne hcd hac had, blk_smul_fst hab, crossA_smul_of_ne hac hbd hbc hbd,
      crossA_smul_of_ne hac hbd hac had]
  by_cases hkb : k = b
  · rw [hkb]
    simp only [smul_add, blk_smul_of_ne hcd hbc hbd, blk_smul_snd hab,
      crossA_smul_of_ne hac hbd hac had, crossA_smul_of_ne hac hbd hbc hbd]
  by_cases hkc : k = c
  · rw [hkc]
    simp only [smul_add, blk_smul_fst hcd, blk_smul_of_ne hab had.symm hbd.symm,
      crossA_smul_d hac hbd hcd.symm hbc, crossA_smul_c hac hbd hcd, blk_smul_of_ne hcd hac had,
      blk_smul_fst hab]
  by_cases hkd : k = d
  · rw [hkd]
    simp only [smul_add, blk_smul_snd hcd, blk_smul_of_ne hab hac.symm hbc.symm,
      blk_smul_of_ne hab had.symm hbd.symm, crossA_smul_c hac hbd hcd,
      crossA_smul_d hac hbd hcd.symm hbc, blk_smul_of_ne hcd hbc hbd, blk_smul_snd hab]
    abel
  · simp only [blk_smul_of_ne hcd hkc hkd, blk_smul_of_ne hab hka hkb,
      crossA_smul_of_ne hac hbd hkc hkd]

theorem transvection_mul_crossA {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SpecialLinearGroup.transvection hab.symm 1 * crossA hac hbd =
      SpecialLinearGroup.transvection hbc 1 * crossA hac hbd *
        SpecialLinearGroup.transvection hab.symm 1 := by
  apply SL_ext_smul
  intro k
  simp only [mul_smul]
  by_cases hka : k = a
  · rw [hka]
    simp only [smul_add, crossA_smul_of_ne hac hbd hac had, transvection_smul_single_snd' hab.symm,
      crossA_smul_of_ne hac hbd hbc hbd, transvection_smul_single_of_ne hbc hac,
      transvection_smul_single_of_ne hbc hbc]
  by_cases hkb : k = b
  · rw [hkb]
    simp only [crossA_smul_of_ne hac hbd hbc hbd, transvection_smul_single_of_ne hab.symm hab.symm,
      transvection_smul_single_of_ne hbc hbc]
  by_cases hkc : k = c
  · rw [hkc]
    simp only [smul_add, crossA_smul_c hac hbd hcd,
      transvection_smul_single_of_ne hab.symm hac.symm, transvection_smul_single_snd' hab.symm,
      transvection_smul_single_snd' hbc, transvection_smul_single_of_ne hbc hac]
    abel
  by_cases hkd : k = d
  · rw [hkd]
    simp only [smul_add, crossA_smul_d hac hbd hcd.symm hbc,
      transvection_smul_single_of_ne hab.symm had.symm,
      transvection_smul_single_of_ne hab.symm hab.symm, transvection_smul_single_of_ne hbc hcd.symm,
      transvection_smul_single_of_ne hbc hbc]
  · simp only [crossA_smul_of_ne hac hbd hkc hkd, transvection_smul_single_of_ne hab.symm hka,
      transvection_smul_single_of_ne hbc hkc]

theorem commutator_transvection_crossA {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ⁅SpecialLinearGroup.transvection hab.symm (1 : GaloisField 2 1), crossA hac hbd⁆ =
      SpecialLinearGroup.transvection hbc 1 := by
  rw [commutatorElement_def, transvection_mul_crossA hab hcd hac had hbc hbd, mul_inv_cancel_right,
    mul_inv_cancel_right]

theorem commute_crossA_blk {a b c d e f : Fin n} (hac : a ≠ c) (hbd : b ≠ d) (hef : e ≠ f)
    (hae : a ≠ e) (haf : a ≠ f) (hbe : b ≠ e) (hbf : b ≠ f) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) : Commute (crossA hac hbd) (blk hef) :=
  Commute.mul_left (commute_blk_transvection hef hac hae haf hce hcf 1).symm
    (commute_blk_transvection hef hbd hbe hbf hde hdf 1).symm

theorem crossA_mem_hyperCent {P : Subgroup SL(n, GaloisField 2 1)} (hP27 : Nat.card P = 27)
    {a b c d e f : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) (h1 : blk hab ∈ P)
    (h2 : blk hcd ∈ P) (h3 : blk hef ∈ P) : crossA hac hbd ∈ hyperCent P := by
  have hpq : Commute (blk hab) (blk hcd) := commute_blk_blk hab hcd hac had hbc hbd
  have hX3 : (blk hab * blk hcd) ^ 3 = 1 := by
    rw [hpq.mul_pow, blk_pow_three, blk_pow_three, one_mul]
  have hX1 : blk hab * blk hcd ≠ 1 := by
    intro h
    apply blk_smul_fst_ne hab
    have h' := congrArg (· • (Pi.single a 1 : Fin n → GaloisField 2 1)) h
    simp only [mul_smul, one_smul, blk_smul_of_ne hcd hac had] at h'
    exact h'
  have hXe : (blk hab * blk hcd) • (Pi.single e 1 : Fin n → GaloisField 2 1) = Pi.single e 1 := by
    rw [mul_smul, blk_smul_of_ne hcd hce.symm hde.symm, blk_smul_of_ne hab hae.symm hbe.symm]
  have hR := isElemAbelian_zpowers_sup hX3 hX1 (blk_pow_three hef)
    (notMem_zpowers_of_smul hXe (blk_smul_fst_ne hef))
    (Commute.mul_left (commute_blk_blk hab hef hae haf hbe hbf)
      (commute_blk_blk hcd hef hce hcf hde hdf)).eq
  exact mem_hyperCent_of_commute_sup hP27
    (sup_le (Subgroup.zpowers_le.mpr (P.mul_mem h1 h2)) (Subgroup.zpowers_le.mpr h3)) hR.2
    (commute_crossA hab hcd hac had hbc hbd).symm.eq
    (commute_crossA_blk hac hbd hef hae haf hbe hbf hce hcf hde hdf).symm.eq

theorem cross_mem {H : Subgroup SL(n, GaloisField 2 1)} {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbc_mem : SpecialLinearGroup.transvection hbc 1 ∈ H)
    (hab_mem : SpecialLinearGroup.transvection hab 1 ∈ H)
    (hcd_mem : SpecialLinearGroup.transvection hcd 1 ∈ H) :
    SpecialLinearGroup.transvection hac 1 ∈ H ∧ SpecialLinearGroup.transvection had 1 ∈ H ∧
      SpecialLinearGroup.transvection hbd 1 ∈ H := by
  have comm_mem : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ H := fun x hx y hy => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have hac_mem : SpecialLinearGroup.transvection hac 1 ∈ H := by
    have h := SpecialLinearGroup.commutatorElement_transvection hab hbc hac
      (1 : GaloisField 2 1) 1
    rw [mul_one] at h
    rw [← h]
    exact comm_mem _ hab_mem _ hbc_mem
  have hbd_mem : SpecialLinearGroup.transvection hbd 1 ∈ H := by
    have h := SpecialLinearGroup.commutatorElement_transvection hbc hcd hbd
      (1 : GaloisField 2 1) 1
    rw [mul_one] at h
    rw [← h]
    exact comm_mem _ hbc_mem _ hcd_mem
  have had_mem : SpecialLinearGroup.transvection had 1 ∈ H := by
    have h := SpecialLinearGroup.commutatorElement_transvection hab hbd had
      (1 : GaloisField 2 1) 1
    rw [mul_one] at h
    rw [← h]
    exact comm_mem _ hab_mem _ hbd_mem
  exact ⟨hac_mem, had_mem, hbd_mem⟩

theorem cross_mem_closure {P : Subgroup SL(n, GaloisField 2 1)} (hP27 : Nat.card P = 27)
    {a b c d e f : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) (h1 : blk hab ∈ P)
    (h2 : blk hcd ∈ P) (h3 : blk hef ∈ P)
    (hab_mem : SpecialLinearGroup.transvection hab 1 ∈ Subgroup.closure (hyperCent P))
    (hba_mem : SpecialLinearGroup.transvection hab.symm 1 ∈ Subgroup.closure (hyperCent P))
    (hcd_mem : SpecialLinearGroup.transvection hcd 1 ∈ Subgroup.closure (hyperCent P)) :
    SpecialLinearGroup.transvection hbc 1 ∈ Subgroup.closure (hyperCent P) ∧
      SpecialLinearGroup.transvection had 1 ∈ Subgroup.closure (hyperCent P) ∧
      SpecialLinearGroup.transvection hbd 1 ∈ Subgroup.closure (hyperCent P) := by
  set H := Subgroup.closure (hyperCent P)
  have hA : crossA hac hbd ∈ H := Subgroup.subset_closure
    (crossA_mem_hyperCent hP27 hab hcd hef hac had hae haf hbc hbd hbe hbf hce hcf hde hdf h1 h2
      h3)
  have hbc_mem : SpecialLinearGroup.transvection hbc 1 ∈ H := by
    rw [← commutator_transvection_crossA hab hcd hac had hbc hbd, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hba_mem hA) (H.inv_mem hba_mem)) (H.inv_mem hA)
  obtain ⟨-, had_mem, hbd_mem⟩ := cross_mem hab hcd hac had hbc hbd hbc_mem hab_mem hcd_mem
  exact ⟨hbc_mem, had_mem, hbd_mem⟩

end Cross

namespace L62

noncomputable def t₁ : SL(6, GaloisField 2 1) := blk (show (0 : Fin 6) ≠ 1 by decide)

noncomputable def t₂ : SL(6, GaloisField 2 1) := blk (show (2 : Fin 6) ≠ 3 by decide)

noncomputable def t₃ : SL(6, GaloisField 2 1) := blk (show (4 : Fin 6) ≠ 5 by decide)

noncomputable def z : Fin 3 → SL(6, GaloisField 2 1) := ![t₁, t₂, t₃]

def blockPerm : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro x
    fin_cases x <;> rfl
  right_inv := by
    intro x
    fin_cases x <;> rfl

noncomputable def tw : SL(6, GaloisField 2 1) := permSL blockPerm

theorem comm₁₂ : Commute t₁ t₂ :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem comm₁₃ : Commute t₁ t₃ :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem comm₂₃ : Commute t₂ t₃ :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem t₁_pow_smul (m : ℕ) {k : Fin 6} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    t₁ ^ m • (Pi.single k 1 : Fin 6 → GaloisField 2 1) = Pi.single k 1 :=
  pow_smul_eq_of_smul_eq (blk_smul_of_ne _ hk0 hk1) m

theorem t₂_pow_smul (m : ℕ) {k : Fin 6} (hk2 : k ≠ 2) (hk3 : k ≠ 3) :
    t₂ ^ m • (Pi.single k 1 : Fin 6 → GaloisField 2 1) = Pi.single k 1 :=
  pow_smul_eq_of_smul_eq (blk_smul_of_ne _ hk2 hk3) m

theorem t₃_pow_smul (m : ℕ) {k : Fin 6} (hk4 : k ≠ 4) (hk5 : k ≠ 5) :
    t₃ ^ m • (Pi.single k 1 : Fin 6 → GaloisField 2 1) = Pi.single k 1 :=
  pow_smul_eq_of_smul_eq (blk_smul_of_ne _ hk4 hk5) m

theorem conj_t₁ : tw * t₁ * tw⁻¹ = t₂ :=
  permSL_conj_blk blockPerm (a := 0) (b := 1) (c := 2) (d := 3) _ _ rfl rfl

theorem wreathFacts : WreathFacts z tw where
  pow_z i := by
    fin_cases i
    · exact blk_pow_three _
    · exact blk_pow_three _
    · exact blk_pow_three _
  comm_z i j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact comm₁₂.eq
    · exact comm₁₃.eq
    · exact comm₁₂.symm.eq
    · rfl
    · exact comm₂₃.eq
    · exact comm₁₃.symm.eq
    · exact comm₂₃.symm.eq
    · rfl
  inj v hv := by
    have hv' : t₁ ^ (v 0).val * t₂ ^ (v 1).val * t₃ ^ (v 2).val = 1 := hv
    have hfix : ∀ k : Fin 6, (t₁ ^ (v 0).val * t₂ ^ (v 1).val * t₃ ^ (v 2).val) •
        (Pi.single k 1 : Fin 6 → GaloisField 2 1) = Pi.single k 1 := fun k => by
      rw [hv', one_smul]
    have h0 : (v 0).val = 0 := by
      have h := hfix 0
      rw [mul_smul, mul_smul, t₃_pow_smul (k := 0) _ (by decide) (by decide),
        t₂_pow_smul (k := 0) _ (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul _ (ZMod.val_lt _) h
    have h1 : (v 1).val = 0 := by
      have h := hfix 2
      rw [(Commute.pow_pow comm₁₂ (v 0).val (v 1).val).eq, mul_assoc, mul_smul, mul_smul,
        t₃_pow_smul (k := 2) _ (by decide) (by decide),
        t₁_pow_smul (k := 2) _ (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul _ (ZMod.val_lt _) h
    have h2 : (v 2).val = 0 := by
      have h := hfix 4
      have hc : Commute (t₁ ^ (v 0).val * t₂ ^ (v 1).val) (t₃ ^ (v 2).val) :=
        Commute.mul_left (Commute.pow_pow comm₁₃ _ _) (Commute.pow_pow comm₂₃ _ _)
      rw [hc.eq, mul_smul, mul_smul, t₂_pow_smul (k := 4) _ (by decide) (by decide),
        t₁_pow_smul (k := 4) _ (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul _ (ZMod.val_lt _) h
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h0
    · exact (ZMod.val_eq_zero _).mp h1
    · exact (ZMod.val_eq_zero _).mp h2
  pow_t := by
    apply SL_ext_smul
    intro k
    rw [one_smul, pow_three, mul_smul, mul_smul, tw, permSL_smul_single, permSL_smul_single,
      permSL_smul_single]
    congr 1
    fin_cases k <;> rfl
  conj0 := conj_t₁
  conj1 := permSL_conj_blk blockPerm (a := 2) (b := 3) (c := 4) (d := 5) _ _ rfl rfl
  conj2 := permSL_conj_blk blockPerm (a := 4) (b := 5) (c := 0) (d := 1) _ _ rfl rfl
  t_ne v hv := by
    have hc : Commute (vecElt z v) t₁ :=
      Commute.mul_left (Commute.mul_left (Commute.pow_left (Commute.refl t₁) _)
        (Commute.pow_left comm₁₂.symm _)) (Commute.pow_left comm₁₃.symm _)
    rw [hv] at hc
    have h1 := conj_t₁
    rw [hc.eq, mul_inv_cancel_right] at h1
    have h2 : t₂ • (Pi.single 0 1 : Fin 6 → GaloisField 2 1) = Pi.single 0 1 :=
      blk_smul_of_ne _ (by decide) (by decide)
    rw [← h1] at h2
    exact blk_smul_fst_ne _ h2

theorem card_SL6 : Nat.card SL(6, GaloisField 2 1) = 20158709760 := by
  rw [card_SL_gf2 (by norm_num)]
  decide

theorem factorization_card_SL6 : (Nat.card SL(6, GaloisField 2 1)).factorization 3 = 4 := by
  rw [card_SL6, show (20158709760 : ℕ) = 3 ^ 4 * 248872960 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW : Nat.card (wreathW z tw) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts)
  rw [factorization_card_SL6] at hle
  have := le_card_wreathW wreathFacts
  norm_num at hle
  omega

theorem closure_hyperCent_baseA : Subgroup.closure (hyperCent (baseA z)) = ⊤ := by
  have hf := wreathFacts
  have h27 := card_baseA hf
  have R12 := (Item434Kit.isElemAbelian_sup_zpowers hf (show (1 : Fin 3) ≠ 2 by decide)).2
  have R02 := (Item434Kit.isElemAbelian_sup_zpowers hf (show (0 : Fin 3) ≠ 2 by decide)).2
  have R01 := (Item434Kit.isElemAbelian_sup_zpowers hf (show (0 : Fin 3) ≠ 1 by decide)).2
  have m1 : blk (show (0 : Fin 6) ≠ 1 by decide) ∈ baseA z := z_mem_baseA 0
  have m2 : blk (show (2 : Fin 6) ≠ 3 by decide) ∈ baseA z := z_mem_baseA 1
  have m3 : blk (show (4 : Fin 6) ≠ 5 by decide) ∈ baseA z := z_mem_baseA 2
  have T01 : SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) 1 ∈
      Subgroup.closure (hyperCent (baseA z)) :=
    Subgroup.subset_closure (mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 1 2) R12
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq)
  have T10 : SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) 1 ∈
      Subgroup.closure (hyperCent (baseA z)) :=
    Subgroup.subset_closure (mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 1 2) R12
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq)
  have T23 : SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) 1 ∈
      Subgroup.closure (hyperCent (baseA z)) :=
    Subgroup.subset_closure (mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 2) R02
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq)
  have T32 : SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 2 by decide) 1 ∈
      Subgroup.closure (hyperCent (baseA z)) :=
    Subgroup.subset_closure (mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 2) R02
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq)
  have T45 : SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) 1 ∈
      Subgroup.closure (hyperCent (baseA z)) :=
    Subgroup.subset_closure (mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 1) R01
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq)
  have T54 : SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) 1 ∈
      Subgroup.closure (hyperCent (baseA z)) :=
    Subgroup.subset_closure (mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 1) R01
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq
      (commute_blk_transvection _ _ (by decide) (by decide) (by decide) (by decide) 1).eq)
  obtain ⟨-, T05, T15⟩ := cross_mem_closure h27 (a := 0) (b := 1) (c := 4) (d := 5) (e := 2)
    (f := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m1 m3 m2 T01 T10 T45
  obtain ⟨-, T25, T35⟩ := cross_mem_closure h27 (a := 2) (b := 3) (c := 4) (d := 5) (e := 0)
    (f := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m2 m3 m1 T23 T32 T45
  obtain ⟨T50, -, T51⟩ := cross_mem_closure h27 (a := 4) (b := 5) (c := 0) (d := 1) (e := 2)
    (f := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m3 m1 m2 T45 T54 T01
  obtain ⟨T52, -, T53⟩ := cross_mem_closure h27 (a := 4) (b := 5) (c := 2) (d := 3) (e := 0)
    (f := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) m3 m2 m1 T45 T54 T23
  apply eq_top_of_hub (5 : Fin 6)
  · intro i hi
    fin_cases i
    · exact T05
    · exact T15
    · exact T25
    · exact T35
    · exact T45
    · exact absurd rfl hi
  · intro i hi
    fin_cases i
    · exact T50
    · exact T51
    · exact T52
    · exact T53
    · exact T54
    · exact absurd rfl hi

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem gen_SL6 (h : Ctx434Core G A M Q) (h27 : Nat.card h.layerStar = 27) :
    ∀ P : Subgroup SL(6, GaloisField 2 1), CFSG.Assembly.IsElemAbelian 3 P →
      Nat.card P = Nat.card h.layerStar → Subgroup.closure (hyperCent P) = ⊤ := by
  intro P hP hPc
  rw [h27] at hPc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW z tw)
    (by rw [card_wreathW, factorization_card_SL6]; norm_num) hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom = baseA z :=
    eq_baseA_of_le_wreathW hf card_wreathW (Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hPc])
  have hPeq : P = (baseA z).map (MulAut.conj g).toMonoidHom := by
    rw [← hPg, Item434AltPerm.map_conj_map_conj_inv]
  rw [hPeq]
  exact closure_hyperCent_map_conj closure_hyperCent_baseA g

theorem false_of_L62
    (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 6 (GaloisField 2 1)) : False := by
  have hZ := center_layer_eq_bot_of_projSL_gf2 h (by norm_num) e
  have hf := wreathFacts
  let ψ := slEquivProjSL (n := 6) (by norm_num)
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434Spor.false_of_card_nine h hZ e
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ.toMonoidHom _
        (isElemAbelian_baseA hf))
      (by rw [Subgroup.card_map_of_injective ψ.injective, card_baseA hf]) h9
  · exact false_of_gen h hZ e (not_three_dvd_card_outer_projSL_gf2 (by norm_num))
      (center_projSL_gf2 (by norm_num)) (gen_of_mulEquiv ψ (gen_SL6 h h27))

end Ctx

end L62

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtL62 : Item434SecFor IsSmallTwoOtherL62 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.L62.false_of_L62 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
