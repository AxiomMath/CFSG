module

public import CFSG.Monster.B.CTIB.Fourteen
public import CFSG.Monster.B.CTIB.CoreCensus
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3027
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem isConj_of_odd {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1) {m : ℕ}
    (hm : Odd m) (h : (a * b) ^ m = 1) : IsConj a b := by
  set c := a * b with hc
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hcinv : a * c⁻¹ * a = c := by
    rw [hc, _root_.mul_inv_rev, ha', hb']
    calc a * (b * a) * a = a * b * (a * a) := by group
      _ = a * b := by rw [ha, mul_one]
  have hpow : ∀ k : ℕ, a * (c⁻¹) ^ k * a = c ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, mul_one, ha]
    | succ k ih =>
      calc a * c⁻¹ ^ (k + 1) * a = (a * c⁻¹ ^ k * a) * (a * c⁻¹ * a) := by
            rw [pow_succ]
            calc a * (c⁻¹ ^ k * c⁻¹) * a = a * c⁻¹ ^ k * (a * a) * c⁻¹ * a := by
                  rw [ha]; group
              _ = (a * c⁻¹ ^ k * a) * (a * c⁻¹ * a) := by group
        _ = c ^ (k + 1) := by rw [ih, hcinv, pow_succ]
  obtain ⟨j, hj⟩ := hm
  rw [isConj_iff]
  refine ⟨(c ^ (j + 1))⁻¹, ?_⟩
  calc (c ^ (j + 1))⁻¹ * a * (c ^ (j + 1))⁻¹⁻¹
      = (a * a) * (c⁻¹) ^ (j + 1) * a * c ^ (j + 1) := by rw [ha, inv_pow, inv_inv]; group
    _ = a * (a * c⁻¹ ^ (j + 1) * a) * c ^ (j + 1) := by group
    _ = a * c ^ (j + 1) * c ^ (j + 1) := by rw [hpow]
    _ = a * (c ^ m * c) := by
        rw [mul_assoc, ← pow_add, hj, ← pow_succ]
        congr 2
        omega
    _ = b := by rw [h, one_mul, hc, ← mul_assoc, ha, one_mul]

abbrev IsLetter3 (l : ℤ) : Prop := IsLetter2 l ∨ l = 3 ∨ l = -3

theorem letterS_three :
    letterS 3 = gs 2 := by
  rw [letterS, ite_eq_left (by decide), show (3 : ℤ).toNat - 1 = 2 by decide]

theorem letterS_neg_three :
    letterS (-3) = (gs 2)⁻¹ := by
  rw [letterS, ite_eq_right (by decide), show (- -3 : ℤ).toNat - 1 = 2 by decide]

theorem letterS_neg3
    {l : ℤ} (hl : IsLetter3 l) : letterS (-l) = (letterS l)⁻¹ := by
  rcases hl with hl | rfl | rfl
  · exact letterS_neg hl
  · rw [letterS_neg_three, letterS_three]
  · rw [show -(-3 : ℤ) = 3 from rfl, letterS_three, letterS_neg_three, inv_inv]

theorem wordS'_invWord3 :
    ∀ {w : List ℤ}, (∀ l ∈ w, IsLetter3 l) →
    wordS' (invWord w) = (wordS' w)⁻¹
  | [], _ => by rw [invWord, List.map_nil, List.reverse_nil, wordS'_nil, inv_one]
  | l :: w, hw => by
    have hl := hw l (List.mem_cons_self ..)
    rw [invWord, List.map_cons, List.reverse_cons, ← invWord, wordS'_append,
      wordS'_invWord3 fun l' h => hw l' (List.mem_cons_of_mem _ h)]
    rw [show wordS' [-l] = letterS (-l) by rw [wordS']; simp, letterS_neg3 hl,
      show wordS' (l :: w) = letterS l * wordS' w by rw [wordS']; simp [wordS'],
      _root_.mul_inv_rev]

theorem invWord_letters3 {w : List ℤ} (hw : ∀ l ∈ w, IsLetter3 l) :
    ∀ l ∈ invWord w, IsLetter3 l := by
  intro l hl
  rw [invWord, List.mem_reverse, List.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  rcases hw a ha with (rfl | rfl | rfl | rfl) | rfl | rfl <;> decide

theorem gs2_pow_three :
    gs 2 ^ 3 = 1 := by
  show (op taubar) ^ 3 = 1
  rw [← op_pow, taubar_pow_three, op_one]

theorem gs2_inv :
    (gs 2)⁻¹ = gs 2 * gs 2 := by
  rw [inv_eq_iff_mul_eq_one, ← gs2_pow_three, pow_three]

theorem beta_gs2 :
    (βr (gs 2)) = Qn 25 := by
  have h := betaS_explicit.gen 25 (by norm_num)
  rw [gSeq_last] at h
  exact h

theorem beta_letterS3
    {l : ℤ} (hl : IsLetter3 l) : (βr (letterS l)) = Dyadic.letterK l := by
  rcases hl with hl | rfl | rfl
  · exact beta_letterS hl
  · have e : Dyadic.letterK 3 = Dyadic.QnK 25 := rfl
    rw [letterS_three, beta_gs2, e, Qn]
  · have e : Dyadic.letterK (-3) = Dyadic.QnK 25 * Dyadic.QnK 25 := rfl
    rw [letterS_neg_three, gs2_inv, map_mul, Units.val_mul, beta_gs2, e, Qn]

theorem beta_wordS3 :
    ∀ {w : List ℤ}, (∀ l ∈ w, IsLetter3 l) → (βr (wordS' w)) = Dyadic.wordK w
  | [], _ => by rw [wordS'_nil, map_one, Units.val_one, Dyadic.wordK, List.map_nil, Dyadic.prodK]
  | l :: w, hw => by
    rw [wordS'_cons, map_mul, Units.val_mul, beta_letterS3 (hw l List.mem_cons_self),
      beta_wordS3 fun l' h => hw l' (List.mem_cons_of_mem _ h), Dyadic.wordK, Dyadic.wordK,
      List.map_cons, Dyadic.prodK]

theorem beta_conj_of
    {w r : Sbp} {A : MatB}
    (h : (βr w) * A = (βr r) * (βr w)) : A = βr (w⁻¹ * r * w) := by
  refine (Units.mul_right_inj (betaRow Dyadic.betaS w)).1 ?_
  have e : w * (w⁻¹ * r * w) = r * w := by group
  rw [h, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, e]

theorem globalFusion_ok : ∀ f ∈ globalFusion, f.1 < 14 ∧ f.2.1 < 14 ∧ Odd f.2.2.1 ∧
    ∀ l ∈ f.2.2.2, IsLetter3 l := by
  decide

theorem globalFusion_pairs : globalFusion.map (fun f => (f.1, f.2.1)) =
    [(2, 0), (4, 3), (6, 1), (7, 0), (8, 3), (9, 3), (10, 3), (11, 0), (12, 3), (13, 5)] := rfl

theorem globalFusion_exps : globalFusion.map (·.2.2.1) = [5, 35, 3, 5, 27, 39, 17, 5, 21, 35] :=
  rfl

theorem fusion_eq
    {f : ℕ × ℕ × ℕ × List ℤ} (hf : f ∈ globalFusion) :
    (rs f.2.1 * (wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2) ^ f.2.2.1 = 1 := by
  obtain ⟨-, -, -, hw⟩ := globalFusion_ok f hf
  obtain ⟨C, hC, hm⟩ := Certificates.certificate3012 f hf
  have hc := beta_conj_of (w := wordS' f.2.2.2) (r := rs f.1) (A := C) (by
    rw [beta_wordS3 hw, beta_rs]
    exact hC)
  have e : rs f.2.1 * (wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2 =
      rs f.2.1 * ((wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2) := by group
  rw [hc, ← beta_rs, ← Units.val_mul, ← map_mul, ← Units.val_pow_eq_pow_val, ← map_pow,
    ← Units.val_one, ← map_one (betaRow Dyadic.betaS)] at hm
  rw [e]
  exact betaRow_inj betaS_explicit.injective hm

theorem rs_mem_cosetInv
    {i : ℕ} (hi : 4 ≤ i) (hi' : i < 14) :
    rs i ∈ cosetInv (repTable.getD i (0, 0)).1 := by
  have key : ∀ k, IsRank k → ∀ r ∈ fusionRecsN k, cosetElt k r.2.2 ∈ cosetInv k :=
    fun k hk r hr => validK_mem hk (fOrbit_facts hk hr).1
  obtain ⟨h6, h8, h10⟩ := fusionRecs_eq
  interval_cases i
  · exact key 6 (.inl rfl) (270, 34560, 43) (by rw [h6]; simp)
  · exact key 6 (.inl rfl) (256, 32768, 61) (by rw [h6]; simp)
  · exact key 6 (.inl rfl) (1, 64, 10541) (by rw [h6]; simp)
  · exact key 6 (.inl rfl) (1, 128, 26925) (by rw [h6]; simp)
  · exact key 6 (.inl rfl) (1, 64, 46090) (by rw [h6]; simp)
  · exact key 8 (.inr (.inl rfl)) (1, 256, 0) (by rw [h8]; simp)
  · exact key 8 (.inr (.inl rfl)) (35, 17920, 128) (by rw [h8]; simp)
  · exact key 8 (.inr (.inl rfl)) (1, 256, 35764) (by rw [h8]; simp)
  · exact key 10 (.inr (.inr rfl)) (2, 4096, 107) (by rw [h10]; simp)
  · exact key 10 (.inr (.inr rfl)) (1, 2048, 66038) (by rw [h10]; simp)

theorem rs_mul_self
    {i : ℕ} (hi : i < 14) : rs i * rs i = 1 := by
  by_cases h4 : i < 4
  · have hmem : rs i ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := by
      rw [invs_eq]
      interval_cases i
      · exact .inl (.inl (.inl (mem_jClass_self _)))
      · exact .inl (.inl (.inr (mem_jClass_self _)))
      · exact .inl (.inr (mem_jClass_self _))
      · exact .inr (mem_jClass_self _)
    exact hmem.2.1
  · exact (rs_mem_cosetInv (by omega) hi).2

theorem rs_ne_one
    {i : ℕ} (hi : i < 14) : rs i ≠ 1 := by
  intro h
  have := rank_rs hi
  rw [h, map_one, Units.val_one, sub_self, Matrix.rank_zero] at this
  interval_cases i <;> simp [repRanks] at this

theorem fusion_conj
    {f : ℕ × ℕ × ℕ × List ℤ} (hf : f ∈ globalFusion) :
    IsConj (rs f.1) (rs f.2.1) := by
  obtain ⟨hs, ht, hm, -⟩ := globalFusion_ok f hf
  have hb : (wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2 *
      ((wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2) = 1 := by
    calc (wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2 *
          ((wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2)
        = (wordS' f.2.2.2)⁻¹ * (rs f.1 * rs f.1) * wordS' f.2.2.2 := by group
      _ = 1 := by rw [rs_mul_self hs]; group
  have h := isConj_of_odd (rs_mul_self ht) hb hm (by
    rw [← fusion_eq hf]
    congr 1
    group)
  have h2 : IsConj (rs f.1) ((wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2) := by
    rw [isConj_iff]
    exact ⟨(wordS' f.2.2.2)⁻¹, by group⟩
  exact h2.trans h.symm

end CFSG.Monster.B.CTIB
