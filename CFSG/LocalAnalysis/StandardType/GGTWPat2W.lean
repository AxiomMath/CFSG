module

public import CFSG.LocalAnalysis.StandardType.GGTWExt2AB
public import CFSG.LocalAnalysis.StandardType.GGTWExt2D
public import CFSG.LocalAnalysis.StandardType.GGTWExt2E
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private noncomputable def l05nS1_xiE (N : ℕ) :
    Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} where
  toFun k := ⟨⟨k.val + 1, by omega⟩, by
    simp only [ggTWInJ]; exact ⟨by omega, by omega⟩⟩
  invFun j := ⟨j.val.val - 1, by have := j.2; simp only [ggTWInJ] at this; omega⟩
  left_inv k := by apply Fin.ext; simp
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hj : 1 ≤ j.val.val := by
      have := j.2; simp only [ggTWInJ] at this; exact this.1
    simp only [Fin.val_mk]
    omega

private noncomputable def l05nS1_xiA (N : ℕ) :
    Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} where
  toFun k := ⟨⟨k.val, by omega⟩, by
    simp only [ggTWInJ]; exact (by omega : k.val + 4 ≤ N)⟩
  invFun j := ⟨j.val.val, by have := j.2; simp only [ggTWInJ] at this; omega⟩
  left_inv k := by apply Fin.ext; rfl
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.val_mk]

private theorem l05nS1_pat1_cox {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {N : ℕ} {pos : GGTWPos} {c : ℕ} {a b : ι} (hab : a ≠ b)
    (hinJ : ggTWInJ N pos c) (hpos : GGTWPosCox N pos c (M a b)) :
    GGTWPat1 N pos c (C a b) (C b a) := by
  refine ⟨hinJ, ?_⟩
  unfold GGTWPosCox GGTWPosCoxK at hpos
  rcases hpos with ⟨hend, hm | hm⟩ | ⟨hk, hsec, hm⟩ | ⟨hk, hk7, hthird, hm⟩
  · rcases hC.2 a b hab with ⟨hm', -, -⟩ | ⟨-, h1, h2⟩ | ⟨hm', h1, h2, h3⟩ | ⟨hm', h1, h2, h3⟩
    · rw [hm] at hm'; omega
    · exact Or.inl ⟨hend, Or.inl ⟨h1, h2⟩⟩
    · rw [hm] at hm'; omega
    · rw [hm] at hm'; omega
  · rcases hC.2 a b hab with ⟨hm', -, -⟩ | ⟨hm', -, -⟩ | ⟨-, hprod, hneg1, hneg2⟩ |
      ⟨hm', -, -, -⟩
    · rw [hm] at hm'; omega
    · rw [hm] at hm'; omega
    · rcases int_neg_pair_of_mul_eq (Or.inl rfl) hneg1 hneg2 hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hend, Or.inr (Or.inl ⟨h1, h2⟩)⟩
      · exact Or.inl ⟨hend, Or.inr (Or.inr ⟨h1, h2⟩)⟩
    · rw [hm] at hm'; omega
  · rcases hC.2 a b hab with ⟨hm', -, -⟩ | ⟨-, h1, h2⟩ | ⟨hm', -, -, -⟩ | ⟨hm', -, -, -⟩
    · rw [hm] at hm'; omega
    · exact Or.inr (Or.inl ⟨hk, hsec, h1, h2⟩)
    · rw [hm] at hm'; omega
    · rw [hm] at hm'; omega
  · rcases hC.2 a b hab with ⟨hm', -, -⟩ | ⟨-, h1, h2⟩ | ⟨hm', -, -, -⟩ | ⟨hm', -, -, -⟩
    · rw [hm] at hm'; omega
    · exact Or.inr (Or.inr ⟨hk, hk7, hthird, h1, h2⟩)
    · rw [hm] at hm'; omega
    · rw [hm] at hm'; omega

private theorem l05nS1_pat1_end {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {N : ℕ} {pos : GGTWPos} {c : ℕ} {a b : ι} (hab : a ≠ b)
    (hinJ : ggTWInJ N pos c) (hM4 : M a b = 4)
    (hend : ggTWPlace pos c = 0 ∨ ggTWPlace pos c + 1 = N - 3) :
    GGTWPat1 N pos c (C a b) (C b a) := by
  refine ⟨hinJ, Or.inl ⟨hend, ?_⟩⟩
  rcases hC.2 a b hab with ⟨hm', -, -⟩ | ⟨hm', -, -⟩ | ⟨-, hprod, hneg1, hneg2⟩ |
    ⟨hm', -, -, -⟩
  · rw [hM4] at hm'; omega
  · rw [hM4] at hm'; omega
  · rcases int_neg_pair_of_mul_eq (Or.inl rfl) hneg1 hneg2 hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · rw [hM4] at hm'; omega

private theorem l05nS1_translate {N : ℕ} {pos : GGTWPos} {Λa : Type}
    {MK : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK) {a : Λa} (hcox : GGTWExt2Cox N pos MK a) :
    (∃ (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n ∧
      ∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK (Sum.inr a) (Sum.inl j) = (if j.1 = c0 then m else 0) ∧
          CK (Sum.inl j) (Sum.inr a) = (if j.1 = c0 then n else 0)) ∨
    ((∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK (Sum.inr a) (Sum.inl j) = 0 ∧ CK (Sum.inl j) (Sum.inr a) = 0) ∧
      ∃ (b : Λa) (c0 : Fin (N - 1)) (m n : ℤ), b ≠ a ∧ GGTWPat1 N pos c0.val m n ∧
        GGTWPat1 N pos c0.val (-(CK (Sum.inr a) (Sum.inr b)) * m)
          (-(CK (Sum.inr b) (Sum.inr a)) * n) ∧
        ∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
          CK (Sum.inr b) (Sum.inl j) = (if j.1 = c0 then m else 0) ∧
            CK (Sum.inl j) (Sum.inr b) = (if j.1 = c0 then n else 0)) := by
  rcases hcox with ⟨c0h, hpos, hrow⟩ | ⟨hrowall, b, c0h, hba, hposb, hrowb, hbond⟩
  · left
    refine ⟨c0h.1, CK (Sum.inr a) (Sum.inl c0h), CK (Sum.inl c0h) (Sum.inr a), ?_, ?_⟩
    · exact l05nS1_pat1_cox hCK (a := Sum.inr a) (b := Sum.inl c0h) Sum.inr_ne_inl c0h.2 hpos
    · intro j
      by_cases hj : j.1 = c0h.1
      · have hje : j = c0h := Subtype.ext hj
        subst hje
        simp
      · have hjc : j ≠ c0h := fun h => hj (congrArg Subtype.val h)
        have hk := hrow j hjc
        rcases hCK.2 (Sum.inr a) (Sum.inl j) Sum.inr_ne_inl with
          ⟨-, h1, h2⟩ | ⟨hm3, -, -⟩ | ⟨hm4, -, -, -⟩ | ⟨hm6, -, -, -⟩
        · exact ⟨by rw [if_neg hj, h1], by rw [if_neg hj, h2]⟩
        · rw [hk] at hm3; omega
        · rw [hk] at hm4; omega
        · rw [hk] at hm6; omega
  · right
    have hpatb : GGTWPat1 N pos c0h.1.val (CK (Sum.inr b) (Sum.inl c0h))
        (CK (Sum.inl c0h) (Sum.inr b)) :=
      l05nS1_pat1_cox hCK (a := Sum.inr b) (b := Sum.inl c0h) Sum.inr_ne_inl c0h.2 hposb
    refine ⟨?_, b, c0h.1, CK (Sum.inr b) (Sum.inl c0h), CK (Sum.inl c0h) (Sum.inr b),
      hba, hpatb, ?_, ?_⟩
    · intro j
      have hk := hrowall j
      rcases hCK.2 (Sum.inr a) (Sum.inl j) Sum.inr_ne_inl with
        ⟨-, h1, h2⟩ | ⟨hm3, -, -⟩ | ⟨hm4, -, -, -⟩ | ⟨hm6, -, -, -⟩
      · exact ⟨h1, h2⟩
      · rw [hk] at hm3; omega
      · rw [hk] at hm4; omega
      · rw [hk] at hm6; omega
    · rcases hbond with hMab3 | ⟨hMab4, hMbc3, hend⟩
      · rcases hCK.2 (Sum.inr a) (Sum.inr b)
          (fun h => hba (Sum.inr.inj h.symm)) with
          ⟨hm2, -, -⟩ | ⟨-, h1, h2⟩ | ⟨hm4, -, -, -⟩ | ⟨hm6, -, -, -⟩
        · rw [hMab3] at hm2; omega
        · have e1 : -(CK (Sum.inr a) (Sum.inr b)) * CK (Sum.inr b) (Sum.inl c0h) =
              CK (Sum.inr b) (Sum.inl c0h) := by rw [h1]; ring
          have e2 : -(CK (Sum.inr b) (Sum.inr a)) * CK (Sum.inl c0h) (Sum.inr b) =
              CK (Sum.inl c0h) (Sum.inr b) := by rw [h2]; ring
          rw [e1, e2]
          exact hpatb
        · rw [hMab3] at hm4; omega
        · rw [hMab3] at hm6; omega
      · have hm1 : CK (Sum.inr b) (Sum.inl c0h) = -1 ∧ CK (Sum.inl c0h) (Sum.inr b) = -1 := by
          rcases hCK.2 (Sum.inr b) (Sum.inl c0h) Sum.inr_ne_inl with
            ⟨hm2, -, -⟩ | ⟨-, h1, h2⟩ | ⟨hm4, -, -, -⟩ | ⟨hm6, -, -, -⟩
          · rw [hMbc3] at hm2; omega
          · exact ⟨h1, h2⟩
          · rw [hMbc3] at hm4; omega
          · rw [hMbc3] at hm6; omega
        have hconj : GGTWPat1 N pos c0h.1.val (CK (Sum.inr a) (Sum.inr b))
            (CK (Sum.inr b) (Sum.inr a)) :=
          l05nS1_pat1_end hCK (a := Sum.inr a) (b := Sum.inr b)
            (fun h => hba (Sum.inr.inj h.symm)) c0h.2 hMab4 hend
        have e1 : -(CK (Sum.inr a) (Sum.inr b)) * CK (Sum.inr b) (Sum.inl c0h) =
            CK (Sum.inr a) (Sum.inr b) := by rw [hm1.1]; ring
        have e2 : -(CK (Sum.inr b) (Sum.inr a)) * CK (Sum.inl c0h) (Sum.inr b) =
            CK (Sum.inr b) (Sum.inr a) := by rw [hm1.2]; ring
        rw [e1, e2]
        exact hconj
    · intro j
      by_cases hj : j.1 = c0h.1
      · have hje : j = c0h := Subtype.ext hj
        subst hje
        simp
      · have hjc : j ≠ c0h := fun h => hj (congrArg Subtype.val h)
        have hk := hrowb j hjc
        rcases hCK.2 (Sum.inr b) (Sum.inl j) Sum.inr_ne_inl with
          ⟨-, h1, h2⟩ | ⟨hm3, -, -⟩ | ⟨hm4, -, -, -⟩ | ⟨hm6, -, -, -⟩
        · exact ⟨by rw [if_neg hj, h1], by rw [if_neg hj, h2]⟩
        · rw [hk] at hm3; omega
        · rw [hk] at hm4; omega
        · rw [hk] at hm6; omega

theorem ggTW_pattern2W {N : ℕ} (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10) (pos : GGTWPos)
    {Λa : Type} (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      CK (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1) (a : Λa) :
    (∃ (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n ∧
      ∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK (Sum.inr a) (Sum.inl j) = (if j.1 = c0 then m else 0) ∧
          CK (Sum.inl j) (Sum.inr a) = (if j.1 = c0 then n else 0)) ∨
    ((∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK (Sum.inr a) (Sum.inl j) = 0 ∧ CK (Sum.inl j) (Sum.inr a) = 0) ∧
      ∃ (b : Λa) (c0 : Fin (N - 1)) (m n : ℤ), b ≠ a ∧ GGTWPat1 N pos c0.val m n ∧
        GGTWPat1 N pos c0.val (-(CK (Sum.inr a) (Sum.inr b)) * m)
          (-(CK (Sum.inr b) (Sum.inr a)) * n) ∧
        ∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
          CK (Sum.inr b) (Sum.inl j) = (if j.1 = c0 then m else 0) ∧
            CK (Sum.inl j) (Sum.inr b) = (if j.1 = c0 then n else 0)) := by
  have hN5 : 5 ≤ N := by rcases hN with h | h | h | h | h <;> omega
  have hNmem : N - 1 = 4 ∨ N - 1 = 5 ∨ N - 1 = 6 ∨ N - 1 = 8 ∨ N - 1 = 9 := by
    rcases hN with h | h | h | h | h <;> omega
  have hFinΛa : Finite Λa := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card Λa)).2
  haveI : Finite Λa := hFinΛa
  have hcardJ : Nat.card {c : Fin (N - 1) // ggTWInJ N pos c.val} = N - 3 := by
    cases pos
    · exact (Nat.card_congr (l05nS1_xiE N)).symm.trans (Nat.card_fin (N - 3))
    · exact (Nat.card_congr (l05nS1_xiA N)).symm.trans (Nat.card_fin (N - 3))
  have hcardι : Nat.card ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) = N - 1 := by
    rw [Nat.card_sum, hcardJ, hΛa]
    omega
  have hJcox : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      MK (Sum.inl i) (Sum.inl j) = CoxeterMatrix.A (N - 1) i.1 j.1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [MK.diagonal, (CoxeterMatrix.A (N - 1)).diagonal]
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hne : (Sum.inl i : {c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ≠ Sum.inl j :=
        fun h => hij (Sum.inl.inj h)
      have hCij := hJ i j
      have hCji := hJ j i
      rcases hCK.2 (Sum.inl i) (Sum.inl j) hne with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · rw [hm]
        exact (l05nDP4_coxeterA_of_cartanA_zero hij' (by rw [← hCij]; exact h1)).symm
      · rw [hm]
        have hlt : CartanMatrix.A (N - 1) i.1 j.1 < 0 := by rw [← hCij, h1]; norm_num
        rw [l05nDP4_coxeterA_of_cartanA_neg hij' hlt]
      · exfalso
        have hlt1 : CartanMatrix.A (N - 1) i.1 j.1 < 0 := by rw [← hCij]; exact h2
        have hlt2 : CartanMatrix.A (N - 1) j.1 i.1 < 0 := by rw [← hCji]; exact h3
        rw [hCij, l05nDP4_cartanA_neg_eq hlt1, hCji, l05nDP4_cartanA_neg_eq hlt2] at h1
        norm_num at h1
      · exfalso
        have hlt1 : CartanMatrix.A (N - 1) i.1 j.1 < 0 := by rw [← hCij]; exact h2
        have hlt2 : CartanMatrix.A (N - 1) j.1 i.1 < 0 := by rw [← hCji]; exact h3
        rw [hCij, l05nDP4_cartanA_neg_eq hlt1, hCji, l05nDP4_cartanA_neg_eq hlt2] at h1
        norm_num at h1
  rw [GGIsWeylMatrix] at hWK
  rcases hWK with ⟨n, e, -, hcase⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ |
    ⟨e, hMe⟩
  · have hn : n = N - 1 := by
      have h1 := Nat.card_congr e
      rw [Nat.card_fin] at h1
      rw [h1, hcardι]
    subst n
    rcases hcase with hMA | ⟨-, hMB⟩ | ⟨-, hMD⟩
    · exact l05nS1_translate hCK (ggTWExt2Cox_of_all hN5 pos hΛa
        (ggTWExt2All_A (n := N - 1) hNmem) e hMA hJcox a)
    · exact l05nS1_translate hCK (ggTWExt2Cox_of_all hN5 pos hΛa
        (ggTWExt2All_B (n := N - 1) hNmem) e hMB hJcox a)
    · exact l05nS1_translate hCK (ggTWExt2Cox_of_all hN5 pos hΛa
        (ggTWExt2All_D (n := N - 1) hNmem) e hMD hJcox a)
  · have hN7 : N = 7 := by
      have h1 := Nat.card_congr e
      rw [Nat.card_fin, hcardι] at h1
      omega
    subst N
    exact l05nS1_translate hCK (ggTWExt2Cox_of_all (by omega) pos hΛa
      ggTWExt2All_E6 e hMe hJcox a)
  · exfalso
    have h1 := Nat.card_congr e
    rw [Nat.card_fin, hcardι] at h1
    rcases hN with h | h | h | h | h <;> omega
  · have hN9 : N = 9 := by
      have h1 := Nat.card_congr e
      rw [Nat.card_fin, hcardι] at h1
      omega
    subst N
    exact l05nS1_translate hCK (ggTWExt2Cox_of_all (by omega) pos hΛa
      ggTWExt2All_E8 e hMe hJcox a)
  · have hN5' : N = 5 := by
      have h1 := Nat.card_congr e
      rw [Nat.card_fin, hcardι] at h1
      omega
    subst N
    exact l05nS1_translate hCK (ggTWExt2Cox_of_all (by omega) pos hΛa
      ggTWExt2All_F4 e hMe hJcox a)
  · exfalso
    have h1 := Nat.card_congr e
    rw [Nat.card_fin, hcardι] at h1
    rcases hN with h | h | h | h | h <;> omega

end CFSG.StandardType

end
