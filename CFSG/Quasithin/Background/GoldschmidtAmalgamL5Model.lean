module

public import CFSG.Quasithin.Recognition.M12AmalClass
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Rel

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.M12Amal CFSG.Sporadic.Bridge CFSG.Quasithin Equiv

@[expose] def newCodes : List (List ℕ) :=
  [[0, 0, 2], [0, 3, 0], [2, 1, 2, 4], [0, 2, 1, 3, 4], [8], [0, 4, 6, 1]]

@[expose] def backCodes : List (List ℕ) :=
  [[0, 0, 4, 6], [1, 2, 2], [0, 2, 6], [10, 0, 3], [8]]

@[expose] def genN (k : ℕ) : M12G := wordProd genG (decode (newCodes.getD k []))

@[expose] def permN (k : ℕ) : Perm (Fin 12) := wordProd genP (decode (newCodes.getD k []))

theorem newLetters : ∀ k < 6, ∀ l ∈ decode (newCodes.getD k []), l.1 < 5 := by decide +kernel

theorem newLettersT : ∀ k < 4, ∀ l ∈ decode (newCodes.getD k []), l.1 < 3 := by decide +kernel

theorem newLettersA : ∀ l ∈ decode (newCodes.getD 5 []), l.1 < 4 := by decide +kernel

theorem backLetters : ∀ k < 5, ∀ l ∈ decode (backCodes.getD k []), l.1 < 6 := by decide +kernel

theorem backLettersT : ∀ k < 3, ∀ l ∈ decode (backCodes.getD k []), l.1 < 4 := by decide +kernel

theorem backLettersA : ∀ l ∈ decode (backCodes.getD 3 []), l.1 < 4 ∨ l.1 = 5 := by decide +kernel

theorem genN_coe (k : ℕ) (hk : k < 6) : ((genN k : M12G) : Perm (Fin 12)) = permN k :=
  wordProd_genG_coe _ (newLetters k hk)

theorem back_perm : ∀ k < 5, genP k = wordProd permN (decode (backCodes.getD k [])) := by
  decide +kernel

theorem genG_back (k : ℕ) (hk : k < 5) :
    genG k = wordProd genN (decode (backCodes.getD k [])) := by
  apply Subtype.ext
  rw [coe_wordProd, genG_coe k hk, back_perm k hk]
  exact wordProd_congr _ (fun l hl => (genN_coe l.1 (backLetters k hk l hl)).symm)

theorem perm_TRel : TRel (permN 0) (permN 1) (permN 2) where
  ha := by decide +kernel
  hb := by decide +kernel
  hs := by decide +kernel
  hab := by decide +kernel
  hsa := by decide +kernel
  hsb := by decide +kernel

theorem perm_RhoRel : RhoRel (permN 0) (permN 1) (permN 2) (permN 3) where
  hρ := by decide +kernel
  hρa := by decide +kernel
  hρb := by decide +kernel
  hρs := by decide +kernel

theorem perm_ARel : ARel (permN 0) (permN 1) (permN 2) (permN 4) where
  toTRel := perm_TRel
  hx := by decide +kernel
  hxa := by decide +kernel
  hxb := by decide +kernel
  hxs := by decide +kernel

theorem perm_ARho : ARho (permN 0) (permN 1) (permN 2) (permN 4) (permN 3) where
  toRhoRel := perm_RhoRel
  hρx := by decide +kernel

theorem perm_MRelB : MRelB (permN 0) (permN 1) (permN 2) (permN 3) (permN 5) where
  hy := by decide +kernel
  hyc := by decide +kernel
  hyp := by decide +kernel
  hyq := by decide +kernel
  hyr := by decide +kernel
  hyt := by decide +kernel

section Transfer

variable {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)

include hφ

theorem tRel_of_inj {a b s : G} (h : TRel (φ a) (φ b) (φ s)) : TRel a b s where
  ha := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.ha)
  hb := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hb)
  hs := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hs)
  hab := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hab)
  hsa := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hsa)
  hsb := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hsb)

theorem rhoRel_of_inj {a b s ρ : G} (h : RhoRel (φ a) (φ b) (φ s) (φ ρ)) : RhoRel a b s ρ where
  hρ := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hρ)
  hρa := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hρa)
  hρb := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hρb)
  hρs := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hρs)

theorem aRel_of_inj {a b s x : G} (h : ARel (φ a) (φ b) (φ s) (φ x)) : ARel a b s x where
  toTRel := tRel_of_inj φ hφ h.toTRel
  hx := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hx)
  hxa := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hxa)
  hxb := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hxb)
  hxs := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hxs)

theorem aRho_of_inj {a b s x ρ : G} (h : ARho (φ a) (φ b) (φ s) (φ x) (φ ρ)) :
    ARho a b s x ρ where
  toRhoRel := rhoRel_of_inj φ hφ h.toRhoRel
  hρx := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hρx)

theorem mRelB_of_inj {a b s ρ y : G} (h : MRelB (φ a) (φ b) (φ s) (φ ρ) (φ y)) :
    MRelB a b s ρ y where
  hy := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hy)
  hyc := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hyc)
  hyp := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hyp)
  hyq := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hyq)
  hyr := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hyr)
  hyt := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hyt)

end Transfer

theorem subtype_genN (k : ℕ) (hk : k < 6) :
    (CFSG.Open.quasithinM12).subtype (genN k) = permN k := genN_coe k hk

theorem model_ARel : ARel (genN 0) (genN 1) (genN 2) (genN 4) := by
  refine aRel_of_inj (CFSG.Open.quasithinM12).subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genN 0 (by norm_num), subtype_genN 1 (by norm_num), subtype_genN 2 (by norm_num),
    subtype_genN 4 (by norm_num)]
  exact perm_ARel

theorem model_ARho : ARho (genN 0) (genN 1) (genN 2) (genN 4) (genN 3) := by
  refine aRho_of_inj (CFSG.Open.quasithinM12).subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genN 0 (by norm_num), subtype_genN 1 (by norm_num), subtype_genN 2 (by norm_num),
    subtype_genN 4 (by norm_num), subtype_genN 3 (by norm_num)]
  exact perm_ARho

theorem model_MRelB : MRelB (genN 0) (genN 1) (genN 2) (genN 3) (genN 5) := by
  refine mRelB_of_inj (CFSG.Open.quasithinM12).subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genN 0 (by norm_num), subtype_genN 1 (by norm_num), subtype_genN 2 (by norm_num),
    subtype_genN 3 (by norm_num), subtype_genN 5 (by norm_num)]
  exact perm_MRelB

theorem m12_T_eq : m12Data.T = Subgroup.closure ({genG 0, genG 1, genG 2} : Set M12G) := rfl
theorem m12_A_eq : m12Data.A = Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set M12G) := rfl
theorem m12_B_eq : m12Data.B = Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set M12G) := rfl

theorem genN_mem_T (k : ℕ) (hk : k < 4) : genN k ∈ m12Data.T := by
  unfold genN
  refine wordProd_mem_letters (P := fun i => i < 3) (fun i hi => ?_) (newLettersT k hk)
  show genG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2} : Set M12G)
  apply Subgroup.subset_closure
  interval_cases i <;> simp

theorem genN_five_mem_A : genN 5 ∈ m12Data.A := by
  unfold genN
  refine wordProd_mem_letters (P := fun i => i < 4) (fun i hi => ?_) newLettersA
  show genG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set M12G)
  apply Subgroup.subset_closure
  interval_cases i <;> simp

theorem genN_four_eq : genN 4 = genG 4 := by
  unfold genN
  simp [newCodes, decode, wordProd]

theorem genG_mem_T (k : ℕ) (hk : k < 3) :
    genG k ∈ Subgroup.closure ({genN 0, genN 1, genN 2, genN 3} : Set M12G) := by
  rw [genG_back k (by omega)]
  refine wordProd_mem_letters (P := fun i => i < 4) (fun i hi => ?_)
    (backLettersT k hk)
  apply Subgroup.subset_closure
  interval_cases i <;> simp

theorem closure_T5 :
    Subgroup.closure ({genN 0, genN 1, genN 2, genN 3} : Set M12G) = m12Data.T := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact genN_mem_T 0 (by norm_num)
    · exact genN_mem_T 1 (by norm_num)
    · exact genN_mem_T 2 (by norm_num)
    · exact genN_mem_T 3 (by norm_num)
  · rw [m12_T_eq]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact genG_mem_T 0 (by norm_num)
    · exact genG_mem_T 1 (by norm_num)
    · exact genG_mem_T 2 (by norm_num)

theorem closure_A5 :
    Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 5} : Set M12G) = m12Data.A := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hTA : m12Data.T ≤ m12Data.A := by
      rw [m12_T_eq, m12_A_eq, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hTA (genN_mem_T 0 (by norm_num))
    · exact hTA (genN_mem_T 1 (by norm_num))
    · exact hTA (genN_mem_T 2 (by norm_num))
    · exact hTA (genN_mem_T 3 (by norm_num))
    · exact genN_five_mem_A
  · rw [m12_A_eq]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hTle : Subgroup.closure ({genN 0, genN 1, genN 2, genN 3} : Set M12G) ≤
        Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 5} : Set M12G) := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    rcases hg with rfl | rfl | rfl | rfl
    · exact hTle (genG_mem_T 0 (by norm_num))
    · exact hTle (genG_mem_T 1 (by norm_num))
    · exact hTle (genG_mem_T 2 (by norm_num))
    · rw [genG_back 3 (by norm_num)]
      refine wordProd_mem_letters (P := fun i => i < 4 ∨ i = 5) (fun i hi => ?_) backLettersA
      apply Subgroup.subset_closure
      rcases hi with hi | rfl
      · interval_cases i <;> simp
      · simp

theorem closure_B5 :
    Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 4} : Set M12G) = m12Data.B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hTB : m12Data.T ≤ m12Data.B := by
      rw [m12_T_eq, m12_B_eq, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hTB (genN_mem_T 0 (by norm_num))
    · exact hTB (genN_mem_T 1 (by norm_num))
    · exact hTB (genN_mem_T 2 (by norm_num))
    · exact hTB (genN_mem_T 3 (by norm_num))
    · rw [genN_four_eq, m12_B_eq]
      exact Subgroup.subset_closure (by simp)
  · rw [m12_B_eq]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hTle : Subgroup.closure ({genN 0, genN 1, genN 2, genN 3} : Set M12G) ≤
        Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 4} : Set M12G) := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    rcases hg with rfl | rfl | rfl | rfl
    · exact hTle (genG_mem_T 0 (by norm_num))
    · exact hTle (genG_mem_T 1 (by norm_num))
    · exact hTle (genG_mem_T 2 (by norm_num))
    · rw [← genN_four_eq]
      exact Subgroup.subset_closure (by simp)

theorem model_card_T :
    Nat.card (Subgroup.closure ({genN 0, genN 1, genN 2, genN 3} : Set M12G)) = 64 := by
  rw [closure_T5]
  exact m12_card_T

theorem model_inf :
    Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 5} : Set M12G) ⊓
      Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 4} : Set M12G) =
      Subgroup.closure ({genN 0, genN 1, genN 2, genN 3} : Set M12G) := by
  rw [closure_A5, closure_B5, closure_T5]
  exact m12Data.inf_AB

theorem m12_isTwoLocalAmalgam : IsTwoLocalAmalgam m12Data.A m12Data.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨m12Extra.isMaximalTwoLocal_A, m12Extra.isMaximalTwoLocal_B, ?_, ?_⟩
  · intro h
    apply m12Data.T_ne_A
    rw [← m12Data.inf_AB, ← h]
    exact inf_idem _
  · refine ⟨m12_syl.1.toSylow m12_syl.2, ?_⟩
    show m12Data.T = m12Data.A ⊓ m12Data.B
    exact m12Data.inf_AB.symm

theorem isM12_M12G : IsM12 M12G :=
  ⟨(MulEquiv.subgroupCongr nativeM12_eq_quasithinM12.symm).symm⟩

theorem isYAmalgam_M12_of_iso {D : Type*} [Group D] {H₁ H₂ : Subgroup D}
    (h : IsAmalgamIso H₁ H₂
      (Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 5} : Set M12G))
      (Subgroup.closure ({genN 0, genN 1, genN 2, genN 3, genN 4} : Set M12G))) :
    IsYAmalgam IsM12 H₁ H₂ := by
  refine ⟨M12G, inferInstance, inferInstance, _, _, isM12_M12G, ?_, h⟩
  rw [closure_A5, closure_B5]
  exact m12_isTwoLocalAmalgam

end CFSG.Quasithin.F6.GoldAmL5
