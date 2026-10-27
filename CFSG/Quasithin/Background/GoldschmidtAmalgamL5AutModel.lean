module

public import CFSG.Quasithin.Recognition.M12AmalAutFeit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutRel
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Model
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Main

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.M12AmalAut CFSG.Sporadic.Bridge CFSG.Quasithin Equiv

@[expose] def autNewCodes : List (List ℕ) :=
  [[3, 4, 3], [0, 2, 2, 4, 0], [2, 0, 3, 4, 3], [0, 3, 0, 2], [2, 9, 3, 8], [3, 6, 2],
    [0, 3, 4, 3, 4]]

@[expose] def autBackCodes : List (List ℕ) :=
  [[0, 0, 6, 12], [2, 12, 4], [0, 6], [6, 10], [0, 9, 3]]

@[expose] def genNA (k : ℕ) : AutG := wordProd genG (decode (autNewCodes.getD k []))

@[expose] def permNA (k : ℕ) : Perm (Fin 24) := wordProd genP (decode (autNewCodes.getD k []))

theorem autNewLetters : ∀ k < 7, ∀ l ∈ decode (autNewCodes.getD k []), l.1 < 5 := by
  decide +kernel

theorem autNewLettersT : ∀ k < 7, k ≠ 4 → k ≠ 5 → ∀ l ∈ decode (autNewCodes.getD k []),
    l.1 < 3 := by decide +kernel

theorem autNewLettersX : ∀ l ∈ decode (autNewCodes.getD 4 []), l.1 < 3 ∨ l.1 = 4 := by
  decide +kernel

theorem autNewLettersY : ∀ l ∈ decode (autNewCodes.getD 5 []), l.1 < 4 := by decide +kernel

theorem autBackLetters : ∀ k < 5, ∀ l ∈ decode (autBackCodes.getD k []), l.1 < 7 := by
  decide +kernel

theorem autBackLettersT : ∀ k < 3, ∀ l ∈ decode (autBackCodes.getD k []),
    l.1 < 4 ∨ l.1 = 6 := by decide +kernel

theorem autBackLettersA : ∀ l ∈ decode (autBackCodes.getD 3 []),
    l.1 < 4 ∨ l.1 = 5 ∨ l.1 = 6 := by decide +kernel

theorem autBackLettersB : ∀ l ∈ decode (autBackCodes.getD 4 []),
    l.1 < 5 ∨ l.1 = 6 := by decide +kernel

theorem genNA_coe (k : ℕ) (hk : k < 7) : ((genNA k : AutG) : Perm (Fin 24)) = permNA k :=
  wordProd_genG_coe _ (autNewLetters k hk)

theorem autBack_perm : ∀ k < 5, genP k = wordProd permNA (decode (autBackCodes.getD k [])) := by
  decide +kernel

theorem genG_backA (k : ℕ) (hk : k < 5) :
    genG k = wordProd genNA (decode (autBackCodes.getD k [])) := by
  apply Subtype.ext
  rw [coe_wordProd, genG_coe k hk, autBack_perm k hk]
  exact wordProd_congr _ (fun l hl => (genNA_coe l.1 (autBackLetters k hk l hl)).symm)

theorem permA_TRel : TRel (permNA 0) (permNA 1) (permNA 2) where
  ha := by decide +kernel
  hb := by decide +kernel
  hs := by decide +kernel
  hab := by decide +kernel
  hsa := by decide +kernel
  hsb := by decide +kernel

theorem permA_RhoRel : RhoRel (permNA 0) (permNA 1) (permNA 2) (permNA 3) where
  hρ := by decide +kernel
  hρa := by decide +kernel
  hρb := by decide +kernel
  hρs := by decide +kernel

theorem permA_ARel : ARel (permNA 0) (permNA 1) (permNA 2) (permNA 4) where
  toTRel := permA_TRel
  hx := by decide +kernel
  hxa := by decide +kernel
  hxb := by decide +kernel
  hxs := by decide +kernel

theorem permA_ARho : ARho (permNA 0) (permNA 1) (permNA 2) (permNA 4) (permNA 3) where
  toRhoRel := permA_RhoRel
  hρx := by decide +kernel

theorem permA_MRelB : MRelB (permNA 0) (permNA 1) (permNA 2) (permNA 3) (permNA 5) where
  hy := by decide +kernel
  hyc := by decide +kernel
  hyp := by decide +kernel
  hyq := by decide +kernel
  hyr := by decide +kernel
  hyt := by decide +kernel

theorem permA_TauRel : TauRel (permNA 0) (permNA 1) (permNA 2) (permNA 3) (permNA 4) (permNA 5)
    (permNA 6) where
  hτ := by decide +kernel
  hτa := by decide +kernel
  hτb := by decide +kernel
  hτs := by decide +kernel
  hτρ := by decide +kernel
  hτx := by decide +kernel
  hτy := by decide +kernel

theorem tauRel_of_inj {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {a b s ρ x y τ : G}
    (h : TauRel (φ a) (φ b) (φ s) (φ ρ) (φ x) (φ y) (φ τ)) : TauRel a b s ρ x y τ where
  hτ := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτ)
  hτa := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτa)
  hτb := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτb)
  hτs := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτs)
  hτρ := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτρ)
  hτx := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτx)
  hτy := hφ (by simpa only [map_mul, map_inv, map_pow, map_one] using h.hτy)

theorem subtype_genNA (k : ℕ) (hk : k < 7) : autM12Model.subtype (genNA k) = permNA k :=
  genNA_coe k hk

theorem aut_ARel : ARel (genNA 0) (genNA 1) (genNA 2) (genNA 4) := by
  refine aRel_of_inj autM12Model.subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genNA 0 (by norm_num), subtype_genNA 1 (by norm_num),
    subtype_genNA 2 (by norm_num), subtype_genNA 4 (by norm_num)]
  exact permA_ARel

theorem aut_ARho : ARho (genNA 0) (genNA 1) (genNA 2) (genNA 4) (genNA 3) := by
  refine aRho_of_inj autM12Model.subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genNA 0 (by norm_num), subtype_genNA 1 (by norm_num),
    subtype_genNA 2 (by norm_num), subtype_genNA 4 (by norm_num),
    subtype_genNA 3 (by norm_num)]
  exact permA_ARho

theorem aut_MRelB : MRelB (genNA 0) (genNA 1) (genNA 2) (genNA 3) (genNA 5) := by
  refine mRelB_of_inj autM12Model.subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genNA 0 (by norm_num), subtype_genNA 1 (by norm_num),
    subtype_genNA 2 (by norm_num), subtype_genNA 3 (by norm_num),
    subtype_genNA 5 (by norm_num)]
  exact permA_MRelB

theorem aut_TauRel : TauRel (genNA 0) (genNA 1) (genNA 2) (genNA 3) (genNA 4) (genNA 5)
    (genNA 6) := by
  refine tauRel_of_inj autM12Model.subtype (Subgroup.subtype_injective _) ?_
  rw [subtype_genNA 0 (by norm_num), subtype_genNA 1 (by norm_num),
    subtype_genNA 2 (by norm_num), subtype_genNA 3 (by norm_num),
    subtype_genNA 4 (by norm_num), subtype_genNA 5 (by norm_num),
    subtype_genNA 6 (by norm_num)]
  exact permA_TauRel

theorem aut_T_eq : autData.T = Subgroup.closure ({genG 0, genG 1, genG 2} : Set AutG) := rfl
theorem aut_A_eq :
    autData.A = Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set AutG) := rfl
theorem aut_B_eq :
    autData.B = Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set AutG) := rfl

theorem genNA_mem_T (k : ℕ) (hk : k < 7) (h4 : k ≠ 4) (h5 : k ≠ 5) : genNA k ∈ autData.T := by
  unfold genNA
  refine wordProd_mem_letters (P := fun i => i < 3) (fun i hi => ?_) (autNewLettersT k hk h4 h5)
  show genG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2} : Set AutG)
  apply Subgroup.subset_closure
  interval_cases i <;> simp

theorem genNA_four_mem_B : genNA 4 ∈ autData.B := by
  unfold genNA
  refine wordProd_mem_letters (P := fun i => i < 3 ∨ i = 4) (fun i hi => ?_) autNewLettersX
  show genG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set AutG)
  apply Subgroup.subset_closure
  rcases hi with hi | rfl
  · interval_cases i <;> simp
  · simp

theorem genNA_five_mem_A : genNA 5 ∈ autData.A := by
  unfold genNA
  refine wordProd_mem_letters (P := fun i => i < 4) (fun i hi => ?_) autNewLettersY
  show genG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set AutG)
  apply Subgroup.subset_closure
  interval_cases i <;> simp

theorem genG_mem_closure_T (k : ℕ) (hk : k < 3) :
    genG k ∈ Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 6} : Set AutG) := by
  rw [genG_backA k (by omega)]
  refine wordProd_mem_letters (P := fun i => i < 4 ∨ i = 6) (fun i hi => ?_)
    (autBackLettersT k hk)
  apply Subgroup.subset_closure
  rcases hi with hi | rfl
  · interval_cases i <;> simp
  · simp

theorem closure_T_aut :
    Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 6} : Set AutG) = autData.T := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact genNA_mem_T 0 (by norm_num) (by norm_num) (by norm_num)
    · exact genNA_mem_T 1 (by norm_num) (by norm_num) (by norm_num)
    · exact genNA_mem_T 2 (by norm_num) (by norm_num) (by norm_num)
    · exact genNA_mem_T 3 (by norm_num) (by norm_num) (by norm_num)
    · exact genNA_mem_T 6 (by norm_num) (by norm_num) (by norm_num)
  · rw [aut_T_eq, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact genG_mem_closure_T 0 (by norm_num)
    · exact genG_mem_closure_T 1 (by norm_num)
    · exact genG_mem_closure_T 2 (by norm_num)

theorem closure_A_aut :
    Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 5, genNA 6} : Set AutG) =
      autData.A := by
  have hTA : autData.T ≤ autData.A := by
    rw [aut_T_eq, aut_A_eq, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hTA (genNA_mem_T 0 (by norm_num) (by norm_num) (by norm_num))
    · exact hTA (genNA_mem_T 1 (by norm_num) (by norm_num) (by norm_num))
    · exact hTA (genNA_mem_T 2 (by norm_num) (by norm_num) (by norm_num))
    · exact hTA (genNA_mem_T 3 (by norm_num) (by norm_num) (by norm_num))
    · exact genNA_five_mem_A
    · exact hTA (genNA_mem_T 6 (by norm_num) (by norm_num) (by norm_num))
  · rw [aut_A_eq, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hTle : Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 6} : Set AutG) ≤
        Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 5, genNA 6} : Set AutG) := by
      apply Subgroup.closure_mono
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp
    rcases hg with rfl | rfl | rfl | rfl
    · exact hTle (genG_mem_closure_T 0 (by norm_num))
    · exact hTle (genG_mem_closure_T 1 (by norm_num))
    · exact hTle (genG_mem_closure_T 2 (by norm_num))
    · rw [genG_backA 3 (by norm_num)]
      refine wordProd_mem_letters (P := fun i => i < 4 ∨ i = 5 ∨ i = 6) (fun i hi => ?_)
        autBackLettersA
      apply Subgroup.subset_closure
      rcases hi with hi | rfl | rfl
      · interval_cases i <;> simp
      · simp
      · simp

theorem closure_B_aut :
    Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 4, genNA 6} : Set AutG) =
      autData.B := by
  have hTB : autData.T ≤ autData.B := by
    rw [aut_T_eq, aut_B_eq, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hTB (genNA_mem_T 0 (by norm_num) (by norm_num) (by norm_num))
    · exact hTB (genNA_mem_T 1 (by norm_num) (by norm_num) (by norm_num))
    · exact hTB (genNA_mem_T 2 (by norm_num) (by norm_num) (by norm_num))
    · exact hTB (genNA_mem_T 3 (by norm_num) (by norm_num) (by norm_num))
    · exact genNA_four_mem_B
    · exact hTB (genNA_mem_T 6 (by norm_num) (by norm_num) (by norm_num))
  · rw [aut_B_eq, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hTle : Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 6} : Set AutG) ≤
        Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 4, genNA 6} : Set AutG) := by
      apply Subgroup.closure_mono
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp
    rcases hg with rfl | rfl | rfl | rfl
    · exact hTle (genG_mem_closure_T 0 (by norm_num))
    · exact hTle (genG_mem_closure_T 1 (by norm_num))
    · exact hTle (genG_mem_closure_T 2 (by norm_num))
    · rw [genG_backA 4 (by norm_num)]
      refine wordProd_mem_letters (P := fun i => i < 5 ∨ i = 6) (fun i hi => ?_)
        autBackLettersB
      apply Subgroup.subset_closure
      rcases hi with hi | rfl
      · interval_cases i <;> simp
      · simp

@[expose] def blockSub : Subgroup (Perm (Fin 24)) where
  carrier := {g | ∀ i : Fin 24, (g i).val < 12 ↔ i.val < 12}
  mul_mem' := fun {g h} hg hh i => by
    show ((g * h) i).val < 12 ↔ i.val < 12
    rw [Equiv.Perm.mul_apply]
    exact (hg (h i)).trans (hh i)
  one_mem' := fun i => Iff.rfl
  inv_mem' := fun {g} hg i => by
    simpa using (hg (g⁻¹ i)).symm

theorem permNA_block : ∀ k < 6, ∀ i : Fin 24, ((permNA k) i).val < 12 ↔ i.val < 12 := by
  decide +kernel

theorem permNA_six_not_block : ¬ ∀ i : Fin 24, ((permNA 6) i).val < 12 ↔ i.val < 12 := by
  decide +kernel

@[expose] def blockG : Subgroup AutG := blockSub.comap autM12Model.subtype

theorem genNA_mem_blockG (k : ℕ) (hk : k < 6) : genNA k ∈ blockG := by
  show autM12Model.subtype (genNA k) ∈ blockSub
  rw [subtype_genNA k (by omega)]
  exact permNA_block k hk

theorem genNA_six_not_mem_blockG : genNA 6 ∉ blockG := by
  intro h
  have : autM12Model.subtype (genNA 6) ∈ blockSub := h
  rw [subtype_genNA 6 (by norm_num)] at this
  exact permNA_six_not_block this

theorem tau_not_mem_closure_y :
    genNA 6 ∉ Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 5} : Set AutG) := by
  intro h
  apply genNA_six_not_mem_blockG
  refine (Subgroup.closure_le _).mpr (fun g hg => ?_) h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact genNA_mem_blockG _ (by norm_num)

theorem tau_not_mem_closure_x :
    genNA 6 ∉ Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 4} : Set AutG) := by
  intro h
  apply genNA_six_not_mem_blockG
  refine (Subgroup.closure_le _).mpr (fun g hg => ?_) h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact genNA_mem_blockG _ (by norm_num)

theorem tau_not_mem_closure_T' :
    genNA 6 ∉ Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3} : Set AutG) := by
  intro h
  apply genNA_six_not_mem_blockG
  refine (Subgroup.closure_le _).mpr (fun g hg => ?_) h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact genNA_mem_blockG _ (by norm_num)

theorem relIndex_twoExt {D : Type*} [Group D] {A : Subgroup D} {ρ : D} (hρ : ρ * ρ = 1)
    (hn : ∀ g ∈ A, ρ * g * ρ ∈ A) (hρA : ρ ∉ A) :
    A.relIndex (twoExt A ρ hρ hn) = 2 := by
  show (A.subgroupOf (twoExt A ρ hρ hn)).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨ρ, Or.inr (by rw [hρ]; exact A.one_mem)⟩, ?_⟩
  rintro ⟨b, hb⟩
  have hbA : (b ∈ A) ∨ (b * ρ ∈ A) := hb
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases h1 : b ∈ A
  · right
    refine ⟨h1, fun h2 => hρA ?_⟩
    have := A.mul_mem (A.inv_mem h1) h2
    simpa using this
  · left
    refine ⟨?_, h1⟩
    rcases hbA with h | h
    · exact absurd h h1
    · exact h

theorem card_closure_T' :
    Nat.card ↥(Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3} : Set AutG)) = 64 := by
  have hτ := aut_TauRel
  set A : Subgroup AutG := Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3} : Set AutG)
    with hAdef
  have hmem : ∀ k, k < 4 → genNA k ∈ A := fun k hk =>
    Subgroup.subset_closure (by interval_cases k <;> simp)
  have hn : ∀ g ∈ A, genNA 6 * g * genNA 6 ∈ A := by
    refine normalizes_of_gens hAdef hτ.hτ ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [hτ.hτa]
      exact A.mul_mem (A.mul_mem (A.inv_mem (hmem 0 (by norm_num))) (hmem 1 (by norm_num)))
        (hmem 1 (by norm_num))
    · rw [hτ.hτb]
      exact A.mul_mem (A.mul_mem (hmem 0 (by norm_num)) (hmem 0 (by norm_num)))
        (hmem 1 (by norm_num))
    · rw [hτ.hτs]
      exact A.mul_mem (hmem 2 (by norm_num)) (hmem 3 (by norm_num))
    · rw [hτ.hτρ]
      exact hmem 3 (by norm_num)
  have hτA : genNA 6 ∉ A := tau_not_mem_closure_T'
  have hT : autData.T = twoExt A (genNA 6) hτ.hτ hn := by
    rw [← closure_T_aut, ← closure_union_eq hτ.hτ hn, hAdef, ← closure_union_closure]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
  have hle : A ≤ autData.T := by
    rw [hT]
    exact fun g hg => Or.inl hg
  have hidx : A.relIndex autData.T = 2 := by
    rw [hT]
    exact relIndex_twoExt hτ.hτ hn hτA
  have := card_eq_of_relIndex_two hle hidx
  rw [aut_card_T] at this
  omega

theorem aut_isTwoLocalAmalgam : IsTwoLocalAmalgam autData.A autData.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨autExtra.isMaximalTwoLocal_A, autExtra.isMaximalTwoLocal_B, ?_, ?_⟩
  · intro h
    apply autData.T_ne_A
    rw [← autData.inf_AB, ← h]
    exact inf_idem _
  · refine ⟨aut_syl.1.toSylow aut_syl.2, ?_⟩
    show autData.T = autData.A ⊓ autData.B
    exact autData.inf_AB.symm

theorem isAutM12_AutG :
    IsAutM12 AutG :=
  autM12PermModel

theorem isYAmalgam_Aut_of_iso
    {D : Type*} [Group D] {H₁ H₂ : Subgroup D}
    (h : IsAmalgamIso H₁ H₂
      (Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 5, genNA 6} : Set AutG))
      (Subgroup.closure ({genNA 0, genNA 1, genNA 2, genNA 3, genNA 4, genNA 6} : Set AutG))) :
    IsYAmalgam IsAutM12 H₁ H₂ := by
  refine ⟨AutG, inferInstance, inferInstance, _, _, isAutM12_AutG, ?_, h⟩
  rw [closure_A_aut, closure_B_aut]
  exact aut_isTwoLocalAmalgam

end CFSG.Quasithin.F6.GoldAmL5
