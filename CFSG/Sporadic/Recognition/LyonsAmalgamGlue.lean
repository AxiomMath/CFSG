module

public import CFSG.Sporadic.Recognition.LyonsAmalgam
public import CFSG.Sporadic.Recognition.LyonsModel

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th

structure ModelGlue : Type where
  ιY : ↥Ly0.Y0 ≃* ↥Ly1080.Y0
  ιT : ↥Ly0.Tx ≃* ↥Ly243.Tx0
  tx : Fin 4 → ↥Ly0.Tx
  txW : Fin 4 → List ℤ
  txW_range : ∀ i, ∀ l ∈ txW i, l ≠ 0 ∧ l.natAbs ≤ 2
  tx_val : ∀ i, (((tx i : ↥Ly0.Tx) : Ly0.B0) : Perm (Fin Ly0.deg)) = Ly0.wG Ly0.gens0 (txW i)
  ιY_u : ∀ i : ℕ, i < 4 → ∃ h : Ly0.uB i ∈ Ly0.Y0,
    (ιY ⟨Ly0.uB i, h⟩ : Perm (Fin Ly1080.deg)) = Ly1080.ug i
  ιT_tx : ∀ i : Fin 4, (ιT (tx i) : Perm (Fin Ly243.deg)) = Ly243.gg i.val
  K_iff : ∀ b : ↥Ly0.Y0, (b : Ly0.B0) ∈ Ly0.Txy ↔
    (ιY b : Perm (Fin Ly1080.deg)) ∈ Ly1080.Txy0
  agree : ∀ (j : ℕ) (b : Ly0.B0) (hY : b ∈ Ly0.Y0) (hT : b ∈ Ly0.Tx), j < 5 →
    (ιY ⟨b, hY⟩ : Perm (Fin Ly1080.deg)) = Ly1080.txyG j →
      (ιT ⟨b, hT⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG j

section Borel

variable {G : Type} [Group G] {x₁ x₂ x₃ : G}

@[expose] def txEquivSubgroupOf : ↥(TxN x₁ x₂ x₃) ≃*
    ↥((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)) where
  toFun x := ⟨⟨(x : G), x.2.2⟩, x.2.1⟩
  invFun p := ⟨((p : ↥(NormX x₁)) : G), ⟨p.2, (p : ↥(NormX x₁)).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def borelPhiY (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0)
    (ιY : ↥Ly0.Y0 ≃* ↥Ly1080.Y0) : ↥(NN x₁ x₂) ≃* ↥Ly1080.Y0 :=
  (Subgroup.subgroupOfEquivOfLe (inf_le_left : NN x₁ x₂ ≤ NormX x₁)).symm.trans
    ((MulEquiv.subgroupMap φ _).trans ((MulEquiv.subgroupCongr hY).trans ιY))

theorem borelPhiY_apply (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0)
    (ιY : ↥Ly0.Y0 ≃* ↥Ly1080.Y0) (g : G) (hN : g ∈ NN x₁ x₂)
    (hmem : (φ ⟨g, hN.1⟩ : Ly0.B0) ∈ Ly0.Y0) :
    borelPhiY φ hY ιY ⟨g, hN⟩ = ιY ⟨φ ⟨g, hN.1⟩, hmem⟩ := rfl

@[expose] noncomputable def borelPhiT (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hT : ((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Tx)
    (ιT : ↥Ly0.Tx ≃* ↥Ly243.Tx0) : ↥(TxN x₁ x₂ x₃) ≃* ↥Ly243.Tx0 :=
  txEquivSubgroupOf.trans ((MulEquiv.subgroupMap φ _).trans ((MulEquiv.subgroupCongr hT).trans ιT))

theorem borelPhiT_apply (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hT : ((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Tx)
    (ιT : ↥Ly0.Tx ≃* ↥Ly243.Tx0) (g : G) (hX : g ∈ TxN x₁ x₂ x₃)
    (hmem : (φ ⟨g, hX.2⟩ : Ly0.B0) ∈ Ly0.Tx) :
    borelPhiT φ hT ιT ⟨g, hX⟩ = ιT ⟨φ ⟨g, hX.2⟩, hmem⟩ := rfl

theorem mem_KN_iff_borel (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hK : ((NN x₁ x₂ ⊓ normalizer (zpowers x₃ : Set G)).subgroupOf (NormX x₁)).map
      φ.toMonoidHom = Ly0.Txy) (g : G) (hg : g ∈ NormX x₁) :
    g ∈ KN x₁ x₂ x₃ ↔ (φ ⟨g, hg⟩ : Ly0.B0) ∈ Ly0.Txy := by
  have h1 : (⟨g, hg⟩ : ↥(NormX x₁)) ∈
      (NN x₁ x₂ ⊓ normalizer (zpowers x₃ : Set G)).subgroupOf (NormX x₁) ↔ g ∈ KN x₁ x₂ x₃ :=
    Iff.rfl
  rw [← h1, ← hK, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

noncomputable def SmallModelIso.ofBorel (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0)
    (hT : ((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Tx)
    (hK : ((NN x₁ x₂ ⊓ normalizer (zpowers x₃ : Set G)).subgroupOf (NormX x₁)).map
      φ.toMonoidHom = Ly0.Txy) (M : ModelGlue) : SmallModelIso x₁ x₂ x₃ where
  φY := borelPhiY φ hY M.ιY
  φT := borelPhiT φ hT M.ιT
  K_iff y := by
    have hg : (y : G) ∈ NormX x₁ := y.2.1
    have hmem : (φ ⟨(y : G), hg⟩ : Ly0.B0) ∈ Ly0.Y0 := by
      rw [← hY]
      exact Subgroup.mem_map_of_mem _ y.2
    have e : borelPhiY φ hY M.ιY y = M.ιY ⟨φ ⟨(y : G), hg⟩, hmem⟩ := rfl
    rw [mem_KN_iff_borel φ hK (y : G) hg, e]
    exact M.K_iff ⟨φ ⟨(y : G), hg⟩, hmem⟩
  agree j g hN hX hj hg := by
    have hg1 : g ∈ NormX x₁ := hN.1
    have hmemY : (φ ⟨g, hN.1⟩ : Ly0.B0) ∈ Ly0.Y0 := by
      rw [← hY]
      exact Subgroup.mem_map_of_mem _ hN
    have hmemT : (φ ⟨g, hX.2⟩ : Ly0.B0) ∈ Ly0.Tx := by
      rw [← hT]
      exact Subgroup.mem_map_of_mem _ (show (⟨g, hX.2⟩ : ↥(NormX x₁)) ∈
        (normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁) from hX.1)
    rw [borelPhiY_apply φ hY M.ιY g hN hmemY] at hg
    rw [borelPhiT_apply φ hT M.ιT g hX hmemT]
    exact M.agree j (φ ⟨g, hX.2⟩) hmemY hmemT hj hg

end Borel

section Generators

variable {G : Type} [Group G] {x₁ x₂ x₃ : G}

@[expose] noncomputable def borelU (φ : ↥(NormX x₁) ≃* Ly0.B0) (i : ℕ) : G :=
  ((φ.symm (Ly0.uB i) : ↥(NormX x₁)) : G)

@[expose] noncomputable def borelTx (φ : ↥(NormX x₁) ≃* Ly0.B0) (M : ModelGlue) (i : Fin 4) : G :=
  ((φ.symm ((M.tx i : ↥Ly0.Tx) : Ly0.B0) : ↥(NormX x₁)) : G)

theorem borelU_mem (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hφY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0) {i : ℕ}
    (h : Ly0.uB i ∈ Ly0.Y0) : borelU φ i ∈ NN x₁ x₂ := by
  rw [← hφY, Subgroup.mem_map_equiv] at h
  exact h

theorem borelPhiY_borelU (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hφY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0) (M : ModelGlue)
    {i : ℕ} (hi : i < 4) :
    ∃ h : borelU φ i ∈ NN x₁ x₂,
      (borelPhiY φ hφY M.ιY ⟨borelU φ i, h⟩ : Perm (Fin Ly1080.deg)) = Ly1080.ug i := by
  obtain ⟨hmem, e⟩ := M.ιY_u i hi
  refine ⟨borelU_mem φ hφY hmem, ?_⟩
  have h1 : (borelPhiY φ hφY M.ιY ⟨borelU φ i, borelU_mem φ hφY hmem⟩ : ↥Ly1080.Y0) =
      M.ιY ⟨φ ⟨borelU φ i, (borelU_mem φ hφY hmem).1⟩, by simpa [borelU] using hmem⟩ := rfl
  rw [h1]
  have h2 : φ ⟨borelU φ i, (borelU_mem φ hφY hmem).1⟩ = Ly0.uB i := by
    have : (⟨borelU φ i, (borelU_mem φ hφY hmem).1⟩ : ↥(NormX x₁)) = φ.symm (Ly0.uB i) := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have h3 : (⟨φ ⟨borelU φ i, (borelU_mem φ hφY hmem).1⟩, by simpa [borelU] using hmem⟩ :
      ↥Ly0.Y0) = ⟨Ly0.uB i, hmem⟩ := Subtype.ext h2
  rw [h3]
  exact e

theorem borelTx_mem (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hφT : ((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)).map φ.toMonoidHom =
      Ly0.Tx) (M : ModelGlue) (i : Fin 4) : borelTx φ M i ∈ TxN x₁ x₂ x₃ := by
  have h : ((M.tx i : ↥Ly0.Tx) : Ly0.B0) ∈
      ((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)).map φ.toMonoidHom := by
    rw [hφT]
    exact (M.tx i).2
  rw [Subgroup.mem_map_equiv] at h
  exact ⟨h, (φ.symm ((M.tx i : ↥Ly0.Tx) : Ly0.B0)).2⟩

theorem borelPhiT_borelTx (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hφT : ((normalizer (A3 x₁ x₂ x₃ : Set G)).subgroupOf (NormX x₁)).map φ.toMonoidHom =
      Ly0.Tx) (M : ModelGlue) (i : Fin 4) :
    ∃ h : borelTx φ M i ∈ TxN x₁ x₂ x₃,
      (borelPhiT φ hφT M.ιT ⟨borelTx φ M i, h⟩ : Perm (Fin Ly243.deg)) = Ly243.gg i.val := by
  refine ⟨borelTx_mem φ hφT M i, ?_⟩
  have h2 : φ ⟨borelTx φ M i, (borelTx_mem φ hφT M i).2⟩ = ((M.tx i : ↥Ly0.Tx) : Ly0.B0) := by
    have : (⟨borelTx φ M i, (borelTx_mem φ hφT M i).2⟩ : ↥(NormX x₁)) =
        φ.symm ((M.tx i : ↥Ly0.Tx) : Ly0.B0) := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hmem : φ ⟨borelTx φ M i, (borelTx_mem φ hφT M i).2⟩ ∈ Ly0.Tx := by
    rw [h2]
    exact (M.tx i).2
  have h1 : (borelPhiT φ hφT M.ιT ⟨borelTx φ M i, borelTx_mem φ hφT M i⟩ : ↥Ly243.Tx0) =
      M.ιT ⟨φ ⟨borelTx φ M i, (borelTx_mem φ hφT M i).2⟩, hmem⟩ := rfl
  have h3 : (⟨φ ⟨borelTx φ M i, (borelTx_mem φ hφT M i).2⟩, hmem⟩ : ↥Ly0.Tx) = M.tx i :=
    Subtype.ext h2
  rw [h1, h3]
  exact M.ιT_tx i

@[expose] noncomputable def borelCD (φ : ↥(NormX x₁) ≃* Ly0.B0) (k : ℕ) : G :=
  ((φ.symm (if k = 0 then Ly0.cB else Ly0.dB) : ↥(NormX x₁)) : G)

theorem letterG_mem_B0 {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 2) :
    Ly0.letterG Ly0.gens0 l ∈ Ly0.B0 := by
  have := Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem [l] (by simpa using hl)
  simpa using this

theorem borel_letter (φ : ↥(NormX x₁) ≃* Ly0.B0) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 2) :
    ((φ.symm ⟨Ly0.letterG Ly0.gens0 l, letterG_mem_B0 hl⟩ : ↥(NormX x₁)) : G) =
      wordLetter (borelCD φ) l := by
  unfold wordLetter
  by_cases hpos : 0 < l
  · have e1 : (l - 1).toNat = l.toNat - 1 := by omega
    have e : (⟨Ly0.letterG Ly0.gens0 l, letterG_mem_B0 hl⟩ : Ly0.B0) =
        if l.toNat - 1 = 0 then Ly0.cB else Ly0.dB := by
      apply Subtype.ext
      show Ly0.letterG Ly0.gens0 l =
        ((if l.toNat - 1 = 0 then Ly0.cB else Ly0.dB : Ly0.B0) : Perm (Fin Ly0.deg))
      rw [Ly0.letterG_pos _ hpos, e1]
      split_ifs with h0
      · rw [h0, Ly0.gens0_zero]
        rfl
      · have h1 : l.toNat - 1 = 1 := by omega
        rw [h1, Ly0.gens0_one]
        rfl
    rw [e]
    simp only [hpos, ite_true]
    rfl
  · have e1 : (-l - 1).toNat = (-l).toNat - 1 := by omega
    have e : (⟨Ly0.letterG Ly0.gens0 l, letterG_mem_B0 hl⟩ : Ly0.B0) =
        (if (-l).toNat - 1 = 0 then Ly0.cB else Ly0.dB)⁻¹ := by
      apply Subtype.ext
      show Ly0.letterG Ly0.gens0 l =
        (((if (-l).toNat - 1 = 0 then Ly0.cB else Ly0.dB : Ly0.B0)⁻¹ : Ly0.B0) :
          Perm (Fin Ly0.deg))
      rw [Ly0.letterG_neg_of _ hpos, e1]
      split_ifs with h0
      · rw [h0, Ly0.gens0_zero]
        rfl
      · have h1 : (-l).toNat - 1 = 1 := by omega
        rw [h1, Ly0.gens0_one]
        rfl
    rw [e, map_inv]
    simp only [hpos, ite_false]
    rfl

theorem borel_word (φ : ↥(NormX x₁) ≃* Ly0.B0) (w : List ℤ)
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) (hmem : Ly0.wG Ly0.gens0 w ∈ Ly0.B0) :
    ((φ.symm ⟨Ly0.wG Ly0.gens0 w, hmem⟩ : ↥(NormX x₁)) : G) =
      wordG (wordLetter (borelCD φ)) w := by
  induction w with
  | nil =>
    have : (⟨Ly0.wG Ly0.gens0 [], hmem⟩ : Ly0.B0) = 1 := Subtype.ext (by simp)
    rw [this, map_one]
    rfl
  | cons l w ih =>
    have hl := hw l (List.mem_cons_self ..)
    have hw' : ∀ l' ∈ w, l' ≠ 0 ∧ l'.natAbs ≤ 2 := fun l' hl' =>
      hw l' (List.mem_cons_of_mem _ hl')
    have hmem' : Ly0.wG Ly0.gens0 w ∈ Ly0.B0 :=
      Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem w hw'
    have e : (⟨Ly0.wG Ly0.gens0 (l :: w), hmem⟩ : Ly0.B0) =
        ⟨Ly0.letterG Ly0.gens0 l, letterG_mem_B0 hl⟩ * ⟨Ly0.wG Ly0.gens0 w, hmem'⟩ :=
      Subtype.ext (by simp)
    have e2 : wordG (wordLetter (borelCD φ)) (l :: w) =
        wordLetter (borelCD φ) l * wordG (wordLetter (borelCD φ)) w := rfl
    rw [e, map_mul, Subgroup.coe_mul, ih hw' hmem', e2, borel_letter φ hl]

theorem borelU_eq (φ : ↥(NormX x₁) ≃* Ly0.B0) {i : ℕ} (hi : i < 4) :
    borelU φ i = wordG (wordLetter (borelCD φ)) (Ly0.uWords.getD i []) := by
  have hmem : Ly0.wG Ly0.gens0 (Ly0.uWords.getD i []) ∈ Ly0.B0 :=
    Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ (Ly0.uWords_mem i hi)
  have h := borel_word (G := G) φ (Ly0.uWords.getD i []) (Ly0.uWords_mem i hi) hmem
  rw [← h]
  have e : Ly0.uB i = ⟨Ly0.wG Ly0.gens0 (Ly0.uWords.getD i []), hmem⟩ :=
    Subtype.ext (Ly0.uG_def i)
  unfold borelU
  rw [e]

theorem borelTx_eq (φ : ↥(NormX x₁) ≃* Ly0.B0) (M : ModelGlue) (i : Fin 4) :
    borelTx φ M i = wordG (wordLetter (borelCD φ)) (M.txW i) := by
  have hmem : Ly0.wG Ly0.gens0 (M.txW i) ∈ Ly0.B0 := by
    rw [← M.tx_val i]
    exact ((M.tx i : ↥Ly0.Tx) : Ly0.B0).2
  have h := borel_word (G := G) φ (M.txW i) (M.txW_range i) hmem
  rw [← h]
  have e : (((M.tx i : ↥Ly0.Tx) : Ly0.B0)) = ⟨Ly0.wG Ly0.gens0 (M.txW i), hmem⟩ :=
    Subtype.ext (M.tx_val i)
  unfold borelTx
  rw [e]

end Generators

section Stages

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.exists_swap_and_mulEquiv_Tr0_of_borel (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) (M : ModelGlue) :
    ∃ k : G, ∃ hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k,
      ∃ ψ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) ≃* ↥Ly243.Tr0,
        (∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
          (ψ ⟨(x : G), x.2.1⟩ : Perm (Fin Ly243.deg)) =
            (borelPhiT φ hφT M.ιT x : Perm (Fin Ly243.deg))) ∧
        (ψ ⟨k, hk.mem_TrN⟩ : Perm (Fin Ly243.deg)) = Ly243.k0 :=
  D.exists_swap_and_mulEquiv_Tr0 S hY hT hτ (SmallModelIso.ofBorel φ hφY hφT hφK M)

end Stages

section Relators

theorem borel_erelators {G : Type} [Group G] {x₁ x₂ x₃ : G} {φ : ↥(NormX x₁) ≃* Ly0.B0}
    {hφY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0} {M : ModelGlue}
    {k : G} (hk : IsSwapY0 x₁ x₂ x₃ (borelPhiY φ hφY M.ιY) k) (hY : Ly1080.YOK)
    {i : ℕ} (hi : i < 4) :
    k * borelU φ i * k⁻¹ = wordG (wordLetter (borelU φ)) Ly1080.erelWords[i]! :=
  hk.erelators hY (borelU φ) (fun _ hj => borelPhiY_borelU φ hφY M hj) hi

theorem LyData.lift_eq_one_of_tr_borel {G : Type} [Group G] [Finite G] {t : G}
    {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))} (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) (M : ModelGlue) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k)
    (r : FreeGroup (Fin 5)) (hr : FreeGroup.lift (fun i : Fin 5 => Ly243.gg i.val) r = 1) :
    FreeGroup.lift (fun i : Fin 5 =>
      if h : i.val < 4 then borelTx φ M ⟨i.val, h⟩ else k) r = 1 := by
  refine D.lift_eq_one_of_tr S hY hT hτ (SmallModelIso.ofBorel φ hφY hφT hφK M) hk
    (fun i : Fin 5 => if h : i.val < 4 then borelTx φ M ⟨i.val, h⟩ else k) ?_ ?_ r hr
  · intro i hi
    have e : (if h : i.val < 4 then borelTx φ M ⟨i.val, h⟩ else k) =
        borelTx φ M ⟨i.val, hi⟩ := by simp only [hi, ↓reduceDIte]
    obtain ⟨hX, e'⟩ := borelPhiT_borelTx φ hφT M ⟨i.val, hi⟩
    refine ⟨by rw [e]; exact hX, ?_⟩
    have e2 : (⟨(if h : i.val < 4 then borelTx φ M ⟨i.val, h⟩ else k), by rw [e]; exact hX⟩ :
        ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G))) = ⟨borelTx φ M ⟨i.val, hi⟩, hX⟩ := Subtype.ext e
    show (borelPhiT φ hφT M.ιT ⟨(if h : i.val < 4 then borelTx φ M ⟨i.val, h⟩ else k),
      by rw [e]; exact hX⟩ : Perm (Fin Ly243.deg)) = Ly243.gg i.val
    rw [e2]
    exact e'
  · show (if h : (4 : Fin 5).val < 4 then borelTx φ M ⟨(4 : Fin 5).val, h⟩ else k) = k
    simp

end Relators

end CFSG.Sporadic.Recognition.LyonsSims
