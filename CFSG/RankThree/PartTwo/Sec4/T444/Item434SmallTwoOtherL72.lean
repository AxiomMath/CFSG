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
open scoped MatrixGroups

namespace L72

noncomputable def t₁ : SL(7, GaloisField 2 1) := blk (show (0 : Fin 7) ≠ 1 by decide)

noncomputable def t₂ : SL(7, GaloisField 2 1) := blk (show (2 : Fin 7) ≠ 3 by decide)

noncomputable def t₃ : SL(7, GaloisField 2 1) := blk (show (4 : Fin 7) ≠ 5 by decide)

noncomputable def z : Fin 3 → SL(7, GaloisField 2 1) := ![t₁, t₂, t₃]

def blockPerm : Equiv.Perm (Fin 7) where
  toFun := ![2, 3, 4, 5, 0, 1, 6]
  invFun := ![4, 5, 0, 1, 2, 3, 6]
  left_inv := by
    intro x
    fin_cases x <;> rfl
  right_inv := by
    intro x
    fin_cases x <;> rfl

noncomputable def tw : SL(7, GaloisField 2 1) := permSL blockPerm

theorem comm₁₂ : Commute t₁ t₂ :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem comm₁₃ : Commute t₁ t₃ :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem comm₂₃ : Commute t₂ t₃ :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem t₁_pow_smul (m : ℕ) {k : Fin 7} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    t₁ ^ m • (Pi.single k 1 : Fin 7 → GaloisField 2 1) = Pi.single k 1 :=
  pow_smul_eq_of_smul_eq (blk_smul_of_ne _ hk0 hk1) m

theorem t₂_pow_smul (m : ℕ) {k : Fin 7} (hk2 : k ≠ 2) (hk3 : k ≠ 3) :
    t₂ ^ m • (Pi.single k 1 : Fin 7 → GaloisField 2 1) = Pi.single k 1 :=
  pow_smul_eq_of_smul_eq (blk_smul_of_ne _ hk2 hk3) m

theorem t₃_pow_smul (m : ℕ) {k : Fin 7} (hk4 : k ≠ 4) (hk5 : k ≠ 5) :
    t₃ ^ m • (Pi.single k 1 : Fin 7 → GaloisField 2 1) = Pi.single k 1 :=
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
    have hfix : ∀ k : Fin 7, (t₁ ^ (v 0).val * t₂ ^ (v 1).val * t₃ ^ (v 2).val) •
        (Pi.single k 1 : Fin 7 → GaloisField 2 1) = Pi.single k 1 := fun k => by
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
    have h2 : t₂ • (Pi.single 0 1 : Fin 7 → GaloisField 2 1) = Pi.single 0 1 :=
      blk_smul_of_ne _ (by decide) (by decide)
    rw [← h1] at h2
    exact blk_smul_fst_ne _ h2

theorem card_SL7 : Nat.card SL(7, GaloisField 2 1) = 163849992929280 := by
  rw [card_SL_gf2 (by norm_num)]
  decide

theorem factorization_card_SL7 : (Nat.card SL(7, GaloisField 2 1)).factorization 3 = 4 := by
  rw [card_SL7, show (163849992929280 : ℕ) = 3 ^ 4 * 2022839418880 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW : Nat.card (wreathW z tw) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts)
  rw [factorization_card_SL7] at hle
  have := le_card_wreathW wreathFacts
  norm_num at hle
  omega

theorem closure_hyperCent_baseA : Subgroup.closure (hyperCent (baseA z)) = ⊤ := by
  have hf := wreathFacts
  have h27 := card_baseA hf
  have R12 := (Item434Kit.isElemAbelian_sup_zpowers hf (show (1 : Fin 3) ≠ 2 by decide)).2
  have R02 := (Item434Kit.isElemAbelian_sup_zpowers hf (show (0 : Fin 3) ≠ 2 by decide)).2
  have R01 := (Item434Kit.isElemAbelian_sup_zpowers hf (show (0 : Fin 3) ≠ 1 by decide)).2
  apply eq_top_of_hub (6 : Fin 7)
  · intro i hi
    apply Subgroup.subset_closure
    fin_cases i
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 1 2) R12
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 1 2) R12
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 2) R02
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 2) R02
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 1) R01
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 1) R01
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact absurd rfl hi
  · intro i hi
    apply Subgroup.subset_closure
    fin_cases i
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 1 2) R12
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 1 2) R12
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 2) R02
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 2) R02
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 1) R01
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact mem_hyperCent_of_commute_sup h27 (sup_zpowers_le_baseA 0 1) R01
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
        (commute_blk_transvection _ hi (by decide) (by decide) (by decide) (by decide) 1).eq
    · exact absurd rfl hi

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem gen_SL7 (h : Ctx434Core G A M Q) (h27 : Nat.card h.layerStar = 27) :
    ∀ P : Subgroup SL(7, GaloisField 2 1), CFSG.Assembly.IsElemAbelian 3 P →
      Nat.card P = Nat.card h.layerStar → Subgroup.closure (hyperCent P) = ⊤ := by
  intro P hP hPc
  rw [h27] at hPc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW z tw)
    (by rw [card_wreathW, factorization_card_SL7]; norm_num) hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom = baseA z :=
    eq_baseA_of_le_wreathW hf card_wreathW (Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hPc])
  have hPeq : P = (baseA z).map (MulAut.conj g).toMonoidHom := by
    rw [← hPg, Item434AltPerm.map_conj_map_conj_inv]
  rw [hPeq]
  exact closure_hyperCent_map_conj closure_hyperCent_baseA g

theorem false_of_L72
    (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 7 (GaloisField 2 1)) : False := by
  have hZ := center_layer_eq_bot_of_projSL_gf2 h (by norm_num) e
  have hf := wreathFacts
  let ψ := slEquivProjSL (n := 7) (by norm_num)
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434Spor.false_of_card_nine h hZ e
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ.toMonoidHom _
        (isElemAbelian_baseA hf))
      (by rw [Subgroup.card_map_of_injective ψ.injective, card_baseA hf]) h9
  · exact false_of_gen h hZ e (not_three_dvd_card_outer_projSL_gf2 (by norm_num))
      (center_projSL_gf2 (by norm_num)) (gen_of_mulEquiv ψ (gen_SL7 h h27))

end Ctx

end L72

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtL72 : Item434SecFor IsSmallTwoOtherL72 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.L72.false_of_L72 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
