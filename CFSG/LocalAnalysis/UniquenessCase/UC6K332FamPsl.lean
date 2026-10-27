module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathSub
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslBlock
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

theorem orderOf_natCast_mod_three_of_two {q : ℕ} (hq : q % 3 = 2) :
    orderOf ((q : ℕ) : ZMod 3) = 2 := by
  have h : ((q : ℕ) : ZMod 3) = -1 := by
    rw [← ZMod.natCast_mod, hq]
    decide
  rw [h]
  exact orderOf_eq_prime (by decide) (by decide)

theorem exists_frame_statedProj_sl {F : Type} [Field F] [Finite F] {n : ℕ}
    (hq : Nat.card F % 3 = 2) (hn : n / 2 = 3) :
    ∃ a : ℕ, 1 ≤ a ∧
      ∃ φ : (Fin 3 → Multiplicative (ZMod (3 ^ a))) →* StatedProj (StatedSL n F),
        Function.Injective φ ∧
        (∀ i : Fin 3, ∃ g : StatedProj (StatedSL n F), ∀ c,
          g * φ c * g⁻¹ = φ (Function.update c i (c i ^ (Nat.card F : ℤ)))) ∧
        (∃ s : StatedProj (StatedSL n F), s ^ 3 = 1 ∧
          ∀ x, s * φ x * s⁻¹ = φ (Wreath.sh x)) ∧
        ¬ 3 ^ (3 * a + 2) ∣ Nat.card (StatedProj (StatedSL n F)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero n := ⟨by omega⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpq : ¬ 3 ∣ Nat.card F := by omega
  have hpq1 : ¬ 3 ∣ Nat.card F - 1 := by omega
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have he2 : CrossNum.crossE 3 (Nat.card F) = 2 := orderOf_natCast_mod_three_of_two hq
  have ha1 : 1 ≤ CrossNum.crossA 3 (Nat.card F) := CrossNum.one_le_crossA hpq hq1
  have hdvd : 3 ^ CrossNum.crossA 3 (Nat.card F) ∣
      Nat.card F ^ CrossNum.crossE 3 (Nat.card F) - 1 := CrossNum.pow_crossA_dvd hpq
  have hN : ¬ 3 ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) :=
    not_dvd_card_scalars_of_not_dvd_sub_one hpq1
  have hord := factorization_card_projSL hp2 hpq hN
  rw [Nat.factorization_eq_zero_of_not_dvd hpq1, add_zero] at hord
  rw [he2] at hdvd hord
  generalize CrossNum.crossA 3 (Nat.card F) = a at ha1 hdvd hord
  rw [hn] at hord
  haveI : NeZero (3 ^ a) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq
    (L := FiniteField.Extension F (ringChar F) 2) (d := 3 ^ a)
    (by rwa [FiniteField.natCard_extension])
  obtain ⟨ρ₀, hρ₀⟩ := CFSG.GroupTheory.WeirSylow.exists_injective_hom_of_orderOf_eq
    (H := (⊤ : Subgroup (FiniteField.Extension F (ringChar F) 2)ˣ)) (Subgroup.mem_top ζ) hζ
  obtain ⟨T, S, Fr, hTinj, -, hS, hSdet, hFr, hU⟩ :=
    exists_blockFrame F
      ((⊤ : Subgroup (FiniteField.Extension F (ringChar F) 2)ˣ).subtype.comp ρ₀)
      (Subtype.val_injective.comp hρ₀) 3 (n % 2) n
      (by rw [FiniteField.finrank_extension]; omega) (by norm_num)
  have hdet1 : ∀ c, ((T c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := fun c =>
    det_eq_one_of_pow_eq_one hpq1 (k := a) (by rw [← map_pow, pow_pPow_eq_one_pi, map_one])
  have hS1 : ∀ σ : Equiv.Perm (Fin 3),
      ((S σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    intro σ
    rw [hSdet σ, FiniteField.finrank_extension]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  have hΨ : Function.Injective (liftSL T hdet1) :=
    liftSL_injective hTinj (fun c => ⟨a, pow_pPow_eq_one_pi c⟩) hN
  have hσ3 : (finRotate 3) ^ 3 = 1 := by decide
  refine ⟨a, ha1, liftSL T hdet1, hΨ, fun i => ?_,
    ⟨slProj n F ⟨S (finRotate 3), CFSG.Open.StatedAPI.mem_statedSL_of_det (hS1 _)⟩, ?_,
      fun x => ?_⟩, ?_⟩
  · obtain ⟨g', hg'det, hg'⟩ := exists_det_one_conj hU (Fr i)
    refine ⟨slProj n F ⟨g', CFSG.Open.StatedAPI.mem_statedSL_of_det hg'det⟩,
      fun c => liftSL_conj hg'det ?_⟩
    rw [hg', hFr, zpow_natCast]
  · rw [← map_pow]
    have h1 : (⟨S (finRotate 3), CFSG.Open.StatedAPI.mem_statedSL_of_det (hS1 _)⟩ :
        StatedSL n F) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, hσ3, map_one]
    rw [h1, map_one]
  · refine liftSL_conj (hS1 _) ?_
    rw [hS]
    congr 1
    funext i
    simp only [Function.comp_apply, Wreath.sh]
    show x (((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) i) = x (i - 1)
    rw [Wreath.finRotate_three_inv_apply]
  · have hv : (Nat.card (StatedProj (StatedSL n F))).factorization 3 = a * 3 + 1 := by
      rw [hord, ← Nat.factorization_def _ Nat.prime_three, Wreath.factorization_factorial_three]
    intro hdv
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne', hv] at hdv
    omega

theorem listRow_statedProj_sl_three {F : Type} [Field F] [Finite F] {n : ℕ}
    (hq : Nat.card F % 3 = 2) (hn : n / 2 = 3) : ListRow (StatedProj (StatedSL n F)) := by
  obtain ⟨a, ha, φ, hφ, htw, ⟨s, hs3, hs⟩, hS⟩ := exists_frame_statedProj_sl hq hn
  haveI : NeZero (3 ^ a) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hC : Nat.card (Multiplicative (ZMod (3 ^ a))) = 3 ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Wreath.listRow_of_wreath ha hC hφ (by omega) htw hs3 hs hS

theorem listRow_psl6 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSL 6 p f)
    (hq : p ^ f % 3 = 2) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_sl_three (by rw [hK]; exact hq) (by norm_num))

theorem listRow_psl7 (S : Type) [Group S] [Finite S] (p f : ℕ) (h : LieModel S .PSL 7 p f)
    (hq : p ^ f % 3 = 2) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_sl_three (by rw [hK]; exact hq) (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
