module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iL44E16
public import CFSG.RankThree.PartTwo.Sec21.Hering233iL44Exc
public import CFSG.RankThree.PartTwo.Sec21.Hering233iPull

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

namespace Hering233i

open Matrix hiding ext
open CFSG.RankThree.PartTwo.Sec21.TablesL44 CFSG.RankThree.PartTwo.KFacts.KS21.L44
  CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.Assembly.LowTwoRank

theorem center_SL2 : Subgroup.center (SpecialLinearGroup (Fin 2) F4) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 :=
    CFSG.LieType.BorelTits.eq_one_of_pow_char_pow_eq_one 2 (e := 1) (by norm_num [hr])
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

@[expose] noncomputable def equivSL2 : projSL 2 F4 ≃* SpecialLinearGroup (Fin 2) F4 :=
  (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL 2 F4)).symm.trans
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSL 2 F4)).symm.trans
      ((projectiveSpecialLinearGroupEquivStatedProj 2 F4).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq center_SL2).trans QuotientGroup.quotientBot)))

variable {G : Type} [Group G] {I : Subgroup G}

@[expose] noncomputable def pullEquiv (Φ : I ≃* M) (S : Subgroup M) : pull Φ S ≃* S :=
  ((Subgroup.subgroupOfEquivOfLe (pull_le Φ S)).symm.trans
    ((pull Φ S).subgroupOf I |>.equivMapOfInjective Φ.toMonoidHom Φ.injective)).trans
    (MulEquiv.subgroupCongr (pull_map Φ S))

theorem comm_of_Φ (Φ : I ≃* M) {x y : G} (hx : x ∈ I) (hy : y ∈ I)
    (h : Φ ⟨x, hx⟩ * Φ ⟨y, hy⟩ = Φ ⟨y, hy⟩ * Φ ⟨x, hx⟩) : x * y = y * x := by
  have h' : (⟨x, hx⟩ : I) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    apply Φ.injective
    rw [map_mul, map_mul]
    exact h
  exact congrArg Subtype.val h'

theorem δ_ne_one {v : Fin 3 → ZMod 3} (hv : v ≠ 0) : δ (Multiplicative.ofAdd v) ≠ 1 := by
  intro h
  apply hv
  have h1 : δ (Multiplicative.ofAdd v) = δ 1 := by rw [h, map_one]
  exact Multiplicative.ofAdd.injective (δ_injective h1)

theorem components_std0_image {c : M} (hc : c = δ (Multiplicative.ofAdd (std 0)))
    {Y : Subgroup (Subgroup.centralizer ({c} : Set M))} (hY : CFSG.IsComponent Y) :
    Y.map (Subgroup.centralizer ({c} : Set M)).subtype =
      blockSub {i : Fin 4 | i = 2 ∨ i = 3} := by
  subst hc
  have hmem : Y ∈ {Z : Subgroup (Subgroup.centralizer
      ({δ (Multiplicative.ofAdd (std 0))} : Set M)) | CFSG.IsComponent Z} := hY
  rw [components_big (by decide : std 0 ≠ 0)] at hmem
  obtain ⟨κ, rfl⟩ := hmem
  have hκ : κ.1 = 0 := by
    have key : ∀ κ : ZMod 3, (∃ i j : Fin 4, i ≠ j ∧ ext (std 0) i = κ ∧ ext (std 0) j = κ) →
        κ = 0 := by decide
    exact key κ.1 κ.2
  have : ((blockSub {i : Fin 4 | ext (std 0) i = κ.1}).subgroupOf
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set M))).map
        (Subgroup.centralizer ({δ (Multiplicative.ofAdd (std 0))} : Set M)).subtype =
      blockSub {i : Fin 4 | ext (std 0) i = 0} := by
    rw [hκ]
    exact Subgroup.map_subgroupOf_eq_of_le (blockSub_le_cv _ _)
  rw [this, fib0_0]

end Hering233i

open Hering233i CFSG.RankThree.PartTwo.Sec21.TablesL44 CFSG.RankThree.PartTwo.KFacts.KS21.L44
  CFSG.RankThree.PartTwo.Sec21.Tables in
theorem l44ExceptionModel : L44ExceptionModel := by
  intro G _ _ I A hAI hAe hI44 hA27 B hBA hB3 X hX huniq h60
  obtain ⟨e⟩ := hI44
  obtain ⟨Φ₁, hΦ₁A⟩ := exists_Phi hAI hAe e hA27
  obtain ⟨b, hbB, hb1, hBb⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA hbB
  obtain ⟨Φ, i, b₀, hb₀I, hzp, hΦb₀, hΦA⟩ := exists_std_pos hAI Φ₁ hΦ₁A hAe hbA hb1
  have hBb₀ : B = Subgroup.zpowers b₀ := hBb.trans hzp.symm
  subst hBb₀
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hΦH := map_inf_centralizer_zpowers Φ hb₀I
  have hU : UniqueSixtyAt (Φ ⟨b₀, hb₀I⟩) := uniqueSixtyAt_of_data Φ hb₀I X hX huniq h60
  have fin3 : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  have hi0 : i = 0 := by
    rcases fin3 i with rfl | rfl | rfl
    · rfl
    · exfalso
      rw [hΦb₀] at hU
      exact not_uniqueSixty_std1 hU
    · exfalso
      rw [hΦb₀] at hU
      exact not_uniqueSixty_std2 hU
  subst hi0
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (thetaK hHI Φ hΦH) hX
  have hXg0 : ((X.map (I ⊓ Subgroup.centralizer
      ((Subgroup.zpowers b₀ : Subgroup G) : Set G)).subtype).subgroupOf I).map Φ.toMonoidHom =
      blockSub {i : Fin 4 | i = 2 ∨ i = 3} := by
    rw [map_subgroupOf_map_subtype hHI Φ hΦH X]
    exact components_std0_image hΦb₀ hY
  have hXgI : X.map (I ⊓ Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup G) :
      Set G)).subtype ≤ I := (Subgroup.map_subtype_le X).trans hHI
  have hXgpull := eq_pull_of_map hXgI hXg0
  have hrepne : ∀ k : Fin 4, repV k ≠ 0 := by decide
  have hb₀eq : b₀ = gOf Φ (δ (Multiplicative.ofAdd (std 0))) := by
    rw [← hΦb₀, gOf_Φ]
  have hrepA : ∀ k : Fin 4, gOf Φ (δ (Multiplicative.ofAdd (repV k))) ∈ A := fun k =>
    (mem_A_iff_Phi Φ hΦA ⟨gOf Φ (δ (Multiplicative.ofAdd (repV k))), gOf_mem Φ _⟩).mpr
      (by rw [Φ_gOf]; exact δ_mem_A0 _)
  have hrep1 : ∀ k : Fin 4, gOf Φ (δ (Multiplicative.ofAdd (repV k))) ≠ 1 := fun k h =>
    δ_ne_one (hrepne k) ((gOf_eq_one_iff Φ).mp h)
  have hlay : ∀ k : Fin 4, layerCent I
      (Subgroup.zpowers (gOf Φ (δ (Multiplicative.ofAdd (repV k))))) =
      pull Φ (LM (repV k)) := fun k => by
    rw [layerCent_eq_pull Φ (gOf_mem Φ _), Φ_gOf]
  have hbM01 : δ (Multiplicative.ofAdd (std 0)) ∈ blockSub {i : Fin 4 | i = 0 ∨ i = 1} :=
    δ_mem_block (by decide)
  have hset1 : {i : Fin 4 | ext (repV 1) i = 1} = {i : Fin 4 | i = 0 ∨ i = 1} := by
    ext i
    fin_cases i <;> decide
  have hZ23 : blockSub {i : Fin 4 | i = 2 ∨ i = 3} = ι23.range := by
    ext x
    rw [mem_blockSub, mem_range_ι23_iff]
  refine ⟨b₀, gOf Φ (δ (Multiplicative.ofAdd (repV 0))), gOf Φ (δ (Multiplicative.ofAdd (repV 1))),
    gOf Φ (δ (Multiplicative.ofAdd (repV 2))), gOf Φ (δ (Multiplicative.ofAdd (repV 3))),
    gOf Φ wM, pull Φ (blockSub {i : Fin 4 | i = 0 ∨ i = 1}), ?_⟩
  have hX'Y₁ : pull Φ (blockSub {i : Fin 4 | i = 0 ∨ i = 1}) ≤ layerCent I
      (Subgroup.zpowers (gOf Φ (δ (Multiplicative.ofAdd (repV 1))))) := by
    rw [hlay 1]
    refine pull_mono ?_
    have := block_le_LM (v := repV 1) (hrepne 1) (κ := 1) ⟨0, 1, by decide, by decide, by decide⟩
    rwa [hset1] at this
  refine
    { hBb := rfl
      hb1 := ?_
      hbA := hBA (Subgroup.mem_zpowers b₀)
      haA := hrepA 0
      haX := ?_
      ha1 := hrep1 0
      eX := ?_
      hb'A := hrepA 1
      hc₃A := hrepA 2
      hc₄A := hrepA 3
      hb'1 := hrep1 1
      hc₃1 := hrep1 2
      hc₄1 := hrep1 3
      hcover := ?_
      hXw := ?_
      hw2 := ?_
      hwX' := ?_
      hwb := ?_
      hX'simple := ?_
      hbX' := ?_
      hX'Y₁ := hX'Y₁
      hX'N := ?_
      hfree₁ := ?_
      hcount' := ?_
      hX'Y₃ := ?_
      hfree₃ := ?_
      hcount₃ := ?_
      hX'Y₄ := ?_
      hfree₄ := ?_
      hcount₄ := ?_ }
  ·
    intro h
    apply δ_ne_one (by decide : std 0 ≠ 0)
    rw [← hΦb₀, show (⟨b₀, hb₀I⟩ : I) = 1 from Subtype.ext h, map_one]
  ·
    rw [hXgpull, mem_pull]
    exact ⟨gOf_mem Φ _, by rw [Φ_gOf]; exact δ_mem_block (by decide)⟩
  ·
    rw [hXgpull]
    exact ⟨(pullEquiv Φ _).trans ((MulEquiv.subgroupCongr hZ23).trans
      ((MonoidHom.ofInjective ι23_injective).symm.trans equivSL2.symm))⟩
  ·
    intro h hhA hhB
    have hhI : h ∈ I := hAI hhA
    have hhM : Φ ⟨h, hhI⟩ ∈ A0 := (mem_A_iff_Phi Φ hΦA ⟨h, hhI⟩).mp hhA
    have hnot : Φ ⟨h, hhI⟩ ∉ Subgroup.zpowers (δ (Multiplicative.ofAdd (std 0))) := by
      intro hmem
      apply hhB
      rw [zpowers_eq_pull Φ hb₀I, mem_pull]
      exact ⟨hhI, by rw [hΦb₀]; exact hmem⟩
    obtain ⟨k, m, n, hmn⟩ := cover_M hhM hnot
    refine ⟨k, ?_⟩
    have hk : (![gOf Φ (δ (Multiplicative.ofAdd (repV 0))),
        gOf Φ (δ (Multiplicative.ofAdd (repV 1))), gOf Φ (δ (Multiplicative.ofAdd (repV 2))),
        gOf Φ (δ (Multiplicative.ofAdd (repV 3)))] : Fin 4 → G) k =
          gOf Φ (δ (Multiplicative.ofAdd (repV k))) := by
      fin_cases k <;> rfl
    rw [hk, hmn, gOf_mul, gOf_pow, gOf_pow, ← hb₀eq, gOf_Φ Φ hhI]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) m)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers h) n)
  ·
    intro x hx
    rw [hXgpull, mem_pull] at hx
    obtain ⟨hxI, hxZ⟩ := hx
    refine comm_of_Φ Φ hxI (gOf_mem Φ wM) ?_
    rw [Φ_gOf]
    exact block_comm hxZ wM_mem_block
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, ← gOf_mul, wM_mul_self, gOf_one])
      (fun h => wM_ne_one ((gOf_eq_one_iff Φ).mp h))
  ·
    exact mem_pull.mpr ⟨gOf_mem Φ wM, by rw [Φ_gOf]; exact wM_mem_block⟩
  ·
    rw [hb₀eq, ← gOf_inv, ← gOf_mul, ← gOf_mul, wM_conj, gOf_inv]
  ·
    haveI := isSimpleGroup_block01
    exact (pullEquiv Φ _).isSimpleGroup
  ·
    exact mem_pull.mpr ⟨hb₀I, by rw [hΦb₀]; exact hbM01⟩
  ·
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hX'Y₁).mpr fun g hg => ?_
    rw [hlay 1, mem_pull] at hg
    obtain ⟨hgI, hgL⟩ := hg
    have h1 : Φ ⟨g, hgI⟩ ∈ Subgroup.normalizer
        (blockSub {i : Fin 4 | i = 0 ∨ i = 1} : Set M) := by
      have := cent_le_normalizer_block (repV 1) 1 (LM_le_cent _ hgL)
      rwa [hset1] at this
    have := normalizer_of_map_equiv (pull_le Φ (blockSub {i : Fin 4 | i = 0 ∨ i = 1})) Φ
      (e := Φ ⟨g, hgI⟩) (by rw [pull_map]; exact h1)
    simpa using this
  ·
    exact excFree_of_model Φ (gOf_mem Φ _) (by rw [Φ_gOf]; exact not_uniqueSixty_std1)
  ·
    calc (invSet (pull Φ (blockSub {i : Fin 4 | i = 0 ∨ i = 1})) b₀).ncard
        ≤ (invSet (blockSub {i : Fin 4 | i = 0 ∨ i = 1}) (Φ ⟨b₀, hb₀I⟩)).ncard :=
          ncard_invSet_le Φ (pull_le Φ _) (pull_map Φ _) hb₀I
      _ ≤ 4 := by
          rw [hΦb₀]
          exact count_inv (F := {i : Fin 4 | i = 0 ∨ i = 1}) (Or.inl (by decide))
  ·
    rw [hlay 2]
    refine pull_mono (le_trans (blockSub_mono ?_) (block_le_LM (v := repV 2) (hrepne 2)
      (κ := 1) ⟨0, 1, by decide, by decide, by decide⟩))
    intro i hi
    rcases hi with rfl | rfl <;> decide
  ·
    exact excFree_of_model Φ (gOf_mem Φ _) (by rw [Φ_gOf]; exact not_uniqueSixty_C3)
  ·
    rw [hlay 2]
    calc (invSet (pull Φ (LM (repV 2))) b₀).ncard
        ≤ (invSet (LM (repV 2)) (Φ ⟨b₀, hb₀I⟩)).ncard :=
          ncard_invSet_le Φ (pull_le Φ _) (pull_map Φ _) hb₀I
      _ ≤ (invSet (blockSub {i : Fin 4 | ext (repV 2) i = 1})
            (δ (Multiplicative.ofAdd (std 0)))).ncard := by
          rw [hΦb₀]
          exact Set.ncard_le_ncard (invSet_mono (LM_le_block (v := repV 2) (hrepne 2) (κ₀ := 1)
            (by decide)) _) (Set.toFinite _)
      _ ≤ 4 := count_inv (F := {i : Fin 4 | ext (repV 2) i = 1}) (Or.inl (by decide))
  ·
    rw [hlay 3]
    refine pull_mono (le_trans (blockSub_mono ?_) (block_le_LM (v := repV 3) (hrepne 3)
      (κ := 2) ⟨0, 1, by decide, by decide, by decide⟩))
    intro i hi
    rcases hi with rfl | rfl <;> decide
  ·
    exact excFree_of_model Φ (gOf_mem Φ _) (by rw [Φ_gOf]; exact not_uniqueSixty_C4)
  ·
    rw [hlay 3]
    calc (invSet (pull Φ (LM (repV 3))) b₀).ncard
        ≤ (invSet (LM (repV 3)) (Φ ⟨b₀, hb₀I⟩)).ncard :=
          ncard_invSet_le Φ (pull_le Φ _) (pull_map Φ _) hb₀I
      _ ≤ (invSet (blockSub {i : Fin 4 | ext (repV 3) i = 2})
            (δ (Multiplicative.ofAdd (std 0)))).ncard := by
          rw [hΦb₀]
          exact Set.ncard_le_ncard (invSet_mono (LM_le_block (v := repV 3) (hrepne 3) (κ₀ := 2)
            (by decide)) _) (Set.toFinite _)
      _ ≤ 4 := count_inv (F := {i : Fin 4 | ext (repV 3) i = 2}) (Or.inr (by decide))

end CFSG.RankThree.PartTwo.Sec21
