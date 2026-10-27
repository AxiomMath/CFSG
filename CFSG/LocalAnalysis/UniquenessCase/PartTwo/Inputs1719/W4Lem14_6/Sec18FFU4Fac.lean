module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSecMul
public import CFSG.HardMathSupport.U4FF.FromDichotomy
public import CFSG.HardMathSupport.U4FF.ClassMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.K148
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}
variable {H : Subgroup G} {Y Z : Submodule (ZMod 2) V}

private lemma card_secMulImg_eq_two_pow [Finite G] [Finite V] {L B : Subgroup G} [IsSimpleGroup ↥L]
    {m : ℕ} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hm : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)))
    (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) :
    Nat.card ↥(secMulImg hY hZ B) = 2 ^ m := by
  have hYL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y := fun l hl => hY l (Subgroup.mem_sup_left hl)
  have hker : B ⊓ secKer ρ Y Z = B ⊓ Subgroup.centralizer (L : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.inf_secKer_eq hBN hYL hZ hCB hnt le_rfl
      inf_le_left
  have h1 := card_secMulImg_mul (hY := hY) (hZ := hZ) (D := B) (le_sup_right : B ≤ L ⊔ B)
  rw [hker, hm] at h1
  have hpos : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

private lemma one_le_secCost_of_not_centralizing [Finite G] [Finite V]
    {L B : Subgroup G} [IsSimpleGroup ↥L]
    (hBe : CFSG.IsElementaryAbelian 2 ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z)
    (hBL : ¬ B ≤ Subgroup.centralizer (L : Set G)) :
    1 ≤ secCost ρ B Y Z := by
  rcases Nat.eq_zero_or_pos (secCost ρ B Y Z) with h0 | hpos
  · exfalso
    have hYL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Y := fun l hl => hY l (Subgroup.mem_sup_left hl)
    have hZP : Z ≤ Y ⊓ P22x.modFix ρ Z B :=
      le_inf hZY (le_modFix fun a ha => hZ a (Subgroup.mem_sup_right ha))
    have hle : finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) ≤ finrank (ZMod 2) ↥Y :=
      Submodule.finrank_mono inf_le_left
    have hfin : finrank (ZMod 2) ↥Y = finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) := by
      unfold secCost at h0
      omega
    have heq : Y ⊓ P22x.modFix ρ Z B = Y :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left hfin.symm
    have hYle : Y ≤ P22x.modFix ρ Z B := by
      rw [← heq]
      exact inf_le_right
    have hBker : B ≤ secKer ρ Y Z := by
      intro b hb
      rw [mem_secKer]
      refine ⟨fun y hy => (P22x.mem_modFix.1 (hYle hy)) b hb, fun z hz => ?_, fun z hz => ?_⟩
      · exact hZ b (Subgroup.mem_sup_right hb) z hz
      · have hb2 : b * b = 1 := (elemAb_facts hBe).2 b hb
        have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
        rw [hbinv]
        exact hZ b (Subgroup.mem_sup_right hb) z hz
    have hker : B ⊓ secKer ρ Y Z = B ⊓ Subgroup.centralizer (L : Set G) :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.K148.inf_secKer_eq hBN hYL hZ hCB hnt le_rfl
        inf_le_left
    apply hBL
    intro b hb
    have hbker : b ∈ B ⊓ secKer ρ Y Z := ⟨hb, hBker hb⟩
    rw [hker] at hbker
    exact hbker.2
  · exact hpos

theorem isU4Group_of_mulEquiv {S : Type} [CommGroup S] {X : Type} [Group X]
    {L : Subgroup (MulAut S)} {n : ℕ} (h : IsU4 X n) (e : ↥L ≃* X) :
    CFSG.LocalAnalysis.RankThreeUC.IsU4Group n L := by
  have hC := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨q, hv, hp, he, ⟨φ⟩⟩ :=
    KSExact.exists_twistedA_of_statedClassicalModel_PSU (m := 3) hC
  exact ⟨⟨_, hv⟩, ⟨q, hp, he, rfl⟩, ⟨e.trans φ⟩⟩

theorem u4_secNatural
    [Finite G] [Finite V]
    {L B : Subgroup G} [IsSimpleGroup ↥L] {n : ℕ} (hn : 1 < n) (hU4 : IsU4 ↥L n)
    (hBe : CFSG.IsElementaryAbelian 2 ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hm1 : 1 ≤ m)
    (hm : Nat.card ↥B = 2 ^ m * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)))
    (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) → ∀ y ∈ Y, ρ b y = y)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) (hcost : secCost ρ B Y Z ≤ m) :
    CFSG.LocalAnalysis.RankThreeUC.IsIrrOn (secMulImg hY hZ L) ∧
      CFSG.LocalAnalysis.RankThreeUC.NaturalU4Mod n (secMulImg hY hZ L) := by
  have hBL : ¬ B ≤ Subgroup.centralizer (L : Set G) := by
    intro hle
    have hBc : B ⊓ Subgroup.centralizer (L : Set G) = B := inf_eq_left.2 hle
    rw [hBc] at hm
    have h2 : 2 ^ m = 1 := by
      have h1 : 2 ^ m * Nat.card ↥B = 1 * Nat.card ↥B := by
        rw [one_mul]
        exact hm.symm
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have h3 : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hcardA := card_secMulImg_eq_two_pow hBN hm hZY hY hZ hCB hnt
  have hcardS := card_secMul_top (Y := Y) (Z := Z) hZY
  have hcardC := card_fixV_secMulImg (hZY := hZY) (hY := hY) (hZ := hZ) (D := B)
    (le_sup_right : B ≤ L ⊔ B)
  have hZP : Z ≤ Y ⊓ P22x.modFix ρ Z B :=
    le_inf hZY (le_modFix fun a ha => hZ a (Subgroup.mem_sup_right ha))
  have hf1 : finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) ≤ finrank (ZMod 2) ↥Y :=
    Submodule.finrank_mono inf_le_left
  have hf2 : finrank (ZMod 2) ↥Z ≤ finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) :=
    Submodule.finrank_mono hZP
  have hoff : Nat.card (Multiplicative (SecQ Y Z)) ≤
      Nat.card ↥(secMulImg hY hZ B) * Nat.card ↥(CFSG.Quasithin.fixV (secMulImg hY hZ B)) := by
    rw [hcardS, hcardC, hcardA, ← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold secCost at hcost
    omega
  have hS : ∀ s : Multiplicative (SecQ Y Z), s ^ 2 = 1 := by
    intro s
    obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective s
    rw [pow_two, ← ofAdd_add]
    have h2 : x + x = 0 := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [h2, ofAdd_zero]
  have hU4' : CFSG.LocalAnalysis.RankThreeUC.IsU4Group n (secMulImg hY hZ L) :=
    isU4Group_of_mulEquiv hU4 (secMulEquiv (le_sup_left) hY hZ hnt).symm
  have hAe : CFSG.Quasithin.IsElemAbelian2 (secMulImg hY hZ B) :=
    isElemAbelian2_secMulImg hY hZ hBe
  have hAN : secMulImg hY hZ B ≤
      Subgroup.normalizer (secMulImg hY hZ L : Set (MulAut (Multiplicative (SecQ Y Z)))) :=
    secMulImg_le_normalizer (le_sup_left) (le_sup_right) hY hZ hBN
  have hnc : ∃ a ∈ secMulImg hY hZ B, ∃ l ∈ secMulImg hY hZ L, a * l ≠ l * a :=
    exists_noncomm_secMulImg (le_sup_left) (le_sup_right) hY hZ hBN hnt hBL
  have hirr' : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn
      (secMulImg hY hZ L ⊔ secMulImg hY hZ B) :=
    isIrrOn_secMulImg_sup (le_sup_left) (le_sup_right) hZY hY hZ hirr
  exact (CFSG.HardMathSupport.U4FF.u4FFNatural_of_dichotomy
    CFSG.HardMathSupport.U4FF.u4RankDichotomy_holds)
    (Multiplicative (SecQ Y Z)) hS n (secMulImg hY hZ L) (secMulImg hY hZ B)
    hU4' hAe hAN hnc hirr' hoff

theorem u4_factorBound
    [Finite G] [Finite V]
    {L : Subgroup G} [IsSimpleGroup ↥L] {n : ℕ} (hn : 1 < n) (hU4 : IsU4 ↥L n) :
    FactorBound ρ L := by
  intro B hBe hBN m hm1 hm Y Z hZY hY hZ hCB hirr hnt hcost
  obtain ⟨-, hnat⟩ := u4_secNatural hn hU4 hBe hBN hm1 hm hZY hY hZ hCB hirr hnt hcost
  have hBL : ¬ B ≤ Subgroup.centralizer (L : Set G) := by
    intro hle
    have hBc : B ⊓ Subgroup.centralizer (L : Set G) = B := inf_eq_left.2 hle
    rw [hBc] at hm
    have h2 : 2 ^ m = 1 := by
      have h1 : 2 ^ m * Nat.card ↥B = 1 * Nat.card ↥B := by
        rw [one_mul]
        exact hm.symm
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have h3 : 1 < 2 ^ m := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hs1 : 1 ≤ secCost ρ B Y Z :=
    one_le_secCost_of_not_centralizing hBe hBN hZY hY hZ hCB hnt hBL
  have hcardA := card_secMulImg_eq_two_pow hBN hm hZY hY hZ hCB hnt
  have hcardS := card_secMul_top (Y := Y) (Z := Z) hZY
  have hcardC := card_fixV_secMulImg (hZY := hZY) (hY := hY) (hZ := hZ) (D := B)
    (le_sup_right : B ≤ L ⊔ B)
  have hZP : Z ≤ Y ⊓ P22x.modFix ρ Z B :=
    le_inf hZY (le_modFix fun a ha => hZ a (Subgroup.mem_sup_right ha))
  have hf1 : finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) ≤ finrank (ZMod 2) ↥Y :=
    Submodule.finrank_mono inf_le_left
  have hf2 : finrank (ZMod 2) ↥Z ≤ finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) :=
    Submodule.finrank_mono hZP
  have hAe : CFSG.Quasithin.IsElemAbelian2 (secMulImg hY hZ B) :=
    isElemAbelian2_secMulImg hY hZ hBe
  have hAN : secMulImg hY hZ B ≤
      Subgroup.normalizer (secMulImg hY hZ L : Set (MulAut (Multiplicative (SecQ Y Z)))) :=
    secMulImg_le_normalizer (le_sup_left) (le_sup_right) hY hZ hBN
  have hS : ∀ s : Multiplicative (SecQ Y Z), s ^ 2 = 1 := by
    intro s
    obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective s
    rw [pow_two, ← ofAdd_add]
    have h2 : x + x = 0 := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [h2, ofAdd_zero]
  rcases (CFSG.LocalAnalysis.RankThreeUC.naturalU4Mod_iff
    (n := n) (S := Multiplicative (SecQ Y Z)) (L := secMulImg hY hZ L)).1 hnat with hN | hO
  · obtain ⟨F, hF, hFin, hcardF, ε, ψ, hεψ⟩ := hN
    have hpart := CFSG.LocalAnalysis.RankThreeUC.partBN_stmt
      (S := Multiplicative (SecQ Y Z)) (n := n) (F := F) hS (le_of_lt hn) hcardF
      (L := secMulImg hY hZ L) (A := secMulImg hY hZ B) ε ψ hεψ hAe hAN
    have hpart' : 2 ^ (m + (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) - finrank (ZMod 2) ↥Z))
        ≤ 2 ^ (finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) := by
      rw [hcardA, hcardC, hcardS, ← pow_add] at hpart
      exact hpart
    have hmle : m ≤ secCost ρ B Y Z := by
      have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpart'
      unfold secCost
      omega
    omega
  · obtain ⟨F, hF, hFin, b, c, hcardF, hqs, ε, ψ, hεψ⟩ := hO
    have hpart := CFSG.LocalAnalysis.RankThreeUC.partBO_stmt
      (S := Multiplicative (SecQ Y Z)) (n := n) (F := F) (b := b) (c := c) hS
      (le_of_lt hn) hcardF hqs ε ψ hεψ hAe hAN
    have hpart' : 2 ^ (m + (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) - finrank (ZMod 2) ↥Z))
        ≤ 2 ^ ((finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) + 1) := by
      rw [hcardA, hcardC, hcardS, ← pow_add] at hpart
      calc
        2 ^ (m + (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) - finrank (ZMod 2) ↥Z))
            ≤ 2 * 2 ^ (finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) := hpart
        _ = 2 ^ ((finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) + 1) := by
              rw [pow_succ]
              ring
    have hmle : m ≤ secCost ρ B Y Z + 1 := by
      have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpart'
      unfold secCost
      omega
    by_cases hms : m ≤ secCost ρ B Y Z
    · omega
    · have hms1 : m = secCost ρ B Y Z + 1 := by omega
      have hs2 : 2 ≤ secCost ρ B Y Z := by
        by_contra hlt
        push_neg at hlt
        have hs_eq1 : secCost ρ B Y Z = 1 := by omega
        have hBO4 := CFSG.LocalAnalysis.RankThreeUC.partBO4_stmt
          (S := Multiplicative (SecQ Y Z)) (n := n) (F := F) (b := b) (c := c) hS
          (le_of_lt hn) hcardF hqs ε ψ hεψ hAe hAN
        have hA4 : Nat.card ↥(secMulImg hY hZ B) = 4 := by
          rw [hcardA, hms1, hs_eq1]
          norm_num
        have hSC : Nat.card (Multiplicative (SecQ Y Z)) =
            2 * Nat.card ↥(CFSG.Quasithin.fixV (secMulImg hY hZ B)) := by
          rw [hcardS, hcardC]
          have hy : finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z =
              (finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B)) +
                (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) - finrank (ZMod 2) ↥Z) := by
            omega
          rw [hy, show finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z B) =
              secCost ρ B Y Z from rfl, hs_eq1, pow_add, pow_one]
        exact hBO4 ⟨hA4, hSC⟩
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
