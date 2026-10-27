module

public import CFSG.Quasithin.Vol2.Ch10SecK2Ts
public import CFSG.Quasithin.Vol2.Ch10SecK2Tq
public import CFSG.Quasithin.Vol2.Ch10SecK2Tr
public import CFSG.Quasithin.Vol2.Ch10SecKIK2h

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative

variable {Γ : Type} [Group Γ]

structure ValidX (J L R W : Subgroup Γ) (q : ℕ) (X : Subgroup Γ) : Prop where
  le : X ≤ W
  nR : R ⊓ J ≤ Subgroup.normalizer (X : Set Γ)
  nL : L ≤ Subgroup.normalizer (X : Set Γ)
  comm : ⁅X, L⁆ = X
  cO : pCoreOf 2 L ≤ Subgroup.centralizer (X : Set Γ)
  card : (Subgroup.centralizer (L : Set Γ) ⊓ X).relIndex X ≤ q ^ 2

theorem modO2Image_le_normalizer {J L R : Subgroup Γ}
    (hRL : R ≤ Subgroup.normalizer (L : Set Γ)) :
    ((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) ≤
      Subgroup.normalizer ((modO2Image J L : Subgroup _) : Set (↥J ⧸ CFSG.pCore 2 ↥J)) := by
  have h : (R ⊓ J).subgroupOf J ≤
      Subgroup.normalizer ((L.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro l
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hRL (Subgroup.mem_subgroupOf.mp hr).1) l)
  exact (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map _)

theorem modO2Image_ne_bot {J L : Subgroup Γ} (hLJ : L ≤ J) {F : Type} [Field F] [Finite F]
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) [Finite Γ] :
    modO2Image J L ≠ ⊥ := by
  intro h
  obtain ⟨e'⟩ := lbar_modO2_equiv hLJ
  have h1 := one_lt_card_of_levi (e'.trans e)
  rw [h, Subgroup.card_bot] at h1
  exact lt_irrefl _ h1

section Core

variable [Finite Γ]

theorem core_line {J L R W : Subgroup Γ} [IsMulCommutative ↥W] (hW2 : ∀ w : ↥W, w ^ 2 = 1)
    (hJW : J ≤ Subgroup.normalizer (W : Set Γ))
    (hOJ : pCoreOf 2 J ≤ Subgroup.centralizer (W : Set Γ))
    (hJC : ¬ J ≤ Subgroup.centralizer (W : Set Γ)) (hLJ : L ≤ J)
    (hRL : R ≤ Subgroup.normalizer (L : Set Γ))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hZY : Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 1 ∨
      Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 3)
    {P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hP : IsMaxParabolic2 ⊤ P)
    (hLP : modO2Image J L = perfectCore P) (hLne : modO2Image J L ≠ ⊤)
    (hT : IsSylowTwoOf (((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) ⊤)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {Z : Subgroup ↥W} {m : ℕ} (hD : TorusData (autOn J W) Z (2 ^ m))
    {X₀ : Subgroup Γ} (hX₀ : ValidX J L R W (2 ^ n) X₀) (hX₀ne : X₀ ≠ ⊥) :
    ∃ U₂ : Subgroup ↥W, LineFacts (autOn J W) Z U₂ ∧
      LineTorusFacts (autOn J W) (autOn (R ⊓ J) W) Z U₂ (2 ^ n) ∧
      perfectCore (autOn J W ⊓ stabW U₂) = autOn L W ∧
      ∀ X : Subgroup Γ, ValidX J L R W (2 ^ n) X → X ≠ ⊥ →
        X.subgroupOf W = commS (autOn L W) U₂ := by
  have : CharP F 2 := KGNat.charP_two_of_card (by omega) hF
  have h4 : 4 ≤ Nat.card F := four_le_card hn hF
  set ψ := psiW hJW hOJ with hψ
  have hψs := psiW_surjective hJW hOJ
  have hker := ker_psiW_le_center hJW hOJ hq hJC
  have hodd : Odd (Nat.card ψ.ker) := by
    have hd : Nat.card ψ.ker ∣ Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) :=
      Subgroup.card_dvd_of_le hker
    rcases hZY with h | h <;> rw [h] at hd
    · rw [Nat.dvd_one.mp hd]
      exact odd_one
    · rcases (Nat.dvd_prime Nat.prime_three).mp hd with h' | h' <;> rw [h'] <;> decide
  have hbot : perfectCore P ≠ ⊥ := hLP ▸ modO2Image_ne_bot hLJ e
  have hne : perfectCore P ≠ ⊤ := hLP ▸ hLne
  have hTN := modO2Image_le_normalizer (J := J) hRL
  rw [hLP] at hTN
  obtain ⟨hPst, hcore, hS₀, hPS⟩ := parabolic_transfer hψs hker hodd hq hP hne hbot hT hTN
  have hL' : (perfectCore (P.map ψ)).map (autOn J W).subtype = autOn L W := by
    rw [hcore, ← hLP]
    exact map_psiW hJW hOJ hLJ
  have hS' : ((((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map ψ).map
      (autOn J W).subtype = autOn (R ⊓ J) W := map_psiW hJW hOJ inf_le_right
  have hLW : L ≤ Subgroup.normalizer (W : Set Γ) := hLJ.trans hJW
  have hperf : ⁅autOn L W, autOn L W⁆ = autOn L W := by
    rw [← hL', ← Subgroup.map_commutator, perfectCore_perfect]
  have hLne' : autOn L W ≠ ⊥ := by
    intro h
    apply hX₀ne
    rw [← hX₀.comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : conjAct W ⟨l, hLW hl⟩ = 1 := by
      have := InternalSec.conjAct_mem_autOn hLW hl
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have h2 := congrArg (fun φ : MulAut ↥W => ((φ ⟨x, hX₀.le hx⟩ : ↥W) : Γ)) h1
    simp only [Setup.coe_conjAct_apply, MulAut.one_apply] at h2
    calc l * x = l * x * l⁻¹ * l := by group
      _ = x * l := by rw [h2]
  have hnot := not_isPGroup_of_perfect hperf hLne'
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := levi_of_data hD hPst hS₀ hPS
  rw [hL'] at eK
  obtain ⟨eF⟩ := nonempty_levi_of_map (InternalSec.autOnHom_surjective hLW) h4 e hnot
  have hKF : Nat.card K = Nat.card F := eq_of_card_sl2 Nat.card_pos Nat.card_pos (by
    rw [← card_sl2, ← card_sl2, ← Nat.card_congr eK.toEquiv, Nat.card_congr eF.toEquiv])
  have hmn : 2 ^ m = 2 ^ n := by rw [← hK, hKF, hF]
  rw [hmn] at hD
  have hvalid : ∀ X, ValidX J L R W (2 ^ n) X →
      ValidM ((((((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map ψ).map
        (autOn J W).subtype)) ((perfectCore (P.map ψ)).map (autOn J W).subtype) (2 ^ n)
        (X.subgroupOf W) := by
    intro X hX
    rw [hS', hL']
    exact validM_of hJW hLJ hX.le hX.nR hX.nL hX.comm (pCore_autOn_fix hLW h4 e hnot hX.cO)
      hX.card
  have hne' : ∀ X, ValidX J L R W (2 ^ n) X → X ≠ ⊥ → X.subgroupOf W ≠ ⊥ := by
    intro X hX hXne h
    apply hXne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hX.le hx⟩ : ↥W) ∈ X.subgroupOf W := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨U, -, hLU, hLF, hLT, heq⟩ :=
    line_of_data hW2 hD hPst hS₀ hPS (hvalid X₀ hX₀) (hne' X₀ hX₀ hX₀ne)
  rw [hS'] at hLT
  rw [hL'] at hLU
  refine ⟨U, hLF, hLT, hLU.symm, fun X hX hXne => ?_⟩
  rw [heq _ (hvalid X hX) (hne' X hX hXne), ← hLU]

end Core

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
