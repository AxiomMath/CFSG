module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Hyper
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentySwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoUniq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLemmaP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two (D : Data G) (hk : D.k = 1)
    (h13 : R16_13_1 D) (h14 : R16_14 D) (h18 : R16_18 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hC : Counterex16 D ⊥ V L hV)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hA : Choice1613 D ⊥ V hV L A)
    (hAg : A ≤ conjSubgroup V g) (hΔ : Concl1617 D ⊥ V hV L A g Δ)
    (h2 : Case168_2 D ⊥ V hV L) (hS : Case168_2Small D ⊥ V hV L)
    (hn4 : ¬ IsLn ↥(lBar ⊥ V hV L) 4 1) {B U : Subgroup G} (hBU : Hyperplane1618 V A B U) :
    (B = A ⊓ preBarSub D.M ⊥ V hV (centralizer ((oddBar D.M ⊥ V hV :
          Subgroup (MulAut (Vtil ⊥ V hV))) : Set (MulAut (Vtil ⊥ V hV)))) ∧
        ∀ b ∈ B, ∀ I ∈ Δ, conjSubgroup I b = I) ∧
      (∀ I ∈ Δ, Nat.card ↥(I ⊓ centralizer (B : Set G)) = 2) ∧
      barSub ⊥ V hV B ∈ calABar 2 D.M ⊥ V hV := by
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  obtain ⟨I₀, I₁, a, hS₀, hchar, hfix, htrans⟩ :=
    s16c167_twenty_two_swap D hC hA hAel hΔ hS
  obtain ⟨B₀, hB₀, hB₀hyp⟩ := s16c167_twenty_hyper hS₀ hAel hV
  have hBB₀ : B = B₀ :=
    s16c167_twenty_two_unique D hk h13 h14 h18 hC hA hAg hΔ h2 hS hBU hB₀hyp
  subst B
  have hBA : B₀ ≤ A := fun x hx => ((hB₀ x).1 hx).1
  have hB₀I₀ : ∀ x ∈ B₀, conjSubgroup I₀ x = I₀ := fun x hx => ((hB₀ x).1 hx).2
  have hpart2a : B₀ = A ⊓ preBarSub D.M ⊥ V hV (centralizer
      ((oddBar D.M ⊥ V hV : Subgroup (MulAut (Vtil ⊥ V hV))) :
        Set (MulAut (Vtil ⊥ V hV)))) := by
    ext x
    rw [hB₀ x, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxA, hxI⟩
      exact ⟨hxA, (hchar x hxA).1 hxI⟩
    · rintro ⟨hxA, hxP⟩
      exact ⟨hxA, (hchar x hxA).2 hxP⟩
  have hpart2b : ∀ b ∈ B₀, ∀ I ∈ Δ, conjSubgroup I b = I := by
    intro b hb I hIΔ
    exact hfix b (hBA hb) (hB₀I₀ b hb) I hIΔ
  have hI : Insp18 D ⊥ V hV L g Δ :=
    s16c167_insp18_case2 D hk hC.setting hC.conc hΔ h2
  have hcap : E3.mQuot U (V ⊓ centralizer (A : Set G)) ≤ 1 :=
    s16c167_twenty_two_cap D hC (h14 ⊥ V L hV hC) hA hAg hΔ hI h2 hS hn4 hBU
  have hU : U = V ⊓ centralizer (B₀ : Set G) := hBU.2.2.1
  have hchain := s16c167_twenty_chain hS₀ hAel hV hB₀ hU (i := 1) hcap
  have hcard₀ : Nat.card ↥(I₀ ⊓ centralizer (B₀ : Set G)) = 2 := by
    have h₁ := hchain.1
    have h₂ := hchain.2
    norm_num at h₂
    omega
  have hpart3 : ∀ I ∈ Δ, Nat.card ↥(I ⊓ centralizer (B₀ : Set G)) = 2 := by
    intro I hIΔ
    rw [htrans B₀ hBA hB₀I₀ I hIΔ]
    exact hcard₀
  have hAT : A ≤ D.T := hA.1.1
  have hBM : B₀ ≤ D.M := hBA.trans (hAT.trans D.sylowM.le)
  have hM : D.M ≤ normalizer (V : Set G) := hC.setting.hyp16.hyp125.normalizer_eq.ge
  have hBst : B₀ ≤ stabTil ⊥ V := fun x hx => s16c167_mem_stabTil_bot (hM (hBM hx))
  have hBel : IsElemAbelian 2 B₀ := B2F.isElemAbelian_mono hBA hAel
  have hA1 : barSub ⊥ V hV B₀ ≠ ⊥ := by
    intro hbot
    obtain ⟨I, hIΔ⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hΔ.1]; norm_num)
    have hIle : I ≤ Subgroup.centralizer (B₀ : Set G) := by
      intro i hi
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbact : actTil ⊥ V hV ⟨b, hBst hb⟩ = 1 := by
        have hmem := actTil_mem_barSub ⊥ V hV hb (hBst hb)
        rw [hbot] at hmem
        exact Subgroup.mem_bot.1 hmem
      have hcomm := (actTil_eq_one_iff ⊥ V hV ⟨b, hBst hb⟩).1 hbact i (hΔ.2.1 I hIΔ hi)
      have h1 : b * i * b⁻¹ * i⁻¹ = 1 := Subgroup.mem_bot.1 hcomm
      calc b * i = (b * i * b⁻¹ * i⁻¹) * (i * b) := by group
        _ = 1 * (i * b) := by rw [h1]
        _ = i * b := by rw [one_mul]
    have hIeq : I ⊓ centralizer (B₀ : Set G) = I := inf_eq_left.2 hIle
    have hcardI : Nat.card ↥I = 2 := by
      rw [← hIeq]
      exact hpart3 I hIΔ
    have hIg : conjSubgroup I g ∈ deltaConj Δ g := ⟨I, hIΔ, rfl⟩
    have hbig := hI.big (conjSubgroup I g) hIg
    rw [hk] at hbig
    have hcardg : Nat.card ↥(conjSubgroup I g) = Nat.card ↥I := by
      rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    have hrkg : rk ↥(conjSubgroup I g) = 1 := by
      unfold rk
      rw [hcardg, hcardI]
      exact padicValNat_self
    omega
  have hhyp : ∀ C : Subgroup G, C ≤ B₀ → E3.mQuot B₀ C = 1 →
      V ⊓ centralizer (C : Set G) = V ⊓ centralizer (B₀ : Set G) := by
    intro C hCB hC1
    by_contra hbad
    obtain ⟨D', hD'hyp, hD'ne⟩ :=
      s16c167_twenty_extend hS₀ hAel hV hB₀ hCB hC1 hbad
    exact hD'ne (s16c167_twenty_two_unique D hk h13 h14 h18 hC hA hAg hΔ h2 hS
      hD'hyp hB₀hyp)
  exact ⟨⟨hpart2a, hpart2b⟩, hpart3,
    s16c167_barSub_mem_calABar_of_hyperplanes (M := D.M) (V₁ := ⊥) (V := V) (A := B₀)
      hV rfl hBM hBst hBel hA1 hhyp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
