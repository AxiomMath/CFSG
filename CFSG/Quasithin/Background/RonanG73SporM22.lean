module

public import CFSG.Quasithin.Background.RonanG73Aut
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.CaseM22Dispatch
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M24
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2Model

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
open CFSG.QuasithinUnique.Setup.Family

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem sporadic_M22 {G L Γ A : Subgroup (GLV V)} {m : ℕ} [Finite ↥G] (h : G93Hyp Γ A L L m)
    (hΓG : Γ ≤ G) (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22)) :
    (Nonempty (↥L ≃* ↥NativeSporadic.M22) ∧ Module.finrank (ZMod 2) V = 10 ∧
        IsMathieu22CodeOrCocode L) ∨
      (Module.finrank (ZMod 2) V = 12 ∧ ∃ N : Subgroup ↥G, N.Normal ∧ N.index = 2 ∧
        IsHat ↥N ↥NativeSporadic.M22) := by
  haveI : Finite (GLV V) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.finite_GLV_of_finite (V := V)
  have hperf : Group.IsPerfect ↥L := ⟨h.L_comp.2.2.1⟩
  obtain ⟨e⟩ := hM
  rcases m22_center_card_odd_cases (odd_card_center_of_irr' h.H_irr) e with h1 | h3
  ·
    left
    have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨hcase, -, -⟩ := case1_M22_case h hZ ⟨e⟩
    rcases hcase with ⟨hg, hd, -, -, hreal⟩ | ⟨⟨f24⟩, hd, -, -, -⟩
    · exact ⟨hg, hd, hreal⟩
    · exfalso
      have h22 : Nat.card ↥L = 443520 := by
        rw [Nat.card_congr (mulEquiv_of_center_eq_bot hZ e).toEquiv]
        exact CFSG.Sporadic.Mathieu.card_M22
      have h24 : Nat.card ↥L = 244823040 := by
        rw [Nat.card_congr f24.toEquiv]
        exact CFSG.Sporadic.Mathieu.card_M24
      omega
  ·
    right
    obtain ⟨hd12, -⟩ := case2_model h e h3
    have hb := h.bound
    obtain ⟨hm5, hAL⟩ := case2_rank h e
    have hm : m = 5 := by omega
    have hAL' : ¬ A ≤ L := hAL hm
    obtain ⟨a, haA, haL⟩ := SetLike.not_le_iff_exists.1 hAL'
    have haG : a ∈ G := hΓG (h.A_le haA)
    have hLn : (L.subgroupOf G).Normal :=
      (Subgroup.normal_subgroupOf_iff hLG).2 fun l g hl hg => hnorm g hg l hl
    have hcQ : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card NativeSporadic.M22 :=
      Nat.card_congr e.toEquiv
    have hLcard : Nat.card ↥L = Nat.card NativeSporadic.M22 * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hcQ, h3]
    have hGle : Nat.card ↥G ≤ 2 * Nat.card ↥L := by
      have h1 := card_le_center_mul_aut hLG hnorm hcent hperf
      rw [h3, Nat.card_congr (MulAut.congr e).toEquiv] at h1
      have h2 : Nat.card (MulAut ↥NativeSporadic.M22) ≤ 2 * Nat.card ↥NativeSporadic.M22 :=
        CFSG.Sporadic.Schreier.m22_mulAut_card
      calc Nat.card ↥G ≤ 3 * Nat.card (MulAut (NativeSporadic.Carrier .M22)) := h1
        _ ≤ 3 * (2 * Nat.card NativeSporadic.M22) := Nat.mul_le_mul_left _ h2
        _ = 2 * Nat.card ↥L := by rw [hLcard]; ring
    have hidx : (L.subgroupOf G).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      exact haL (Subgroup.mem_subgroupOf.1 (h1 ▸ (Subgroup.mem_top (⟨a, haG⟩ : ↥G))))
    have hidx0 : (L.subgroupOf G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hmul := Subgroup.card_mul_index (L.subgroupOf G)
    have hLcard' : Nat.card (L.subgroupOf G) = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    have hle2 : (L.subgroupOf G).index ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have : Nat.card ↥L * 3 ≤ Nat.card ↥G := by
        rw [← hmul, hLcard']
        exact Nat.mul_le_mul_left _ hgt
      omega
    refine ⟨hd12, L.subgroupOf G, hLn, by omega, ?_⟩
    exact CFSG.Quasithin.H.Mathieu.H12Pf.isHat_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLG).symm (isHat_of_hyp h.L_comp.2.2 h3 e)

theorem sporadic_M24 {L Γ A : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M24)) :
    Nonempty (↥L ≃* ↥NativeSporadic.M24) ∧ Module.finrank (ZMod 2) V = 11 ∧
      IsMathieu24CodeOrCocode L := by
  obtain ⟨e⟩ := hM
  obtain ⟨hcase, -, -⟩ := case1_M24_core h ⟨e⟩
  rcases hcase with ⟨⟨f22⟩, hd, -, -, -⟩ | ⟨hg, hd, -, -, hreal⟩
  · exfalso
    have hdvd : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card ↥L :=
      Subgroup.card_quotient_dvd_card _
    have h24 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 :=
      CFSG.Sporadic.Mathieu.card_M24
    have h22 : Nat.card ↥NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
    rw [Nat.card_congr e.toEquiv, Nat.card_congr f22.toEquiv, h24, h22] at hdvd
    omega
  · exact ⟨hg, hd, hreal⟩

end CFSG.Quasithin.RonanG73
