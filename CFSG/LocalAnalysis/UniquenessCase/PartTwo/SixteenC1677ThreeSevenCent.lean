module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s168e3_seven_card_eq_seven {Z K : Subgroup G} (hcyc : IsCyclic ↥K) (hZK : Z ≤ K)
    (hexp : ∀ z ∈ Z, z ^ 7 = 1) (hne : Z ≠ ⊥) : Nat.card Z = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI hKc : IsCyclic ↥K := hcyc
  haveI hZc : IsCyclic ↥Z := Subgroup.isCyclic_of_le hZK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Z)
  have hg7 : g ^ 7 = 1 := Subtype.ext (by simpa using hexp (g : G) g.2)
  have hg1 : g ≠ 1 := by
    intro h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxg : (⟨x, hx⟩ : ↥Z) ∈ Subgroup.zpowers g := hg ⟨x, hx⟩
    rw [Subgroup.zpowers_eq_bot.mpr h] at hxg
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.1 hxg)
  calc Nat.card Z = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    _ = 7 := orderOf_eq_prime hg7 hg1

theorem s168e3_seven_false_of_cent {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {Δ : Fin (2 + 1) → Subgroup (Vtil V₀ V hV)}
    {σ : ↥(Mbar D.M V₀ V hV) →* Equiv.Perm (Fin (2 + 1))}
    (hctx : s16e_d3_Ctx (Mbar D.M V₀ V hV) (lBar V₀ V hV L) 2 Δ σ) {X P : Subgroup G}
    (hXM : D.M ≤ normalizer (X : Set G)) (hXL : barSub V₀ V hV X ≤ lBar V₀ V hV L)
    (hP : CFSG.ABGLocalTools.IsSylowOf 7 P (F11.O2p 7 D.M))
    (hcyc : IsCyclic ↥(P ⊓ F11.CTilde D.M V₀ V))
    (hYexp : ∀ y ∈ F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X), y ^ 7 = 1)
    (hY49 : Nat.card ↥(F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X)) = 49)
    (hYK : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X) ⊓ F11.CTilde D.M V₀ V ≠ ⊥) : False := by
  have hYle : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X) ≤ P ⊓ ⁅D.M, D.M⁆ ⊓ X :=
    (Subgroup.closure_le _).2 fun x hx => hx.1
  have hYP : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X) ≤ P := hYle.trans (inf_le_left.trans inf_le_left)
  have hYX : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X) ≤ X := hYle.trans inf_le_right
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPM : P ≤ D.M := (uc22p22u_sylow_O2p (by norm_num) (by norm_num) hP).1
  have hYM : F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X) ≤ D.M := hYP.trans hPM
  have hMs : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hZ : Nat.card ↥(F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X) ⊓ F11.CTilde D.M V₀ V) = 7 :=
    s168e3_seven_card_eq_seven (K := P ⊓ F11.CTilde D.M V₀ V) hcyc
      (le_inf (inf_le_left.trans hYP) inf_le_right)
      (fun z hz => hYexp z (Subgroup.mem_inf.1 hz).1) hYK
  have hcf := s16h_z3_card_eq_barSub_mul hV hYM hMn (hYM.trans hMs)
  have hbar : Nat.card ↥(barSub V₀ V hV (F11.Omega1p 7 (P ⊓ ⁅D.M, D.M⁆ ⊓ X))) = 7 := by
    rw [hY49, hZ] at hcf
    omega
  exact s168e3_seven_irred hctx ((barSub_mono V₀ V hV hYX).trans hXL) hbar
    (s168e3_seven_barSub_conj hV c.setting.hyp16.hyp125 (by norm_num) (by norm_num) hXM hP)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
