module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLargeFrame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDualFrob
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFive
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC3Roots
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC3FlagFree
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E8Five
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus Certificates.TcRes
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso GGHasLabel GGInnerDiagOn)

section LeafLarge

private theorem tc_rho_eq_wEnd
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E8 L p₀) (w : WeylGroup .E8)
    (hρ : ∀ γ, IsRoot .E8 γ → S.ρ γ = w • γ) (x : Fin Tag.E8.rank → ℤ) :
    S.ρ x = tcrWEnd Tag.E8 w x := by
  let ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ) := AddMonoidHom.mk' (S.ρ : _ → _) (rho_add' S)
  have h1 : ψ x = ∑ j, x j • ψ (Pi.single j 1) := tch_map_decomp ψ x
  have h2 : tcrWEnd Tag.E8 w x = ∑ j, x j • tcrWEnd Tag.E8 w (Pi.single j 1) :=
    tch_map_decomp _ x
  have h3 : ∀ j : Fin Tag.E8.rank, ψ (Pi.single j 1) = tcrWEnd Tag.E8 w (Pi.single j 1) :=
    fun j => hρ _ (isRoot_single .E8 j)
  show ψ x = _
  rw [h1, h2]
  simp only [h3]

theorem false_E8_four_large_of_inputs
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E8 f) (hc : orderOf ((2 : ZMod p) ^ f) = 4) (hp : p ≠ 5) :
    False := by
  classical
  have hpp := h.prime
  have hp2 := h.ne_two
  have : Fact p.Prime := ⟨hpp⟩
  have hp13 : 13 ≤ p := tc_thirteen_le hpp hp2 hp hc
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E8 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hJG : J ≤ G₀ := h.j_comp.1.trans inf_le_left
  have hJperf : commutator ↥J = ⊤ := (Assembly.isComponentOf_iff_open.1 h.j_comp).2.2.1
  have htor : UToralAt .E8 p (Nat.card B) :=
    utoralAt_of_nonTorsion hpp hp2 (fun _ => by omega) (fun _ => hp) Nat.card_pos
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨K, _, _, _, S₁, fr₁, hq, hBT, hρw, a, i, ha, hap, hspan, h2, hfield, hcard⟩ :=
    uframe_dataLarge hR hpp hp2 hmod h.b_norm h.inner_E8 h.b_faithful h.b_elem h.d_le h.d_card
      hJG (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent ⟨t', m, f', hlt, hm⟩ htor
  have hDT : fr₁.DLang D ≤ S₁.D.torus := fr₁.DLang_le_BLang.trans hBT
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang h.b_elem
  have hcard4 : p ^ 4 ≤ Nat.card fr₁.BLang := by
    rw [fr₁.card_BLang]
    exact h.b_card
  have hρ2 := tc_rho_sq_neg_one_E8 hp2 (by omega) S₁ hq hc hBT hBel₁ hcard4
  have he : componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) = 2 :=
    le_antisymm (tc_componentOrbitLength_le_two S₁.ρ (isRootComponent_componentRoots i)
      (fun γ _ => hρ2 γ)) h2
  rw [he] at hfield
  have hpJ : p ∣ Nat.card ↥J := by
    obtain ⟨eJ⟩ := fr₁.exists_tcCenterQuotEquiv hJG hJperf
    exact tc_dvd_card_of_compFieldSL (tc_dvd_two_pow_four_sub_one hpp hc)
      (hfield.of_centerQuotEquiv eJ.symm)
  obtain ⟨P, iJ, x', ix, hP2, hfrob, hJ2, hxP, hx0, hJx, hne, hsplit, hoth, hiJ⟩ :=
    tc_lang_survivors_E8_comp hR2 hG6 h hpJ fr₁ hq hDT hρw a i ha hap hspan h2
  have hrk : 2 ≤ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := by
    have := (Nat.pow_le_pow_iff_right hpp.one_lt).1 (h.b_card.trans hcard)
    omega
  obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := exists_adjacent_of_two_le_finrank
    (isRootComponent_componentRoots i) hrk
  obtain ⟨w, hw⟩ := hρw
  have hρg : ∀ y, S₁.ρ y = tcrWEnd Tag.E8 w y := tc_rho_eq_wEnd S₁ w hw
  have hφ2 : ∀ y, tcrWEnd Tag.E8 w (tcrWEnd Tag.E8 w y) = -y := fun y => by
    rw [← hρg y, ← hρg (S₁.ρ y)]
    exact hρ2 y
  exact tcC3_of_certificate hp13 hc (tcrWEnd Tag.E8 w) (tcrWEnd_iform _)
    (fun γ hγ => IsRoot.smul hγ _) hφ2 S₁.ρ hρg P hP2 hfrob iJ hJ2
    ⟨a₁, hiJ ▸ ha₁, b₁, hiJ ▸ hb₁, hab⟩ hxP hx0 ix hJx hne hsplit hoth

end LeafLarge

end CFSG.StandardType.TableCRes

end
