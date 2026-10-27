module

public import CFSG.Quasithin.Background.G118CanonNine
public import CFSG.Quasithin.Background.G118CanonNineF2Group
public import CFSG.Quasithin.Background.G118CanonNineF2Omega
public import CFSG.Quasithin.Background.G118CanonNineF2E11
public import CFSG.Quasithin.Background.G118CanonNineF2Gap
public import CFSG.Quasithin.Background.G118Data

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace Canon

@[expose] def G118NineInputF2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ L : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V) (hHI : Invariant (normalClosure Γ L) I)
    (D : E11Data (normalClosure Γ L) I),
    normalClosure Γ L ≤ Γ →
    Module.finrank (ZMod 2) V = 8 → Module.finrank D.F D.U = 2 →
      Nonempty (↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5))) →
      Nonempty (↥(Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ≃*
        Equiv.Perm (Fin 3)) →
      (Nat.card D.F = 2 ∧ ∃ (b c : GaloisField 2 1),
          (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
          IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hHI)
            (StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) b c))) →
      IsG112Nine Γ

@[expose] def G118NineInputF4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ L : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V) (hHI : Invariant (normalClosure Γ L) I)
    (D : E11Data (normalClosure Γ L) I),
    normalClosure Γ L ≤ Γ →
    Module.finrank (ZMod 2) V = 8 → Module.finrank D.F D.U = 2 →
      Nonempty (↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5))) →
      Nonempty (↥(Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ≃*
        Equiv.Perm (Fin 3)) →
      (Nat.card D.F = 4 ∧
          IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hHI)
            (StatedSL 2 (GaloisField 2 2))) →
      IsG112Nine Γ

theorem g118NineInput_of_cases (h2 : G118NineInputF2) (h4 : G118NineInputF4) :
    G118NineInput := by
  unfold G118NineInputF2 G118NineInputF4 at *
  unfold G118NineInput
  intro V _ _ _ Γ L I hHI D hle hd hU hA hC hmod
  rcases hmod with h | h
  · exact h2 V Γ L I hHI D hle hd hU hA hC h
  · exact h4 V Γ L I hHI D hle hd hU hA hC h

section Assembly

open scoped TensorProduct

theorem gap_compat_mul {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {C Dg : Subgroup (GLV V)} (e : ↥C ≃* Equiv.Perm (Fin 3))
    (σ : ↥Dg → Equiv.Perm (Fin 5))
    (ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] ↥(CFSG.Quasithin.permCore 5)))
    (hC : ∀ (c : ↥C) (x : ↥(CFSG.Quasithin.permCore 3)) (a : ↥(CFSG.Quasithin.permCore 5)),
      ψ ((c : GLV V) (ψ.symm (x ⊗ₜ a))) = permActCore 3 (e c) x ⊗ₜ a)
    (hD : ∀ (d : ↥Dg) (x : ↥(CFSG.Quasithin.permCore 3)) (a : ↥(CFSG.Quasithin.permCore 5)),
      ψ ((d : GLV V) (ψ.symm (x ⊗ₜ a))) = x ⊗ₜ permActCore 5 (σ d) a)
    (c : ↥C) (d : ↥Dg) (x : ↥(CFSG.Quasithin.permCore 3)) (a : ↥(CFSG.Quasithin.permCore 5)) :
    ψ (((c : GLV V) * (d : GLV V)) (ψ.symm (x ⊗ₜ a))) =
      permActCore 3 (e c) x ⊗ₜ permActCore 5 (σ d) a := by
  have h1 : (d : GLV V) (ψ.symm (x ⊗ₜ a)) = ψ.symm (x ⊗ₜ permActCore 5 (σ d) a) := by
    rw [← hD d x a, LinearEquiv.symm_apply_apply]
  rw [LinearEquiv.mul_apply, h1, hC c x (permActCore 5 (σ d) a)]

end Assembly

theorem g118NineInputF2_of_gap (T : F2TensorGap) : G118NineInputF2 := by
  unfold G118NineInputF2
  intro V _ _ _ Γ L I hHI D hle hd hU hA hC hmod
  obtain ⟨hF, b, c, hirr, hnat⟩ := hmod
  obtain ⟨φH⟩ := hA
  obtain ⟨e0⟩ := hC
  let e : ↥(F2Group.cC Γ (normalClosure Γ L)) ≃* Equiv.Perm (Fin 3) := e0
  have hN := normalClosure_normal Γ L
  have hnat0 := hnat
  obtain ⟨φ', ψ0, -⟩ := hnat
  have hI4 : Module.finrank (ZMod 2) I = 4 := by
    rw [(F2Omega.psiF2 ψ0).finrank_eq, Module.finrank_fintype_fun_eq_card]
    rfl
  have hfaith := F2E11.faithful_of_E11 hHI D hF hI4 φH
  have hIA5 := F2Omega.isA5Module_of_natural hHI φH hfaith b c hirr hnat0
  have hφI := hIA5
  obtain ⟨φI, -, -⟩ := hφI
  have hcases := F2Group.card_cD_cases hN hle e φI G118.autA5Input
  rcases hcases with h60 | h120
  ·
    let eD := F2Group.eD60 hle φI h60
    let σ : ↥(F2Group.cD Γ (normalClosure Γ L)) → Equiv.Perm (Fin 5) := fun d =>
      ((eD d : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
    obtain ⟨ψ, hCc, hDd⟩ := T V (normalClosure Γ L) I hHI D (F2Group.cC Γ (normalClosure Γ L))
      (F2Group.cD Γ (normalClosure Γ L)) e φI σ hd hU hF
      (fun c hc h hh => (F2Group.mem_cC.1 hc).2 h hh)
      (fun d hd' c hc => (F2Group.mem_cD.1 hd').2 c hc)
      (F2Group.cD_normalizes hN)
      (fun d h g hg => by
        have hgd : g = F2Group.actD hN hle d h := Subtype.ext (by
          rw [F2Group.actD_apply]
          exact hg)
        rw [hgd]
        exact F2Group.eD60_apply hN hle φI h60 d h)
      hIA5
    refine ⟨hd, Or.inr (Or.inl ⟨(F2Group.eΓ hN hle e).trans (MulEquiv.prodCongr e eD), ψ, ?_⟩)⟩
    intro γ a a' b b' ha hb
    have hγ : ((γ : ↥Γ) : GLV V) = ((F2Group.eΓ hN hle e γ).1 : GLV V) *
        ((F2Group.eΓ hN hle e γ).2 : GLV V) := (F2Group.eΓ_prod hN hle e γ).symm
    have ha' : a' = permActCore 3 (e (F2Group.eΓ hN hle e γ).1) a := Subtype.ext ha
    have hb' : b' = permActCore 5 (((eD (F2Group.eΓ hN hle e γ).2 :
        ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))) b := Subtype.ext hb
    rw [hγ, gap_compat_mul e σ ψ hCc hDd]
    rw [ha', hb']
  ·
    have hbij := F2Group.actD_bijective hN hle e φI G118.autA5Input h120
    let eD := F2Group.eD120 hN hle φI G118.autA5Input hbij
    let σ : ↥(F2Group.cD Γ (normalClosure Γ L)) → Equiv.Perm (Fin 5) := fun d => eD d
    obtain ⟨ψ, hCc, hDd⟩ := T V (normalClosure Γ L) I hHI D (F2Group.cC Γ (normalClosure Γ L))
      (F2Group.cD Γ (normalClosure Γ L)) e φI σ hd hU hF
      (fun c hc h hh => (F2Group.mem_cC.1 hc).2 h hh)
      (fun d hd' c hc => (F2Group.mem_cD.1 hd').2 c hc)
      (F2Group.cD_normalizes hN)
      (fun d h g hg => by
        have hgd : g = F2Group.actD hN hle d h := Subtype.ext (by
          rw [F2Group.actD_apply]
          exact hg)
        rw [hgd]
        exact F2Group.eD120_apply hN hle φI G118.autA5Input hbij d h)
      hIA5
    refine ⟨hd, Or.inl ⟨⟨(F2Group.eΓ hN hle e).trans (MulEquiv.prodCongr e eD)⟩,
      Or.inl ⟨(F2Group.eΓ hN hle e).trans (MulEquiv.prodCongr e eD), ψ, ?_⟩⟩⟩
    intro γ a a' b b' ha hb
    have hγ : ((γ : ↥Γ) : GLV V) = ((F2Group.eΓ hN hle e γ).1 : GLV V) *
        ((F2Group.eΓ hN hle e γ).2 : GLV V) := (F2Group.eΓ_prod hN hle e γ).symm
    have ha' : a' = permActCore 3 (e (F2Group.eΓ hN hle e γ).1) a := Subtype.ext ha
    have hb' : b' = permActCore 5 (eD (F2Group.eΓ hN hle e γ).2) b := Subtype.ext hb
    rw [hγ, gap_compat_mul e σ ψ hCc hDd]
    rw [ha', hb']

end Canon

end G11

end CFSG.Quasithin
