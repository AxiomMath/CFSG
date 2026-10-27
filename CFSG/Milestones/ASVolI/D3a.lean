module

public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918M5
public import CFSG.Quasithin.Background.RonanD34
public import CFSG.Milestones.ASVolI.D1

public section

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

structure D31Base [Finite W] (M Mp T : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  exp : ∀ w : W, w ^ 2 = 1
  qsqtk : IsQuotientOfSQTKTC ↥M
  sylow : IsSylowTwoOf T M
  Mp_le : Mp ≤ M
  Mp_normal : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))
  irr : V ∈ IrrPlus Mp (⊤ : Subgroup W)
  o2inv : ∀ g ∈ pCoreOf 2 (Mp ⊔ T), ∀ v ∈ V, g v ∈ V
  gen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤

@[expose] def D31CaseI (M Mp T L : Subgroup (MulAut W)) : Prop :=
  L ∈ cComp M ∧ CFSG.IsQuasisimple ↥L ∧ Mp = conjClosure L T

@[expose] def D31CaseII (Mp T : Subgroup (MulAut W)) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ IsPGroup p ↥Mp ∧ (frattini ↥Mp).map Mp.subtype < Mp ∧
    ∀ N : Subgroup (MulAut W), N ≤ Mp → (frattini ↥Mp).map Mp.subtype ≤ N →
      (∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N) → N = (frattini ↥Mp).map Mp.subtype ∨ N = Mp

structure HypD31 [Finite W] (M Mp T : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  base : D31Base M Mp T V
  cases : (∃ L : Subgroup (MulAut W), D31CaseI M Mp T L) ∨ ∃ p : ℕ, D31CaseII Mp T p

@[expose] def semisimpleTilde (X : Subgroup (MulAut W)) (S : Subgroup W) : Prop :=
  ∀ J : Subgroup (W ⧸ modFix X S), J ≤ tilde X S S → XMod.IsInv ↥X J →
    ∃ J' : Subgroup (W ⧸ modFix X S), J' ≤ tilde X S S ∧ XMod.IsInv ↥X J' ∧ J ⊓ J' = ⊥ ∧
      J ⊔ J' = tilde X S S

@[expose] def IsHomogComp (X : Subgroup (MulAut W)) (S : Subgroup W) (H : Subgroup (W ⧸ modFix X S)) :
    Prop :=
  ∃ I : Subgroup (W ⧸ modFix X S), I ≤ tilde X S S ∧ XMod.IsIrr ↥X I ∧
    H = ⨆ I' ∈ {I' : Subgroup (W ⧸ modFix X S) | I' ≤ tilde X S S ∧ XMod.IsIrr ↥X I' ∧
      XMod.Iso ↥X I' I}, I'

@[expose] def TransOnHomComps (X B : Subgroup (MulAut W)) (S : Subgroup W) : Prop :=
  ∀ H₁ H₂ : Subgroup W, modFix X S ≤ H₁ → H₁ ≤ S → modFix X S ≤ H₂ → H₂ ≤ S →
    IsHomogComp X S (tilde X S H₁) → IsHomogComp X S (tilde X S H₂) →
    ∃ b ∈ B, H₁.map b.toMonoidHom = H₂

@[expose] def fstarSub {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (CFSG.generalizedFitting ↥H).map H.subtype

@[expose] def IsSemisimpleGp {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  CFSG.layer ↥H = ⊤

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_3_4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T : Subgroup (MulAut W)) (V : Subgroup W),
    HypD31 M Mp T V →
      (pCoreOf 2 M = ⊥ ∧ pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥) ∧
      Mp ⊓ centSub (orbSup T V) ≤ (frattini ↥Mp).map Mp.subtype ∧
      (commSub ⊤ Mp = ⊤ ∧ commSub (orbSup T V) Mp = orbSup T V ∧
        semisimpleTilde Mp ⊤ ∧ semisimpleTilde Mp (orbSup T V) ∧
        TransOnHomComps Mp M ⊤ ∧ TransOnHomComps Mp T (orbSup T V)) ∧
      fixV Mp = ⨆ m ∈ M, (V ⊓ fixV Mp).map m.toMonoidHom ∧
      (fstarSub (autSub (Mp ⊔ T) (orbSup T V)) = autSub Mp (orbSup T V) ∧
        fstarSub (autSub (Mp ⊔ T) V) = autSub Mp V ∧
        (∀ L : Subgroup (MulAut W), D31CaseI M Mp T L →
          IsSemisimpleGp (autSub Mp (orbSup T V)) ∧ IsSemisimpleGp (autSub Mp V)) ∧
        (∀ p : ℕ, D31CaseII Mp T p →
          IsPGroup p ↥(autSub Mp (orbSup T V)) ∧ IsPGroup p ↥(autSub Mp V))) ∧
      (V ⊓ fixV Mp = ⊥ → ∀ x ∈ M, V ⊓ V.map x.toMonoidHom = ⊥ ∨ V.map x.toMonoidHom = V)

section D34Proof

open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}

private theorem d34_core (hD : HypD31 M Mp T V) : RonanD34.Core M Mp T V :=
  ⟨hD.base.exp, hD.base.sylow, hD.base.Mp_le, hD.base.Mp_normal, hD.base.irr, hD.base.o2inv,
    hD.base.gen⟩

private theorem d34_D31 (hD : HypD31 M Mp T V) {L : Subgroup (MulAut W)}
    (hL : D31CaseI M Mp T L) : D31 M Mp T L V :=
  ⟨hD.base.exp, hD.base.qsqtk, hD.base.sylow, hL.1, hL.2.1, hL.2.2, hD.base.Mp_normal,
    hD.base.irr, hD.base.o2inv, hD.base.gen⟩

private theorem d34_one_a (hD : HypD31 M Mp T V) : pCoreOf 2 M = ⊥ := by
  rcases hD.cases with ⟨L, hL⟩ | ⟨p, hp⟩
  · exact D31.pCoreOf_eq_bot (d34_D31 hD hL)
  · exact RonanD34.pCoreOf_eq_bot_of_caseII (d34_core hD) hp

private theorem d34_one_b (hD : HypD31 M Mp T V) :
    pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) = ⊥ := by
  rcases hD.cases with ⟨L, hL⟩ | ⟨p, hp⟩
  · exact D31.pCoreOf_autSub_orbSup_eq_bot (d34_D31 hD hL)
  · exact RonanD34.pCoreOf_autSub_orbSup_eq_bot_of_caseII (d34_core hD) hp

private theorem d34_one_c (hD : HypD31 M Mp T V) : pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥ := by
  rcases hD.cases with ⟨L, hL⟩ | ⟨p, hp⟩
  · exact RonanD34.pCoreOf_autSub_eq_bot_of_caseI (d34_core hD) hL
  · exact RonanD34.pCoreOf_autSub_eq_bot_of_caseII (d34_core hD) hp

private theorem d34_two (hD : HypD31 M Mp T V) :
    Mp ⊓ centSub (orbSup T V) ≤ (frattini ↥Mp).map Mp.subtype := by
  rcases hD.cases with ⟨L, hL⟩ | ⟨p, hp⟩
  · exact RonanD34.le_frattini_of_caseI (d34_core hD) hL
  · exact RonanD34.le_frattini_of_caseII (d34_core hD) hp

private theorem d34_semisimple_top (hD : HypD31 M Mp T V) : semisimpleTilde Mp ⊤ := by
  have h := d34_core hD
  have hgen : (⊤ : Subgroup W) = ⨆ t ∈ M, t • V := by
    simp_rw [RonanD34.smul_eq_map]
    exact h.gen.symm
  exact RonanD34.semisimple_tilde_of_orbit (X := Mp) (T := M) (S := ⊤) (I := V) h.Mp_normal
    (fun _ _ _ _ => trivial) h.irr hgen

private theorem d34_semisimple_orbSup (hD : HypD31 M Mp T V) :
    semisimpleTilde Mp (orbSup T V) := by
  have h := d34_core hD
  have hgen : orbSup T V = ⨆ t ∈ T, t • V := by
    simp_rw [RonanD34.smul_eq_map]
    rfl
  exact RonanD34.semisimple_tilde_of_orbit (X := Mp) (T := T) (S := orbSup T V) (I := V)
    h.T_le_normalizer (fun t ht w hw => mem_orbSup_of_mem_map ht hw)
    ⟨le_orbSup T V, (h.irr).2⟩ hgen

private theorem d34_trans_top (hD : HypD31 M Mp T V) : TransOnHomComps Mp M ⊤ := by
  have h := d34_core hD
  have hgen : (⊤ : Subgroup W) = ⨆ t ∈ M, t • V := by
    simp_rw [RonanD34.smul_eq_map]
    exact h.gen.symm
  intro H₁ H₂ hc₁ hs₁ hc₂ hs₂ hH₁ hH₂
  obtain ⟨t, ht, hteq⟩ := RonanD34.trans_tilde_of_orbit (X := Mp) (T := M) (S := ⊤) (I := V)
    h.Mp_normal (fun _ _ _ _ => trivial) h.irr hgen H₁ H₂ hc₁ hs₁ hc₂ hs₂ hH₁ hH₂
  exact ⟨t, ht, by rw [← hteq, RonanD34.smul_eq_map]⟩

private theorem d34_trans_orbSup (hD : HypD31 M Mp T V) : TransOnHomComps Mp T (orbSup T V) := by
  have h := d34_core hD
  have hgen : orbSup T V = ⨆ t ∈ T, t • V := by
    simp_rw [RonanD34.smul_eq_map]
    rfl
  intro H₁ H₂ hc₁ hs₁ hc₂ hs₂ hH₁ hH₂
  obtain ⟨t, ht, hteq⟩ := RonanD34.trans_tilde_of_orbit (X := Mp) (T := T) (S := orbSup T V)
    (I := V) h.T_le_normalizer (fun t ht w hw => mem_orbSup_of_mem_map ht hw)
    ⟨le_orbSup T V, (h.irr).2⟩ hgen H₁ H₂ hc₁ hs₁ hc₂ hs₂ hH₁ hH₂
  exact ⟨t, ht, by rw [← hteq, RonanD34.smul_eq_map]⟩

private theorem d34_fstar_orbSup (hD : HypD31 M Mp T V) :
    fstarSub (autSub (Mp ⊔ T) (orbSup T V)) = autSub Mp (orbSup T V) := by
  have h := d34_core hD
  refine le_antisymm
    (RonanD34.generalizedFitting_autSub_le h h.Mp_le_stabSub_orbSup (d34_one_b hD)) ?_
  rcases hD.cases with ⟨L, hL⟩ | ⟨p, hp⟩
  · exact RonanD34.autSub_le_generalizedFitting_of_layer h
      (RonanD34.layer_autSub_eq_top h.Mp_le_stabSub_orbSup (RonanD34.layer_Mp_eq_top h hL))
  · exact RonanD34.autSub_le_generalizedFitting_of_pGroup h h.Mp_le_stabSub_orbSup hp.1 hp.2.2.1

private theorem d34_fstar_V (hD : HypD31 M Mp T V) :
    fstarSub (autSub (Mp ⊔ T) V) = autSub Mp V := by
  have h := d34_core hD
  refine le_antisymm
    (RonanD34.generalizedFitting_autSub_le h h.Mp_le_stabSub (d34_one_c hD)) ?_
  rcases hD.cases with ⟨L, hL⟩ | ⟨p, hp⟩
  · exact RonanD34.autSub_le_generalizedFitting_of_layer h
      (RonanD34.layer_autSub_eq_top h.Mp_le_stabSub (RonanD34.layer_Mp_eq_top h hL))
  · exact RonanD34.autSub_le_generalizedFitting_of_pGroup h h.Mp_le_stabSub hp.1 hp.2.2.1

theorem as_D_3_4 : D_3_4 := by
  intro W _ _ M Mp T V hD
  have h := d34_core hD
  refine ⟨⟨d34_one_a hD, d34_one_b hD⟩, d34_two hD,
    ⟨h.commSub_top, h.commSub_orbSup, d34_semisimple_top hD, d34_semisimple_orbSup hD,
      d34_trans_top hD, d34_trans_orbSup hD⟩,
    RonanD34.fixV_eq_iSup_map hD.base.Mp_normal hD.base.irr hD.base.gen,
    ⟨d34_fstar_orbSup hD, d34_fstar_V hD, ?_, ?_⟩, h.ti⟩
  · intro L hL
    exact ⟨RonanD34.layer_autSub_eq_top h.Mp_le_stabSub_orbSup (RonanD34.layer_Mp_eq_top h hL),
      RonanD34.layer_autSub_eq_top h.Mp_le_stabSub (RonanD34.layer_Mp_eq_top h hL)⟩
  · intro p hp
    exact ⟨RonanD34.isPGroup_autSub h.Mp_le_stabSub_orbSup hp.2.2.1,
      RonanD34.isPGroup_autSub h.Mp_le_stabSub hp.2.2.1⟩

end D34Proof

@[expose] def D_3_5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V < orbSup T V →
    (∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g) →
      (Mp = L ∧ ∀ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ ∈ L) ∧
      (IsFFModule (autSub (Mp ⊔ T) V) ∧ fstarSub (autSub (Mp ⊔ T) V) = autSub L V ∧
        CFSG.IsQuasisimple ↥(autSub L V)) ∧
      (orbSup T V ⊓ fixV Mp = ⊥ → ∀ A : Subgroup (MulAut W), A ≤ T →
        autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) → A ≤ stabSub V) ∧
      ((∃ t ∈ T, t ∉ stabSub V) ∧
        ∀ t ∈ T, t ∉ stabSub V →
          (∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V) ∧
            IsSumMod (orbSup T V ⊓ fixV L) V (V.map t.toMonoidHom) (orbSup T V)) ∧
      ((∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
        AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
        BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V ⊥)

end CFSG.ASVolI
