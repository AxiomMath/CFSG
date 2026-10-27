module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTriPairAut
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTriSameAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelE
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTransferGen
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
public import CFSG.LieType.HighestRoot.GenModels

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.ClassicalInvolution.Upgrade CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley
  CFSG.LieType.HighestRoot
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgTS_GGLabelIso_triD4 {g g' : ℕ}
    (h : GGLabelIso (⟨.triD4, 0, g'⟩ : LargeEvenLabel) ⟨.triD4, 0, g⟩) : g' = g := by
  rcases h with h | h | h | h | h | h | h | h
  · simpa using h
  · exfalso
    rcases h.1 with h1 | h1
    · have h1' : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.B := h1
      cases h1'
    · have h1' : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.C := h1
      cases h1'
  · exfalso
    have ht : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.D :=
      congrArg LargeEvenLabel.tag h.1
    cases ht
  · exfalso
    have ht : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.A :=
      congrArg LargeEvenLabel.tag h.1
    cases ht
  · exfalso
    have ht : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twD :=
      congrArg LargeEvenLabel.tag h.1
    cases ht
  · exfalso
    have ht : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twA :=
      congrArg LargeEvenLabel.tag h.1
    cases ht
  · exfalso
    have ht : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twD :=
      congrArg LargeEvenLabel.tag h.1
    cases ht
  · exfalso
    have ht : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twD :=
      congrArg LargeEvenLabel.tag h.1
    cases ht

theorem irg_tri_same
    {X : Type} [Group X] {J R Rm : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    (hright : ∃ (F' : Type) (_ : Field F') (_ : Finite F') (σ' : F' →+* F') (g' : ℕ)
      (β' : Fin (triD4Universal F' σ').D.rank → ℤ), TriField F' σ' g' ∧
        GGLongRoot (triD4Universal F' σ').D β' ∧ GGRootPairVia (triD4Universal F' σ') J R Rm β')
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (φ : (triD4Universal F σ).K →* X) (hr : φ.range = J)
    (hk : φ.ker ≤ Subgroup.center (triD4Universal F σ).K) :
    ∃ (β : Fin (triD4Universal F σ).D.rank → ℤ) (u : (triD4Universal F σ).K),
      β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β ∧
      R = ggRootSub (triD4Universal F σ).D φ β u ∧
        Rm = ggRootSub (triD4Universal F σ).D φ (-β) u := by
  obtain ⟨F', hF', hFin', σ', g', β', hT', hlong', hvia⟩ := hright
  letI : Field F' := hF'
  letI : Finite F' := hFin'
  letI : Fintype F' := Fintype.ofFinite F'
  letI : Fintype F := Fintype.ofFinite F
  haveI : Finite (ModGL d4 F) := inferInstance
  haveI : Finite (triD4Universal F σ).K := (inferInstance : Finite ↥(twistedGroup σ))
  obtain ⟨ψ', hr', hk', u'', hR', hRm'⟩ := hvia
  have hcenter' : Subgroup.center (triD4Universal F' σ').K = ⊥ :=
    CFSG.ClassicalInvolution.RouteD.center_twistedGroup_eq_bot_of_card σ' Nat.prime_two
      hT'.1 hT'.2.1 hT'.2.2
  have hcenter : Subgroup.center (triD4Universal F σ).K = ⊥ :=
    CFSG.ClassicalInvolution.RouteD.center_twistedGroup_eq_bot_of_card σ Nat.prime_two
      hT.1 hT.2.1 hT.2.2
  have hker' : ψ'.ker = ⊥ := le_bot_iff.mp (hk'.trans (le_of_eq hcenter'))
  have hker : φ.ker = ⊥ := le_bot_iff.mp (hk.trans (le_of_eq hcenter))
  have hψ'inj : Function.Injective ψ' := (MonoidHom.ker_eq_bot_iff ψ').mp hker'
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hlab' : GGHasLabel (⟨.triD4, 0, g'⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) := irg_hasLabel_tri hqs hT' ψ' hr' hk'
  have hlab : GGHasLabel (⟨.triD4, 0, g⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) := irg_hasLabel_tri hqs hT φ hr hk
  have hiso : GGLabelIso (⟨.triD4, 0, g'⟩ : LargeEvenLabel) ⟨.triD4, 0, g⟩ :=
    ggLabelRigidInput_holds (⟨.triD4, 0, g'⟩ : LargeEvenLabel) (⟨.triD4, 0, g⟩ : LargeEvenLabel)
      (↥J ⧸ Subgroup.center ↥J) (by exact ⟨hT'.1, rfl⟩) (by exact ⟨hT.1, rfl⟩) hlab' hlab
  have hgg : g' = g := irgTS_GGLabelIso_triD4 hiso
  have hcardF : Nat.card F' = Nat.card F := by rw [hT'.2.1, hT.2.1, hgg]
  let e : F' ≃+* F := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hcardF
  have heσ : ∀ c, e (σ' c) = σ (e c) := by
    intro c
    rw [hT'.2.2 c, map_pow, hT.2.2 (e c), hgg]
  let ι : (triD4Universal F' σ').K ≃* (triD4Universal F σ).K :=
    irgTS_twistedCongr (K := F') (L := F) (σK := σ') (σL := σ) e heσ
  have hrootGen : ∀ β, IsRoot .G2 β →
      (twistedRootGroup σ' β).map ι.toMonoidHom = twistedRootGroup σ β :=
    irgTS_exists_rootCompat_equiv (K := F') (L := F) (σK := σ') (σL := σ) e heσ
  have hβ'mem' : β' ∈ (triD4Universal F' σ').D.roots := by
    obtain ⟨w, γ₀, hγ₀, -, hγ⟩ := hlong'
    rw [hγ]
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w
  have hβ'root : IsRoot .G2 β' := by
    have h : β' ∈ (twistedDatum σ').roots := hβ'mem'
    rwa [twistedDatum_roots] at h
  have hP : β' ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β' :=
    ⟨hβ'mem', hlong'⟩
  let φ'' : (triD4Universal F σ).K →* X := ψ'.comp ι.symm.toMonoidHom
  have hr'' : φ''.range = φ.range := by
    have hrange : φ''.range = ψ'.range := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        exact ⟨ι.symm y, rfl⟩
      · rintro x ⟨z, rfl⟩
        exact ⟨ι z, by simp [φ'']⟩
    exact hrange.trans (hr'.trans hr.symm)
  have hφ''inj : Function.Injective φ'' := hψ'inj.comp ι.symm.injective
  have hker'' : φ''.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ'').mpr hφ''inj
  have hk'' : φ''.ker ≤ Subgroup.center (triD4Universal F σ).K := hker''.le.trans bot_le
  have hchar : CharP F 2 := by
    have hKp : Nat.card F = 2 ^ (3 * g) := by
      rw [hT.2.1]
      conv_lhs => rw [← pow_mul, Nat.mul_comm]
    have hg1 : 1 ≤ g := hT.1
    have hk : 1 ≤ 3 * g := by omega
    exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (p := 2) (k := 3 * g) Nat.prime_two hk hKp
  letI : CharP F 2 := hchar
  have hσ3 : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hT.2.1 hT.2.2
  have hP2 : ∀ β : Fin (triD4Universal F σ).D.rank → ℤ,
      (β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β) →
      IsPGroup 2 ((triD4Universal F σ).D.rootGroup β) ∧
      IsPGroup 2 ((triD4Universal F σ).D.rootGroup (-β)) := by
    intro β hβ
    obtain ⟨hβroot, -⟩ := hβ
    have hβroot' : IsRoot .G2 β := by
      have h : β ∈ (twistedDatum σ).roots := hβroot
      rwa [twistedDatum_roots] at h
    exact ⟨isPGroup_twistedD4_rootGroup σ hσ3 hβroot',
      isPGroup_twistedD4_rootGroup σ hσ3 (CFSG.LieType.Chevalley.IsRoot.neg hβroot')⟩
  have hperf : commutator ↥(twistedGroup σ) = ⊤ :=
    Group.isPerfect_def.1 (twistedGroup_isPerfect_of_card (K := F) (σ := σ) (q := 2 ^ g)
      (by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hT.1) hT.2.1 hT.2.2)
  have hodd : Odd (Nat.card (Subgroup.center (triD4Universal F σ).K)) := by
    rw [hcenter]
    simp
  have hM : ∀ θ : MulAut ((triD4Universal F σ).K ⧸
        Subgroup.center (triD4Universal F σ).K),
      ∀ β' : Fin (triD4Universal F σ).D.rank → ℤ,
        β' ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β' →
      ∀ u' : (triD4Universal F σ).K,
      ∃ β : Fin (triD4Universal F σ).D.rank → ℤ,
        (β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β) ∧
        ∃ u : (triD4Universal F σ).K,
          (ggRootSub (triD4Universal F σ).D
              (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) β' u').map
                θ.toMonoidHom =
            ggRootSub (triD4Universal F σ).D
              (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) β u ∧
          (ggRootSub (triD4Universal F σ).D
              (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) (-β') u').map
                θ.toMonoidHom =
            ggRootSub (triD4Universal F σ).D
              (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) (-β) u :=
    fun θ β' hβ' u' => irgTri_pairAut hT θ hβ' u'
  obtain ⟨β₀, hQ, u, hEq, hEqm⟩ :=
    irg_transfer_gen (K := (triD4Universal F σ).K) (D := (triD4Universal F σ).D)
      hperf hodd
      (fun β => β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β)
      (fun β => β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β)
      hP2 hP2 hM φ φ'' hr'' hk hk'' hP (ι u'')
  have hrootβ : (((triD4Universal F' σ').D).rootGroup β').map ι.toMonoidHom =
      ((triD4Universal F σ).D).rootGroup β' :=
    hrootGen β' hβ'root
  have hRtrans : ggRootSub (triD4Universal F' σ').D ψ' β' u'' =
      ggRootSub (triD4Universal F σ).D φ'' β' (ι u'') := by
    have h1 : ((((triD4Universal F' σ').D).rootGroup β').map
          (MulAut.conj u'').toMonoidHom).map ι.toMonoidHom =
        ((((triD4Universal F σ).D).rootGroup β')).map
          (MulAut.conj (ι u'')).toMonoidHom := by
      rw [Subgroup.map_map]
      rw [show ι.toMonoidHom.comp (MulAut.conj u'').toMonoidHom =
          (MulAut.conj (ι u'')).toMonoidHom.comp ι.toMonoidHom from by
        ext x; simp [MulAut.conj_apply, map_mul, map_inv]]
      rw [← Subgroup.map_map, hrootβ]
    calc ggRootSub (triD4Universal F' σ').D ψ' β' u''
        = ((((triD4Universal F' σ').D).rootGroup β').map
            (MulAut.conj u'').toMonoidHom).map ψ' := rfl
      _ = (((((triD4Universal F' σ').D).rootGroup β').map
            (MulAut.conj u'').toMonoidHom).map ι.toMonoidHom).map φ'' := by
          conv_rhs => rw [Subgroup.map_map]
          congr 1
          ext x
          simp [φ'']
      _ = ((((triD4Universal F σ).D).rootGroup β').map
            (MulAut.conj (ι u'')).toMonoidHom).map φ'' := by rw [h1]
      _ = ggRootSub (triD4Universal F σ).D φ'' β' (ι u'') := rfl
  have hRmtrans : ggRootSub (triD4Universal F' σ').D ψ' (-β') u'' =
      ggRootSub (triD4Universal F σ).D φ'' (-β') (ι u'') := by
    have hrootβn : (((triD4Universal F' σ').D).rootGroup (-β')).map ι.toMonoidHom =
        ((triD4Universal F σ).D).rootGroup (-β') := by
      exact hrootGen (-β') (CFSG.LieType.Chevalley.IsRoot.neg hβ'root)
    have h1 : ((((triD4Universal F' σ').D).rootGroup (-β')).map
          (MulAut.conj u'').toMonoidHom).map ι.toMonoidHom =
        ((((triD4Universal F σ).D).rootGroup (-β'))).map
          (MulAut.conj (ι u'')).toMonoidHom := by
      rw [Subgroup.map_map]
      rw [show ι.toMonoidHom.comp (MulAut.conj u'').toMonoidHom =
          (MulAut.conj (ι u'')).toMonoidHom.comp ι.toMonoidHom from by
        ext x; simp [MulAut.conj_apply, map_mul, map_inv]]
      rw [← Subgroup.map_map, hrootβn]
    calc ggRootSub (triD4Universal F' σ').D ψ' (-β') u''
        = ((((triD4Universal F' σ').D).rootGroup (-β')).map
            (MulAut.conj u'').toMonoidHom).map ψ' := rfl
      _ = (((((triD4Universal F' σ').D).rootGroup (-β')).map
            (MulAut.conj u'').toMonoidHom).map ι.toMonoidHom).map φ'' := by
          conv_rhs => rw [Subgroup.map_map]
          congr 1
          ext x
          simp [φ'']
      _ = ((((triD4Universal F σ).D).rootGroup (-β')).map
            (MulAut.conj (ι u'')).toMonoidHom).map φ'' := by rw [h1]
      _ = ggRootSub (triD4Universal F σ).D φ'' (-β') (ι u'') := rfl
  refine ⟨β₀, u, hQ.1, hQ.2, ?_, ?_⟩
  · rw [hR', hRtrans, hEq]
  · exact (hRm'.trans hRmtrans).trans hEqm

end CFSG.StandardType.RCKRP
