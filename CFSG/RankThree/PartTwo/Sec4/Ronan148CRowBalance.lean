module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Assembly
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Residuals
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Heisenberg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4Three
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaUFinal
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRow

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut localDeltaIn IsThreeType IsInnDiagThree)

open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs)

open CFSG.HardMathSupport.Timmesfeld.LocalTwo (IsLpEpsIndex)

open CFSG.GH74.GLS (pPrimeCoreOf)

open scoped commutatorElement

section Delta

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {f : G}
    (hA : f ∈ Subgroup.normalizer (A : Set G)) (hB : f ∈ Subgroup.normalizer (B : Set G)) :
    f ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  set φ : G ≃* G := MulAut.conj f with hφ
  have hmap : ∀ C : Subgroup G, f ∈ Subgroup.normalizer (C : Set G) →
      C.map φ.toMonoidHom = C := by
    intro C hC
    ext x
    rw [Subgroup.mem_map_equiv]
    have h := (Subgroup.mem_normalizer_iff.mp hC (φ.symm x))
    have hx : f * (φ.symm x) * f⁻¹ = x := by
      rw [hφ, MulAut.conj_symm_apply]
      group
    rw [hx] at h
    exact h
  have hsup : (A ⊔ B).map φ.toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hmap A hA, hmap B hB]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : f * x * f⁻¹ = φ x := by rw [hφ, MulAut.conj_apply]
  rw [h1]
  conv_rhs => rw [← hsup]
  exact (Subgroup.mem_map_iff_mem φ.injective).symm

variable [Finite G]

theorem le_pPrimeCoreOf_of_le {R K K' : Subgroup G} (hK' : K' ≤ K) (hRK' : R ≤ K')
    (hR : R ≤ pPrimeCoreOf 3 K) : R ≤ pPrimeCoreOf 3 K' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : pPrimeCoreOf 3 K ⊓ K' ≤ pPrimeCoreOf 3 K' := by
    refine Sec14.le_pPrimeCoreOf inf_le_right ?_ ?_
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp
          (Sec14.le_normalizer_pPrimeCoreOf 3 K (hK' hg)) x).mp hx1,
          K'.mul_mem (K'.mul_mem hg hx2) (K'.inv_mem hg)⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp
          (Sec14.le_normalizer_pPrimeCoreOf 3 K (hK' hg)) x).mpr hx1, ?_⟩
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this]
        exact K'.mul_mem (K'.mul_mem (K'.inv_mem hg) hx2) hg
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (Sec14.coprime_card_pPrimeCoreOf 3 K)
  exact fun r hr => hle ⟨hR hr, hRK' hr⟩

end Delta

theorem isElemAbelian_three_of_le {G : Type*} [Group G] {E F : Subgroup G}
    (hF : CFSG.Open.IsElemAbelian 3 F) (h : E ≤ F) : CFSG.Open.IsElemAbelian 3 E := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hF.2 x (h hx)⟩
  apply Subtype.ext
  have h1 := hF.1.is_comm.comm ⟨a, h a.2⟩ ⟨b, h b.2⟩
  have h2 := congrArg Subtype.val h1
  simpa using h2

section Cfg

variable {S : Type} [Group S] [Finite S]

theorem le_localDeltaIn_of_cfg {F E X R : Subgroup (MulAut S)} (hc : CfgS148 S F E X R) :
    E ≤ Subgroup.normalizer ((innerAut S ⊔ R : Subgroup (MulAut S)) : Set (MulAut S)) ∧
      R ≤ localDeltaIn 3 (innerAut S ⊔ R) E := by
  have hinnN : ∀ f : MulAut S, f ∈ Subgroup.normalizer ((innerAut S : Subgroup (MulAut S)) :
      Set (MulAut S)) := by
    intro f
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hn : (innerAut S).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S
    constructor
    · intro hx
      exact hn.conj_mem x hx f
    · intro hx
      have := hn.conj_mem _ hx f⁻¹
      simpa [mul_assoc] using this
  refine ⟨fun f hf => mem_normalizer_sup (hinnN f) (hc.le_normalizer (hc.le hf)), ?_⟩
  have hRX : R ≤ X := by
    obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
      have h9 := hc.card
      rw [hE1, Subgroup.card_bot] at h9
      omega
    exact (hc.le_core e heE he1).trans ((Sec14.pPrimeCoreOf_le 3 _).trans inf_le_left)
  have hHX : innerAut S ⊔ R ≤ X := sup_le hc.inner_le hRX
  unfold localDeltaIn
  refine le_iInf₂ fun e he => le_iInf fun he1 => ?_
  have hR := hc.le_core e he he1
  have hRC : R ≤ Subgroup.centralizer ({e} : Set (MulAut S)) :=
    hR.trans ((Sec14.pPrimeCoreOf_le 3 _).trans inf_le_right)
  exact le_pPrimeCoreOf_of_le (inf_le_inf_right _ hHX) (le_inf le_sup_right hRC) hR

theorem rowS148_of_localTwoBalance (h : IsLocallyBalancedAbs 3 2 S) : RowS148 S := by
  intro F E X R hc
  obtain ⟨hEN, hRΔ⟩ := le_localDeltaIn_of_cfg hc
  have hE : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_three_of_le hc.isE27.1 hc.le
  have h0 := h E hE (by rw [hc.card]; norm_num) (innerAut S ⊔ R) le_sup_left hEN
  exact le_bot_iff.mp (h0 ▸ hRΔ)

theorem rowS148_of_threeType (hq : CFSG.Open.IsQuasisimple S) (h3 : IsThreeType S) :
    RowS148 S := by
  intro F E X R hc
  obtain ⟨hEN, hRΔ⟩ := le_localDeltaIn_of_cfg hc
  by_cases hΔ : localDeltaIn 3 (innerAut S ⊔ R) E = ⊥
  · exact le_bot_iff.mp (hΔ ▸ hRΔ)
  · have hEk : CFSG.HardMathSupport.Solomon.Coordinator.IsEkIn 3 2 ⊤ E :=
      ⟨le_top, isElemAbelian_three_of_le hc.isE27.1 hc.le, by rw [hc.card]; norm_num⟩
    have hinn := HardMathSupport.Solomon.Coordinator.input19_7_3b_of_model
        HardMathSupport.Solomon.Coordinator.psuModel_holds S hq h3 E
      (innerAut S ⊔ R) hEk le_sup_left hEN hΔ
    rw [hc.eq_commutator, Subgroup.commutator_def, eq_bot_iff, Subgroup.closure_le]
    rintro _ ⟨r, hr, f, hf, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    have hmem : ⁅r, f⁆ ∈ R := by
      rw [commutatorElement_def]
      have : r * f * r⁻¹ * f⁻¹ = r * (f * r⁻¹ * f⁻¹) := by group
      rw [this]
      exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hc.le_normalizer hf) _).mp
        (R.inv_mem hr))
    refine hinn _ (hRΔ hmem) ?_
    rw [commutatorElement_def]
    exact CFSG.HardMathSupport.Solomon.Coordinator.input7_autQuotAbelian_holds S hq h3 r f

end Cfg

section Simple

variable {S : Type} [Group S] [Finite S]

theorem isQuasisimple_of_simple_nonab' (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple S := by
  have hZ : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hmem : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
      apply hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hmem, one_mul]
    · exact h
  · haveI := hs
    have e : (S ⧸ Subgroup.center S) ≃* S :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

theorem isThreeType_of_lpEps (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {idx : TauCeti.ValidLieTypeIndex} (hidx : IsLpEpsIndex 3 idx.1)
    (f : S ≃* (TauCeti.CFSGIndex.lie idx).Group) : IsThreeType S := by
  have hZ : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
  have eZ : (S ⧸ Subgroup.center S) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨d, hv⟩ := idx
  rcases hidx with ⟨Q, rfl, -⟩ | ⟨Q, rfl, -⟩
  · haveI : Fact (Nat.Prime Q.p) := ⟨Q.prime_p⟩
    refine Or.inl ⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance, ⟨?_⟩⟩
    exact eZ.trans (f.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (3 - 1) Q hv).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 _)))
  · obtain ⟨-, K, _, _, hK, ⟨g⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (3 - 1) Q hv f
    exact Or.inr ⟨K, inferInstance, inferInstance, Q.p ^ Q.exponent, hK, ⟨eZ.trans g⟩⟩

section Certs


theorem rowS148_of_crossChar (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group)
    (hc : idx.1.characteristic ≠ 3) : RowS148 S := by
  by_cases hexc : ∃ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx'.1 ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx').Group)
  · obtain ⟨idx', hidx', ⟨f⟩⟩ := hexc
    exact rowS148_of_threeType (isQuasisimple_of_simple_nonab' hs hna)
      (isThreeType_of_lpEps hs hna hidx' f)
  · obtain ⟨k, hk⟩ := CFSG.HardMathSupport.Timmesfeld.DefChar.exists_lieFamily idx.1
    have hbal := CFSG.HardMathSupport.Solomon.Coordinator.LocalTwoCrossFam.of_cat
      (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.localTwoCrossFamCat_three_all
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.psuTwoThreeBalance_holds
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.spTwoThreeBalance_holds
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.orthTwoThreeInnerBalance_holds
        (HardMathSupport.Dickson.LocalTwoBalance.Cross.d4TrialityPlaneThreeBalance_of_coreFree
            HardMathSupport.Dickson.LocalTwoBalance.Cross.d4TrialityCoreFree_holds)
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.e6HeisenbergDiagThreeBalance_holds
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.twistedE6HeisenbergDiagThreeBalance_holds
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.triD4InnerThreeBalance_holds
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.triD4OuterThreeBalance_holds
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.reeF4InnerThreeBalance_holds k)
      S hs hna idx hk ⟨e⟩ hc (fun idx' h => ⟨fun g => hexc ⟨idx', h, ⟨g⟩⟩⟩)
    exact rowS148_of_localTwoBalance hbal

end Certs

end Simple

section Certs


theorem rowSOf148_of_crossChar {X : Type} [Group X] (idx : TauCeti.ValidLieTypeIndex)
    (eX : X ≃* (TauCeti.CFSGIndex.lie idx).Group) (hc : idx.1.characteristic ≠ 3) :
    RowSOf148 X :=
  fun _ _ _ hs hna ⟨e⟩ => rowS148_of_crossChar hs hna idx (e.trans eX) hc

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
