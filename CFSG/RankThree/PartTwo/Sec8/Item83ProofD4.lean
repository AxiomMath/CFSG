module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed
public import CFSG.Adapters.TauCetiExceptional.EvenD4

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}


theorem exists_data83_of_trialityD4_model (hcl : Inputs47ClassesD4) (hKF : KF83TrialityD4)
    {A : Subgroup G} {c a : G} (h : Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hLbar : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (E : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  have hn1 : 1 ≤ n := hn.pos
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout := h.inducesOuterTheta
  have hτ3 : inducedAutHom L E ⟨a, ha⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L E ha ha3
  have hτin : ¬ IsInnerAut (inducedAutHom L E ⟨a, ha⟩) :=
    (not_isInnerAut_inducedAutHom_iff L E ha).mpr hout
  obtain ⟨γ, y, hγ, hγy, hy3, hτγ, hcase⟩ : ∃ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsStdGraphFieldConj σ γ ∧ γ y = y ∧ y ^ 3 = 1 ∧
      inducedAutHom L E ⟨a, ha⟩ = γ * MulAut.conj y ∧
      (y = 1 ∨ IsoPGUThree (autFix (inducedAutHom L E ⟨a, ha⟩)) (2 ^ n)) := by
    rcases hcl n hn K σ hK hσ _ hτ3 hτin with hstd | ⟨γ, y, hγ, hγy, hy3, hτγ, hPGU⟩
    · exact ⟨_, 1, hstd, map_one _, one_pow 3, by rw [map_one, mul_one], Or.inl rfl⟩
    · refine ⟨γ, y, hγ, hγy, ?_, hτγ, Or.inr hPGU⟩
      rw [← hy3]
      exact pow_orderOf_eq_one y
  obtain ⟨β, hβ⟩ := hγ
  obtain ⟨e', he'⟩ : ∃ e' : L ⧸ aschbacherSolvableCore 3 L ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom, e' = E.trans β⁻¹ := ⟨_, rfl⟩
  set σ₀ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fieldActor σ σ with hσ₀
  have hβinv : ∀ w, β (β⁻¹ w) = w := fun w => MulAut.apply_inv_self _ _ _
  have hu : σ₀ (β⁻¹ y) = β⁻¹ y := by
    rcases hβ with rfl | rfl
    · have h1 : β (σ₀ (β⁻¹ y)) = y := hγy
      calc σ₀ (β⁻¹ y) = β⁻¹ (β (σ₀ (β⁻¹ y))) := (MulAut.inv_apply_self _ _ _).symm
        _ = β⁻¹ y := by rw [h1]
    · have h1 : β (σ₀⁻¹ (β⁻¹ y)) = y := hγy
      have h2 : σ₀⁻¹ (β⁻¹ y) = β⁻¹ y := by
        calc σ₀⁻¹ (β⁻¹ y) = β⁻¹ (β (σ₀⁻¹ (β⁻¹ y))) := (MulAut.inv_apply_self _ _ _).symm
          _ = β⁻¹ y := by rw [h1]
      calc σ₀ (β⁻¹ y) = σ₀ (σ₀⁻¹ (β⁻¹ y)) := by rw [h2]
        _ = β⁻¹ y := MulAut.apply_inv_self _ _ _
  obtain ⟨z, hz⟩ := (mem_range_trialityG2Incl_iff σ hchar _).mpr hu
  have hinj : Function.Injective (trialityG2Incl σ hchar) := trialityG2Incl_injective σ hchar
  have hz3 : z ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hz, map_one, ← map_pow, hy3, map_one]
  obtain ⟨y₁, y₂, hy₁3, hy₂3, hy, hy₁1, hy₂₁, hzE, ⟨ι⟩⟩ := hKF n hn K σ hchar hK hσ z hz3
  set w₁ := trialityG2Incl σ hchar y₁ with hw₁
  set w₂ := trialityG2Incl σ hchar y₂ with hw₂
  have hwfix : ∀ w ∈ (trialityG2Incl σ hchar).range, σ₀ w = w := fun w hw =>
    (mem_range_trialityG2Incl_iff σ hchar w).mp hw
  have hcommz : ∀ v ∈ Subgroup.closure ({y₁, y₂} : Set (adjointGroup Tag.G2 (fixSubfield σ))),
      v * z = z * v := fun v hv => commute_of_mem_closure_pair hy hy₁3 hy₂3 hv hzE
  have hτ' : inducedAutHom L e' ⟨a, ha⟩ = β⁻¹ * γ * β * MulAut.conj (β⁻¹ y) := by
    rw [he', inducedAutHom_trans, hτγ, mul_assoc, mul_assoc, ← mul_mulAutConj_mul_inv β⁻¹ y,
      inv_inv]
    group
  have hγ' : β⁻¹ * γ * β = σ₀ ∨ β⁻¹ * γ * β = σ₀⁻¹ := by
    rcases hβ with rfl | rfl
    · left
      group
    · right
      group
  have hfix' : ∀ v ∈ Subgroup.closure ({y₁, y₂} : Set (adjointGroup Tag.G2 (fixSubfield σ))),
      inducedAutHom L e' ⟨a, ha⟩ (trialityG2Incl σ hchar v) = trialityG2Incl σ hchar v := by
    intro v hv
    have hc : (trialityG2Incl σ hchar z) * trialityG2Incl σ hchar v *
        (trialityG2Incl σ hchar z)⁻¹ = trialityG2Incl σ hchar v := by
      rw [← map_inv, ← map_mul, ← map_mul, ← hcommz v hv, mul_assoc, mul_inv_cancel, mul_one]
    have hσv : σ₀ (trialityG2Incl σ hchar v) = trialityG2Incl σ hchar v := hwfix _ ⟨v, rfl⟩
    rw [hτ', MulAut.mul_apply, MulAut.conj_apply, ← hz, hc]
    rcases hγ' with h1 | h1
    · rw [h1]
      exact hσv
    · rw [h1]
      calc σ₀⁻¹ (trialityG2Incl σ hchar v) = σ₀⁻¹ (σ₀ (trialityG2Incl σ hchar v)) := by
            rw [hσv]
        _ = _ := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hy₁mem : y₁ ∈ Subgroup.closure ({y₁, y₂} : Set (adjointGroup Tag.G2 (fixSubfield σ))) :=
    Subgroup.subset_closure (by simp)
  have hy₂mem : y₂ ∈ Subgroup.closure ({y₁, y₂} : Set (adjointGroup Tag.G2 (fixSubfield σ))) :=
    Subgroup.subset_closure (by simp)
  have hw₁3 : w₁ ^ 3 = 1 := by rw [hw₁, ← map_pow, hy₁3, map_one]
  have hw₂3 : w₂ ^ 3 = 1 := by rw [hw₂, ← map_pow, hy₂3, map_one]
  have hw : w₁ * w₂ = w₂ * w₁ := by rw [hw₁, hw₂, ← map_mul, ← map_mul, hy]
  have hw₁1 : w₁ ≠ 1 := fun h1 => hy₁1 (hinj (by rw [← hw₁, h1, map_one]))
  have hw₂₁ : w₂ ∉ Subgroup.zpowers w₁ := by
    rintro ⟨j, hj⟩
    exact hy₂₁ ⟨j, hinj (by rw [map_zpow]; exact hj)⟩
  have hne : inSubgroup perfectResidual (Subgroup.centralizer
      ({w₁} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≠ ⊥ := by
    have := nontrivial_projSL_two (m := 3 * n) (by omega)
    exact ne_bot_of_mulEquiv ι
  have hinner : ∀ d : G, d ∈ L → InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
    intro d hdL
    have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
    exact Or.inl (InducesStdKind.triality n hn1 K hK σ hσ ⟨e', hdN, _,
      (inducedAutHom_eq_conj_of_mem e' hdL hdN).symm⟩)
  have huE : β⁻¹ y ∈ Subgroup.closure
      ({w₁, w₂} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have h1 : (Subgroup.closure ({y₁, y₂} : Set (adjointGroup Tag.G2 (fixSubfield σ)))).map
        (trialityG2Incl σ hchar) =
        Subgroup.closure ({w₁, w₂} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [MonoidHom.map_closure, Set.image_pair]
    rw [← h1, ← hz]
    exact ⟨z, hzE, rfl⟩
  refine exists_data83_of_model h e' hZ (hfix' y₁ hy₁mem) (hfix' y₂ hy₂mem) hw₁3 hw₂3 hw hw₁1
    hw₂₁ hne hn hinner ?_
  rintro A₀ d haA hA₀ hlift ⟨κ⟩
  refine Or.inl ⟨Or.inl hLbar, ⟨κ.trans ι⟩, ?_⟩
  rcases hcase with rfl | hPGU
  ·
    left
    refine isoGTwoEven_barCentralizer_of_conj_fieldActor hn1 hK hσ E ha β ?_
    rw [hτγ, map_one, mul_one]
    exact hβ
  ·
    right
    refine ⟨hLbar, ?_, ?_⟩
    · rw [barCentralizer_zpowers_eq_autFix ha]
      obtain ⟨K', hK'f, hK'fin, hK'c, ⟨φ⟩⟩ := hPGU
      exact ⟨K', hK'f, hK'fin, hK'c, ⟨(autFixCongrEquiv E _).symm.trans φ⟩⟩
    · obtain ⟨x, hxA, hxL, hx⟩ := hlift _ huE
      have hxN : x⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.inv_mem _ (Subgroup.le_normalizer hxL)
      have ha₀N : a * x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.mul_mem _ ha hxN
      have hEx : E (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) = y := by
        have h1 : e' (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) =
            β⁻¹ (E (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩)) := by
          rw [he']
          rfl
        rw [hx] at h1
        calc E (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) =
            β (β⁻¹ (E (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩))) := by
              rw [hβinv]
          _ = y := by rw [← h1, hβinv]
      have hindx : inducedAutHom L E ⟨x, Subgroup.le_normalizer hxL⟩ = MulAut.conj y := by
        rw [inducedAutHom_eq_conj_of_mem E hxL, hEx]
      have hind₀ : inducedAutHom L E ⟨a * x⁻¹, ha₀N⟩ = γ := by
        have h1 : (⟨a * x⁻¹, ha₀N⟩ : Subgroup.normalizer (L : Set G)) =
            ⟨a, ha⟩ * (⟨x, Subgroup.le_normalizer hxL⟩)⁻¹ := rfl
        rw [h1, map_mul, map_inv, hindx, hτγ, mul_inv_cancel_right]
      have hγin : ¬ IsInnerAut γ := not_isInnerAut_of_isStdGraphFieldConj hn1 hK hσ ⟨β, hβ⟩
      have hout₀ : InducesOuterTheta (a * x⁻¹) L :=
        (not_isInnerAut_inducedAutHom_iff L E ha₀N).mp (by rw [hind₀]; exact hγin)
      have ha₀A : a * x⁻¹ ∈ A₀ := A₀.mul_mem haA (A₀.inv_mem hxA)
      have ha₀3 : (a * x⁻¹) ^ 3 = 1 := hA₀.2 _ ha₀A
      refine ⟨a * x⁻¹, ha₀A, ?_, InducesStdKind.triality n hn1 K hK σ hσ
        (inducesKindTriality_graphField hn1 hK hσ L ha₀3 hout₀ E),
        isoGTwoEven_barCentralizer_of_conj_fieldActor hn1 hK hσ E ha₀N β (by rw [hind₀]; exact hβ)⟩
      intro h1
      have h2 : (⟨a * x⁻¹, ha₀N⟩ : Subgroup.normalizer (L : Set G)) = 1 := Subtype.ext h1
      rw [h2, map_one] at hind₀
      exact hγin (hind₀ ▸ ⟨1, map_one _⟩)

theorem exists_data83_of_trialityD4
    (hcl : Inputs47ClassesD4) (hKF : KF83TrialityD4) {A : Subgroup G} {c a : G}
    (h : Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hL : ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      q.p = 2 ∧ q.exponent = n ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  obtain ⟨q, hv, hq2, hqe, ⟨e₁⟩⟩ := hL
  have hLbar : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n := ⟨q, hv, hq2, hqe, ⟨e₁⟩⟩
  have hn1 : 1 ≤ n := hn.pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ TwistTag.D4.order := by
    rw [GaloisField.card 2 (3 * n) (by omega), ← pow_mul, mul_comm]
    rfl
  obtain ⟨σ, hσ, -, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hn1
    (GaloisField 2 (3 * n)) hK
  have hKq : Nat.card (GaloisField 2 (3 * n)) = q.card ^ TwistTag.D4.order := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe]
    exact hK
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 _ hKq
    σ.toRingHom (fun x => by rw [TauCeti.PrimePower.card_def, hq2, hqe]; exact hσ x)
  have e₃ := CFSG.TauCetiBridge.Twisted.nativeEquiv (t := TwistTag.D4)
    (σ := σ.toRingHom) Nat.prime_two hn1 hK hσ
  exact exists_data83_of_trialityD4_model hcl hKF h hn hLbar σ hK hσ (e₁.trans (e₂.symm.trans e₃))

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
