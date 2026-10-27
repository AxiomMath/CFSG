module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4Sub
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcTwE6
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOuter
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularInputs
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE6Outer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6F4

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.Burgoyne.E2 (twE6SignAut)


theorem exists_rElement_fixed_twE6Graph_inv
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) (hK2 : ringChar K ≠ 2)
    (h : ↥(twistedE6RootGroup K σ)) (hh : h ^ 2 = 1)
    (hσh : fieldActor (t := TwistTag.E6) σ σ h = h) :
    ∃ u : ↥(twistedE6RootGroup K σ), u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      Commute u h ∧ fieldActor (t := TwistTag.E6) σ σ u = u := by
  classical
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra hq
    push Not at hq
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  set p := ringChar K with hp_def
  have hp2 : p ≠ 2 := hK2
  have hK' : Nat.card K = (p ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ c, hqf]
  have : Fintype K := Fintype.ofFinite K
  have hσσ : ∀ c, σ (σ c) = c := by
    intro c
    rw [hσ (σ c), hσ c, ← pow_mul, show q * q = Nat.card K by rw [hK, pow_two],
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨-, -, -, -, -, -, hfield, -, -, hdiag, -, -, -, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hpr hp2 hf1 K hK' σ hσ'
  have hσentry : Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.E6.tag K) =
      (h : ModGL TwistTag.E6.tag K) := by
    rw [← hfield σ h, hσh]
  have hC : (h : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom h.2).1
  have hΓ : (h : ModGL TwistTag.E6.tag K) ∈ entrywiseFixedGroup .E6 σ :=
    mem_entrywiseFixedGroup.2 ⟨hC, hσentry⟩
  rw [CFSG.SeitzReduction.E6Pilot.entrywiseFixedGroup_eq_fixedFieldImage_E6 σ hσσ] at hΓ
  obtain ⟨h₀, hh₀C, hh₀eq⟩ := Subgroup.mem_map.1 hΓ
  let h₁ : ModGL TwistTag.E6.tag (fixSubfield σ) := h₀
  have hh₁C : h₁ ∈ adjointGroup TwistTag.E6.tag (fixSubfield σ) := hh₀C
  have hh₁eq : baseChangeGL (fixSubfield σ).subtype h₁ =
      (h : ModGL TwistTag.E6.tag K) := hh₀eq
  have hh₁sq : h₁ ^ 2 = 1 := by
    apply baseChangeGL_injective (f := (fixSubfield σ).subtype)
    rw [map_pow, map_one, hh₁eq]
    simpa using congrArg Subtype.val hh
  have hdiagK : diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) =
      (h : ModGL TwistTag.E6.tag K) * diagramMap TwistTag.E6 K := by
    have h1 : diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹ = (h : ModGL TwistTag.E6.tag K) := by
      rw [← hdiag h]
      exact congrArg Subtype.val hσh
    calc diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) =
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * diagramMap TwistTag.E6 K := by group
      _ = (h : ModGL TwistTag.E6.tag K) * diagramMap TwistTag.E6 K := by rw [h1]
  have hdiag₁ : diagramMap TwistTag.E6 (fixSubfield σ) * h₁ =
      h₁ * diagramMap TwistTag.E6 (fixSubfield σ) := by
    apply baseChangeGL_injective (f := (fixSubfield σ).subtype)
    rw [map_mul, map_mul, baseChangeGL_diagramMap (fixSubfield σ).subtype TwistTag.E6,
      hh₁eq]
    exact hdiagK
  have hh₁ : (⟨h₁, hh₁C⟩ : ↥(adjointGroup TwistTag.E6.tag (fixSubfield σ))) ^ 2 = 1 :=
    Subtype.ext (by simpa using hh₁sq)
  have hγ₁ : diagramConjAut TwistTag.E6 (fixSubfield σ) ⟨h₁, hh₁C⟩ = ⟨h₁, hh₁C⟩ := by
    apply Subtype.ext
    rw [coe_diagramConjAut]
    change diagramMap TwistTag.E6 (fixSubfield σ) * h₁ *
      (diagramMap TwistTag.E6 (fixSubfield σ))⁻¹ = h₁
    rw [hdiag₁, mul_inv_cancel_right]
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := ringChar_fixSubfield_ne_two hK2 σ
  obtain ⟨u₀, hu₀1, ⟨n, hu₀n⟩, hu₀comm, hu₀fix⟩ :=
    exists_rElement_fixed_graph_inv (K := ↥(fixSubfield σ)) hk2 ⟨h₁, hh₁C⟩ hh₁ hγ₁
  have hkchar : ringChar (fixSubfield σ) = ringChar K := by
    have h1 : CharP K (ringChar K) := ringChar.charP K
    have h2 : CharP (fixSubfield σ) (ringChar K) :=
      ((fixSubfield σ).subtype.charP_iff Subtype.val_injective _).2 inferInstance
    exact ringChar.eq _ _
  have hu₀n' : u₀ ^ (ringChar K ^ n) = 1 := by
    rw [← hkchar]
    exact hu₀n
  have hu₀diag : diagramMap TwistTag.E6 (fixSubfield σ) * (u₀ : ModGL TwistTag.E6.tag _) =
      (u₀ : ModGL TwistTag.E6.tag _) * diagramMap TwistTag.E6 (fixSubfield σ) := by
    have h1 : diagramMap TwistTag.E6 (fixSubfield σ) * (u₀ : ModGL TwistTag.E6.tag _) *
        (diagramMap TwistTag.E6 (fixSubfield σ))⁻¹ = (u₀ : ModGL TwistTag.E6.tag _) := by
      have h2 := congrArg Subtype.val hu₀fix
      rwa [coe_diagramConjAut] at h2
    calc diagramMap TwistTag.E6 (fixSubfield σ) * (u₀ : ModGL TwistTag.E6.tag _) =
          diagramMap TwistTag.E6 (fixSubfield σ) * (u₀ : ModGL TwistTag.E6.tag _) *
            (diagramMap TwistTag.E6 (fixSubfield σ))⁻¹ *
              diagramMap TwistTag.E6 (fixSubfield σ) := by group
      _ = (u₀ : ModGL TwistTag.E6.tag _) * diagramMap TwistTag.E6 (fixSubfield σ) := by
            rw [h1]
  let u : ModGL TwistTag.E6.tag K := baseChangeGL (fixSubfield σ).subtype u₀
  have huF4 : u ∈ CFSG.ComponentClassification.Burgoyne.E2.twE6F4Image σ :=
    Subgroup.mem_map_of_mem _ ((mem_twistedFixedGroup_id_iff).2 ⟨u₀.2, hu₀diag⟩)
  have huC : u ∈ twistedE6RootGroup K σ :=
    CFSG.ComponentClassification.Burgoyne.E2.twE6F4Image_le_graphFixedRootGroup σ huF4
  have huM : diagramMap TwistTag.E6 K * u = u * diagramMap TwistTag.E6 K :=
    (mem_twistedFixedGroup_id_iff.1
      ((CFSG.ComponentClassification.Burgoyne.E2.twE6F4Image_le σ huF4).1)).2
  have hcomm : (⟨u, huC⟩ : ↥(twistedE6RootGroup K σ)) * h = h * ⟨u, huC⟩ := by
    apply Subtype.ext
    change u * (h : ModGL TwistTag.E6.tag K) = (h : ModGL TwistTag.E6.tag K) * u
    have h2 := congrArg Subtype.val hu₀comm.eq
    have h1 := congrArg (baseChangeGL (fixSubfield σ).subtype) h2
    simpa [hh₁eq] using h1
  have hfix : fieldActor (t := TwistTag.E6) σ σ ⟨u, huC⟩ = ⟨u, huC⟩ := by
    apply Subtype.ext
    rw [hdiag ⟨u, huC⟩]
    change diagramMap TwistTag.E6 K * u * (diagramMap TwistTag.E6 K)⁻¹ = u
    rw [huM, mul_inv_cancel_right]
  refine ⟨⟨u, huC⟩, ?_, ⟨n, ?_⟩, (commute_iff_eq _ _).mpr hcomm, hfix⟩
  · intro hu1
    apply hu₀1
    apply Subtype.ext
    apply baseChangeGL_injective (f := (fixSubfield σ).subtype)
    simpa using congrArg Subtype.val hu1
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change u ^ (ringChar K ^ n) = 1
    have hu₀n'' : (↑u₀ : ModGL TwistTag.E6.tag (fixSubfield σ)) ^ (ringChar K ^ n) = 1 := by
      simpa using congrArg Subtype.val hu₀n'
    rw [show u = baseChangeGL (fixSubfield σ).subtype u₀ from rfl, ← map_pow, hu₀n'', map_one]


theorem exists_fixed_rElement_four_twistedE6_or_signedGraph
    {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (q : ℕ) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (hK2 : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    (∃ y : ↥(twistedE6RootGroup K σ), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y) ∨
    ∃ (x : MulAut ↥(twistedE6RootGroup K σ)) (h : ↥(twistedE6RootGroup K σ))
      (δ δ' : MulAut ↥(twistedE6RootGroup K σ)),
      x ∈ E ∧ MulAut.conj h ∈ E ∧ h ≠ 1 ∧ h ^ 2 = 1 ∧ x h = h ∧
      δ * x * δ⁻¹ = twE6SignAut σ ∧ δ' * (x * MulAut.conj h) * δ'⁻¹ = twE6SignAut σ := by
  classical
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_pow_ringChar_of_card_sq K q hK hq2
  set p := ringChar K with hp_def
  have hp2 : p ≠ 2 := hK2
  have hK' : Nat.card K = (p ^ f) ^ 2 := by rw [hK, hqf]
  have hσ' : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ c, hqf]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hpow3, -⟩, -, -, hcenter, -, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hpr hp2 hf1 K hK' σ hσ'
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have : Finite (MulAut ↥(twistedE6RootGroup K σ)) :=
    Finite.of_injective (fun e : MulAut ↥(twistedE6RootGroup K σ) => (e : _ → _))
      DFunLike.coe_injective
  have hZ : ∀ c : ↥(twistedE6RootGroup K σ), MulAut.conj c = 1 → c = 1 := by
    intro c hc
    have hcZ : c ∈ Subgroup.center ↥(twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : c * g * c⁻¹ = g := by
        have := congrArg (fun φ : MulAut ↥(twistedE6RootGroup K σ) => φ g) hc
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * c = c * g * c⁻¹ * c := by rw [h1]
        _ = c * g := by group
    rwa [hcenter, Subgroup.mem_bot] at hcZ
  have hconj : Function.Injective
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) :=
    (injective_iff_map_eq_one _).2 hZ
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := hE.2
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinnker : ∀ e : MulAut ↥(twistedE6RootGroup K σ), e ∈ Θ.ker → e ^ 2 = 1 →
      e ∈ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range := by
    intro e he he2
    have heK : e ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker]; exact he
    let ē : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
        (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ) :=
      QuotientGroup.mk ⟨e, heK⟩
    have hē2 : ē ^ 2 = 1 := by
      have h1 : (⟨e, heK⟩ : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ)) ^ 2 = 1 :=
        Subtype.ext (by simpa using he2)
      rw [show ē = QuotientGroup.mk'
          ((twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ))
          ⟨e, heK⟩ from rfl, ← map_pow, h1, map_one]
    have hē3 : ē ^ 3 = 1 := hpow3 ē
    have hē1 : ē = 1 := by
      calc ē = ē ^ 3 * (ē ^ 2)⁻¹ := by group
        _ = 1 := by rw [hē3, hē2, one_mul, inv_one]
    have hmem : (⟨e, heK⟩ : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ)) ∈
        (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ) :=
      (QuotientGroup.eq_one_iff
        (⟨e, heK⟩ : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ))).mp hē1
    exact Subgroup.mem_subgroupOf.1 hmem
  have hfix_of_two : ∀ {y : MulAut ↥(twistedE6RootGroup K σ)}
      {g a : ↥(twistedE6RootGroup K σ)},
      y ∈ E → MulAut.conj g ∈ E → y ^ 2 = 1 → (MulAut.conj g) ^ 2 = 1 →
      y * MulAut.conj g = MulAut.conj g * y → y ≠ 1 → MulAut.conj g ≠ 1 →
      MulAut.conj g ≠ y → y a = a → MulAut.conj g a = a → ∀ e ∈ E, e a = a := by
    intro y g a hyE hgE hy2 hg2 hcomm' hy1 hg1 hne hfixy hfixg
    obtain ⟨hmem, -, -, hcard⟩ :=
      CFSG.GH74.GLS.Stage1.Main.four_of_invols
        (by rw [← sq]; exact hg2) (by rw [← sq]; exact hy2) hcomm'.symm hg1 hy1 hne
    have hEeq : zpowers (MulAut.conj g) ⊔ zpowers y = E :=
      Subgroup.eq_of_le_of_card_ge
        (sup_le (zpowers_le.2 hgE) (zpowers_le.2 hyE))
        (by rw [hcard, h4])
    intro e he
    rw [← hEeq] at he
    rcases hmem e he with rfl | rfl | rfl | rfl
    · rfl
    · exact hfixg
    · exact hfixy
    · rw [MulAut.mul_apply, hfixy, hfixg]
  by_cases hin : ∀ e ∈ E, e ∈ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range
  ·
    set A := E.comap (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _) with hA
    have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha =>
      hconj (by rw [map_pow, map_one]; exact hE2 _ ha)
    have hAcard : Nat.card A = 2 ^ 2 := by
      have hmap : A.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _) = E :=
        Subgroup.map_comap_eq_self fun e he => hin e he
      rw [← Subgroup.card_map_of_injective hconj, hmap, h4]
      norm_num
    let A' : Subgroup (ModGL TwistTag.E6.tag K) := A.map (twistedE6RootGroup K σ).subtype
    have hA'C : A' ≤ twistedE6RootGroup K σ := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hA'2 : ∀ a ∈ A', a ^ 2 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      simpa using congrArg Subtype.val (hA2 a ha)
    have hA'card : Nat.card A' = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective (twistedE6RootGroup K σ).subtype_injective, hAcard]
    obtain ⟨u, huC, hu1, hun, hucomm⟩ :=
      exists_rElement_commute_four_twistedE6 σ q hσ hK hK2 hA'C hA'2 hA'card
    refine Or.inl ⟨⟨u, huC⟩, ?_, ?_, ?_⟩
    · intro hc
      exact hu1 (congrArg Subtype.val hc)
    · obtain ⟨n, hn⟩ := hun
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · intro e he
      obtain ⟨c, rfl⟩ := hin e he
      have hc : c ∈ A := he
      have hcomm := hucomm (c : ModGL TwistTag.E6.tag K)
        (Subgroup.mem_map_of_mem (twistedE6RootGroup K σ).subtype hc)
      apply Subtype.ext
      rw [MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hcomm.eq, mul_inv_cancel_right]
  ·
    obtain ⟨x, hxE, hx⟩ :
        ∃ x ∈ E, x ∉ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range := by
      by_contra hne
      exact hin fun e he => by_contra fun h => hne ⟨e, he, h⟩
    have hx2 : x ^ 2 = 1 := hE2 x hxE
    obtain ⟨h, hh1, hhE⟩ : ∃ h : ↥(twistedE6RootGroup K σ), h ≠ 1 ∧ MulAut.conj h ∈ E := by
      have hfin : Fintype K := Fintype.ofFinite K
      obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
      have hKc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
      obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hKc
      have hAutFin : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
        DFunLike.coe_injective
      have hAutFintype : Fintype (RingAut K) := Fintype.ofFinite _
      have hRootFin : Finite {γ : RingAut K // γ ^ 2 = 1} := Subtype.finite
      have hH : Nat.card {γ : RingAut K // γ ^ 2 = 1} ≤ 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
      have hEfin : Finite E := Subtype.finite
      obtain ⟨a, b, hab, hθab⟩ :=
        CFSG.HardMathSupport.Lang.E6Descent.exists_ne_map_eq_of_plane Nat.prime_two Θ hH E
          hE2 (by rw [h4]; norm_num)
      have hmem : (a : MulAut ↥(twistedE6RootGroup K σ))⁻¹ * b ∈ Θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hθab, inv_mul_cancel]
      have he2 : ((a : MulAut ↥(twistedE6RootGroup K σ))⁻¹ * b) ^ 2 = 1 :=
        hE2 _ (E.mul_mem (E.inv_mem a.2) b.2)
      obtain ⟨h, hh⟩ := hinnker _ hmem he2
      refine ⟨h, ?_, ?_⟩
      · rintro rfl
        rw [map_one] at hh
        apply hab
        refine Subtype.ext ?_
        have h1 := congrArg (fun z => (a : MulAut ↥(twistedE6RootGroup K σ)) * z) hh
        simpa using h1
      · rw [hh]
        exact E.mul_mem (E.inv_mem a.2) b.2
    have hh2 : h ^ 2 = 1 := hconj (by rw [map_pow, map_one]; exact hE2 _ hhE)
    have hcomm : x * MulAut.conj h = MulAut.conj h * x :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hxE⟩ : E) (⟨MulAut.conj h, hhE⟩ : E))
    have hxh : x h = h := by
      apply hconj
      have e1 : x * MulAut.conj h * x⁻¹ = MulAut.conj (x h) :=
        MulEquiv.ext fun u => by
          simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
            MulAut.apply_inv_self]
      rw [← e1, hcomm, mul_inv_cancel_right]
    have hconj2 : MulAut.conj h * MulAut.conj h = 1 := by
      rw [← sq, ← map_pow, hh2, map_one]
    have hch1 : MulAut.conj h ≠ 1 := fun hce => hh1 (hZ h hce)
    have hx1 : x ≠ 1 := fun hxe => hx ⟨1, by rw [map_one, hxe]⟩
    have hxne : MulAut.conj h ≠ x := fun hxe => hx ⟨h, hxe⟩
    let x' : MulAut ↥(twistedE6RootGroup K σ) := x * MulAut.conj h
    have hx'E : x' ∈ E := E.mul_mem hxE hhE
    have hx'2 : x' ^ 2 = 1 := hE2 x' hx'E
    have hx'h : x' h = h := by
      change (x * MulAut.conj h) h = h
      rw [MulAut.mul_apply, MulAut.conj_apply, mul_inv_cancel_right, hxh]
    have hcomm' : x' * MulAut.conj h = MulAut.conj h * x' := hEcomm x' hx'E _ hhE
    have hx'outer : x' ∉ (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut _).range := by
      rintro ⟨g, hg⟩
      apply hx
      refine ⟨g * h⁻¹, ?_⟩
      calc MulAut.conj (g * h⁻¹) = MulAut.conj g * MulAut.conj h⁻¹ :=
              map_mul (MulAut.conj) g h⁻¹
        _ = MulAut.conj g * (MulAut.conj h)⁻¹ := by rw [map_inv]
        _ = x' * (MulAut.conj h)⁻¹ := by rw [hg]
        _ = x := by
              rw [show x' = x * MulAut.conj h from rfl]; group
    have hx'1 : x' ≠ 1 := by
      intro hc
      apply hx
      refine ⟨h⁻¹, ?_⟩
      have h1 : x = (MulAut.conj h)⁻¹ := by
        calc x = x' * (MulAut.conj h)⁻¹ := by
                rw [show x' = x * MulAut.conj h from rfl]; group
          _ = 1 * (MulAut.conj h)⁻¹ := by rw [hc]
          _ = (MulAut.conj h)⁻¹ := one_mul _
      rw [h1, map_inv]
    have hne' : MulAut.conj h ≠ x' := by
      intro hc
      have h1 : x = 1 := by
        calc x = x' * (MulAut.conj h)⁻¹ := by
                rw [show x' = x * MulAut.conj h from rfl]; group
          _ = MulAut.conj h * (MulAut.conj h)⁻¹ := by rw [← hc]
          _ = 1 := by group
      exact hx1 h1
    obtain ⟨ψ, hψx_or⟩ :=
      CFSG.ComponentClassification.Burgoyne.E2.TwE6In.twE6_outer_involution_conj
        (p := p) (f := f) hpr hp2 hf1 K hK' σ hσ' x hx2 hx
    obtain ⟨ψ', hψx'_or⟩ :=
      CFSG.ComponentClassification.Burgoyne.E2.TwE6In.twE6_outer_involution_conj
        (p := p) (f := f) hpr hp2 hf1 K hK' σ hσ' x' hx'2 hx'outer
    rcases hψx_or with hψx | hψx
    ·
      have hh'2 : (ψ h) ^ 2 = 1 := by
        rw [← map_pow, hh2, map_one]
      have hσh' : fieldActor (t := TwistTag.E6) σ σ (ψ h) = ψ h := by
        have h1 : (ψ * x * ψ⁻¹) (ψ h) = ψ h := by
          simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hxh]
        rwa [hψx] at h1
      obtain ⟨u, hu1, ⟨n, hun⟩, hucomm, huσ⟩ :=
        exists_rElement_fixed_twE6Graph_inv σ q hσ hK hK2 (ψ h) hh'2 hσh'
      have hxw : x (ψ.symm u) = ψ.symm u := by
        apply ψ.injective
        rw [ψ.apply_symm_apply]
        have h1 : (ψ * x * ψ⁻¹) u = u := by rw [hψx, huσ]
        simpa only [MulAut.mul_apply, MulAut.inv_apply] using h1
      have hcommw : ψ.symm u * h = h * ψ.symm u := by
        have h1 := congrArg ψ.symm hucomm.eq
        simpa only [map_mul, MulEquiv.symm_apply_apply] using h1
      have hfixh : MulAut.conj h (ψ.symm u) = ψ.symm u := by
        rw [MulAut.conj_apply, ← hcommw, mul_inv_cancel_right]
      have hfixE := hfix_of_two hxE hhE hx2 hconj2 hcomm hx1 hch1 hxne hxw hfixh
      refine Or.inl ⟨ψ.symm u, ?_, ⟨n, ?_⟩, hfixE⟩
      · intro hc
        have h1 := congrArg ψ hc
        rw [map_one, ψ.apply_symm_apply] at h1
        exact hu1 h1
      · apply ψ.injective
        rw [map_pow, ψ.apply_symm_apply, hun, map_one]
    · rcases hψx'_or with hψx' | hψx'
      ·
        have hh'2 : (ψ' h) ^ 2 = 1 := by
          rw [← map_pow, hh2, map_one]
        have hσh' : fieldActor (t := TwistTag.E6) σ σ (ψ' h) = ψ' h := by
          have h1 : (ψ' * x' * ψ'⁻¹) (ψ' h) = ψ' h := by
            simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hx'h]
          rwa [hψx'] at h1
        obtain ⟨u, hu1, ⟨n, hun⟩, hucomm, huσ⟩ :=
          exists_rElement_fixed_twE6Graph_inv σ q hσ hK hK2 (ψ' h) hh'2 hσh'
        have hxw : x' (ψ'.symm u) = ψ'.symm u := by
          apply ψ'.injective
          rw [ψ'.apply_symm_apply]
          have h1 : (ψ' * x' * ψ'⁻¹) u = u := by rw [hψx', huσ]
          simpa only [MulAut.mul_apply, MulAut.inv_apply] using h1
        have hcommw : ψ'.symm u * h = h * ψ'.symm u := by
          have h1 := congrArg ψ'.symm hucomm.eq
          simpa only [map_mul, MulEquiv.symm_apply_apply] using h1
        have hfixh : MulAut.conj h (ψ'.symm u) = ψ'.symm u := by
          rw [MulAut.conj_apply, ← hcommw, mul_inv_cancel_right]
        have hfixE := hfix_of_two hx'E hhE hx'2 hconj2 hcomm' hx'1 hch1 hne' hxw hfixh
        refine Or.inl ⟨ψ'.symm u, ?_, ⟨n, ?_⟩, hfixE⟩
        · intro hc
          have h1 := congrArg ψ' hc
          rw [map_one, ψ'.apply_symm_apply] at h1
          exact hu1 h1
        · apply ψ'.injective
          rw [map_pow, ψ'.apply_symm_apply, hun, map_one]
      ·
        exact Or.inr ⟨x, h, ψ, ψ', hxE, hhE, hh1, hh2, hxh, hψx, hψx'⟩

end CFSG.LocalAnalysis.WeakClosure81
