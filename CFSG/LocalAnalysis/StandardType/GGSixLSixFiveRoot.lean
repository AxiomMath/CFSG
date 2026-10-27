module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFivePumpup
public import CFSG.LocalAnalysis.StandardType.GGPComponentInvolutionNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Data

variable {G : Type} [Group G]

@[expose] def GGSixRootFourData (p : ℕ) (D J R : Subgroup G) : Prop :=
  R ≤ J ∧ IsElemAbelian 2 R ∧ 4 ≤ Nat.card R ∧ ¬ R ≤ Subgroup.centralizer (J : Set G) ∧
    ∀ e ∈ D, e ≠ 1 → ∀ A : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer {e}) A →
      J ≤ A → ∀ r ∈ R, r ≠ 1 →
        ⁅R, pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ⊓ Subgroup.centralizer {e}⁆ ≤
          LargeEvenPPrimeCoreOf p A

@[expose] def GGSixRootTwoData (J V : Subgroup G) (r : G) : Prop :=
  r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ 4 ≤ Nat.card V ∧ r ∉ Subgroup.centralizer (J : Set G) ∧
    (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) ∧
    V ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G))

end Data

section RootTwo

variable {G : Type} [Group G] [Finite G]

theorem ggLe_centralizer_of_rootTwoData {J V E : Subgroup G} {r : G}
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hd : GGSixRootTwoData J V r)
    (hJE : J ≤ Subgroup.normalizer (E : Set G)) (hE : Odd (Nat.card E)) :
    E ≤ Subgroup.centralizer (J : Set G) := by
  obtain ⟨hrV, hVJ, hV, hV4, hrZ, hconj, hVP⟩ := hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := E ⊓ Subgroup.centralizer ({r} : Set G) with hF
  have hFv : ∀ v ∈ V, v ≠ 1 → E ⊓ Subgroup.centralizer ({v} : Set G) = F := by
    intro v hv hv1
    have hle : F ≤ E ⊓ Subgroup.centralizer ({v} : Set G) := by
      intro f hf
      obtain ⟨hfE, hfr⟩ := Subgroup.mem_inf.mp hf
      refine Subgroup.mem_inf.mpr ⟨hfE, ?_⟩
      have hcE : ⁅v, f⁆ ∈ E := ggCommutatorElement_mem_right hfE (hJE (hVJ hv))
      have hcP : ⁅v, f⁆ ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) :=
        ggCommutatorElement_mem_left (hVP hv) (mem_normalizer_pCoreOf hfr)
      have h1 := ggEq_one_of_mem_odd_of_mem_two hE (ggIsPGroup_pCoreOf_two _) hcE hcP
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h1.symm
    obtain ⟨j, hj, rfl⟩ := hconj v hv hv1
    have hmap : (E ⊓ Subgroup.centralizer ({j * r * j⁻¹} : Set G)).map
        (MulAut.conj j⁻¹).toMonoidHom ≤ F := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyE, hyv⟩ := Subgroup.mem_inf.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyv
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.mp (hJE (J.inv_mem hj)) y).mp hyE
        simpa using h
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc j⁻¹ * y * j * r = j⁻¹ * (y * (j * r * j⁻¹)) * j := by group
          _ = j⁻¹ * ((j * r * j⁻¹) * y) * j := by rw [hyv]
          _ = r * (j⁻¹ * y * j) := by group
    have hcard : Nat.card (E ⊓ Subgroup.centralizer ({j * r * j⁻¹} : Set G) : Subgroup G) ≤
        Nat.card F := by
      have h1 := Subgroup.card_le_of_le hmap
      rwa [Subgroup.card_map_of_injective (MulAut.conj j⁻¹).injective] at h1
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hE2 : ¬ 2 ∣ Nat.card E := fun h => (Nat.not_even_iff_odd.mpr hE) (even_iff_two_dvd.mpr h)
  have hV4' : 2 ^ 2 ≤ Nat.card V := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hV4
  have hrE : Subgroup.zpowers r ≤ Subgroup.centralizer (E : Set G) := by
    refine ggLe_centralizer_of_generation_le hV hV4' hE2 (hVJ.trans hJE) fun v hv hv1 => ?_
    rw [hFv v hv hv1, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hf).2
  have hJN : J ≤ Subgroup.normalizer
      ((J ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := fun j hj =>
    ggMem_normalizer_inf_of (Subgroup.le_normalizer hj)
      (normalizer_le_normalizer_centralizer E (hJE hj))
  rcases ggLe_center_or_eq_of_normalized hJ inf_le_left hJN with h | h
  · exact absurd (h ⟨hVJ hrV, hrE (Subgroup.mem_zpowers r)⟩) hrZ
  · rw [Subgroup.le_centralizer_iff]
    exact h.symm.le.trans inf_le_right

end RootTwo

section RootFourGeneric

variable {G : Type} [Group G] [Finite G] {p : ℕ} {D J R E : Subgroup G}

theorem ggLe_centralizer_of_rootFourData (hG : IsCharTwoType G) [Fact p.Prime]
    (hp2 : p ≠ 2) (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2)
    (hDJ : D ≤ Subgroup.centralizer (J : Set G))
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hR : GGSixRootFourData p D J R)
    (hlines : ∀ e ∈ D, e ≠ 1 → ∃ A : Subgroup G,
      LargeEvenPComponent p (Subgroup.centralizer {e}) A ∧ J ≤ A ∧
        Odd (Nat.card (LargeEvenPPrimeCoreOf p A)))
    (hJE : J ≤ Subgroup.normalizer (E : Set G)) (hE : Odd (Nat.card E)) :
    E ≤ Subgroup.centralizer (J : Set G) := by
  obtain ⟨hRJ, hRe, hR4, hRZ, hRL⟩ := hR
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hRe.1.is_comm.comm (⟨a, ha⟩ : ↥R) ⟨b, hb⟩)
  refine ggLe_centralizer_of_le_pCoreOf_two hJ hRJ hRe hR4 hRZ hJE hE ?_
  intro r hr hr1
  have hr2 : orderOf r = 2 := orderOf_eq_prime (hRe.2 r hr) hr1
  have hDr : D ≤ Subgroup.centralizer ({r} : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hDJ he) r (hRJ hr)).symm
  have hRr : R ≤ Subgroup.centralizer ({r} : Set G) := fun s hs => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hRcomm s hs r hr
  refine ggLe_pCoreOf_two_of_generation hG hp2 hr2 hD hDc hDr hRr fun e he he1 => ?_
  obtain ⟨Ae, hAe, hJAe, hOdd⟩ := hlines e he he1
  exact ⟨_, hOdd, hRL e he he1 Ae hAe hJAe r hr hr1⟩

end RootFourGeneric

section Proof

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.le_centralizer_of_rootFour (hPU : GGPumpupInput)
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (hpJ : p ∣ Nat.card J)
    (hZJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hZK : ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    {R : Subgroup G} (hR : GGSixRootFourData p D J R) {E : Subgroup G}
    (hJE : J ≤ Subgroup.normalizer (E : Set G)) (hE : Odd (Nat.card E)) :
    E ≤ Subgroup.centralizer (J : Set G) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  exact ggLe_centralizer_of_rootFourData h.charTwo h.ne_two h.stdSub.1.2.1
    h.stdSub.1.2.2.1 h.le_centralizer_J h.j_comp.2.2 hR
    (fun e he he1 => h.exists_pComponent_odd hPU hpJ hZJ hZK he he1) hJE hE

end Proof

section Inputs

@[expose] def GGSixPCompRootInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
      (∃ R : Subgroup G, GGSixRootFourData p D J R) ∨
        (∃ (V : Subgroup G) (r : G), GGSixRootTwoData J V r) ∨
        ∀ d ∈ D, d ≠ 1 → ∀ A : Subgroup G,
          LargeEvenPComponent p (Subgroup.centralizer {d}) A → J ≤ A →
          A = J ⊔ LargeEvenPPrimeCoreOf p A → Odd (Nat.card (LargeEvenPPrimeCoreOf p A)) →
            LargeEvenPPrimeCoreOf p A ≤ Subgroup.centralizer (J : Set G)

theorem ggSixPCompCentralizeInput_of_root (hPU : GGPumpupInput) (hP : GGStdSubPrimeInput)
    (h : GGSixPCompRootInput) : GGSixPCompCentralizeInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd hZJ hZK d hd hd1 A hA hJA hAeq hEodd
  have hJE : J ≤ Subgroup.normalizer (LargeEvenPPrimeCoreOf p A : Set G) := fun j hj =>
    ggNormalizer_le_normalizer_pPrimeCoreOf p A (Subgroup.le_normalizer (hJA hj))
  rcases h G p B Bs x L D J t n f ψ hctx hodd hZJ hZK with ⟨R, hR⟩ | ⟨V, r, hV⟩ | hc
  · exact hctx.le_centralizer_of_rootFour hPU (hP G p B x L D J hctx.thmI hctx.stdSub) hZJ hZK hR
      hJE hEodd
  · exact ggLe_centralizer_of_rootTwoData hctx.j_comp.2.2 hV hJE hEodd
  · exact hc d hd hd1 A hA hJA hAeq hEodd

end Inputs

end CFSG.StandardType
