module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassSetup

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

section Coset

variable {G : Type*} [Group G]

theorem conj_eq_self_of_mem_centralizer {c u : G}
    (hc : c ∈ Subgroup.centralizer ({u} : Set G)) : c⁻¹ * u * c = u := by
  rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hc, inv_mul_cancel_left]

theorem mem_centralizer_of_conj_eq_self {c u : G} (h : c⁻¹ * u * c = u) :
    c ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  conv_lhs => rw [← h]
  group

theorem exists_mem_diff_one_ne [Finite G] {Q : Subgroup G} (hQ4 : 4 ≤ Nat.card Q) (e : G) :
    ∃ f ∈ (Q : Set G) \ {1}, f ≠ e := by
  by_contra hnone
  push Not at hnone
  have hsub : (Q : Set G) \ {1} ⊆ {e} := fun f hf => hnone f hf
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, card_diff_one] at hle
  omega

theorem inf_centralizer_le_normalizer {H Q : Subgroup G} {z : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (u : G) :
    H ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer
      ((fun e => u * e) '' ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G)) := by
  have hQnorm := point_subgroup_normalized hQclass
  have hmaps : ∀ c ∈ H ⊓ Subgroup.centralizer ({u} : Set G),
      ∀ x ∈ (fun e => u * e) '' ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G),
        c⁻¹ * x * c ∈ (fun e => u * e) ''
          ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) := by
    rintro c ⟨hcH, hcu⟩ x ⟨e, ⟨heQ, heu⟩, rfl⟩
    have hcu' : c⁻¹ * u * c = u := conj_eq_self_of_mem_centralizer hcu
    refine ⟨c⁻¹ * e * c, ⟨hQnorm c hcH e heQ, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcu) heu) hcu
    · change u * (c⁻¹ * e * c) = c⁻¹ * (u * e) * c
      calc u * (c⁻¹ * e * c) = (c⁻¹ * u * c) * (c⁻¹ * e * c) := by rw [hcu']
        _ = c⁻¹ * (u * e) * c := by group
  intro c hc
  apply mem_normalizer_of_conj_mem (hmaps c hc)
  intro x hx
  have hc' : c⁻¹ ∈ H ⊓ Subgroup.centralizer ({u} : Set G) := Subgroup.inv_mem _ hc
  simpa only [inv_inv] using hmaps c⁻¹ hc' x hx

theorem coset_two_transitive {H Q : Subgroup G} {z u : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (htransE : ∀ a ∈ ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1},
        ∃ c ∈ H ⊓ Subgroup.centralizer ({u} : Set G), c⁻¹ * a * c = b)
    (htrans : ∀ x ∈ (fun e => u * e) ''
        ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G),
      ∃ n ∈ H ⊓ Subgroup.normalizer ((fun e => u * e) ''
        ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G)), n⁻¹ * u * n = x) :
    let Δ := (fun e => u * e) '' ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G)
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
      ∃ n ∈ H ⊓ Subgroup.normalizer Δ, n⁻¹ * a * n = c ∧ n⁻¹ * b * n = d := by
  intro Δ
  refine two_transitive_of_conj (fun n hn x hx => conj_mem_of_mem_normalizer hn.2 hx) htrans ?_
  rintro x ⟨e₁, he₁, rfl⟩ y ⟨e₂, he₂, rfl⟩ hx hy
  have he₁1 : e₁ ≠ 1 := fun h1 => hx (by simp [h1])
  have he₂1 : e₂ ≠ 1 := fun h1 => hy (by simp [h1])
  obtain ⟨c, hc, hce⟩ := htransE e₁ ⟨he₁, he₁1⟩ e₂ ⟨he₂, he₂1⟩
  have hcu : c⁻¹ * u * c = u := conj_eq_self_of_mem_centralizer hc.2
  refine ⟨c, ⟨hc.1, inf_centralizer_le_normalizer hQclass u hc⟩, hcu, ?_⟩
  calc c⁻¹ * (u * e₁) * c = (c⁻¹ * u * c) * (c⁻¹ * e₁ * c) := by group
    _ = u * e₂ := by rw [hcu, hce]

theorem le_normalizer_conjugacyWithin (Q : Subgroup G) (u : G) :
    Q ≤ Subgroup.normalizer (conjugacyWithin Q u) := by
  have hmaps : ∀ q ∈ Q, ∀ x ∈ conjugacyWithin Q u, q⁻¹ * x * q ∈ conjugacyWithin Q u := by
    rintro q hq x ⟨k, rfl⟩
    exact ⟨k * ⟨q, hq⟩, by simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]⟩
  intro q hq
  apply mem_normalizer_of_conj_mem (hmaps q hq)
  intro x hx
  simpa only [inv_inv] using hmaps q⁻¹ (Q.inv_mem hq) x hx

theorem inf_centralizer_le_normalizer_of_mem {H Q : Subgroup G} {z u : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {e : G} (he : e ∈ Q) :
    H ⊓ Subgroup.centralizer ({u * e} : Set G) ≤
      Subgroup.normalizer ((fun f => u * f) '' (Q : Set G)) := by
  have hQnorm := point_subgroup_normalized hQclass
  have hmaps : ∀ c ∈ H ⊓ Subgroup.centralizer ({u * e} : Set G),
      ∀ x ∈ (fun f => u * f) '' (Q : Set G), c⁻¹ * x * c ∈ (fun f => u * f) '' (Q : Set G) := by
    rintro c ⟨hcH, hcv⟩ x ⟨f, hf, rfl⟩
    have hcv' : c⁻¹ * (u * e) * c = u * e := conj_eq_self_of_mem_centralizer hcv
    refine ⟨e * (c⁻¹ * (e⁻¹ * f) * c), Q.mul_mem he (hQnorm c hcH _ (Q.mul_mem (Q.inv_mem he)
      hf)), ?_⟩
    change u * (e * (c⁻¹ * (e⁻¹ * f) * c)) = c⁻¹ * (u * f) * c
    calc u * (e * (c⁻¹ * (e⁻¹ * f) * c)) = (c⁻¹ * (u * e) * c) * (c⁻¹ * (e⁻¹ * f) * c) := by
          rw [hcv']
          group
      _ = c⁻¹ * (u * f) * c := by group
  intro c hc
  apply mem_normalizer_of_conj_mem (hmaps c hc)
  intro x hx
  simpa only [inv_inv] using hmaps c⁻¹ (Subgroup.inv_mem _ hc) x hx

theorem coset_transitive_of_centralizing {H Q : Subgroup G} {z u : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hQ4 : 4 ≤ Nat.card Q) [Finite G]
    (htrans : ∀ e ∈ Q, ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃ c ∈ H ⊓ Subgroup.centralizer ({u * e} : Set G), c⁻¹ * a * c = b) :
    ∀ x ∈ (fun f => u * f) '' (Q : Set G),
      ∃ n ∈ H ⊓ Subgroup.normalizer ((fun f => u * f) '' (Q : Set G)), n⁻¹ * u * n = x := by
  have hsqQ : ∀ x ∈ Q, x * x = 1 := fun x hx => by rw [← sq]; exact hQ.2 x hx
  have hinvQ : ∀ x ∈ Q, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsqQ x hx)
  rintro x ⟨e, he, rfl⟩
  by_cases he1 : e = 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [he1]
    group
  obtain ⟨f, ⟨hfQ, hf1⟩, hfe⟩ := exists_mem_diff_one_ne hQ4 e
  have hef1 : e * f ≠ 1 := by
    intro h1
    apply hfe
    rw [← inv_eq_of_mul_eq_one_right h1, hinvQ e he]
  obtain ⟨c₁, hc₁, hc₁e⟩ := htrans e he e ⟨he, he1⟩ (e * f) ⟨Q.mul_mem he hfQ, hef1⟩
  obtain ⟨c₂, hc₂, hc₂f⟩ := htrans 1 Q.one_mem f ⟨hfQ, hf1⟩ e ⟨he, he1⟩
  rw [mul_one] at hc₂
  have hc₁v : c₁⁻¹ * (u * e) * c₁ = u * e := conj_eq_self_of_mem_centralizer hc₁.2
  have hc₂u : c₂⁻¹ * u * c₂ = u := conj_eq_self_of_mem_centralizer hc₂.2
  have hN₁ := inf_centralizer_le_normalizer_of_mem (u := u) hQclass he hc₁
  have hN₂ := inf_centralizer_le_normalizer_of_mem (u := u) hQclass Q.one_mem
    (by rw [mul_one]; exact hc₂)
  refine ⟨c₁ * c₂, ⟨Subgroup.mul_mem _ hc₁.1 hc₂.1, Subgroup.mul_mem _ hN₁ hN₂⟩, ?_⟩
  have hu1 : c₁⁻¹ * u * c₁ = u * f := by
    calc c₁⁻¹ * u * c₁ = (c₁⁻¹ * (u * e) * c₁) * (c₁⁻¹ * e⁻¹ * c₁) := by group
      _ = (u * e) * (c₁⁻¹ * e * c₁) := by rw [hc₁v, hinvQ e he]
      _ = u * (e * (e * f)) := by rw [hc₁e]; group
      _ = u * f := by rw [← mul_assoc e e f, hsqQ e he, one_mul]
  calc (c₁ * c₂)⁻¹ * u * (c₁ * c₂) = c₂⁻¹ * (c₁⁻¹ * u * c₁) * c₂ := by group
    _ = (c₂⁻¹ * u * c₂) * (c₂⁻¹ * f * c₂) := by rw [hu1]; group
    _ = u * e := by rw [hc₂u, hc₂f]

end Coset

variable {G : Type} [Group G] [Finite G]

theorem centralizer_transitive_of_second_fixed
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {v : G} (hvH : v ∈ H) (hv : orderOf v = 2)
    (hQv : minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer ({v} : Set G))
    {γ : rightCosetSpace H} (hγ : γ ≠ rightCosetMk H 1)
    (hγv : rightCosetTranslate H γ v = γ) :
    ∀ a ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1},
      ∀ b ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1},
        ∃ c ∈ H ⊓ Subgroup.centralizer ({v} : Set G), c⁻¹ * a * c = b := by
  set Q := minimalLocalFailurePairActionPointHull H z
  obtain ⟨hQ, hQ4, hQclass, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have htwo := ambient_two_transitive h.local_datum h.central_sylow hQ hQ4 hQclass
  obtain ⟨g, hgH, hgB⟩ := exists_conj_mem_pairPointStabilizer htwo hbeta hvH hγ hγv
  have hv' : orderOf (g * v * g⁻¹) = 2 := by
    have hconj := orderOf_conj_eq v g⁻¹
    rw [inv_inv] at hconj
    rw [hconj, hv]
  obtain ⟨-, -, -, -, -, htransE, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      hgB hv'
  have hQnorm := point_subgroup_normalized hQclass
  have hgQ : ∀ a ∈ Q, g * a * g⁻¹ ∈ Q := fun a ha => by
    simpa only [inv_inv] using hQnorm g⁻¹ (H.inv_mem hgH) a ha
  have hQv' : ∀ a ∈ Q, a ∈ Subgroup.centralizer ({g * v * g⁻¹} : Set G) := by
    intro a ha
    have hc : Commute (g⁻¹ * a * g) v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQv (hQnorm g hgH a ha))
    have hc' := hc.conj g
    rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at hc'
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc'.eq
  have hmemE : ∀ a ∈ (Q : Set G) \ {1}, g * a * g⁻¹ ∈
      ((Q ⊓ Subgroup.centralizer ({g * v * g⁻¹} : Set G) : Subgroup G) : Set G) \ {1} := by
    intro a ha
    refine ⟨⟨hgQ a ha.1, hQv' _ (hgQ a ha.1)⟩, ?_⟩
    have hne := conj_ne_one (w := g⁻¹) ha.2
    rwa [inv_inv] at hne
  intro a ha b hb
  obtain ⟨c, hc, hcab⟩ := htransE _ (hmemE a ha) _ (hmemE b hb)
  refine ⟨g⁻¹ * c * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hgH) hc.1) hgH, ?_⟩, ?_⟩
  · have hcv : Commute c (g * v * g⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hcv' := hcv.conj g⁻¹
    rw [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group, inv_inv] at hcv'
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcv'.eq
  · calc (g⁻¹ * c * g)⁻¹ * a * (g⁻¹ * c * g) = g⁻¹ * (c⁻¹ * (g * a * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [hcab]
      _ = b := by group

end CFSG.ShultStronglyClosedTI.MixedClass
