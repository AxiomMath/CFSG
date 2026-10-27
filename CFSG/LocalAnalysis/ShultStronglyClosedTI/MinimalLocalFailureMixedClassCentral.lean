module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassCount
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassSupport

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem coset_subset_class_of_centralizing
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hQu : minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer ({u} : Set G)) :
    ∀ e ∈ minimalLocalFailurePairActionPointHull H z, u * e ∈ involutionPointClass u := by
  obtain ⟨hQ, hQ4, hQclass, -, -, -, -, -, -, -, -, -, -, -, -, -, heven, hprod⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, htransE, hΔorbit, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      huB hu
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  have hdatum := h.local_datum
  have horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
      rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} := hΔorbit.symm
  have hE : Q ⊓ Subgroup.centralizer ({u} : Set G) = Q := inf_eq_left.mpr hQu
  have htransQ : ∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
      ∃ c ∈ H ⊓ Subgroup.centralizer ({u} : Set G), c⁻¹ * a * c = b := by
    intro a ha b hb
    exact htransE a (by rw [hE]; exact ha) b (by rw [hE]; exact hb)
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact absurd hu (by norm_num)
  have huD : u ∉ involutionPointClass z := not_mem_pointClass_of_two_fixed hdatum hbeta huB
  have hzu : ¬ IsConj z u := fun hc => huD (mem_pointClass_iff_isConj.mpr hc)
  have huQ : u ∉ Q := fun huQ => huD (point_subgroup_class hdatum hQclass ⟨huQ, hu1⟩)
  have hsqQ : ∀ a ∈ Q, a * a = 1 := fun a ha => by rw [← sq]; exact hQ.2 a ha
  have hinvQ : ∀ a ∈ Q, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsqQ a ha)
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hQH : Q ≤ H := point_subgroup_le hdatum.distinguished_mem hQclass
  have hQnorm := point_subgroup_normalized hQclass
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  have hcommu : ∀ f ∈ Q, u * f = f * u := fun f hf =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hQu hf)).symm
  have heven' : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s :=
    fun r s hr hs => heven r s (mem_pointClass_iff_isConj.mpr hr) (mem_pointClass_iff_isConj.mpr hs)
  have hprod' : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s) :=
    fun r s hr hs hne hrs => mem_pointClass_iff_isConj.mp
      (hprod r s (mem_pointClass_iff_isConj.mpr hr) (mem_pointClass_iff_isConj.mpr hs) hne hrs)
  have horder : ∀ f ∈ (Q : Set G) \ {1}, orderOf (u * f) = 2 := by
    intro f hf
    apply orderOf_eq_prime
    · rw [sq, show u * f * (u * f) = u * (f * u) * f by group, ← hcommu f hf.1,
        show u * (u * f) * f = (u * u) * (f * f) by group, hu2, hsqQ f hf.1, one_mul]
    · intro h1
      apply huQ
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Q.inv_mem hf.1
  have hQuf : ∀ f ∈ Q, Q ≤ Subgroup.centralizer ({u * f} : Set G) := by
    intro f hf a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [show a * (u * f) = (a * u) * f by group, ← hcommu a ha, mul_assoc, hQab a ha f hf,
      ← mul_assoc]
  intro e he
  by_cases he1 : e = 1
  · rw [he1, mul_one]
    exact distinguished_mem_pointClass u
  by_contra hne
  have hV1 : ∀ f ∈ (Q : Set G) \ {1}, ¬ IsConj u (u * f) := by
    intro f hf hfU
    obtain ⟨c, hc, hcf⟩ := htransQ f hf e ⟨he, he1⟩
    apply hne
    have hcu : c⁻¹ * u * c = u := conj_eq_self_of_mem_centralizer hc.2
    have hconj : c⁻¹ * (u * f) * c = u * e := by
      calc c⁻¹ * (u * f) * c = (c⁻¹ * u * c) * (c⁻¹ * f * c) := by group
        _ = u * e := by rw [hcu, hcf]
    rw [← hconj]
    exact conj_mem_pointClass (mem_pointClass_iff_isConj.mpr hfU) c
  have hV2 : ∀ f ∈ (Q : Set G) \ {1}, ∀ γ : rightCosetSpace H,
      rightCosetTranslate H γ (u * f) = γ → γ = rightCosetMk H 1 := by
    intro f hf γ hγ
    by_contra hγα
    have htv := centralizer_transitive_of_second_fixed h hcomm hsmallerR1 hbeta ht hproper
      (H.mul_mem huH (hQH hf.1)) (horder f hf) (hQuf f hf.1) hγα hγ
    obtain ⟨g, hg, hgf⟩ := exists_mem_diff_one_ne hQ4 f
    have hfg1 : f * g ≠ 1 := by
      intro h1
      apply hgf
      rw [eq_inv_of_mul_eq_one_right h1, hinvQ f hf.1]
    obtain ⟨c, hc, hcf⟩ := htv f hf (f * g) ⟨Q.mul_mem hf.1 hg.1, hfg1⟩
    apply hV1 g hg
    have hcv : c⁻¹ * (u * f) * c = u * f := conj_eq_self_of_mem_centralizer hc.2
    have hcu : c⁻¹ * u * c = u * g := by
      calc c⁻¹ * u * c = (c⁻¹ * (u * f) * c) * (c⁻¹ * f⁻¹ * c) := by group
        _ = (u * f) * (c⁻¹ * f * c) := by rw [hcv, hinvQ f hf.1]
        _ = u * (f * (f * g)) := by rw [hcf]; group
        _ = u * g := by rw [← mul_assoc f f g, hsqQ f hf.1, one_mul]
    exact isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hcu⟩
  set w := u * e with hwdef
  have hw2 : orderOf w = 2 := horder e ⟨he, he1⟩
  have hwH : Subgroup.centralizer ({w} : Set G) ≤ H := by
    intro c hc
    have hfix : rightCosetTranslate H (rightCosetTranslate H (rightCosetMk H 1) c) w =
        rightCosetTranslate H (rightCosetMk H 1) c := by
      rw [rightCosetTranslate_mul, Subgroup.mem_centralizer_singleton_iff.mp hc,
        ← rightCosetTranslate_mul, (translate_base_iff H w).mpr (H.mul_mem huH (hQH he))]
    exact (translate_base_iff H c).mp (hV2 e ⟨he, he1⟩ _ hfix)
  have hwu : Subgroup.centralizer ({w} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro c hc
    have hcH := hwH hc
    have hcw : c⁻¹ * w * c = w := conj_eq_self_of_mem_centralizer hc
    have hfQ : e * (c⁻¹ * e * c) ∈ Q := Q.mul_mem he (hQnorm c hcH e he)
    have hcu : c⁻¹ * u * c = u * (e * (c⁻¹ * e * c)) := by
      calc c⁻¹ * u * c = (c⁻¹ * w * c) * (c⁻¹ * e⁻¹ * c) := by rw [hwdef]; group
        _ = u * (e * (c⁻¹ * e * c)) := by rw [hcw, hinvQ e he, hwdef]; group
    have hf1 : e * (c⁻¹ * e * c) = 1 := by
      by_contra hf1
      exact hV1 _ ⟨hfQ, hf1⟩ (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hcu⟩)
    rw [hf1, mul_one] at hcu
    exact mem_centralizer_of_conj_eq_self hcu
  have hcardHu : Nat.card (H ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
      (Nat.card Q - 1) * Nat.card (Subgroup.centralizer ({w} : Set G)) := by
    have horbE : conjugacyWithin (H ⊓ Subgroup.centralizer ({u} : Set G)) e =
        (Q : Set G) \ {1} := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨hQnorm c c.2.1 e he, conj_ne_one he1⟩
      · intro hx
        obtain ⟨c, hc, hcx⟩ := htransQ e ⟨he, he1⟩ x hx
        exact ⟨⟨c, hc⟩, hcx⟩
    have hstab : Subgroup.centralizer ({e} : Set G) ⊓
        (H ⊓ Subgroup.centralizer ({u} : Set G)) = Subgroup.centralizer ({w} : Set G) := by
      ext c
      constructor
      · rintro ⟨hce, -, hcu⟩
        have h1 : Commute c u := Subgroup.mem_centralizer_singleton_iff.mp hcu
        have h2 : Commute c e := Subgroup.mem_centralizer_singleton_iff.mp hce
        exact Subgroup.mem_centralizer_singleton_iff.mpr (h1.mul_right h2).eq
      · intro hc
        refine ⟨?_, hwH hc, hwu hc⟩
        have h1 : Commute c u := Subgroup.mem_centralizer_singleton_iff.mp (hwu hc)
        have h2 : Commute c w := Subgroup.mem_centralizer_singleton_iff.mp hc
        have h3 := h1.mul_right h2
        rw [hwdef, ← mul_assoc, hu2, one_mul] at h3
        exact Subgroup.mem_centralizer_singleton_iff.mpr h3.eq
    have hmul := Subgroup.card_mul_index
      ((Subgroup.centralizer ({e} : Set G)).subgroupOf (H ⊓ Subgroup.centralizer ({u} : Set G)))
    rw [← conjugacyWithin_card_eq_centralizer_index, horbE, card_diff_one, card_subgroupOf_eq,
      hstab] at hmul
    rw [← hmul, mul_comm]
  have hzH : Nat.card (Subgroup.centralizer ({z} : Set G)) * (Nat.card Q - 1) = Nat.card H := by
    rw [← card_diff_one, hQclass]
    exact card_centralizer_mul_card_conjugacyWithin (point_centralizer_le hdatum)
  have hfixcard : Nat.card {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} *
      Nat.card (H ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) := by
    rw [← horbit]
    exact card_base_orbit_mul H _
  have hcent : ∀ v : G, IsConj u v → ∀ g : G,
      rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g →
        ∀ q ∈ Q, Commute v (g⁻¹ * q * g) := fun v hv g hfix q hq =>
    commute_conj_point_subgroup hQclass hQu horbit (mem_pointClass_iff_isConj.mpr hv) hfix hq
  have hmixedV : ∀ v r : G, IsConj u v → IsConj z r → Commute v r → IsConj w (v * r) := by
    intro v r hv hr hvr
    have hW : ∀ x ∈ involutionPointClass w, ∀ g : G, g⁻¹ * x * g ∈ involutionPointClass w :=
      fun x hx g => conj_mem_pointClass hx g
    have hcoset : ∀ f ∈ ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) \ {1},
        u * f ∈ involutionPointClass w := by
      intro f hf
      rw [hE] at hf
      obtain ⟨c, hc, hcf⟩ := htransQ e ⟨he, he1⟩ f hf
      have hcu : c⁻¹ * u * c = u := conj_eq_self_of_mem_centralizer hc.2
      refine ⟨c, ?_⟩
      change c⁻¹ * w * c = u * f
      calc c⁻¹ * w * c = (c⁻¹ * u * c) * (c⁻¹ * e * c) := by rw [hwdef]; group
        _ = u * f := by rw [hcu, hcf]
    exact mem_pointClass_iff_isConj.mp (mul_mem_of_coset_mem hdatum hQclass horbit hW hcoset
      (mem_pointClass_iff_isConj.mpr hv) (mem_pointClass_iff_isConj.mpr hr) hvr)
  have hsupp : ∀ a : G, orderOf a = 2 → ¬ IsConj w a →
      InvolutionCounting.thompsonPairCount u z a = 0 := fun a ha hwa =>
    thompsonPairCount_eq_zero_of_not_isConj hdatum hQclass heven' hprod' hu hzu hcent hmixedV
      ha hwa
  have hone : InvolutionCounting.thompsonPairCount u z w = 1 :=
    thompsonPairCount_eq_one hdatum hQ hQclass heven' hprod' hu hzu hcent ⟨he, he1⟩ hw2 hwH hV1
  have hthompson := card_mul_card_centralizer_eq_of_single_class hu hdatum.distinguished_order
    (fun hc => hzu hc.symm) hsupp hone hw2
  have hall := fixes_all_of_counts (by omega : 1 < Nat.card Q) hthompson hzH hcardHu hfixcard
  exact hu1 (eq_one_of_fixes_all hsimple hdatum.proper hall)

end CFSG.ShultStronglyClosedTI.MixedClass
