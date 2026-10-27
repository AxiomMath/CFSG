module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreHyp
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreWeight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem odd_card_fusionOddCore' (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

section Core


theorem seven_eight_core {V H E J L N : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) (hNK : N ≤ kSub V H E)
    (hNnorm : kSub V H E ≤ Subgroup.normalizer (N : Set G))
    (hJN : kSub V H E ⊓ J ≤ N) (hNodd : Odd ((kSub V H E ⊓ J).relIndex N)) :
    ⁅L, N⁆ ≤ J := by
  have hVnotJ : ¬ V ≤ J := by
    obtain ⟨g, -, -, hnotO⟩ := mem_omegaSet.mp h.mem
    intro hVJ
    exact hnotO (hVJ.trans h.pcore_le)
  obtain ⟨v, hv, hvJ⟩ := Set.not_subset.mp hVnotJ
  haveI : (J.subgroupOf H).Normal := h.jnormal
  let Q := ↥H ⧸ J.subgroupOf H
  let φ : ↥H →* Q := QuotientGroup.mk' (J.subgroupOf H)
  have hφ : IsBarMap H J φ :=
    ⟨QuotientGroup.mk'_surjective (J.subgroupOf H), fun k => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]⟩
  haveI : Finite Q := Quotient.finite _
  have hvH : v ∈ H := h.omega_le V h.mem hv
  have hNH : N ≤ H := hNK.trans (kSub_le_of_forall_le h.omega_le)
  apply Hyp78.commutator_le_of_forall_commutator_mem h hV2 hNK hNnorm hv hvJ
  intro n hn
  by_contra hcon
  have hNe : ⁅barSub H φ N, Subgroup.zpowers (φ ⟨v, hvH⟩)⁆ ≠ ⊥ := by
    intro hbot
    exact hcon (forall_commutator_mem_of_commutator_eq_bot hφ hNH hvH hbot n hn)
  have hF : SevenEightFrame (barSub H φ L) (barSub H φ (pCoreOf 2 L))
      (barSet H φ {u | ∃ U ∈ omegaWithin V H E L, u ∈ U ∧ u ∉ J})
      (φ ⟨v, hvH⟩) :=
    Hyp78.sevenEightFrame h hV2 hφ hv hvJ
  have hvbL : φ ⟨v, hvH⟩ ∈ barSub H φ L := by
    rw [← hF.closure_eq]
    exact Subgroup.subset_closure hF.mem
  have hvb2 : φ ⟨v, hvH⟩ * φ ⟨v, hvH⟩ = 1 := hF.mul_self _ hF.mem
  have hLN : barSub H φ L ≤ Subgroup.normalizer ((barSub H φ N : Subgroup Q) : Set Q) :=
    barSub_le_normalizer_barSub φ (h.le_kSub.trans hNnorm)
  obtain ⟨Xb, hXN, hX⟩ := exists_isMinCommInvariant_le hLN hNe
  have hNodd' : Odd (Nat.card (barSub H φ N)) :=
    Hyp78.odd_card_barSub h hφ hNK hJN hNodd
  have hodd : Odd (Nat.card Xb) := hNodd'.of_dvd_nat (Subgroup.card_dvd_of_le hXN)
  obtain ⟨p, hp, hp2, hXp⟩ := hX.exists_prime_isPGroup hvbL hvb2 hodd
  have hcl : ∀ x ∈ Xb, ∀ y ∈ Xb, ∀ z ∈ Xb, ⁅⁅x, y⁆, z⁆ = 1 :=
    hX.commutator_commutator_eq_one hvbL hvb2 hp hp2 hXp
  have hexp : ∀ x ∈ Xb, x ^ p = 1 :=
    hX.pow_eq_one hvbL hvb2 hp hp2 hXp hcl
  have hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q) := hX.normalizes
  have hne : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hvH⟩),
      ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥ := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact hX.commutator_conj_ne_bot (hF.le hx)
  have hcent := Hyp78.commute_of_mem_commutator_zpowers_deltaSet h hV2 hφ hv hvJ hXL hp hp2
    hXp hexp hne
  have hinf := Hyp78.inf_commutator_zpowers_eq_bot h hV2 hφ hv hvJ hXL hp hp2 hXp hexp hne
  obtain ⟨hXab, hgen⟩ := hF.isMulCommutative_and_iSup_eq hX hp hp2 hXp hcl hcent hinf
  have hMleXb : ∀ a : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hvH⟩)),
      ⁅Xb, Subgroup.zpowers (a : Q)⁆ ≤ Xb := by
    intro a
    have h := le_iSup (fun a : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hvH⟩)) =>
      ⁅Xb, Subgroup.zpowers (a : Q)⁆) a
    rw [hgen] at h
    exact h
  have hcard : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hvH⟩),
      Nat.card ↥(⁅Xb, Subgroup.zpowers a⁆ : Subgroup Q) = p := by
    intro a ha
    exact Hyp78.card_commutator_zpowers_eq h hV2 hφ hv hvJ hXL hp hp2 hXp hexp ha (hne a ha)
      (fun m hm m' hm' => hXab m (hMleXb ⟨a, ha⟩ hm) m' (hMleXb ⟨a, ha⟩ hm'))
  obtain ⟨d, hdD, h3⟩ := hF.exists_pow_three
  obtain ⟨k₀, hk₀S, hk₀d⟩ := mem_barSet.mp hdD
  obtain ⟨U₀, hU₀, hk₀U₀, hk₀J⟩ := hk₀S
  have hXK : Xb ≤ barSub H φ (kSub V H E) :=
    hXN.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono H hNK))
  obtain ⟨k, l, hmap⟩ := Hyp78.exists_map_conj_eq h hV2 hφ hv hvJ hXK hXL hp hp2 hXab hexp
    hgen hcent hcard hU₀.1 hU₀.2 hk₀U₀ hk₀J
  have hd_eq : φ ⟨(k₀ : G), h.omega_le U₀ hU₀.1 hk₀U₀⟩ = d := by
    rw [show (⟨(k₀ : G), h.omega_le U₀ hU₀.1 hk₀U₀⟩ : ↥H) = k₀ from Subtype.ext rfl, hk₀d]
  rw [hd_eq] at hmap
  exact hF.false_of_map_conj_eq hX hodd hXab hcent (hF.mul_self d hdD) h3 hmap

theorem seven_eight {V H E J L N : Subgroup G} (h : Hyp78 V H E J L)
    (hNK : N ≤ kSub V H E) (hNnorm : kSub V H E ≤ Subgroup.normalizer (N : Set G))
    (hJN : kSub V H E ⊓ J ≤ N) (hNodd : Odd ((kSub V H E ⊓ J).relIndex N)) :
    ⁅L, N⁆ ≤ J := by
  have hVnotJ : ¬ V ≤ J := by
    obtain ⟨g, -, -, hnotO⟩ := mem_omegaSet.mp h.mem
    intro hVJ
    exact hnotO (hVJ.trans h.pcore_le)
  have hne1 : J.relIndex V ≠ 1 := fun h1 => hVnotJ (Subgroup.relIndex_eq_one.mp h1)
  have hne0 : J.relIndex V ≠ 0 := by
    haveI : Finite (↥V ⧸ (J.subgroupOf V)) := inferInstance
    exact Subgroup.index_ne_zero_of_finite
  rcases eq_or_lt_of_le (show 2 ≤ J.relIndex V by omega) with h2 | h2
  · exact seven_eight_core h h2.symm hNK hNnorm hJN hNodd
  · exact commutator_le_of_two_lt_relIndex h.toHyp73 h.transitive h2 h.le_kSub h.generated
      hNK hNnorm hJN hNodd

theorem seven_eight_barSub {V H E J L : Subgroup G} (h : Hyp78 V H E J L) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) :
    ⁅barSub (kSub V H E) φ L, fusionOddCore X⁆ = ⊥ := by
  let N₀ : Subgroup G := ((fusionOddCore X).comap φ).map (kSub V H E).subtype
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hN₀K : N₀ ≤ kSub V H E := Subgroup.map_subtype_le _
  have hN₀norm : kSub V H E ≤ Subgroup.normalizer (N₀ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk n hn
    obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hn
    rw [Subgroup.mem_map]
    refine ⟨⟨k, hk⟩ * n' * ⟨k, hk⟩⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hconj : φ (⟨k, hk⟩ * n' * ⟨k, hk⟩⁻¹) =
        φ ⟨k, hk⟩ * φ n' * (φ ⟨k, hk⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact (inferInstance : (fusionOddCore X).Normal).conj_mem (φ n') hn' (φ ⟨k, hk⟩)
  have hJN₀ : kSub V H E ⊓ J ≤ N₀ := by
    intro j hj
    obtain ⟨hjK, hjJ⟩ := Subgroup.mem_inf.mp hj
    rw [Subgroup.mem_map]
    refine ⟨⟨j, hjK⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, (hφ.ker_iff ⟨j, hjK⟩).mpr hjJ]
    exact (fusionOddCore X).one_mem
  have hφ' : IsBarMap (kSub V H E) (kSub V H E ⊓ J) φ :=
    ⟨hφ.surjective, fun k => by
      rw [hφ.ker_iff k]
      exact ⟨fun hkJ => Subgroup.mem_inf.mpr ⟨k.2, hkJ⟩,
        fun hk => (Subgroup.mem_inf.mp hk).2⟩⟩
  have hObar : barSub (kSub V H E) φ N₀ = fusionOddCore X := by
    change (N₀.subgroupOf (kSub V H E)).map φ = fusionOddCore X
    have hsub : N₀.subgroupOf (kSub V H E) = (fusionOddCore X).comap φ := by
      change (((fusionOddCore X).comap φ).map (kSub V H E).subtype).subgroupOf
          (kSub V H E) = (fusionOddCore X).comap φ
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (kSub V H E).subtype_injective]
    rw [hsub]
    exact Subgroup.map_comap_eq_self_of_surjective hφ.surjective (fusionOddCore X)
  have hN₀odd : Odd ((kSub V H E ⊓ J).relIndex N₀) := by
    rw [← card_barSub_eq_relIndex_of_isBarMap (K := kSub V H E) (N := kSub V H E ⊓ J)
      (A := N₀) hN₀K inf_le_left hφ']
    rw [hObar]
    exact odd_card_fusionOddCore' X
  have hseven : ⁅L, N₀⁆ ≤ J := seven_eight h hN₀K hN₀norm hJN₀ hN₀odd
  refine le_bot_iff.mp ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot]
  obtain ⟨l, hlL, rfl⟩ := mem_barSub.mp hx
  rw [← hObar] at hy
  obtain ⟨n, hnN₀, rfl⟩ := mem_barSub.mp hy
  rw [← map_commutatorElement φ l n]
  refine (hφ.ker_iff ⁅l, n⁆).mpr ?_
  rw [show ((⁅l, n⁆ : ↥(kSub V H E)) : G) = ⁅(l : G), (n : G)⁆ from
    map_commutatorElement (kSub V H E).subtype l n]
  exact hseven (Subgroup.commutator_mem_commutator hlL hnN₀)

end Core

end CFSG.LocalAnalysis.WeakClosure81
