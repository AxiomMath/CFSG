module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20j

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem Subgroup
open CFSG.ASVolI.ChIJK (IsSplitBNPair)

@[expose] def uc22p20kDiv (X : Type) [Group X] [Finite X] : Prop :=
  ∀ U : Sylow 2 X, ∀ Y : Subgroup X, (U : Subgroup X) ≤ Y → ¬ Y ≤ normalizer (U : Set X) →
    ∃ k : ℕ, 1 ≤ k ∧ (2 ^ k + 1) ∣ Nat.card Y

section Unit

variable {X : Type*} [Group X] {B N U : Subgroup X} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem uc22p20k_relIndex_dvd_card_of_mem_Jset [Finite X] {p : ℕ} (hbn : IsBNPair B N S)
    (hS : uc22p20jSplitUnit p B N U) {Y : Subgroup X} (hUY : U ≤ Y) {s : WeylGroup B N}
    (hs : s ∈ uc22p20jJset S Y) : B.relIndex (parabolic B N {s}) ∣ Nat.card Y := by
  have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 hs.1
  have hBP : B ≤ parabolic B N {s} := hbn.le_parabolic hsS
  have hNP : uc22p20jN2J B N U {s} ≤ parabolic B N {s} := hS.N2J_le_parabolic hbn hsS
  have hNY : uc22p20jN2J B N U {s} ≤ Y := hS.N2J_single_le hbn hUY hs
  have hPle : parabolic B N {s} ≤ uc22p20jN2J B N U {s} ⊔ B := hS.parabolic_le_sup hbn hsS
  have hBnorm := hS.B_le_normalizer_N2J {s}
  have hPnorm : parabolic B N {s} ≤ normalizer (uc22p20jN2J B N U {s} : Set X) :=
    hPle.trans (sup_le Subgroup.le_normalizer hBnorm)
  haveI hNn : ((uc22p20jN2J B N U {s}).subgroupOf (parabolic B N {s})).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hPnorm
  set N' := (uc22p20jN2J B N U {s}).subgroupOf (parabolic B N {s}) with hN'
  set B' := B.subgroupOf (parabolic B N {s}) with hB'
  have hsup : B' ⊔ N' = ⊤ := by
    rw [sup_comm, eq_top_iff]
    intro x _
    obtain ⟨n, hn, k, hk, hxe⟩ := uc22p20j_mem_sup_of_le_normalizer hBnorm (hPle x.2)
    have hn' : (⟨n, hNP hn⟩ : ↥(parabolic B N {s})) ∈ N' := hn
    have hk' : (⟨k, hBP hk⟩ : ↥(parabolic B N {s})) ∈ B' := hk
    have hx : x = ⟨n, hNP hn⟩ * ⟨k, hBP hk⟩ := Subtype.ext hxe
    rw [hx]
    exact Subgroup.mul_mem_sup hn' hk'
  have h1 : N'.relIndex (B' ⊔ N') = N'.relIndex B' := Subgroup.relIndex_sup_right B' N'
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have ha : Nat.card B' * B'.index = Nat.card ↥(parabolic B N {s}) := Subgroup.card_mul_index B'
  have hb : Nat.card N' * N'.index = Nat.card ↥(parabolic B N {s}) := Subgroup.card_mul_index N'
  have hc : Nat.card (N'.subgroupOf B') * (N'.subgroupOf B').index = Nat.card B' :=
    Subgroup.card_mul_index _
  have hidx : (N'.subgroupOf B').index = N'.index := h1.symm
  have hpos : 0 < N'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : Nat.card (N'.subgroupOf B') * B'.index = Nat.card N' := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (N'.subgroupOf B') * B'.index * N'.index
        = (Nat.card (N'.subgroupOf B') * (N'.subgroupOf B').index) * B'.index := by rw [hidx]; ring
      _ = Nat.card B' * B'.index := by rw [hc]
      _ = Nat.card N' * N'.index := by rw [ha, hb]
  have hd1 : B'.index ∣ Nat.card N' := Dvd.intro_left _ key
  have hcard : Nat.card N' = Nat.card (uc22p20jN2J B N U {s}) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hd2 : Nat.card (uc22p20jN2J B N U {s}) ∣ Nat.card Y := Subgroup.card_dvd_of_le hNY
  exact (hcard ▸ hd1).trans hd2

theorem uc22p20k_relIndex_eq [Finite X] (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit 2 B N U)
    {s : WeylGroup B N} (hs : s ∈ S) :
    ∃ k : ℕ, 1 ≤ k ∧ B.relIndex (parabolic B N {s}) = 2 ^ k + 1 := by
  classical
  have hss : s * s = 1 := hbn.mul_self_eq_one hs
  have hsS : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 hs
  have hBP : B ≤ parabolic B N {s} := hbn.le_parabolic hsS
  have hUP : U ≤ parabolic B N {s} := hS.hUB.trans hBP
  obtain ⟨sn, hsn⟩ := QuotientGroup.mk_surjective s
  have hsnP : (sn : X) ∈ parabolic B N {s} :=
    hbn.dc_subset_parabolic hsS (Subgroup.subset_closure rfl) (hsn ▸ coe_mem_dc sn)
  obtain ⟨u₀, hu₀U, hu₀B⟩ := hS.exists_unit_conj_not_mem hbn hs hsn
  set P := parabolic B N {s} with hP
  set B' : Subgroup ↥P := B.subgroupOf P with hB'
  set A : Subgroup ↥P := U.subgroupOf P with hA
  haveI hAp : IsPGroup 2 ↥A := hS.hUp.comap_subtype
  let ω₀ : ↥P ⧸ B' := QuotientGroup.mk 1
  let ω₁ : ↥P ⧸ B' := QuotientGroup.mk ⟨(sn : X), hsnP⟩
  have hcover : ∀ ω : ↥P ⧸ B', ω = ω₀ ∨ ω ∈ MulAction.orbit ↥A ω₁ := by
    intro ω
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
    obtain ⟨w₀, hw₀, hxw⟩ := (hbn.mem_parabolic_iff hsS).1 x.2
    rcases eq_one_or_eq_of_mem_closure_singleton hss hw₀ with rfl | rfl
    · left
      show QuotientGroup.mk x = QuotientGroup.mk 1
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.2 (by simpa using B.inv_mem ((mem_dc_one).1 hxw))
    · right
      obtain ⟨u, hu, b, hb, hxe⟩ := hS.dc_form hsn hxw
      refine ⟨⟨⟨u, hUP hu⟩, Subgroup.mem_subgroupOf.2 hu⟩, ?_⟩
      show QuotientGroup.mk (⟨u, hUP hu⟩ * ⟨(sn : X), hsnP⟩) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      have hmul : (((⟨u, hUP hu⟩ : ↥P) * ⟨(sn : X), hsnP⟩)⁻¹ * x : ↥P) = ⟨b, hBP hb⟩ := by
        apply Subtype.ext
        simp [hxe, mul_assoc]
      rw [hmul]
      exact Subgroup.mem_subgroupOf.2 hb
  have hdisj : ω₀ ∉ MulAction.orbit ↥A ω₁ := by
    rintro ⟨a, ha⟩
    have h1 : (QuotientGroup.mk ((a : ↥P) * ⟨(sn : X), hsnP⟩) : ↥P ⧸ B') = QuotientGroup.mk 1 := ha
    rw [QuotientGroup.eq] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    have h3 : ((a : ↥P) : X) * (sn : X) ∈ B := by
      simpa using B.inv_mem h2
    have haU : ((a : ↥P) : X) ∈ U := Subgroup.mem_subgroupOf.1 a.2
    have hsnB : (sn : X) ∈ B := by
      have := B.mul_mem (B.inv_mem (hS.hUB haU)) h3
      simpa [mul_assoc] using this
    have : (sn : WeylGroup B N) = 1 := mk_eq_one_iff.2 hsnB
    rw [hsn] at this
    exact hbn.ne_one hs this
  set a₁ : ↥A := ⟨⟨u₀⁻¹, hUP (U.inv_mem hu₀U)⟩, Subgroup.mem_subgroupOf.2 (U.inv_mem hu₀U)⟩ with ha₁
  have hmove : ω₁ ≠ a₁ • ω₁ := by
    intro h
    have h1 : (QuotientGroup.mk ⟨(sn : X), hsnP⟩ : ↥P ⧸ B') =
        QuotientGroup.mk (⟨u₀⁻¹, hUP (U.inv_mem hu₀U)⟩ * ⟨(sn : X), hsnP⟩) := h
    rw [QuotientGroup.eq] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    apply hu₀B
    simpa [mul_assoc] using B.inv_mem h2
  have hfin : (MulAction.orbit ↥A ω₁).Finite := Set.toFinite _
  have hunion : (Set.univ : Set (↥P ⧸ B')) = {ω₀} ∪ MulAction.orbit ↥A ω₁ := by
    ext ω
    simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, true_iff]
    exact hcover ω
  have hdisj' : Disjoint ({ω₀} : Set (↥P ⧸ B')) (MulAction.orbit ↥A ω₁) := by
    rw [Set.disjoint_singleton_left]; exact hdisj
  have hcard : Nat.card (↥P ⧸ B') = 1 + Nat.card (MulAction.orbit ↥A ω₁) := by
    rw [← Set.ncard_univ, hunion, Set.ncard_union_eq hdisj', Set.ncard_singleton, Nat.card_coe_set_eq]
  obtain ⟨k, hk⟩ := hAp.card_orbit ω₁
  have hge : 2 ≤ Nat.card (MulAction.orbit ↥A ω₁) := by
    have hsub : ({ω₁, a₁ • ω₁} : Set (↥P ⧸ B')) ⊆ MulAction.orbit ↥A ω₁ := by
      intro ω hω
      rcases hω with rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact MulAction.mem_orbit _ _
    rw [Nat.card_coe_set_eq]
    calc 2 = ({ω₁, a₁ • ω₁} : Set (↥P ⧸ B')).ncard := (Set.ncard_pair hmove).symm
      _ ≤ _ := Set.ncard_le_ncard hsub hfin
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk; omega
    · exact h0
  refine ⟨k, hk1, ?_⟩
  have hrel : B.relIndex P = Nat.card (↥P ⧸ B') := Subgroup.index_eq_card B'
  rw [hrel, hcard, hk]
  ring

theorem uc22p20k_exists_div [Finite X] (hbn : IsBNPair B N S) (hS : uc22p20jSplitUnit 2 B N U)
    {Y : Subgroup X} (hUY : U ≤ Y) (hYB : ¬ Y ≤ B) :
    ∃ k : ℕ, 1 ≤ k ∧ (2 ^ k + 1) ∣ Nat.card Y := by
  have hne : (uc22p20jJset S Y).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h := hS.le_parabolic_Jset hbn hUY
    rw [hcon] at h
    exact hYB (h.trans uc22p20j_parabolic_empty_le)
  obtain ⟨s, hs⟩ := hne
  obtain ⟨k, hk1, hk⟩ := uc22p20k_relIndex_eq hbn hS hs.1
  exact ⟨k, hk1, hk ▸ uc22p20k_relIndex_dvd_card_of_mem_Jset hbn hS hUY hs⟩

end Unit

theorem uc22p20k_div_of_splitBN {Z : Type} [Group Z] [Finite Z] {B N : Subgroup Z}
    (hBN : IsSplitBNPair 2 B N) : uc22p20kDiv Z := by
  haveI : (cartan B N).Normal := hBN.normal_inter
  intro U₁ Y hY hYn
  obtain ⟨U, hUnorm, hSU, -⟩ := uc22p20j_exists_splitUnit hBN
  obtain ⟨S, hbn⟩ := CFSG.ASVolI.ChIJK.burnsideI2BN_exists_isBNPair
    (CFSG.ASVolI.ChIJK.burnsideI2BN_toPre hBN)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Z U U₁
  have hmem : ∀ x : Z, x ∈ (U₁ : Subgroup Z) ↔ g⁻¹ * x * g ∈ (U : Subgroup Z) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_apply, mul_assoc]
  let Y' : Subgroup Z := Y.comap (MulAut.conj g).toMonoidHom
  have hUY' : (U : Subgroup Z) ≤ Y' := by
    intro u hu
    show g * u * g⁻¹ ∈ Y
    apply hY
    rw [hmem]
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rw [e]; exact hu
  have hcard : Nat.card Y' = Nat.card Y := by
    have h1 : Y' = Y.map (MulAut.conj g⁻¹).toMonoidHom := by
      ext x
      constructor
      · intro hx
        refine ⟨(MulAut.conj g) x, hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨y, hy, rfl⟩
        show (MulAut.conj g) ((MulAut.conj g⁻¹) y) ∈ Y
        simp only [MulAut.conj_apply]
        have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
        rw [e]; exact hy
    rw [h1]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hYB : ¬ Y' ≤ B := by
    intro hYB
    apply hYn
    intro y hy
    show y ∈ normalizer ((U₁ : Subgroup Z) : Set Z)
    have hb : g⁻¹ * y * g ∈ B := hYB (show (MulAut.conj g) (g⁻¹ * y * g) ∈ Y by
      have e : (MulAut.conj g) (g⁻¹ * y * g) = y := by simp [MulAut.conj_apply, mul_assoc]
      rw [e]; exact hy)
    rw [← hUnorm] at hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmem, hmem]
    have e : g⁻¹ * (y * h * y⁻¹) * g = (g⁻¹ * y * g) * (g⁻¹ * h * g) * (g⁻¹ * y * g)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 hb (g⁻¹ * h * g)
  obtain ⟨k, hk1, hk⟩ := uc22p20k_exists_div hbn hSU hUY' hYB
  exact ⟨k, hk1, hcard ▸ hk⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
