module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveMod
public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCMin
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

@[expose] def iSubFix (V H E : Subgroup G) : Subgroup G :=
  iSub V H E ⊓ Subgroup.centralizer (pCoreOf 2 (kSub V H E) : Set G)

private theorem seven_twelve_setup_conj_mem_centralizer {V₀ : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (V₀ : Set G))
    (hk : k ∈ Subgroup.centralizer (V₀ : Set G)) :
    g * k * g⁻¹ ∈ Subgroup.centralizer (V₀ : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro v hv
  have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem hg) v).mp hv
  have := hk _ hw
  calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
    _ = g * k * g⁻¹ * v := by group

private theorem seven_twelve_setup_normalizer_le_normalizer_centralizer (V₀ : Subgroup G) :
    Subgroup.normalizer (V₀ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V₀ : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => seven_twelve_setup_conj_mem_centralizer hg hx, fun hx => ?_⟩
  have := seven_twelve_setup_conj_mem_centralizer (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem iSubFix_le_iSub : iSubFix V H E ≤ iSub V H E := by
  unfold iSubFix
  exact inf_le_left

theorem pCoreOf_kSub_le_centralizer_iSubFix :
    pCoreOf 2 (kSub V H E) ≤ Subgroup.centralizer (iSubFix V H E : Set G) := by
  refine Subgroup.le_centralizer_iff.mpr ?_
  unfold iSubFix
  exact inf_le_right

theorem kSub_le_normalizer_iSubFix (h : Hyp711 V H E) :
    kSub V H E ≤ Subgroup.normalizer (iSubFix V H E : Set G) := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hIleH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hKNI : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    hKH.trans (le_normalizer_of_subgroupOf_normal hIleH
      (iSub_subgroupOf_normal h.le h.normal))
  have hKNC : kSub V H E ≤
      Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 (kSub V H E) : Set G) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kSub V H E)).trans
      (seven_twelve_setup_normalizer_le_normalizer_centralizer
        (pCoreOf 2 (kSub V H E)))
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  change y ∈ iSubFix V H E ↔ x * y * x⁻¹ ∈ iSubFix V H E
  unfold iSubFix
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr ((Subgroup.mem_normalizer_iff.mp (hKNI hx)) y)
    ((Subgroup.mem_normalizer_iff.mp (hKNC hx)) y)

theorem commutator_iSubFix_sup_pCoreOf (h : Hyp711 V H E) {Y : Subgroup G}
    (hY : Y ≤ kSub V H E) :
    ⁅iSubFix V H E, Y ⊔ pCoreOf 2 (kSub V H E)⁆ = ⁅iSubFix V H E, Y⁆ := by
  have hYNF : Y ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
    hY.trans (kSub_le_normalizer_iSubFix h)
  have hSF : ⁅iSubFix V H E, Y⁆ ≤ iSubFix V H E :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hYNF
  have hSYN : Y ≤ Subgroup.normalizer ((⁅iSubFix V H E, Y⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_of_le hYNF (Subgroup.le_normalizer (H := Y))
  have hSJN : pCoreOf 2 (kSub V H E) ≤
      Subgroup.normalizer ((⁅iSubFix V H E, Y⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    have hbot : ⁅⁅iSubFix V H E, Y⁆, pCoreOf 2 (kSub V H E)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (Subgroup.mem_centralizer_iff.mp
        (pCoreOf_kSub_le_centralizer_iSubFix hj) s (hSF hs)).symm
    rw [hbot]
    exact bot_le
  have hSsub : ((Y : Set G) ∪ (pCoreOf 2 (kSub V H E) : Set G)) ⊆
      Subgroup.normalizer ((⁅iSubFix V H E, Y⁆ : Subgroup G) : Set G) :=
    Set.union_subset hSYN hSJN
  have hgen : ∀ a ∈ iSubFix V H E,
      ∀ y ∈ ((Y : Set G) ∪ (pCoreOf 2 (kSub V H E) : Set G)),
      ⁅a, y⁆ ∈ ⁅iSubFix V H E, Y⁆ := by
    intro a ha y hy
    rcases hy with hyY | hyJ
    · exact Subgroup.commutator_mem_commutator ha hyY
    · have h1 : ⁅a, y⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp (pCoreOf_kSub_le_centralizer_iSubFix hyJ) a ha
      rw [h1]
      exact Subgroup.one_mem _
  apply le_antisymm
  · rw [Subgroup.sup_eq_closure]
    exact commutator_closure_le_of_forall hSsub hgen
  · exact Subgroup.commutator_mono_right le_sup_left

theorem le_centralizer_kSub_of_commutator_eq_bot (h : Hyp711 V H E) {A : Subgroup G}
    (hAK : kSub V H E ≤ Subgroup.normalizer (A : Set G)) (hAV : ⁅A, V⁆ = ⊥) :
    A ≤ Subgroup.centralizer (kSub V H E : Set G) := by
  refine Subgroup.le_centralizer_iff.mp ?_
  unfold kSub
  refine iSup₂_le fun U hU => ?_
  obtain ⟨k, hk, rfl⟩ := h.transitive U hU
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : k * a * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hAK hk) a).mp ha
  have hv' : k * u * k⁻¹ ∈ V := CFSG.Quasithin.mem_conjSubgroup_iff.mp hu
  have hcomm : (k * u * k⁻¹) * (k * a * k⁻¹) = (k * a * k⁻¹) * (k * u * k⁻¹) :=
    Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAV) ha') (k * u * k⁻¹) hv'
  calc a * u = k⁻¹ * ((k * a * k⁻¹) * (k * u * k⁻¹)) * k := by group
    _ = k⁻¹ * ((k * u * k⁻¹) * (k * a * k⁻¹)) * k := by rw [← hcomm]
    _ = u * a := by group


theorem iSubFix_ne_bot (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hV2 : Nat.card (barSub (kSub V H E) φ V) = 2) : iSubFix V H E ≠ ⊥ := by
  have hrel : (pCoreOf 2 (kSub V H E)).relIndex V = 2 := by
    have h := card_barSub_eq_relIndex_of_isBarMap (K := kSub V H E)
      (N := pCoreOf 2 (kSub V H E)) (A := V) (le_kSub h.mem)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E)) hφ
    rw [hV2] at h
    exact h.symm
  have hcard : 2 * Nat.card ↥(pCoreOf 2 (kSub V H E) ⊓ V) = Nat.card V := by
    simpa only [hrel] using
      Subgroup.relIndex_mul_card (H := pCoreOf 2 (kSub V H E)) (K := V)
  have hgt : 1 < Nat.card ↥(pCoreOf 2 (kSub V H E) ⊓ V) := by
    have h2 : 2 * 1 < 2 * Nat.card ↥(pCoreOf 2 (kSub V H E) ⊓ V) := by
      rw [hcard]
      simpa using h.noncyclic
    exact lt_of_mul_lt_mul_left h2 (Nat.zero_le 2)
  have hJinfV_ne : pCoreOf 2 (kSub V H E) ⊓ V ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot (pCoreOf 2 (kSub V H E) ⊓ V)).mp hgt
  have hVI_ne : V ⊓ iSub V H E ≠ ⊥ := by
    rw [inf_iSub_eq_inf_J h.mem h.iSub_le h.pcore_le, inf_comm]
    exact hJinfV_ne
  have hIne : iSub V H E ≠ ⊥ := fun hbot => hVI_ne (by rw [hbot, inf_bot_eq])
  have hI : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hIp : IsPGroup 2 ↥(iSub V H E) := isPGroup_two_of_isElemAbelian hI
  have hIab : ∀ a ∈ iSub V H E, ∀ b ∈ iSub V H E, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hI.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hIleH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hHNI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal)
  have hJNI : pCoreOf 2 (kSub V H E) ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E)).trans (hKH.trans hHNI)
  have hJp : IsPGroup 2 ↥(pCoreOf 2 (kSub V H E)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (kSub V H E)
  have hPB : pCoreOf 2 (kSub V H E) ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp
  have hBA : (⊥ : Subgroup G) < iSub V H E := lt_of_le_of_ne bot_le (Ne.symm hIne)
  obtain ⟨a, haI, haB, hcommJ⟩ :=
    exists_mem_sdiff_forall_commutator_mem (P := pCoreOf 2 (kSub V H E))
      (A := iSub V H E) (B := ⊥) hJp hIp hIab hJNI hPB hBA
  have haC : a ∈ Subgroup.centralizer (pCoreOf 2 (kSub V H E) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp (hcommJ n hn))).symm
  have haF : a ∈ iSubFix V H E := by
    unfold iSubFix
    exact ⟨haI, haC⟩
  exact fun hbot => haB (hbot ▸ haF)

theorem sevenSevenModule_commutator_iSubFix (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {V₂ V₃ : Subgroup G} (hV₂ : V₂ ∈ omegaSet V H E) (hV₃ : V₃ ∈ omegaSet V H E)
    (hperf : ⁅barSub (kSub V H E) φ (V ⊔ V₂ ⊔ V₃), barSub (kSub V H E) φ (V ⊔ V₂ ⊔ V₃)⁆ =
      barSub (kSub V H E) φ (V ⊔ V₂ ⊔ V₃))
    (hne : ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ ≠ ⊥) :
    SevenSevenModule V H E V V₂ V₃ ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ := by
  have hXK : V ⊔ V₂ ⊔ V₃ ≤ kSub V H E :=
    sup_le (sup_le (le_kSub h.mem) (le_kSub hV₂)) (le_kSub hV₃)
  have hXNF : V ⊔ V₂ ⊔ V₃ ≤ Subgroup.normalizer (iSubFix V H E : Set G) :=
    hXK.trans (kSub_le_normalizer_iSubFix h)
  have hAF : ⁅iSubFix V H E, V ⊔ V₂ ⊔ V₃⁆ ≤ iSubFix V H E :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hXNF
  have hI : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hFab : ∀ a ∈ iSubFix V H E, ∀ b ∈ iSubFix V H E, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (hI.1.is_comm.comm ⟨a, iSubFix_le_iSub ha⟩ ⟨b, iSubFix_le_iSub hb⟩)
  have hJle : pCoreOf 2 (kSub V H E) ≤ Subgroup.centralizer (iSubFix V H E : Set G) :=
    pCoreOf_kSub_le_centralizer_iSubFix
  have hperf' : ∀ x ∈ V ⊔ V₂ ⊔ V₃, ∃ c ∈ ⁅V ⊔ V₂ ⊔ V₃, V ⊔ V₂ ⊔ V₃⁆,
      c⁻¹ * x ∈ pCoreOf 2 (kSub V H E) :=
    exists_mem_commutator_inv_mul_mem hφ hXK hperf
  refine ⟨hAF.trans iSubFix_le_iSub, ?_, ?_, hne⟩
  · exact le_normalizer_commutator_of_le_of_le hXNF
      (Subgroup.le_normalizer (H := V ⊔ V₂ ⊔ V₃))
  · exact commutator_commutator_eq_of_forall_inv_mul_mem hFab hXNF hJle hperf'

end CFSG.LocalAnalysis.WeakClosure81
