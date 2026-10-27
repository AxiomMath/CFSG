module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenConfB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup CFSG.ASVolI.ChIJK
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem seven_sixteen (hF₁ : PSUThreeRootFacts) (hF₂ : PerfectPSUThreeFact)
    {V H E : Subgroup G} (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} (hφ : IsBarMap (kSub V H E) (iSub V H E) φ) {n : ℕ}
    (hQ : IsPSUGp (Q ⧸ Subgroup.center Q) 3 n) (hn : rk ↥(barSub (kSub V H E) φ V) = n)
    {X : Subgroup G} (hXK : X ≤ kSub V H E) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card ↥X))
    (hXC : ∀ x ∈ X, ∀ v ∈ V, ⁅x, v⁆ ∈ iSub V H E) :
    ⁅V ⊓ iSub V H E, X⁆ ≠ ⊥ := by
  intro hcomm
  have hVK : V ≤ kSub V H E := le_kSub h.mem
  have hIK : iSub V H E ≤ kSub V H E := iSub_le_kSub V H E
  have hn2 : 2 ≤ n := two_le_of_isPSUGp hQ
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := nontrivial_of_isPSUGp hQ
  have hxI : ∀ w ∈ V ⊓ iSub V H E, ∀ x ∈ X, ⁅w, x⁆ = 1 := fun w hw x hx => by
    have hmem := Subgroup.commutator_mem_commutator hw hx
    rw [hcomm] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hVZ : barSub (kSub V H E) φ V ⊓ Subgroup.center Q = ⊥ := barSub_inf_center_eq_bot h hφ
  have hψ : Function.Surjective ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) :=
    (QuotientGroup.mk'_surjective _).comp hφ.surjective
  have hcard : Nat.card ↥(barSub (kSub V H E)
      ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) V) = 2 ^ n := by
    rw [card_barSub_comp_mk φ hVZ]
    exact card_barSub_eq_two_pow h hn
  have hxcomm : ∀ x w : ↥(kSub V H E), (x : G) ∈ X → ((⁅x, w⁆ : ↥(kSub V H E)) : G) ∈ iSub V H E →
      Commute (φ x) (φ w) := by
    intro x w _ hw
    have h2 : φ ⁅x, w⁆ = 1 := (hφ.ker_iff _).mpr hw
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_commute.mp h2
  have hXV : ∀ x v : ↥(kSub V H E), (x : G) ∈ X → (v : G) ∈ V →
      Commute (((QuotientGroup.mk' (Subgroup.center Q)).comp φ) x)
        (((QuotientGroup.mk' (Subgroup.center Q)).comp φ) v) := fun x v hx hv =>
    (hxcomm x v hx (hXC _ hx _ hv)).map (QuotientGroup.mk' (Subgroup.center Q))
  obtain ⟨a, b, hVa, hS, hMtop, hXA⟩ :=
    exists_good_conjugates hF₁ hVK h.elemAbelian hψ hQ hcard hXK hXodd hXV
  have ha : (a : G) ∈ kSub V H E := a.2
  have hb : (b : G) ∈ kSub V H E := b.2
  have hAK : conjSubgroup V (a : G) ≤ kSub V H E :=
    le_kSub (conjSubgroup_mem_omegaSet_of_mem_kSub h ha)
  have hBK : conjSubgroup V (b : G) ≤ kSub V H E :=
    le_kSub (conjSubgroup_mem_omegaSet_of_mem_kSub h hb)
  obtain ⟨hP, hP'⟩ := pairHyp_conj h ha hVa
  have hker := pair_kernel_eq hP hVK hAK ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) hn2 hS
  obtain ⟨hN1, hN2⟩ := nIn_eq_inf_iSub h hφ hVZ hker
  have hYI : pairY V (conjSubgroup V (a : G)) ≤ iSub V H E := by
    unfold pairY
    rw [hN1, hN2]
    exact sup_le inf_le_right inf_le_right
  have hperf : commutator Q = ⊤ :=
    commutator_eq_top_of_pair hφ hVK hAK hn2 hS hker hYI (normalClosure_barSub_iSub_eq_top h hφ)
  have hMK : V ⊔ conjSubgroup V (a : G) ⊔ conjSubgroup V (b : G) ≤ kSub V H E :=
    sup_le (sup_le hVK hAK) hBK
  have hKeq : kSub V H E = iSub V H E ⊔ (V ⊔ conjSubgroup V (a : G) ⊔ conjSubgroup V (b : G)) :=
    eq_sup_of_perfect hφ hIK hMK hperf hMtop
  have hpow : ∀ x : G, x ∈ X → x ^ Nat.card ↥X = 1 := fun x hx => by
    have hx1 : (⟨x, hx⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    have hx2 := congrArg Subtype.val hx1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hx2
  have hXA' : ∀ x ∈ X, ∀ w ∈ conjSubgroup V (a : G), ⁅x, w⁆ ∈ iSub V H E := by
    intro x hx w hw
    have hx' : (⟨x, hXK hx⟩ : ↥(kSub V H E)) ^ Nat.card ↥X = 1 := Subtype.ext (hpow x hx)
    have hw' : (⟨w, hAK hw⟩ : ↥(kSub V H E)) * ⟨w, hAK hw⟩ = 1 :=
      Subtype.ext (CFSG.Open.IsElemAbelian.mul_self_eq_one
        (isElemAbelian_conjSubgroup' h.elemAbelian (a : G)) hw)
    exact commutator_mem_of_odd hφ hXodd hx' hw' (hXA ⟨x, hXK hx⟩ ⟨w, hAK hw⟩ hx hw)
  have hXY : ∀ x ∈ X, pairY V (conjSubgroup V (a : G)) ≤ Subgroup.centralizer ({x} : Set G) :=
    fun x hx => pairY_le_centralizer h ha hP' hN1 (fun w hw => hXA' x hx w hw)
      (fun w hw => hxI w hw x hx)
  have hRg : conjSubgroup (barSub (kSub V H E) φ V) (φ a) =
      barSub (kSub V H E) φ (conjSubgroup V (a : G)) := (barSub_conjSubgroup φ V a).symm
  have hRL : barSub (kSub V H E) φ V ⊔ conjSubgroup (barSub (kSub V H E) φ V) (φ a) =
      barSub (kSub V H E) φ (V ⊔ conjSubgroup V (a : G)) := by
    rw [hRg, barSub_sup hVK hAK φ]
  have hXL : barSub (kSub V H E) φ X ≤
      Subgroup.centralizer (barSub (kSub V H E) φ (V ⊔ conjSubgroup V (a : G)) : Set Q) := by
    rw [Subgroup.le_centralizer_iff, barSub_sup hVK hAK φ]
    refine sup_le ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩ _ ⟨x, hx, rfl⟩
      exact (hxcomm x v hx (hXC _ hx _ hv)).eq
    · rintro _ ⟨w, hw, rfl⟩ _ ⟨x, hx, rfl⟩
      exact (hxcomm x w hx (hXA' x hx w hw)).eq
  have hg : conjSubgroup (barSub (kSub V H E) φ V) (φ a) ≠ barSub (kSub V H E) φ V := by
    intro heq
    have h1 : barSub (kSub V H E) φ (V ⊔ conjSubgroup V (a : G)) =
        barSub (kSub V H E) φ V := by
      rw [← hRL, heq, sup_idem]
    have h3 : barSub (kSub V H E) ((QuotientGroup.mk' (Subgroup.center Q)).comp φ)
        (V ⊔ conjSubgroup V (a : G)) = barSub (kSub V H E)
          ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) V := by
      rw [barSub_comp, barSub_comp, h1]
    rw [h3] at hS
    haveI := (isElemAbelian_barSub h.elemAbelian
      ((QuotientGroup.mk' (Subgroup.center Q)).comp φ)).1
    exact not_isSolvable_of_isL2Gp hn2 hS
      (isSolvable_of_comm fun u v => Subtype.ext (setLike_mul_comm u.2 v.2))
  have hXbar_odd : Odd (Nat.card ↥(barSub (kSub V H E) φ X)) := by
    have hdvd : Nat.card ↥(barSub (kSub V H E) φ X) ∣
        Nat.card ↥(X.subgroupOf (kSub V H E)) :=
        Subgroup.card_map_dvd (X.subgroupOf (kSub V H E)) φ
    have hc : Nat.card ↥(X.subgroupOf (kSub V H E)) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
    rw [hc] at hdvd
    exact Odd.of_dvd_nat hXodd hdvd
  obtain ⟨x₁, hx₁X, hx₁⟩ := exists_not_central h hφ hXK hX1 hXodd hxI
  have hXnc : ¬ barSub (kSub V H E) φ X ≤ Subgroup.center Q := fun hle =>
    hx₁ (hle (mem_barSub.mpr ⟨x₁, hx₁X, rfl⟩))
  obtain ⟨k, x, hx, hk1, hk2⟩ := hF₂ Q n hperf hQ _ (isElemAbelian_barSub h.elemAbelian φ)
    (card_barSub_eq_two_pow h hn) (φ a) hg _ hXbar_odd (by rw [hRL]; exact hXL) hXnc
  obtain ⟨x₀, hx₀, rfl⟩ := mem_barSub.mp hx
  obtain ⟨k₀, rfl⟩ := hφ.surjective k
  have hy₁ : φ (k₀⁻¹ * x₀ * k₀) ∈ barSub (kSub V H E) φ (V ⊔ conjSubgroup V (a : G)) ⊔
      barSub (kSub V H E) φ X := by
    rw [map_mul, map_mul, map_inv]
    rwa [hRL] at hk1
  have hy₂ : φ (k₀⁻¹ * x₀ * k₀) ∉ barSub (kSub V H E) φ X := by
    rw [map_mul, map_mul, map_inv]
    exact hk2
  have hbot := inf_centralizer_conj_eq_bot h hφ ha hP hn2 hS hYI hXK hXodd hXY hXL hx₀ hy₁ hy₂
  have hk₀ : (k₀ : G) ∈ Subgroup.normalizer (iSub V H E : Set G) :=
    kSub_le_normalizer_iSub h k₀.2
  have hcardC := card_inf_centralizer_conj hk₀ (x₀ : G)
  have hYle : pairY V (conjSubgroup V (a : G)) ≤
      iSub V H E ⊓ Subgroup.centralizer ({(x₀ : G)} : Set G) := le_inf hYI (hXY _ hx₀)
  refine false_of_card_bounds (I := iSub V H E) (Y := pairY V (conjSubgroup V (a : G)))
    (C := iSub V H E ⊓ Subgroup.centralizer
      ({((k₀⁻¹ * x₀ * k₀ : ↥(kSub V H E)) : G)} : Set G))
    (T := V ⊓ iSub V H E) hYI inf_le_left ?_ (inf_iSub_ne_bot h) ?_ ?_
    (card_iSub_le_pow_three h ha hb hKeq)
  · rw [← inf_assoc, inf_eq_left.mpr hYI]
    exact hbot
  · rw [card_pairY hP, hN1, hN2, card_conjSubgroup_inf_iSub h ha, sq]
  · exact (Subgroup.card_le_of_le hYle).trans hcardC.symm.le

end CFSG.LocalAnalysis.WeakClosure81
