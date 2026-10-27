module

public import CFSG.Quasithin.EmptyFaithful.E23JRepl
public import CFSG.Quasithin.Vol2.Ch3wJ
public import CFSG.Quasithin.Vol2.Ch3wPair
public import CFSG.Quasithin.Vol2.Ch3xLem317
public import CFSG.Quasithin.EmptyFaithful.S152FinChief
public import CFSG.Quasithin.Vol2.Ch3zGood

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits G6 RegularWreathProduct
  CFSG.Quasithin.Ch3z CFSG.Quasithin.Ch3w

namespace E23J

section Block

variable {V : Type} [CommGroup V] [Finite V] {X H₁ H₂ : Subgroup (MulAut V)} {m : ℕ}

theorem not_commute_of_mem_left (h : TwoBlk X H₁ H₂ m) {a x : MulAut V} (haH : a ∈ H₁)
    (ha1 : a ≠ 1) (hxX : x ∈ X) (hx : x ∉ H₁ ⊔ H₂) : x * a * x⁻¹ ≠ a := by
  intro hc
  rcases h.conj_block hxX with h1 | h2
  · refine hx (h.mem_sup_of_normalizes hxX ?_)
    refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
    · have : x * y * x⁻¹ ∈ B6.conjSub x H₁ := B6.mem_conjSub.mpr (by simpa [mul_assoc] using hy)
      rwa [h1] at this
    · have hy' : y ∈ B6.conjSub x H₁ := by rwa [h1]
      simpa [mul_assoc] using B6.mem_conjSub.mp hy'
  · have hc' : x⁻¹ * a * x = a := by
      calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [hc]
        _ = a := by group
    have : a ∈ B6.conjSub x H₁ := B6.mem_conjSub.mpr (by rw [hc']; exact haH)
    rw [h2] at this
    have hmem : a ∈ H₁ ⊓ H₂ := ⟨haH, this⟩
    rw [h.inf, Subgroup.mem_bot] at hmem
    exact ha1 hmem

theorem not_commute_of_mem_right (h : TwoBlk X H₁ H₂ m) {a x : MulAut V} (haH : a ∈ H₂)
    (ha1 : a ≠ 1) (hxX : x ∈ X) (hx : x ∉ H₁ ⊔ H₂) : x * a * x⁻¹ ≠ a :=
  not_commute_of_mem_left h.symm haH ha1 hxX (by rwa [sup_comm])

end Block

section Setting

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem setting_of_quadratic (h : Hyp319 T M M₀ H V) (hT : quasithinIsSylowTwo T)
    (hsq : IsSQTKSub H) (hD125 : D15Proof.D125 H T (conjClosure V H))
    (hser : IsChiefSeriesFrom H (conjClosure V H) (conjClosure V H) 2) {D : Subgroup G}
    (hDT : IsMaxElemAbelian T D) (hDn : ¬ D ≤ pCoreOf 2 H)
    (hDq : ⁅⁅conjClosure V H, D⁆, D⁆ = ⊥) :
    Setting H T (H ⊓ M) (conjClosure V H) D := by
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hUe := D15Proof.isElemAbelian_conjClosure hD hnff h.le_pCore
  have hUT := conjClosure_le_T hD h.le_pCore
  have hTH : T ≤ H := h.hStar.1.1
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V h.reduced.2.2.1 := h.q_eq.ge
  have hDnc := not_le_centralizer_conjClosure hD hnff hDT.1 hDn
  obtain ⟨-, -, -, -, hst, -⟩ := Ch3y.chain_two hD hnff h.le_pCore hD125 hq2 le_rfl hser
    hDT.1 hDT.2.1 hDq hDnc (card_le_relIndex_mul_card hUe hUT hDT)
  refine ⟨hmp, hsq, hUT, hUe, hDT, hDn, fun L N hstep hnc => ?_⟩
  obtain ⟨hu₀, hD'⟩ := hst L N hstep hnc
  have hL : IsNormalIn H (conjClosure V H) L := hstep.2.1
  have hNH : N ≤ H := hstep.1.1.trans (hUT.trans hTH)
  refine ⟨?_, ?_⟩
  · rw [cSecIn_eq_centralizerMod (U := conjClosure V H) (H := H) (hDT.1.trans hTH) hL, hD',
      inf_comm]
  · rw [fixSecIn_eq_centralizerMod (U := conjClosure V H) hNH hL]
    exact count_four_of (centralizerMod_le_left L N D) hu₀

end Setting

section Image

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem chiefPsi_eq_one_of_mem (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N) {u : G}
    (hu : u ∈ U) : chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨u, h.UH hu⟩ = 1 := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := h.hNL hstep
  have hg := (chiefHom_eq_one_iff hHL hHN hNL ⟨u, h.UH hu⟩).2 ⟨h.UH hu, hHL (h.UH hu),
    fun n hn => ?_⟩
  · exact congrArg Subtype.val hg
  · have hcomm := h.Ue.1.is_comm.comm ⟨u, hu⟩ ⟨n, hstep.1.1 hn⟩
    have e : u * n * u⁻¹ * n⁻¹ = 1 := by
      have := congrArg Subtype.val hcomm
      simp only [Subgroup.coe_mul] at this
      rw [this]
      group
    rw [e]
    exact L.one_mem

theorem chiefImg_eq_bot_of_le_pCore (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    {K : Subgroup G} (hK : K ≤ pCoreOf 2 H) :
    chiefImg (Setting.hHL hstep) (Setting.hHN hstep) K = ⊥ := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := h.hNL hstep
  rw [eq_bot_iff]
  rintro y ⟨a, ha, rfl⟩
  have haP : (a : G) ∈ pCoreOf 2 H := hK (Subgroup.mem_subgroupOf.mp ha)
  rw [Subgroup.mem_bot]
  have hg := (chiefHom_eq_one_iff hHL hHN hNL a).2 ⟨a.2, hHL a.2,
    fun n hn => S152Fin.commutator_pCoreOf_le h.Ue hstep (a : G) haP n hn⟩
  exact congrArg Subtype.val hg

theorem chiefImg_mono_of_le_sup (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    {D A' : Subgroup G} (hDA : D ≤ A' ⊔ U) (hA'H : A' ≤ H) :
    chiefImg (Setting.hHL hstep) (Setting.hHN hstep) D ≤
      chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A' := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hUH := h.UH
  have hψU : (U.subgroupOf H).map (chiefPsi hHL hHN) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨u, hu, rfl⟩
    rw [Subgroup.mem_bot]
    exact chiefPsi_eq_one_of_mem h hstep (Subgroup.mem_subgroupOf.mp hu)
  unfold chiefImg
  calc (D.subgroupOf H).map (chiefPsi hHL hHN)
      ≤ ((A' ⊔ U).subgroupOf H).map (chiefPsi hHL hHN) :=
        Subgroup.map_mono (Subgroup.comap_mono hDA)
    _ = (A'.subgroupOf H ⊔ U.subgroupOf H).map (chiefPsi hHL hHN) := by
        rw [Subgroup.subgroupOf_sup hA'H hUH]
    _ = (A'.subgroupOf H).map (chiefPsi hHL hHN) := by
        rw [Subgroup.map_sup, hψU, sup_bot_eq]

theorem chiefImg_le_base (hB1 : B69One) (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N)
    (hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 H →
      ∃ D : Subgroup G, Setting H T M₂ U D ∧ D ≤ A' ⊔ U)
    {m : ℕ} {H₁ H₂ : Subgroup (MulAut ↥(chiefMod L N))}
    {θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)} {θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)}
    {β₁ β₂ : ↥(coreMod m) →* ↥(chiefMod L N)}
    {Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥(chiefAut H L N)}
    (hd : @WreathData ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T) m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ)
    {A' : Subgroup G} (hA' : IsMaxElemAbelian T A') :
    chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A' ≤ H₁ ⊔ H₂ := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  have hA'H : A' ≤ H := hA'.1.trans h.mp.isSylow.1
  by_cases hA'R : A' ≤ pCoreOf 2 H
  · rw [chiefImg_eq_bot_of_le_pCore h hstep hA'R]
    exact bot_le
  · obtain ⟨D, hD, hDA⟩ := hrepl A' hA' hA'R
    have hstrong := h.noStrong hB1 hstep hnc
    obtain ⟨hDe, hD1, hDoff⟩ := hD.offender hstep hnc
    have hDX : chiefImg hHL hHN D ≤ chiefAut H L N := chiefImg_le_chiefAut hHL hHN D
    have hDJ : chiefImg hHL hHN D ≤ H₁ ⊔ H₂ :=
      hd.ffJ_eq ▸ le_ffJ_of_offender hstrong hDX hDe hD1 hDoff
    have hodd := hd.tb.exists_odd_offender θ₁ θ₂ β₁ β₂ hd.eq₁ hd.range₁ hd.ker₁ hd.eq₂ hd.range₂
      hd.ker₂ hstrong hDJ hDe hD1 hDoff
    have hDA' : chiefImg hHL hHN D ≤ chiefImg hHL hHN A' :=
      chiefImg_mono_of_le_sup h hstep hDA hA'H
    have hA'e : IsElemAbelian2 (chiefImg hHL hHN A') := by
      rw [chiefImg_eq_autOn hHL hHN hA'H]
      have hBt : IsElemAbelian 2 (secImg (Subgroup.normalizer (L : Set G)) L A') :=
        isElemAbelian_secImg hA'.2.1
      have hn := secImg_le_normalizer_secImg (K := L) (E := N) (X := A') (hA'H.trans hHN)
      exact isElemAbelian2_autOn hE hBt hn
    intro x hx
    by_contra hxn
    have hxX : x ∈ chiefAut H L N := chiefImg_le_chiefAut hHL hHN A' hx
    have hcomm : ∀ a ∈ chiefImg hHL hHN D, x * a * x⁻¹ = a := fun a ha => by
      have := hA'e.1 x hx a (hDA' ha)
      calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [this]
        _ = a := by group
    rcases hodd with ⟨a, haD, haH, hsg⟩ | ⟨a, haD, haH, hsg⟩
    · have ha1 : a ≠ 1 := by
        intro h1
        have : (⟨a, haH⟩ : ↥H₁) = 1 := Subtype.ext h1
        rw [this, map_one, map_one] at hsg
        exact absurd hsg (by decide)
      exact not_commute_of_mem_left hd.tb haH ha1 hxX hxn (hcomm a haD)
    · have ha1 : a ≠ 1 := by
        intro h1
        have : (⟨a, haH⟩ : ↥H₂) = 1 := Subtype.ext h1
        rw [this, map_one, map_one] at hsg
        exact absurd hsg (by decide)
      exact not_commute_of_mem_right hd.tb haH ha1 hxX hxn (hcomm a haD)

end Image

section SettingJ

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem psi_J_le_ffJ' (hB1 : B69One) (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N)
    (hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 H →
      ∃ D : Subgroup G, Setting H T M₂ U D ∧ D ≤ A' ⊔ U)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {m : ℕ} {H₁ H₂ : Subgroup (MulAut ↥(chiefMod L N))}
    {θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)} {θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)}
    {β₁ β₂ : ↥(coreMod m) →* ↥(chiefMod L N)}
    {Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥(chiefAut H L N)}
    (hd : @WreathData ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T) m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ) :
    ∀ x : ↥H, (x : G) ∈ thompsonJ H →
      chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) x ∈
        @ffJ ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N) := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  set P : Subgroup G := ((ffJ (chiefAut H L N)).comap (chiefPsi hHL hHN)).map H.subtype with hP
  have hmemP : ∀ x : ↥H, chiefPsi hHL hHN x ∈ ffJ (chiefAut H L N) → (x : G) ∈ P :=
    fun x hx => ⟨x, hx, rfl⟩
  have hPmem : ∀ x : G, x ∈ P → ∃ hxH : x ∈ H,
      chiefPsi hHL hHN ⟨x, hxH⟩ ∈ ffJ (chiefAut H L N) := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have hK : twoResidual H ≤ P := by
    rw [F6.twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le P).mpr ?_
    rintro x ⟨hxH, hodd⟩
    refine hmemP ⟨x, hxH⟩ ?_
    have h1 : orderOf (chiefPsi hHL hHN ⟨x, hxH⟩) ∣ orderOf (⟨x, hxH⟩ : ↥H) := orderOf_map_dvd _ _
    have h2 : Odd (orderOf (⟨x, hxH⟩ : ↥H)) := by
      rw [← Subgroup.orderOf_coe]
      exact hodd
    exact Ch3w.odd_mem_ffJ hctx (chiefPsi_mem hHL hHN ⟨x, hxH⟩) (h2.of_dvd_nat h1)
  have hJT : thompsonJ T ≤ P := by
    refine iSup₂_le fun A' hA' a ha => ?_
    have haH : a ∈ H := h.mp.isSylow.1 (hA'.1 ha)
    refine hmemP ⟨a, haH⟩ ?_
    have hA'ff : chiefImg hHL hHN A' ≤ ffJ (chiefAut H L N) := by
      have := chiefImg_le_base hB1 h hstep hnc hrepl hd hA'
      rw [← hd.ffJ_eq] at this
      exact this
    exact hA'ff ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  intro x hx
  rw [thompsonJ_eq_sup_of_not_le h.mp h.AT h.An] at hx
  obtain ⟨hxH, hxP⟩ := hPmem x (sup_le hK hJT hx)
  exact hxP

theorem map_J_base_of_twoWit' (hB1 : B69One) (h : Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 H →
      ∃ D : Subgroup G, Setting H T M₂ U D ∧ D ≤ A' ⊔ U)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {m : ℕ} {H₁ H₂ : Subgroup (MulAut ↥(chiefMod L N))}
    {θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)} {θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)}
    {β₁ β₂ : ↥(coreMod m) →* ↥(chiefMod L N)}
    {Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥(chiefAut H L N)}
    (hd : @WreathData ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
      (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T) m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ)
    (hodd : (∃ a ∈ chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A, ∃ ha : a ∈ H₁,
        Equiv.Perm.sign (θ₁ ⟨a, ha⟩) = -1) ∨
      ∃ a ∈ chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A, ∃ ha : a ∈ H₂,
        Equiv.Perm.sign (θ₂ ⟨a, ha⟩) = -1) :
    ((thompsonJ H).subgroupOf H).map
      (Ψ.symm.toMonoidHom.comp (chiefHom (Setting.hHL hstep) (Setting.hHN hstep))) =
      (RegularWreathProduct.rightHom : Equiv.Perm (Fin m) ≀ᵣ Q2 →* Q2).ker := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG (h.hE hstep)
  refine Ch3w.map_J_eq_base_of_wreathData hd (chiefHom hHL hHN) (chiefHom_surjective hHL hHN)
    (Ch3w.oTwoUpper_le_thompsonJ h) (Ch3w.thompsonJ_conj_mem H)
    (fun x hx => psi_J_le_ffJ' hB1 h hstep hnc hrepl hctx hd x hx) ?_
  rcases hodd with ⟨a, haA, ha, hs⟩ | ⟨a, haA, ha, hs⟩
  · obtain ⟨x, hxJ, hxa⟩ := Ch3w.exists_mem_of_chiefImg h hstep haA
    have hmem : ((chiefHom hHL hHN x : ↥(chiefAut H L N)) : MulAut ↥(chiefMod L N)) ∈ H₁ := by
      show chiefPsi hHL hHN x ∈ H₁
      rw [hxa]
      exact ha
    refine ⟨x, hxJ, Or.inl ⟨hmem, ?_⟩⟩
    have : (⟨_, hmem⟩ : ↥H₁) = ⟨a, ha⟩ := Subtype.ext hxa
    rw [this]
    exact hs
  · obtain ⟨x, hxJ, hxa⟩ := Ch3w.exists_mem_of_chiefImg h hstep haA
    have hmem : ((chiefHom hHL hHN x : ↥(chiefAut H L N)) : MulAut ↥(chiefMod L N)) ∈ H₂ := by
      show chiefPsi hHL hHN x ∈ H₂
      rw [hxa]
      exact ha
    refine ⟨x, hxJ, Or.inr ⟨hmem, ?_⟩⟩
    have : (⟨_, hmem⟩ : ↥H₂) = ⟨a, ha⟩ := Subtype.ext hxa
    rw [this]
    exact hs

end SettingJ

section Shape

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem chiefFactorShape_of_setting' (hB69 : B69Struct) (hB1 : B69One) (h : Setting H T M₂ U A)
    (hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 H →
      ∃ D : Subgroup G, Setting H T M₂ U D ∧ D ≤ A' ⊔ U)
    {L₀ N₀ : Subgroup G} (hstep₀ : IsChiefStep H U L₀ N₀) (hnc₀ : ¬ IsCentralStep H L₀ N₀)
    {χ₀ : ↥H →* ℤˣ}
    (hχC : ∀ g : ↥H, (g : G) ∈ centralizerMod L₀ H N₀ → χ₀ g = 1) {a : G} (haA : a ∈ A)
    (haH : a ∈ H) (hχa : χ₀ ⟨a, haH⟩ = -1) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) : ChiefFactorShape H L N := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  obtain ⟨𝓗, hctx⟩ := h.blkCtx hB69 hstep hnc
  have hsym := h.symBlk_all hB1 hstep₀ hnc₀ hχC haA haH hχa hstep hnc hctx
  have hstrong := h.noStrong hB1 hstep hnc
  obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
  have hAX : chiefImg hHL hHN A ≤ chiefAut H L N := chiefImg_le_chiefAut hHL hHN A
  have hshape := hctx.shape_wit (h.rank hstep) hsym hstrong hAX hAe hA1 hoff
  have hnorm : (L.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNL
  refine ⟨hnorm, ?_⟩
  rcases hshape with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨hm35, θ, β, hβeq, hβr, hβk, a', ha'A, ha', hsg⟩ := hm
    have hmodd : Odd m := by rcases hm35 with rfl | rfl <;> decide
    have hJ := map_J_top_of_oneWit h hstep θ ha'A ha' hsg
    have key := translate_one hstep h.UH hmodd θ β hβeq hβr hβk hJ
    rcases hm35 with rfl | rfl
    · exact Or.inl key
    · exact Or.inr (Or.inl key)
  · obtain ⟨H₁, H₂, θ₁, θ₂, β₁, β₂, Ψ, hd, hodd⟩ := hm
    have hmodd : Odd m := by rcases hd.m35 with rfl | rfl <;> decide
    have hJ := map_J_base_of_twoWit' hB1 h hstep hnc hrepl hctx hd hodd
    have key := translate_two hstep h.UH hE hmodd hd hJ
    rcases hd.m35 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl key))
    · exact Or.inr (Or.inr (Or.inr key))

end Shape

section Main

variable {G : Type} [Group G] [Finite G]

theorem lemma319Shape_of_theorem317 (hB69 : B69Struct) (hB1 : B69One)
    (hT317 : Theorem317Statement) (hD125 : D125NonsolvableSQTK) : Lemma319Shape := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hmain hyp5 L N hstep hnc
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hsq : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hUe := hmain.elemAbelian
  have hUT : conjClosure V H ≤ T := conjClosure_le_T hD h.le_pCore
  have hRT := h.pCoreOf_le hT
  have hTH : T ≤ H := h.hStar.1.1
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V h.reduced.2.2.1 := h.q_eq.ge
  have hD125' : D15Proof.D125 H T (conjClosure V H) :=
    d125_of_input hD125 hD hsq h.not_qInt_le_one h.le_pCore hUe
  have hZ : quasithinOmegaOneCenter T ≤ centerOf H := by
    rcases hT317 G T hs hnab hK hT M M₀ H V hM ⟨h.toHyp315Base, Or.inr h.caseII⟩
        (hD.thompsonJ_le hnff) with ⟨hZ, -⟩ | hex
    · exact hZ
    · exact absurd hex h.not_exists_normal
  obtain ⟨A, hA⟩ := hmain.exists_A
  have hset : Setting H T (H ⊓ M) (conjClosure V H) A :=
    ⟨hmp, hsq, hUT, hUe, hA.1, hA.not_le hRT,
      fun L' N' hs' hnc' => hmain.count_four A hA L' N' hs' hnc'⟩
  have hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 H →
      ∃ D : Subgroup G, Setting H T (H ⊓ M) (conjClosure V H) D ∧ D ≤ A' ⊔ conjClosure V H := by
    intro A' hA' hA'R
    have hA'n : ¬ IsMaxElemAbelian (pCoreOf 2 H) A' := fun hmax => hA'R hmax.1
    obtain ⟨D, hDT, hDn, hDq, hDA⟩ := exists_quadratic_below hD hnff h.le_pCore hq2 hA' hA'n
    exact ⟨D, setting_of_quadratic h hT hsq hD125' hmain.chief hDT hDn hDq, hDA⟩
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := fun t ht =>
    hII (Subgroup.mem_inf.mpr ⟨hTH ht, h.le_M (h.T_le ht)⟩)
  have hgen : ∀ W : Subgroup G, IsNormalIn H (conjClosure V H) W → V ≤ W → conjClosure V H ≤ W :=
    fun W hW hVW => conjClosure_le fun g hg z hz => hW.2 g hg z (hVW hz)
  obtain ⟨L₀, N₀, hstep₀, hnc₀, z, hzV, hzN, hzL, hzT⟩ := exists_good_step hmp.isSylow hUT hUe
    (le_normalizer_conjClosure V H) (le_conjClosure V H) hgen hTV ⟨L, N, hstep, hnc⟩
  have hodd : ∀ d ∈ H ⊓ M, Odd (orderOf d) → d * z * d⁻¹ * z⁻¹ ∈ L₀ := by
    intro d hd ho
    have hdC : d ∈ M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      ⟨(Subgroup.mem_inf.mp hd).2, Subgroup.mem_centralizer_iff.mpr fun x hx =>
        ((Subgroup.mem_centralizer_iff.mp (hZ hx).2) d (Subgroup.mem_inf.mp hd).1).symm⟩
    have hdV : d ∈ Subgroup.centralizer (V : Set G) := hyp5 (mem_oTwoUpper_of_odd hdC ho)
    have hcomm := Subgroup.mem_centralizer_iff.mp hdV z hzV
    have e : d * z * d⁻¹ * z⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [e]
    exact L₀.one_mem
  obtain ⟨χ₀, hχC, a, haA, haH, hχa⟩ := hset.good hB69 hB1 hstep₀ hnc₀ hzN hzL hzT hodd
  exact chiefFactorShape_of_setting' hB69 hB1 hset hrepl hstep₀ hnc₀ hχC haA haH hχa hstep hnc

theorem lemma319Shape_of_inputs (hB69 : B69Struct) (hB1 : B69One) (hC58 : TheoremC58)
    (hN : AS317SylowNonsolvable) (hD125 : D125NonsolvableSQTK) : Lemma319Shape :=
  lemma319Shape_of_theorem317 hB69 hB1 (theorem317Statement_of_core_inputs hC58 hN) hD125

end Main

end E23J

end CFSG.Quasithin
