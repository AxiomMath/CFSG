module

public import CFSG.Quasithin.MS93.S32G2V

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Pairing

variable {Γ : Type*} [Group Γ]

structure IsA1Pairing (F : Type) [Field F] (U C Z' : Subgroup Γ) (ξ θ : Γ → Fin 3 → F) :
    Prop where
  surj : ∀ x, ∃ u ∈ U, ξ u = x
  pair : ∀ z ∈ Z', ∃ y, ∀ u ∈ U, θ ⁅z, u⁆ = a1Pair (ξ u) y
  pair_surj : ∀ y, ∃ z ∈ Z', ∀ u ∈ U, θ ⁅z, u⁆ = a1Pair (ξ u) y
  add : ∀ r ∈ U, ∀ r' ∈ U, θ (r * r') = θ r + θ r'
  ker_le : ∀ c ∈ C, θ c = 0
  le_ker : ∀ r ∈ ⁅Z', U⁆, θ r = 0 → r ∈ C

theorem IsA1Pairing.map {F : Type} [Field F] {U C Z' : Subgroup Γ} {ξ θ : Γ → Fin 3 → F}
    (hP : IsA1Pairing F U C Z' ξ θ) (f : Γ ≃* Γ) :
    IsA1Pairing F (U.map f.toMonoidHom) (C.map f.toMonoidHom) (Z'.map f.toMonoidHom)
      (ξ ∘ f.symm) (θ ∘ f.symm) where
  surj x := by
    obtain ⟨u, hu, rfl⟩ := hP.surj x
    exact ⟨f u, ⟨u, hu, rfl⟩, by simp⟩
  pair := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy⟩ := hP.pair z hz
    refine ⟨y, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_commutatorElement, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hy u hu
  pair_surj y := by
    obtain ⟨z, hz, hy⟩ := hP.pair_surj y
    refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_commutatorElement, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hy u hu
  add := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hP.add r hr r' hr'
  ker_le := by
    rintro _ ⟨c, hc, rfl⟩
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hP.ker_le c hc
  le_ker r hr hr0 := by
    rw [← Subgroup.map_commutator] at hr
    obtain ⟨r, hr, rfl⟩ := hr
    simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hr0
    exact ⟨r, hP.le_ker r hr hr0, rfl⟩

theorem forall_eq_zero_or_eq_one_of_pairings {F : Type} [Field F] [Finite F] [CharP F 2]
    {U U' Z Z' C : Subgroup Γ} {ξ θ ξ' θ' : Γ → Fin 3 → F} (P : IsA1Pairing F U C Z' ξ θ)
    (P' : IsA1Pairing F U' C Z ξ' θ') (hUZ : U ≤ Z) (hUZ' : U' ≤ Z') (hR : ⁅Z', U⁆ = ⁅Z, U'⁆)
    (hRU : ⁅Z', U⁆ ≤ U) (hRU' : ⁅Z, U'⁆ ≤ U')
    (hdec : ∀ z ∈ Z', ∃ u' ∈ U', ∀ u ∈ U, ⁅z, u⁆ = ⁅u', u⁆)
    (hsymm : ∀ u ∈ U, ∀ u' ∈ U', ⁅u', u⁆ = ⁅u, u'⁆) (c : F) : c = 0 ∨ c = 1 := by
  have hRU'' : ⁅Z', U⁆ ≤ U' := hR ▸ hRU'
  have hsub : ∀ {θ₀ : Γ → Fin 3 → F} {W : Subgroup Γ},
      (∀ r ∈ W, ∀ r' ∈ W, θ₀ (r * r') = θ₀ r + θ₀ r') →
        ∀ r ∈ W, ∀ s ∈ W, θ₀ (r * s⁻¹) = θ₀ r - θ₀ s := by
    intro θ₀ W hadd r hr s hs
    have := hadd (r * s⁻¹) (W.mul_mem hr (W.inv_mem hs)) s hs
    rw [inv_mul_cancel_right] at this
    rw [this, add_sub_cancel_right]
  have htr : ∀ r ∈ ⁅Z', U⁆, ∀ s ∈ ⁅Z', U⁆, θ r = θ s → θ' r = θ' s := by
    intro r hr s hs hrs
    have hrs' : r * s⁻¹ ∈ ⁅Z', U⁆ := Subgroup.mul_mem _ hr (Subgroup.inv_mem _ hs)
    have h0 : θ (r * s⁻¹) = 0 := by rw [hsub P.add r (hRU hr) s (hRU hs), hrs, sub_self]
    have h1 := P'.ker_le _ (P.le_ker _ hrs' h0)
    rw [hsub P'.add r (hRU'' hr) s (hRU'' hs)] at h1
    exact sub_eq_zero.mp h1
  have htr' : ∀ r ∈ ⁅Z', U⁆, ∀ s ∈ ⁅Z', U⁆, θ' r = θ' s → θ r = θ s := by
    intro r hr s hs hrs
    have hrs' : r * s⁻¹ ∈ ⁅Z', U⁆ := Subgroup.mul_mem _ hr (Subgroup.inv_mem _ hs)
    have h0 : θ' (r * s⁻¹) = 0 := by rw [hsub P'.add r (hRU'' hr) s (hRU'' hs), hrs, sub_self]
    have h1 := P.ker_le _ (P'.le_ker _ (hR ▸ hrs') h0)
    rw [hsub P.add r (hRU hr) s (hRU hs)] at h1
    exact sub_eq_zero.mp h1
  have hsurj : ∀ t : Fin 3 → F, ∃ r ∈ ⁅Z', U⁆, θ r = t := by
    intro t
    obtain ⟨u, hu, hx⟩ := P.surj ![t 0, t 2, t 1]
    obtain ⟨z, hz, hzy⟩ := P.pair_surj ![1, 0, 0]
    refine ⟨⁅z, u⁆, Subgroup.commutator_mem_commutator hz hu, ?_⟩
    rw [hzy u hu, hx, a1Pair_one]
    funext i
    fin_cases i <;> rfl
  choose r hr hθr using hsurj
  let Φ : (Fin 3 → F) →+ (Fin 3 → F) := AddMonoidHom.mk' (fun t => θ' (r t)) (fun t s => by
    have hmem : r t * r s ∈ ⁅Z', U⁆ := Subgroup.mul_mem _ (hr t) (hr s)
    have := htr (r (t + s)) (hr _) _ hmem
      (by rw [hθr, P.add _ (hRU (hr t)) _ (hRU (hr s)), hθr, hθr])
    rw [this, P'.add _ (hRU'' (hr t)) _ (hRU'' (hr s))])
  have hΦ : Function.Injective Φ := by
    intro t s hts
    have := htr' (r t) (hr t) (r s) (hr s) hts
    rwa [hθr, hθr] at this
  have hy' : ∀ y, ∃ u' ∈ U', ∀ u ∈ U, θ ⁅u', u⁆ = a1Pair (ξ u) y := by
    intro y
    obtain ⟨z, hz, hzy⟩ := P.pair_surj y
    obtain ⟨u', hu', hzu⟩ := hdec z hz
    exact ⟨u', hu', fun u hu => by rw [← hzu u hu]; exact hzy u hu⟩
  choose uy huy huyeq using hy'
  have hx' : ∀ x, ∃ u ∈ U, ξ u = x ∧ ∃ y, ∀ u' ∈ U', θ' ⁅u, u'⁆ = a1Pair (ξ' u') y := by
    intro x
    obtain ⟨u, hu, hux⟩ := P.surj x
    exact ⟨u, hu, hux, P'.pair u (hUZ hu)⟩
  choose ux hux hξux yx hyx using hx'
  refine eq_zero_or_eq_one_of_a1Pair Φ hΦ (fun y => ξ' (uy y)) yx (fun x y => ?_) c
  have hw : ⁅uy y, ux x⁆ ∈ ⁅Z', U⁆ :=
    Subgroup.commutator_mem_commutator (hUZ' (huy y)) (hux x)
  show θ' (r (a1Pair x y)) = _
  rw [htr _ (hr _) _ hw (by rw [hθr, huyeq y _ (hux x), hξux]), hsymm _ (hux x) _ (huy y),
    hyx x _ (huy y)]

end Pairing

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_extend (h : PUHyp M T L) {β : Type*}
    (f : IntMod (Uq M T L) h.isElemAbelian_Uq → β) (b : β) :
    ∃ f' : (puAmalgam h.le).Universal → β, ∀ (x : ↥M) (hx : (x : G) ∈ Uq M T L),
      f' ((puAmalgam h.le).ofA x) = f (IntMod.mk h.isElemAbelian_Uq ⟨x, hx⟩) := by
  classical
  let ι : IntMod (Uq M T L) h.isElemAbelian_Uq → (puAmalgam h.le).Universal :=
    fun v => (puAmalgam h.le).ofA ⟨v.val, Uq_le h.L_le v.val_mem⟩
  have hι : Function.Injective ι := fun v w hvw => by
    have := congrArg Subtype.val ((puAmalgam h.le).ofA_injective hvw)
    exact IntMod.val_injective this
  refine ⟨Function.extend ι f (fun _ => b), fun x hx => ?_⟩
  have : (puAmalgam h.le).ofA x = ι (IntMod.mk h.isElemAbelian_Uq ⟨x, hx⟩) := rfl
  rw [this, hι.extend_apply]

theorem pairing_base (h : PUHyp M T L) (hN : NoStrongOffU h) {F : Type} [Field F]
    (hco : ∀ A : Subgroup (MulAut (IntMod (Uq M T L) h.isElemAbelian_Uq)),
      A ≤ autI h.isElemAbelian_Uq M → A ≠ ⊥ → IsElemAbelian2 A →
      Nat.card (IntMod (Uq M T L) h.isElemAbelian_Uq) ≤
        Nat.card A * Nat.card ↥(fixQuot A (fixV (autI h.isElemAbelian_Uq L))) →
      ∃ (ξ θ : IntMod (Uq M T L) h.isElemAbelian_Uq →* Multiplicative (Fin 3 → F))
        (η : ↥A → (Fin 3 → F)), Function.Surjective ξ ∧ Function.Bijective η ∧
        (∀ (a : ↥A) (v : IntMod (Uq M T L) h.isElemAbelian_Uq),
          Multiplicative.toAdd (θ ((a : MulAut _) v * v⁻¹)) =
            a1Pair (Multiplicative.toAdd (ξ v)) (η a)) ∧
        (∀ z ∈ fixV (autI h.isElemAbelian_Uq L), θ z = 1) ∧
        (∀ w ∈ commV A, θ w = 1 → w ∈ fixV (autI h.isElemAbelian_Uq L)))
    {δ : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) δ) :
    ∃ ξ θ : (puAmalgam h.le).Universal → Fin 3 → F,
      IsA1Pairing F (imM h.le (Uq M T L)) (imM h.le (Uq M T L ⊓ Zq M L)) (ZM _ δ) ξ θ := by
  set hU := h.isElemAbelian_Uq
  obtain ⟨m, hm, hg⟩ := exists_stab_smul_geo h hc
  have hmα : m • baseA (puAmalgam h.le) = baseA (puAmalgam h.le) := (mem_stab _).mp hm
  have hc₀ : IsCritical (puAmalgam h.le) (baseA _) (m • δ) := by
    have := (isCritical_smul _ m (baseA _) δ).2 hc
    rwa [hmα] at this
  suffices H : ∃ ξ θ : (puAmalgam h.le).Universal → Fin 3 → F,
      IsA1Pairing F (imM h.le (Uq M T L)) (imM h.le (Uq M T L ⊓ Zq M L)) (ZM _ (m • δ)) ξ θ by
    obtain ⟨ξ, θ, hP⟩ := H
    have hP' := hP.map (MulAut.conj m⁻¹)
    have hm' : m⁻¹ ∈ stab (puAmalgam h.le) (baseA (puAmalgam h.le)) := Subgroup.inv_mem _ hm
    rw [map_conj_eq_of_mem_normalizer
        (stab_le_normalizer_imM h (le_normalizer_Uq h.le_normalizer) hm'),
      map_conj_eq_of_mem_normalizer (stab_le_normalizer_imM h (le_normalizer_inf
        (le_normalizer_Uq h.le_normalizer) (le_normalizer_Zq h.le_normalizer)) hm'),
      ← zm_smul, inv_smul_smul] at hP'
    exact ⟨_, _, hP'⟩
  have hZT := zm_le_imM_T h hc₀ hg
  set E := pullM h (ZM _ (m • δ)) with hE
  have hET : E ≤ T := pullM_le_T h hZT
  have hEM : E ≤ M := hET.trans h.le
  have hEim : imM h.le E = ZM _ (m • δ) := imM_pullM h (hZT.trans (imM_mono h.le h.le))
  have hEab : IsElemAbelian 2 E := isElemAbelian_pullM h
    (isElemAbelian_zm _ h.hyp20 h.critDist_pos (hc₀.isMVtx_right _ h.hyp20))
  have hEN : E ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    hET.trans (h.le.trans (le_normalizer_Uq h.le_normalizer))
  obtain ⟨hA1, hoff⟩ := autI_pullM_offender h hN hc₀ hZT
  obtain ⟨ξ₀, θ₀, η₀, hξs, hηb, hpair, hθZ, hθk⟩ :=
    hco (autI hU E) (autI_mono hU hEM) hA1 (isElemAbelian2_autI hU hEab hEN) hoff
  obtain ⟨ξ, hξ⟩ := exists_extend h (fun v => Multiplicative.toAdd (ξ₀ v)) 0
  obtain ⟨θ, hθ⟩ := exists_extend h (fun v => Multiplicative.toAdd (θ₀ v)) 0
  have hcomm : ∀ (e : ↥M) (he : (e : G) ∈ E) (x : ↥M) (hx : (x : G) ∈ Uq M T L),
      θ ⁅(puAmalgam h.le).ofA e, (puAmalgam h.le).ofA x⁆ = a1Pair (ξ ((puAmalgam h.le).ofA x))
        (η₀ ⟨convI hU ⟨e, hEN he⟩, convI_mem_autI hU he (hEN he)⟩) := by
    intro e he x hx
    have hex : ((⁅e, x⁆ : ↥M) : G) ∈ Uq M T L := by
      show (e : G) * x * (e : G)⁻¹ * (x : G)⁻¹ ∈ Uq M T L
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hEN he) x).mp hx)
        (Subgroup.inv_mem _ hx)
    rw [← map_commutatorElement, hθ _ hex, hξ _ hx, ← hpair]
    congr 2
  rw [← hEim]
  refine ⟨ξ, θ, ⟨fun x => ?_, ?_, fun y => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := hξs (Multiplicative.ofAdd x)
    refine ⟨(puAmalgam h.le).ofA ⟨v.val, Uq_le h.L_le v.val_mem⟩, ⟨_, v.val_mem, rfl⟩, ?_⟩
    rw [hξ _ v.val_mem]
    exact congrArg Multiplicative.toAdd hv
  · rintro _ ⟨e, he, rfl⟩
    exact ⟨_, fun u hu => by
      obtain ⟨x, hx, rfl⟩ := hu
      exact hcomm e he x hx⟩
  · obtain ⟨⟨a, ha⟩, hay⟩ := hηb.2 y
    obtain ⟨e, he, rfl⟩ := (mem_autI hU).1 ha
    refine ⟨(puAmalgam h.le).ofA ⟨e, hEM he⟩, ⟨_, he, rfl⟩, fun u hu => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hu
    rw [hcomm ⟨e, hEM he⟩ he x hx, ← hay]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← map_mul, hθ (x * x') (Subgroup.mem_subgroupOf.mp (Subgroup.mul_mem _ hx hx')),
      hθ x hx, hθ x' hx', ← toAdd_mul, ← map_mul]
    rfl
  · rintro _ ⟨x, hx, rfl⟩
    have hxU : (x : G) ∈ Uq M T L := hx.1
    rw [hθ _ hxU, hθZ _ ?_, toAdd_one]
    rw [← C124.mem_toG_iff_of_mem hU, toG_fixV_Uq h]
    exact hx
  · intro r hr hr0
    rw [← imM_commutator h.le hEM (Uq_le h.L_le)] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hxR : (x : G) ∈ ⁅E, Uq M T L⁆ := hx
    rw [← C124.toG_commV hU hEN] at hxR
    obtain ⟨w, hw, hwx⟩ := (C124.mem_toG hU).1 hxR
    have hxU : (x : G) ∈ Uq M T L := hwx ▸ w.val_mem
    have hw' : IntMod.mk hU ⟨x, hxU⟩ = w := IntMod.val_injective hwx.symm
    rw [hθ _ hxU, hw'] at hr0
    have hwF := hθk w hw (toAdd_eq_zero.mp hr0)
    refine ⟨x, ?_, rfl⟩
    show (x : G) ∈ Uq M T L ⊓ Zq M L
    rw [← toG_fixV_Uq h]
    exact (C124.mem_toG hU).2 ⟨w, hwF, hwx⟩

theorem zm_eq_sup_at (h : PUHyp M T L) (hN : NoStrongOffU h) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA _) δ) :
    puTrans h.le (Uq M T L) δ ⊔ (ZM _ δ ⊓
      Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _)) = ZM _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ (hc.isMVtx_right _ h.hyp20)
  have hc' : IsCritical _ (baseA _) (g⁻¹ • baseA (puAmalgam h.le)) := by
    have h3 := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    have := (isCritical_smul _ g⁻¹ (g • baseA _) (baseA _)).2 h3
    rwa [inv_smul_smul] at this
  have hgδ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA _ := smul_inv_smul g _
  have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (zm_eq_sup_of_crit h hN hc')
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← PU.centralizer_map_mulEquiv, ← zm_smul, ← zm_smul, hgδ,
    ← puTrans_smul_baseA (uq_subgroupOf_normal h)] at this
  exact this

theorem commutatorElement_mul_left_of_commute {Γ : Type*} [Group Γ] {u c e : Γ}
    (hce : c * e = e * c) : ⁅u * c, e⁆ = ⁅u, e⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  calc u * c * e * (c⁻¹ * u⁻¹) * e⁻¹ = u * (c * e * c⁻¹) * u⁻¹ * e⁻¹ := by group
    _ = u * e * u⁻¹ * e⁻¹ := by rw [hce, mul_inv_cancel_right]

theorem s32PartG2Large_of (hG2C : MS15G2Comm) (hSQ : SQTKQuot) : S32PartG2Large := by
  intro G _ _ M T L h n hn hG2 hcase
  set hU := h.isElemAbelian_Uq with hUdef
  have hs := isSecW_Uq h
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := id hG2
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  have hKX : autI hU L ≤ autI hU M := hs.autI_L_le h
  have hXN : autI hU M ≤ Subgroup.normalizer (autI hU L : Set (MulAut (IntMod (Uq M T L) hU))) :=
    hs.autI_le_normalizer h
  have hXZ : ∀ x ∈ autI hU M, ∀ z ∈ fixV (autI hU L), x z ∈ fixV (autI hU L) :=
    fun x hx z hz => B1Red.fixV_inv_of_normalizes
      (fun b hb k hk => (Subgroup.mem_normalizer_iff.mp (hXN hb) k).mp hk) x hx z hz
  have h15 : fixV (autI hU L) ≠ ⊥ →
      MS15Hyp (autI hU M) (autI hU L) ∧ MS15CaseG2 (autI hU M) (autI hU L) := by
    intro hC
    rcases hcase with hC' | ⟨-, hirr, hcase⟩
    · exact (hC hC').elim
    · exact ⟨hs.ms15Hyp h hSQ (commV_autI_Uq h) hC hirr
        (h.isFFModule_of_le_Z0q hs (Uq_le_Z0q h.L_le)), hcase⟩
  have hfaith : ∀ x ∈ autI hU M, (∀ v, x v * v⁻¹ ∈ fixV (autI hU L)) → x = 1 := by
    intro x hx hxv
    by_cases hC : fixV (autI hU L) = ⊥
    · ext v
      have := hxv v
      rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    · have hbot := MS15Hyp.faithful IntMod.sq_eq_one (h15 hC).1
      have hmem : x ∈ autI hU M ⊓ centSec ⊤ (fixV (autI hU L)) :=
        ⟨hx, fun _ => Iff.rfl, fun w _ => hxv w⟩
      rw [hbot] at hmem
      exact hmem
  have hN4 : ∀ A : Subgroup (MulAut (IntMod (Uq M T L) hU)), A ≤ autI hU M → IsElemAbelian2 A →
      Nat.card A * Nat.card (fixV A) ≤ Nat.card (IntMod (Uq M T L) hU) ∧
        (A ≠ ⊥ → Nat.card (IntMod (Uq M T L) hU) ≤
          Nat.card A * Nat.card ↥(fixQuot A (fixV (autI hU L))) → A ≤ autI hU L) :=
    fun A hA hAe => card_mul_card_fixV_le_g2 hn hG2 hKX hXN hXZ hfaith hA hAe
  have hN : NoStrongOffU h := fun A hA hAe => (hN4 A hA hAe).1
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 (isMVtx_baseA (puAmalgam h.le))
  have hα' := hc.isMVtx_right _ h.hyp20
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hα'
  have hc' : IsCritical (puAmalgam h.le) (baseA _) (g⁻¹ • baseA (puAmalgam h.le)) := by
    have h3 := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    have := (isCritical_smul _ g⁻¹ (g • baseA _) (baseA _)).2 h3
    rwa [inv_smul_smul] at this
  have hgδ : g • (g⁻¹ • baseA (puAmalgam h.le)) = baseA _ := smul_inv_smul g _
  have hCC : (imM h.le (Uq M T L ⊓ Zq M L)).map (MulAut.conj g).toMonoidHom =
      imM h.le (Uq M T L ⊓ Zq M L) := by
    by_cases hC : fixV (autI hU L) = ⊥
    · have hbot : imM h.le (Uq M T L ⊓ Zq M L) = ⊥ := by
        rw [Uq_inf_Zq_eq_bot h hC, imM_eq_bot_iff h.le bot_le]
      rw [hbot, Subgroup.map_bot]
    · obtain ⟨h15', hcase'⟩ := h15 hC
      have hv := (vertex_clause_of_comm h hN (fun δ hδ => commCharAt_base h hN
        (fun A hAX hA1 hAe hoff => hG2C _ IntMod.sq_eq_one _ _ h15' hcase' A hAX hA1 hAe hoff)
        hδ) _ hc).1
      rw [← puTrans_inf_centralizer h g, ← hv]
  have hco := fun (A : Subgroup (MulAut (IntMod (Uq M T L) hU))) (hAX : A ≤ autI hU M)
      (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
      (hoff : Nat.card (IntMod (Uq M T L) hU) ≤
        Nat.card A * Nat.card ↥(fixQuot A (fixV (autI hU L)))) =>
    exists_a1Coords hF (by omega) hπ ((hN4 A hAX hAe).2 hA1 hoff) hA1 hAe hoff
  obtain ⟨ξ, θ, P⟩ := pairing_base h hN hco hc
  obtain ⟨ξ₂, θ₂, P₂⟩ := pairing_base h hN hco hc'
  have P' := P₂.map (MulAut.conj g)
  rw [← puTrans_smul_baseA (uq_subgroupOf_normal h), hCC, ← zm_smul, hgδ] at P'
  have hab : ∀ δ : Vtx (puAmalgam h.le), IsMVtx (puAmalgam h.le) δ →
      ∀ x ∈ ZM _ δ, ∀ y ∈ ZM _ δ, x * y = y * x :=
    fun δ hδ x hx y hy => congrArg Subtype.val
      ((isElemAbelian_zm _ h.hyp20 h.critDist_pos hδ).1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hUα : imM h.le (Uq M T L) ≤ ZM (puAmalgam h.le) (baseA _) := by
    rw [puAmalgam.zm_baseA h.le]
    exact imM_mono h.le (Uq_le_Z0q h.L_le)
  have hUα' : puTrans h.le (Uq M T L) (g • baseA (puAmalgam h.le)) ≤
      ZM _ (g • baseA (puAmalgam h.le)) := by
    rw [puTrans_smul_baseA (uq_subgroupOf_normal h), zm_smul]
    exact Subgroup.map_mono hUα
  have sup2 := zm_eq_sup_at h hN hc
  obtain ⟨com1, -⟩ :=
    commutator_eq_of_sup_eq hUα (hab _ (isMVtx_baseA _)) (zm_eq_sup_of_crit h hN hc)
  obtain ⟨com2, -⟩ := commutator_eq_of_sup_eq hUα' (hab _ hα') sup2
  have hc'' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  have hRU : ⁅ZM _ (g • baseA (puAmalgam h.le)), imM h.le (Uq M T L)⁆ ≤ imM h.le (Uq M T L) := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_critical h hc'').trans
      (stab_le_normalizer_imM h (le_normalizer_Uq h.le_normalizer)))
  have hRU' : ⁅ZM _ (baseA (puAmalgam h.le)), puTrans h.le (Uq M T L) (g • baseA (puAmalgam h.le))⁆
      ≤ puTrans h.le (Uq M T L) (g • baseA (puAmalgam h.le)) := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_critical h hc).trans
      (stab_le_normalizer_puTrans h.le (uq_subgroupOf_normal h) _))
  have hRZ : ⁅ZM _ (baseA (puAmalgam h.le)), ZM _ (g • baseA (puAmalgam h.le))⁆ ≤
      ZM _ (baseA (puAmalgam h.le)) :=
    commutator_le_left_of_le_normalizer ((zm_le_stab_of_critical h hc'').trans
      (stab_le_normalizer_zm _ _))
  have hinv : ∀ v ∈ ZM _ (baseA (puAmalgam h.le)), v⁻¹ = v := fun v hv =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]
      exact (isElemAbelian_zm _ h.hyp20 h.critDist_pos (isMVtx_baseA _)).2 v hv)
  have hR : ⁅ZM _ (g • baseA (puAmalgam h.le)), imM h.le (Uq M T L)⁆ =
      ⁅ZM _ (baseA (puAmalgam h.le)), puTrans h.le (Uq M T L) (g • baseA (puAmalgam h.le))⁆ := by
    rw [com1, com2, Subgroup.commutator_comm]
  have hdec : ∀ z ∈ ZM _ (g • baseA (puAmalgam h.le)),
      ∃ u' ∈ puTrans h.le (Uq M T L) (g • baseA (puAmalgam h.le)),
        ∀ u ∈ imM h.le (Uq M T L), ⁅z, u⁆ = ⁅u', u⁆ := by
    intro z hz
    obtain ⟨u', hu', c, hc, rfl⟩ := exists_mul_eq_of_sup_eq hUα' (hab _ hα') sup2 hz
    exact ⟨u', hu', fun u hu => commutatorElement_mul_left_of_commute
      (Subgroup.mem_centralizer_iff.mp hc.2 u (hUα hu)).symm⟩
  have hsymm : ∀ u ∈ imM h.le (Uq M T L),
      ∀ u' ∈ puTrans h.le (Uq M T L) (g • baseA (puAmalgam h.le)), ⁅u', u⁆ = ⁅u, u'⁆ := by
    intro u hu u' hu'
    rw [← commutatorElement_inv,
      hinv _ (hRZ (Subgroup.commutator_mem_commutator (hUα hu) (hUα' hu')))]
  have key := forall_eq_zero_or_eq_one_of_pairings P P' hUα hUα' hR hRU hRU' hdec hsymm
  have hle : Nat.card F ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : F) else 0)
      (fun c => ?_)
    rcases key c with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  have hB : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hB, hF] at hle
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

end CFSG.Quasithin.MS93.S32
