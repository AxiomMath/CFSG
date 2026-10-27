module

public import CFSG.Quasithin.H13.L32NLem144Ba
public import CFSG.Quasithin.H13.L32NLem14411d

public section

namespace CFSG.Quasithin.H13.L144B

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L1442M Mat8Cert

variable {G : Type} [Group G]

theorem form_of_quadOf {U : Subgroup G} (D : HatModelU U) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    {Q : Matrix (Fin 8) (Fin 8) (ZMod 2)} (hZ : Nat.card (centerOf U) = 2)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U)
    (hq : ∀ u ∈ U, quadOf Q (e (D.π u)) = 0 ↔ u * u = 1) (x y : D.V) :
    D.B x y = quadOf Q (e x + e y) + quadOf Q (e x) + quadOf Q (e y) := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj x
  obtain ⟨v, hv, rfl⟩ := D.π_surj y
  have hsq : ∀ w ∈ U, w * w ∈ centerOf U := fun w hw => by
    rw [← L128A.HatU.π_eq_zero_iff D (U.mul_mem hw hw), D.π_mul w hw w hw]
    exact add_self_zmod2 _
  have hq' : ∀ w ∈ U, quadOf Q (e (D.π w)) = ind (w * w) := fun w hw =>
    L128A.HatU.zmod_two_eq_of_iff (by rw [hq w hw, ind_eq_zero])
  have hB : D.B (D.π u) (D.π v) = ind (u * v * u⁻¹ * v⁻¹) :=
    L128A.HatU.zmod_two_eq_of_iff (by rw [D.B_spec u hu v hv, ind_eq_zero])
  have hc : u⁻¹ * v * u * v⁻¹ ∈ centerOf U := by
    have := hcomm u⁻¹ (U.inv_mem hu) v hv
    simpa using this
  have hcd : ind (u⁻¹ * v * u * v⁻¹) = ind (u * v * u⁻¹ * v⁻¹) := by
    apply L128A.HatU.zmod_two_eq_of_iff
    rw [ind_eq_zero, ind_eq_zero]
    constructor
    · intro h
      have hvu : v * u = u * v := by
        calc v * u = u * (u⁻¹ * v * u * v⁻¹) * v := by group
          _ = u * v := by rw [h]; group
      calc u * v * u⁻¹ * v⁻¹ = (v * u) * u⁻¹ * v⁻¹ := by rw [hvu]
        _ = 1 := by group
    · intro h
      have huv : u * v = v * u := by
        calc u * v = (u * v * u⁻¹ * v⁻¹) * v * u := by group
          _ = v * u := by rw [h]; group
      calc u⁻¹ * v * u * v⁻¹ = u⁻¹ * (v * u) * v⁻¹ := by group
        _ = u⁻¹ * (u * v) * v⁻¹ := by rw [huv]
        _ = 1 := by group
  have hprod : (u * v) * (u * v) = (u * u) * ((u⁻¹ * v * u * v⁻¹) * (v * v)) := by group
  have hind : ind ((u * v) * (u * v)) =
      ind (u * u) + (ind (u⁻¹ * v * u * v⁻¹) + ind (v * v)) := by
    rw [hprod, ind_mul hZ (hsq u hu) ((centerOf U).mul_mem hc (hsq v hv)),
      ind_mul hZ hc (hsq v hv)]
  rw [hB, ← map_add, ← D.π_mul u hu v hv, hq' _ (U.mul_mem hu hv), hq' u hu, hq' v hv, hind, hcd]
  generalize ind (u * u) = p
  generalize ind (v * v) = r
  generalize ind (u * v * u⁻¹ * v⁻¹) = s
  revert p r s
  decide

theorem img8_eq_of_iso {T V : Subgroup G} {D : HatModelU (fsuU T V)}
    {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {Q : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    {Γ : Subgroup (GL (Fin 8) (ZMod 2))} (hiso : IsModelIso D (l32nH T V) e Q Γ) :
    img8 D e (l32nH T V) = Γ := by
  ext γ
  rw [mem_img8]
  constructor
  · rintro ⟨y, hy, hyN, rfl⟩
    obtain ⟨γ', hγ', hγ'e⟩ := (hiso.img _).mp (L128A.HatU.rho_mem_img D hy hyN)
    rwa [(matOf_eq_iff e _ γ').mpr hγ'e]
  · intro hγ
    have hψ : e.trans ((linOf γ).trans e.symm) ∈ D.img (l32nH T V) :=
      (hiso.img _).mpr ⟨γ, hγ, fun v => by simp [linOf_apply]⟩
    obtain ⟨y, hy, hyN, hye⟩ := (L128A.HatU.mem_img D).mp hψ
    refine ⟨y, hy, hyN, ?_⟩
    rw [hye, matOf_eq_iff]
    intro v
    simp [linOf_apply]

variable [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Base

variable (C : Base G T L V V₂ g)
include C

theorem card_img_eq (D : HatModelU (fsuU T V)) {Y : Subgroup G} (hYH : Y ≤ l32nH T V) :
    Nat.card (D.img Y) = (pCoreOf 2 (l32nH T V)).relIndex Y := by
  refine L128A.HatU.card_img_eq_relIndex D (hYH.trans HN) fun x hx => ?_
  constructor
  · rintro ⟨hxN, h1⟩
    rw [← C.cHat]
    exact (L14332.rho_eq_one_iff_mem (hYH hx) hxN).mp h1
  · intro hxQ
    refine ⟨HN (hYH hx), ?_⟩
    rw [← C.cHat] at hxQ
    exact (L14332.rho_eq_one_iff_mem (hYH hx) (HN (hYH hx))).mpr hxQ

theorem QT : pCoreOf 2 (l32nH T V) ≤ T :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  le_of_normalizes (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (C.TH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem card_imgT (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {Γ : Subgroup (GL (Fin 8) (ZMod 2))}
    (himgH : img8 D e (l32nH T V) = Γ) {m k : ℕ} (hΓ : Nat.card Γ = 2 ^ m * k) (hk : Odd k) :
    Nat.card (img8 D e T) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : (pCoreOf 2 (l32nH T V)).relIndex (l32nH T V) = 2 ^ m * k := by
    rw [← C.card_img_eq D le_rfl, ← card_img8 D e, himgH, hΓ]
  have hT : Nat.card (img8 D e T) = (pCoreOf 2 (l32nH T V)).relIndex T := by
    rw [card_img8, C.card_img_eq D C.TH]
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (l32nH T V) C.QT C.TH
  rw [hH, ← hT] at hmul
  have hodd : ¬ 2 ∣ T.relIndex (l32nH T V) :=
    (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH).2.2
  have h2 : IsPGroup 2 ↥(img8 D e T) := by
    rw [img8_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH.trans HN)).symm).map _
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn] at hmul ⊢
  have hk2 : Nat.Coprime 2 k := Nat.coprime_two_left.mpr hk
  have ht2 : Nat.Coprime 2 (T.relIndex (l32nH T V)) :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have h1 : 2 ^ n ∣ 2 ^ m :=
    (Nat.Coprime.pow_left n hk2).dvd_of_dvd_mul_right (Dvd.intro _ hmul)
  have h2' : 2 ^ m ∣ 2 ^ n :=
    (Nat.Coprime.pow_left m ht2).dvd_of_dvd_mul_right (Dvd.intro _ hmul.symm)
  exact Nat.dvd_antisymm h1 h2'

theorem exists_normalized (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    {Γ P : Subgroup (GL (Fin 8) (ZMod 2))} (himgH : img8 D e (l32nH T V) = Γ)
    {F : (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) → ZMod 2} (hform : ∀ x y, D.B x y = F (e x) (e y))
    (hPΓ : P ≤ Γ) (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.relIndex Γ)
    (hcard : Nat.card (img8 D e T) = Nat.card P) :
    ∃ e' : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), img8 D e' (l32nH T V) = Γ ∧
      (∀ x y, D.B x y = F (e' x) (e' y)) ∧ img8 D e' T = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKΓ : img8 D e T ≤ Γ := himgH ▸ img8_mono D e C.TH
  have hK2 : IsPGroup 2 ↥(img8 D e T) := by
    rw [img8_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH.trans HN)).symm).map _
  have hKi : ¬ 2 ∣ (img8 D e T).relIndex Γ := by
    have h1 := Subgroup.relIndex_mul_card (img8 D e T) Γ
    have h2 := Subgroup.relIndex_mul_card P Γ
    rw [inf_eq_left.mpr hKΓ, hcard] at h1
    rw [inf_eq_left.mpr hPΓ] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : (img8 D e T).relIndex Γ = P.relIndex Γ := by
      have := h1.trans h2.symm
      exact Nat.eq_of_mul_eq_mul_right hpos this
    rw [this]
    exact hPi
  obtain ⟨c, hcΓ, hc⟩ := exists_conj_of_sylow hKΓ hPΓ hK2 hP2 hKi hPi
  obtain ⟨y, hyH, hyN, hyc⟩ := (mem_img8 D e).mp (himgH ▸ hcΓ)
  have hce : ∀ x : D.V, (c : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e x) =
      e (D.ρ ⟨y, hyN⟩ x) := fun x => by rw [← hyc, matOf_mulVec]
  refine ⟨e.trans (linOf c), ?_, fun x x' => ?_, ?_⟩
  · rw [img8_trans, himgH, map_conj_of_mem hcΓ]
  · simp only [LinearEquiv.trans_apply, linOf_apply, hce]
    rw [← hform, L128A.HatU.B_rho]
  · have hle : img8 D (e.trans (linOf c)) T ≤ P := by
      rw [img8_trans]
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [img8_trans, Subgroup.card_map_of_injective (MulEquiv.injective _), hcard]

theorem T_fix (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ img8 D e T) :
    (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
  obtain ⟨t, ht, htN, rfl⟩ := (mem_img8 D e).mp hγ
  rw [matOf_mulVec, C.rho_T_pi_a D ha haV ht htN]

theorem Wg_fix (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {a : G} (ha : a ∈ V₂)
    {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) :
    (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hγ
  rw [matOf_mulVec, C.rho_Wg_pi_a D ha hw hwN]

theorem img_Wg_comm (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
    ∀ x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g),
      ∀ y ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g), x * y = y * x := by
  intro x hx y hy
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  obtain ⟨w', hw', hw'N, rfl⟩ := (mem_img8 D e).mp hy
  have hm : w * w' * w⁻¹ * w'⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hw') (Subgroup.inv_mem _ hw))
      (Subgroup.inv_mem _ hw')
  have h1 := (C.matOf_eq_one_iff D e (C.WgH hm)).mpr (C.comm_mem_Q D hw hw')
  have e1 : (⟨w * w' * w⁻¹ * w'⁻¹, L14332.l32nH_le_normalizer_fsuU T V (C.WgH hm)⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨w, hwN⟩ * ⟨w', hw'N⟩ * ⟨w, hwN⟩⁻¹ * ⟨w', hw'N⟩⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
    map_inv] at h1
  calc matOf e (D.ρ ⟨w, hwN⟩) * matOf e (D.ρ ⟨w', hw'N⟩)
      = (matOf e (D.ρ ⟨w, hwN⟩) * matOf e (D.ρ ⟨w', hw'N⟩) * (matOf e (D.ρ ⟨w, hwN⟩))⁻¹ *
          (matOf e (D.ρ ⟨w', hw'N⟩))⁻¹) * matOf e (D.ρ ⟨w', hw'N⟩) *
            matOf e (D.ρ ⟨w, hwN⟩) := by group
    _ = matOf e (D.ρ ⟨w', hw'N⟩) * matOf e (D.ρ ⟨w, hwN⟩) := by rw [h1, one_mul]

theorem img_Wg_sq (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {x : GL (Fin 8) (ZMod 2)}
    (hx : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) : x * x = 1 := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  rw [← map_mul, ← map_mul]
  have e1 : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨w, hwN⟩ =
      ⟨w * w, L14332.l32nH_le_normalizer_fsuU T V (C.WgH (Subgroup.mul_mem _ hw hw))⟩ := rfl
  rw [e1]
  exact (C.matOf_eq_one_iff D e (C.WgH (Subgroup.mul_mem _ hw hw))).mpr (C.sq_mem_Q D hw)

theorem conj_mem_img_Wg (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {n : GL (Fin 8) (ZMod 2)} (hn : n ∈ img8 D e (l32nH T V))
    (hnfix : (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a))
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) :
    n * x * n⁻¹ ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  obtain ⟨h, hh, hhN, rfl⟩ := (mem_img8 D e).mp hn
  have hfix : D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ (D.π a) = D.π a := by
    apply e.injective
    rw [← matOf_mulVec]
    exact hnfix
  have hhV₂ := C.mem_normalizer_of_fix D ha haV hh hfix
  have hconj : h * w * h⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V :=
    (Subgroup.mem_normalizer_iff.mp (C.nWg ⟨hh, hhV₂⟩) w).mp (Subgroup.mem_sup_left hw)
  have h1 : img8 D e (CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V) =
      img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [img8_sup D e (C.WgH.trans HN) (fun c (hc : c ∈ l32nCHat T V) => HN hc.1),
      img8_cHat, sup_bot_eq]
  rw [← h1]
  refine (mem_img8 D e).mpr ⟨h * w * h⁻¹, hconj,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN) (Subgroup.inv_mem _ hhN), ?_⟩
  rw [show (⟨h * w * h⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN)
      (Subgroup.inv_mem _ hhN)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨h, hhN⟩ * ⟨w, hwN⟩ * ⟨h, hhN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, map_mul,
    map_mul, map_inv]

theorem mulVec_add_mem_hatE (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {x : GL (Fin 8) (ZMod 2)}
    (hx : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) {v : Fin 8 → ZMod 2}
    (hv : D.B (e.symm v) (D.π a) = 0) :
    (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v ∈
      (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨_, S⟩ := C.set14
  have haU := C.V2U ha
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm v)
  have hev : e (D.π u) = v := by rw [hue, LinearEquiv.apply_symm_apply]
  have huW : u ∈ l32nW T V V₂ := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v' hv' => ?_⟩
    have hua : u * a * u⁻¹ * a⁻¹ = 1 := (D.B_spec u hu a haU).mp (by rw [hue]; exact hv)
    have hua' : a * u = u * a := by
      calc a * u = (u * a * u⁻¹ * a⁻¹)⁻¹ * u * a := by group
        _ = u * a := by rw [hua]; group
    have hcen : ∀ z ∈ fsuV1 T V, z * u = u * z := fun z hz => by
      rw [← C.zU] at hz
      exact (Subgroup.mem_centralizer_iff.mp hz.2 u hu).symm
    rcases S.mem_V2 ha haV hv' with h1 | h1
    · exact hcen v' h1
    · have haa : a * a = 1 := S.mul_self_V (C.plane.1.1 ha)
      have hv'' : v' = a * (a * v') := by rw [← mul_assoc, haa, one_mul]
      rw [hv'']
      calc a * (a * v') * u = a * ((a * v') * u) := by group
        _ = a * (u * (a * v')) := by rw [hcen _ h1]
        _ = (a * u) * (a * v') := by group
        _ = u * (a * (a * v')) := by rw [hua']; group
  have hcommE : w * u * w⁻¹ * u⁻¹ ∈ l32nE T V V₂ g := by
    have h1 := C.wwE (Subgroup.commutator_mem_commutator huW hw)
    have h2 : w * u * w⁻¹ * u⁻¹ = (u * w * u⁻¹ * w⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.inv_mem _ (by simpa [commutatorElement_def] using h1)
  have hcU : w * u * w⁻¹ * u⁻¹ ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem hwN hu) (Subgroup.inv_mem _ hu)
  refine ⟨D.π (w * u * w⁻¹ * u⁻¹), L128A.HatU.π_mem_hat D hcommE hcU, ?_⟩
  rw [← L128A.HatU.rho_sub_π D hwN hu, sub_eq_add_neg, neg_eq_self_zmod2, LinearEquiv.coe_coe,
    map_add, ← matOf_mulVec, hev]

theorem T_L1 : T ≤ Subgroup.normalizer (lOne L (fsuV1 T V) : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  rw [lOne_eq_L₁Of]
  exact S.T_Lp

theorem relIndex_L1_inf : (lOne L (fsuV1 T V) ⊓ T).relIndex (lOne L (fsuV1 T V)) = 3 := by
  obtain ⟨_, S⟩ := C.set14
  have hP3 : (pCoreOf 2 (lOne L (fsuV1 T V))).relIndex (lOne L (fsuV1 T V)) = 3 := by
    rw [lOne_eq_L₁Of]
    exact S.Lp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPT : pCoreOf 2 (lOne L (fsuV1 T V)) ≤ T :=
    le_of_normalizes (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans L14411.L1H)
      (C.T_L1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hPle : pCoreOf 2 (lOne L (fsuV1 T V)) ≤ lOne L (fsuV1 T V) ⊓ T :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hPT
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (lOne L (fsuV1 T V)))
    (lOne L (fsuV1 T V) ⊓ T) (lOne L (fsuV1 T V)) hPle inf_le_left
  rw [hP3] at hmul
  have hdvd : (lOne L (fsuV1 T V) ⊓ T).relIndex (lOne L (fsuV1 T V)) ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h3
  · exfalso
    have hle : lOne L (fsuV1 T V) ≤ T :=
      (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    obtain ⟨n, hn⟩ := (C.hyp.fsu.sylow.1.to_le hle).exists_card_eq
    have h3d : 3 ∣ Nat.card (lOne L (fsuV1 T V)) := by
      rw [← hP3]
      exact Dvd.intro _ (Subgroup.relIndex_mul_card _ _)
    rw [hn] at h3d
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3d) (by norm_num)
  · exact h3

theorem relIndex_L1T : T.relIndex (lOne L (fsuV1 T V) ⊔ T) = 3 := by
  have h1 := L32NSet14.card_sup_mul_card_inf C.T_L1
  rw [sup_comm, inf_comm] at h1
  have h2 := Subgroup.relIndex_mul_card (lOne L (fsuV1 T V) ⊓ T) (lOne L (fsuV1 T V))
  rw [C.relIndex_L1_inf, inf_right_comm, inf_idem] at h2
  have h3 := Subgroup.relIndex_mul_card T (lOne L (fsuV1 T V) ⊔ T)
  rw [inf_eq_left.mpr le_sup_right] at h3
  have hpos : 0 < Nat.card ↥(lOne L (fsuV1 T V) ⊓ T) := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have h4 : Nat.card ↥(lOne L (fsuV1 T V) ⊔ T) = 3 * Nat.card T := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← h2]
    ring
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right hTpos (by rw [h3])

theorem L1TH : lOne L (fsuV1 T V) ⊔ T ≤ l32nH T V := sup_le L14411.L1H C.TH

theorem card_img_L1T (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
    Nat.card (img8 D e (lOne L (fsuV1 T V) ⊔ T)) = Nat.card (img8 D e T) * 3 := by
  rw [card_img8, card_img8, C.card_img_eq D C.L1TH, C.card_img_eq D C.TH,
    ← Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (lOne L (fsuV1 T V) ⊔ T) C.QT
      le_sup_right, C.relIndex_L1T]

theorem exists_L1_move {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    ∃ l, ∃ hl : l ∈ lOne L (fsuV1 T V),
      D.ρ ⟨l, HN (L14411.L1H hl)⟩ (D.π a) ≠ D.π a := by
  obtain ⟨_, S⟩ := C.set14
  by_contra hall
  push Not at hall
  have hN : ∀ l ∈ lOne L (fsuV1 T V), l ∈ Subgroup.normalizer (V₂ : Set G) := fun l hl =>
    C.mem_normalizer_of_fix D ha haV (L14411.L1H hl) (hall l hl)
  have hle : conjClosure V₂ (L₁Of L (fsuV1 T V)) ≤ V₂ :=
    conjClosure_le fun x hx v hv =>
      (Subgroup.mem_normalizer_iff.mp (hN x (by rw [lOne_eq_L₁Of]; exact hx)) v).mp hv
  rw [S.gen] at hle
  have h := Subgroup.card_le_of_le hle
  rw [S.card_V, C.plane.1.2.1] at h
  norm_num at h

theorem L1_eq_oTwoUpper : lOne L (fsuV1 T V) = oTwoUpper (lOne L (fsuV1 T V) ⊔ T) :=
  eq_oTwoUpper_of_pow_mem le_sup_left
    (fun _ hx => L128P.exists_two_pow_mem_of_le_sup C.hyp.fsu.sylow.1 C.T_L1 le_rfl hx)
    L14411.L1_eq

end Base

end CFSG.Quasithin.H13.L144B
