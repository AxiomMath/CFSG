module

public import CFSG.Quasithin.H13.L32NLem14412a
public import CFSG.Quasithin.H13.L32NLem144Bb

public section

namespace CFSG.Quasithin.H13.L144B

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L1442M

variable {n : ℕ} {G : Type} [Group G]

theorem form_of_quadOfN {U : Subgroup G} (D : HatModelU U) (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    {Q : Matrix (Fin n) (Fin n) (ZMod 2)} (hZ : Nat.card (centerOf U) = 2)
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

theorem imgN_eq_of_iso {T V : Subgroup G} {D : HatModelU (fsuU T V)}
    {e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)} {Q : Matrix (Fin n) (Fin n) (ZMod 2)}
    {Γ : Subgroup (GL (Fin n) (ZMod 2))} (hiso : IsModelIso D (l32nH T V) e Q Γ) :
    imgN D e (l32nH T V) = Γ := by
  ext γ
  rw [mem_imgN]
  constructor
  · rintro ⟨y, hy, hyN, rfl⟩
    obtain ⟨γ', hγ', hγ'e⟩ := (hiso.img _).mp (L128A.HatU.rho_mem_img D hy hyN)
    rwa [(matOfN_eq_iff e _ γ').mpr hγ'e]
  · intro hγ
    have hψ : e.trans ((linOfN γ).trans e.symm) ∈ D.img (l32nH T V) :=
      (hiso.img _).mpr ⟨γ, hγ, fun v => by simp [linOfN_apply]⟩
    obtain ⟨y, hy, hyN, hye⟩ := (L128A.HatU.mem_img D).mp hψ
    refine ⟨y, hy, hyN, ?_⟩
    rw [hye, matOfN_eq_iff]
    intro v
    simp [linOfN_apply]

theorem imgN_cHat {T V : Subgroup G} {D : HatModelU (fsuU T V)}
    {e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)} : imgN D e (l32nCHat T V) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  obtain ⟨c, hc, hcN, rfl⟩ := (mem_imgN D e).mp hγ
  rw [Subgroup.mem_bot, (L14332.rho_eq_one_iff_mem hc.1 hcN).mpr hc, map_one]

variable [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Base

variable (C : Base G T L V V₂ g)
include C

theorem matOfN_eq_one_iff (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    {h : G} (hh : h ∈ l32nH T V) :
    matOfN e (D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩) = 1 ↔
      h ∈ pCoreOf 2 (l32nH T V) := by
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem hh (L14332.l32nH_le_normalizer_fsuU T V hh),
    ← (matOfN e).map_one]
  exact (matOfN_injective e).eq_iff

theorem card_imgTN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {Γ : Subgroup (GL (Fin n) (ZMod 2))}
    (himgH : imgN D e (l32nH T V) = Γ) {m k : ℕ} (hΓ : Nat.card Γ = 2 ^ m * k) (hk : Odd k) :
    Nat.card (imgN D e T) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : (pCoreOf 2 (l32nH T V)).relIndex (l32nH T V) = 2 ^ m * k := by
    rw [← C.card_img_eq D le_rfl, ← card_imgN D e, himgH, hΓ]
  have hT : Nat.card (imgN D e T) = (pCoreOf 2 (l32nH T V)).relIndex T := by
    rw [card_imgN, C.card_img_eq D C.TH]
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (l32nH T V) C.QT C.TH
  rw [hH, ← hT] at hmul
  have hodd : ¬ 2 ∣ T.relIndex (l32nH T V) :=
    (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH).2.2
  have h2 : IsPGroup 2 ↥(imgN D e T) := by
    rw [imgN_eq_map]
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

theorem exists_normalizedN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    {Γ P : Subgroup (GL (Fin n) (ZMod 2))} (himgH : imgN D e (l32nH T V) = Γ)
    {F : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2} (hform : ∀ x y, D.B x y = F (e x) (e y))
    (hPΓ : P ≤ Γ) (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.relIndex Γ)
    (hcard : Nat.card (imgN D e T) = Nat.card P) :
    ∃ e' : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2), imgN D e' (l32nH T V) = Γ ∧
      (∀ x y, D.B x y = F (e' x) (e' y)) ∧ imgN D e' T = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKΓ : imgN D e T ≤ Γ := himgH ▸ imgN_mono D e C.TH
  have hK2 : IsPGroup 2 ↥(imgN D e T) := by
    rw [imgN_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH.trans HN)).symm).map _
  have hKi : ¬ 2 ∣ (imgN D e T).relIndex Γ := by
    have h1 := Subgroup.relIndex_mul_card (imgN D e T) Γ
    have h2 := Subgroup.relIndex_mul_card P Γ
    rw [inf_eq_left.mpr hKΓ, hcard] at h1
    rw [inf_eq_left.mpr hPΓ] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : (imgN D e T).relIndex Γ = P.relIndex Γ := by
      have := h1.trans h2.symm
      exact Nat.eq_of_mul_eq_mul_right hpos this
    rw [this]
    exact hPi
  obtain ⟨c, hcΓ, hc⟩ := exists_conj_of_sylow hKΓ hPΓ hK2 hP2 hKi hPi
  obtain ⟨y, hyH, hyN, hyc⟩ := (mem_imgN D e).mp (himgH ▸ hcΓ)
  have hce : ∀ x : D.V, (c : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e x) =
      e (D.ρ ⟨y, hyN⟩ x) := fun x => by rw [← hyc, matOfN_mulVec]
  refine ⟨e.trans (linOfN c), ?_, fun x x' => ?_, ?_⟩
  · rw [imgN_trans, himgH, map_conj_of_mem hcΓ]
  · simp only [LinearEquiv.trans_apply, linOfN_apply, hce]
    rw [← hform, L128A.HatU.B_rho]
  · have hle : imgN D (e.trans (linOfN c)) T ≤ P := by
      rw [imgN_trans]
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [imgN_trans, Subgroup.card_map_of_injective (MulEquiv.injective _), hcard]

theorem T_fixN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {γ : GL (Fin n) (ZMod 2)} (hγ : γ ∈ imgN D e T) :
    (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
  obtain ⟨t, ht, htN, rfl⟩ := (mem_imgN D e).mp hγ
  rw [matOfN_mulVec, C.rho_T_pi_a D ha haV ht htN]

theorem Wg_fixN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    {γ : GL (Fin n) (ZMod 2)} (hγ : γ ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g)) :
    (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgN D e).mp hγ
  rw [matOfN_mulVec, C.rho_Wg_pi_a D ha hw hwN]

theorem conj_mem_img_WgN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {ν : GL (Fin n) (ZMod 2)} (hν : ν ∈ imgN D e (l32nH T V))
    (hνfix : (ν : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a))
    {x : GL (Fin n) (ZMod 2)} (hx : x ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g)) :
    ν * x * ν⁻¹ ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgN D e).mp hx
  obtain ⟨h, hh, hhN, rfl⟩ := (mem_imgN D e).mp hν
  have hfix : D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ (D.π a) = D.π a := by
    apply e.injective
    rw [← matOfN_mulVec]
    exact hνfix
  have hhV₂ := C.mem_normalizer_of_fix D ha haV hh hfix
  have hconj : h * w * h⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V :=
    (Subgroup.mem_normalizer_iff.mp (C.nWg ⟨hh, hhV₂⟩) w).mp (Subgroup.mem_sup_left hw)
  have h1 : imgN D e (CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V) =
      imgN D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [imgN_sup D e (C.WgH.trans HN) (fun c (hc : c ∈ l32nCHat T V) => HN hc.1),
      imgN_cHat, sup_bot_eq]
  rw [← h1]
  refine (mem_imgN D e).mpr ⟨h * w * h⁻¹, hconj,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN) (Subgroup.inv_mem _ hhN), ?_⟩
  rw [show (⟨h * w * h⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN)
      (Subgroup.inv_mem _ hhN)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨h, hhN⟩ * ⟨w, hwN⟩ * ⟨h, hhN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, map_mul,
    map_mul, map_inv]

theorem mulVec_add_mem_hatEN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {x : GL (Fin n) (ZMod 2)}
    (hx : x ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g)) {v : Fin n → ZMod 2}
    (hv : D.B (e.symm v) (D.π a) = 0) :
    (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v ∈
      (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨_, S⟩ := C.set14
  have haU := C.V2U ha
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgN D e).mp hx
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
    map_add, ← matOfN_mulVec, hev]

theorem card_img_L1TN (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (imgN D e (lOne L (fsuV1 T V) ⊔ T)) = Nat.card (imgN D e T) * 3 := by
  rw [card_imgN, card_imgN, C.card_img_eq D C.L1TH, C.card_img_eq D C.TH,
    ← Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (lOne L (fsuV1 T V) ⊔ T) C.QT
      le_sup_right, C.relIndex_L1T]

end Base

end CFSG.Quasithin.H13.L144B
