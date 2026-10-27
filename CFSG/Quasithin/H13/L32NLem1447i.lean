module

public import CFSG.Quasithin.H13.L32NLem1447g
public import CFSG.Quasithin.H13.L32N1447Model
public import CFSG.Quasithin.H13.L32NLem144Bb

public section

namespace CFSG.Quasithin.H13.L1447

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

omit [Finite G] in
theorem img8_eq_of_modelIso {X : Subgroup G} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    {Q : Matrix (Fin 8) (Fin 8) (ZMod 2)} {Γ : Subgroup (GL (Fin 8) (ZMod 2))}
    (hiso : IsModelIso D X e Q Γ) : img8 D e X = Γ := by
  ext γ
  rw [mem_img8]
  constructor
  · rintro ⟨y, hy, hyN, rfl⟩
    obtain ⟨γ', hγ', hγ'e⟩ := (hiso.img _).mp (L128A.HatU.rho_mem_img D hy hyN)
    rwa [(matOf_eq_iff e _ γ').mpr hγ'e]
  · intro hγ
    have hψ : e.trans ((linOf γ).trans e.symm) ∈ D.img X :=
      (hiso.img _).mpr ⟨γ, hγ, fun v => by simp [linOf_apply]⟩
    obtain ⟨y, hy, hyN, hye⟩ := (L128A.HatU.mem_img D).mp hψ
    refine ⟨y, hy, hyN, ?_⟩
    rw [hye, matOf_eq_iff]
    intro v
    simp [linOf_apply]

theorem not_small_of_coords {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (e : M ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {ψ : M ≃ₗ[ZMod 2] M} {δ : GL (Fin n) (ZMod 2)}
    (hδ : ∀ v, (δ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) = e (ψ v))
    (h : 4 < Nat.card ↥(LinearMap.range (ψ.toLinearMap - LinearMap.id)))
    (F : Finset (Fin n → ZMod 2)) (hF : F.card ≤ 4) :
    ∃ w, (δ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w ∉ F := by
  by_contra hne
  push Not at hne
  have h1 := card_range_le ψ (F.map e.symm.toEquiv.toEmbedding) fun v => by
    refine Finset.mem_map.mpr ⟨(δ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) + e v,
      hne _, ?_⟩
    show e.symm ((δ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) + e v) = ψ v - v
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, hδ, map_sub]
    exact (sub_eq_add_vec _ _).symm
  rw [Finset.card_map] at h1
  omega

section Cert


theorem conj_mem_omega3F {n x : GL (Fin 8) (ZMod 2)} (hn : n ∈ omega3N) (hx : x ∈ omega3F) :
    n * x * n⁻¹ ∈ omega3F := by
  have hidx : omega3F.relIndex omega3N = 2 := by
    have h := Subgroup.relIndex_mul_card omega3F omega3N
    rw [inf_eq_left.mpr omega3F_le_omega3N, card_omega3F, card_omega3N] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 7200) (h.trans (by norm_num))
  have hN : (omega3F.subgroupOf omega3N).Normal := Subgroup.normal_of_index_eq_two hidx
  have h1 := hN.conj_mem ⟨x, omega3F_le_omega3N hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨n, hn⟩
  rw [Subgroup.mem_subgroupOf] at h1
  exact h1

theorem pOrd_eq {c : ℕ} (hc : c < 2) : pOrd c = 2 ^ (5 + c) := by
  interval_cases c <;> rfl

structure Ctx3 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (c : ℕ) : Prop where
  base : Base G T L V V₂ g
  hc : c < 2
  imgH : img8 D e (l32nH T V) = gam c
  form : ∀ x y : D.V, D.B x y = G5Cert.b5V (e x) (e y)
  imgT : img8 D e T = PP c
  oTwo : oTwoUpper (gam c) = omega3
  WW_le : WW c ≤ img8 D e (CFSG.conjugate (l32nW T V V₂) g)

theorem exists_ctx3 (B : Base G T L V V₂ g) (h3 : Case1442Three T V V₂ g D) :
    ∃ (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (c : ℕ), Ctx3 G T L V V₂ g D e c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀, hiso, hHN, xs, hxsW, ⟨γ, -, hγF, hγe⟩, hrk, hWeq⟩ := h3
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact B.ext.2.2.2
  have hform₀ : ∀ x y, D.B x y = G5Cert.b5V (e₀ x) (e₀ y) := by
    intro x y
    have h1 := form_of_quadOf D e₀ hZ2 B.comm_center hiso.quad x y
    rw [q3_eq] at h1
    exact h1
  have hK : img8 D e₀ (oTwoUpper (l32nH T V)) = omega3 := img8_eq_of_modelIso hiso
  have hHle : img8 D e₀ (l32nH T V) ≤ omega3N := by
    intro δ hδ
    obtain ⟨y, hy, hyN, rfl⟩ := (mem_img8 D e₀).mp hδ
    obtain ⟨δ', hδ', hδ'e⟩ := hHN _ (L128A.HatU.rho_mem_img D hy hyN)
    rwa [(matOf_eq_iff e₀ _ δ').mpr hδ'e]
  have h3H : omega3 ≤ img8 D e₀ (l32nH T V) := hK ▸ img8_mono D e₀ (oTwoUpper_le _)
  have hxsγ : matOf e₀ xs = γ := (matOf_eq_iff e₀ xs γ).mpr hγe
  subst hxsγ
  have hxsW8 : matOf e₀ xs ∈ img8 D e₀ (CFSG.conjugate (l32nW T V V₂) g) :=
    Subgroup.mem_map_of_mem _ hxsW
  have hxsH : matOf e₀ xs ∈ img8 D e₀ (l32nH T V) := img8_mono D e₀ B.WgH hxsW8
  have hbig16 : 4 < Nat.card ↥(LinearMap.range (xs.toLinearMap - LinearMap.id)) := by
    have : Module.Finite (ZMod 2) ↥(LinearMap.range (xs.toLinearMap - LinearMap.id)) :=
      Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hrk]
    norm_num
  obtain ⟨c, hc, hΓ⟩ : ∃ c < 2, img8 D e₀ (l32nH T V) = gam c := by
    rcases eq_of_le_omega3N h3H hHle hxsH hγF with hH1 | hH2 | hH3
    · exfalso
      obtain ⟨F, hF, hFx⟩ := h1_small (hH1 ▸ hxsH) hγF (B.img_Wg_sq e₀ hxsW8)
      obtain ⟨w, hw⟩ := not_small_of_coords e₀ (matOf_mulVec e₀ xs) hbig16 F hF
      exact hw (hFx w)
    · exact ⟨0, by norm_num, hH2⟩
    · exact ⟨1, by norm_num, hH3⟩
  have hoTwo : oTwoUpper (gam c) = omega3 := by
    rw [← hΓ, ← img8_oTwoUpper D e₀ HN, hK]
  have hT := B.card_imgT e₀ hΓ (m := 5 + c) (k := 225)
    (by rw [card_gam hc, pOrd_eq hc]) (by decide)
  have hKΓ : img8 D e₀ T ≤ gam c := hΓ ▸ img8_mono D e₀ B.TH
  have hK2 : IsPGroup 2 ↥(img8 D e₀ T) := IsPGroup.of_card hT
  have hP2 : IsPGroup 2 ↥(PP c) := IsPGroup.of_card (n := 5 + c) (by rw [card_PP hc, pOrd_eq hc])
  have hidx : (PP c).relIndex (gam c) = 225 := by
    have h := Subgroup.relIndex_mul_card (PP c) (gam c)
    rw [inf_eq_left.mpr (PP_le_gam hc), card_PP hc, card_gam hc] at h
    have hpos : 0 < pOrd c := by interval_cases c <;> decide
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))
  have hKi : (img8 D e₀ T).relIndex (gam c) = 225 := by
    have h := Subgroup.relIndex_mul_card (img8 D e₀ T) (gam c)
    rw [inf_eq_left.mpr hKΓ, hT, card_gam hc, pOrd_eq hc] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h.trans (mul_comm _ _))
  obtain ⟨k, hkΓ, hkc⟩ := exists_conj_of_sylow hKΓ (PP_le_gam hc) hK2 hP2
    (by rw [hKi]; decide) (by rw [hidx]; decide)
  obtain ⟨y, hyH, hyN, hyk⟩ := (mem_img8 D e₀).mp (hΓ ▸ hkΓ)
  have hke : ∀ x : D.V, (k : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e₀ x) =
      e₀ (D.ρ ⟨y, hyN⟩ x) := fun x => by rw [← hyk, matOf_mulVec]
  set e := e₀.trans (linOf k) with he
  have himgH : img8 D e (l32nH T V) = gam c := by
    rw [he, img8_trans, hΓ, map_conj_of_mem hkΓ]
  have himgT : img8 D e T = PP c := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [he, img8_trans]
      rintro _ ⟨x, hx, rfl⟩
      exact hkc x hx
    · rw [he, img8_trans, Subgroup.card_map_of_injective (MulEquiv.injective _), hT, card_PP hc,
        pOrd_eq hc]
  have hform : ∀ x x' : D.V, D.B x x' = G5Cert.b5V (e x) (e x') := by
    intro x x'
    simp only [he, LinearEquiv.trans_apply, linOf_apply, hke]
    rw [← hform₀, L128A.HatU.B_rho]
  have hxF : matOf e xs ∉ omega3F := by
    rw [he, matOf_trans]
    intro hmem
    apply hγF
    have hkN : k ∈ omega3N := gam_le_omega3N hc hkΓ
    have h1 := conj_mem_omega3F (omega3N.inv_mem hkN) hmem
    simpa [mul_assoc] using h1
  have hxW : matOf e xs ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) :=
    Subgroup.mem_map_of_mem _ hxsW
  have hxP : matOf e xs ∈ PP c := himgT ▸ img8_mono D e B.Wg_le_T hxW
  have hWW := eq_WW_of hc hxP hxF (B.img_Wg_sq e hxW)
    (not_small_of_coords e (matOf_mulVec e xs) hbig16)
  have hK' : img8 D e (oTwoUpper (l32nH T V)) = omega3 := by
    rw [img8_oTwoUpper D e HN, himgH, hoTwo]
  have hWle : WW c ≤ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [← hWW]
    refine sup_le (fun z hz => ?_) ((Subgroup.zpowers_le).mpr hxW)
    obtain ⟨⟨hzP, hz3⟩, hzc⟩ := hz
    rw [← himgT] at hzP
    rw [← hK'] at hz3
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hzP
    obtain ⟨φ', hφ', hφφ'⟩ := Subgroup.mem_map.mp hz3
    have hφe : φ' = φ := matOf_injective e hφφ'
    subst hφe
    have hcomm : φ' ∈ Subgroup.centralizer ({xs} : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hzc
      rw [← map_mul, ← map_mul] at h1
      exact matOf_injective e h1
    have hmem : φ' ∈ D.img (CFSG.conjugate (l32nW T V V₂) g) := by
      rw [hWeq]
      exact Subgroup.mem_sup_left ⟨⟨hφ, hφ'⟩, hcomm⟩
    exact Subgroup.mem_map_of_mem _ hmem
  exact ⟨e, c, B, hc, himgH, hform, himgT, hoTwo, hWle⟩

theorem Ctx3.e_pi_a {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ}
    (C : Ctx3 G T L V V₂ g D e c) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    e (D.π a) = vec8 (vS c) := by
  rcases eq_of_fixed_PP C.hc (e (D.π a))
      (fun γ hγ => C.base.T_fix e ha haV (by rw [C.imgT]; exact hγ)) with h | h
  · exact absurd ((map_eq_zero_iff e e.injective).mp h) (C.base.pi_a_ne D ha haV)
  · exact h

theorem facts_of_ctx3 (h12213 : Stmt12_2_13)
    {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} (C : Ctx3 G T L V V₂ g D e c) :
    F1 T V V₂ ∧ F2 T V V₂ g ∧ F3 T V V₂ g := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  have hva := C.e_pi_a ha haV
  refine ⟨C.base.F1_of_coords_vec D e (matOf e) (matOf_mulVec e) ha haV C.form
      fun γ hγ h1 h2 => ?_,
    C.base.F2_of_coords D e (matOf e) h12213 (matOf_mulVec e) ha haV fun γ hγ h1 h2 => ?_,
    C.base.F3_of_map D (matOf e) (matOf_injective e) ?_⟩
  · have hγ' : γ ∈ img8 D e (l32nH T V) := hγ
    rw [C.imgH] at hγ'
    rw [hva]
    exact inv_spec C.hc hγ' h1 h2
  · have hγ' : γ ∈ img8 D e (l32nH T V) := img8_mono D e C.base.WgH hγ
    rw [C.imgH] at hγ'
    rw [hva]
    exact o3_big C.hc hγ' h1 h2
  · show oTwoUpper (img8 D e (l32nH T V)) ≤ _
    rw [C.imgH, C.oTwo]
    refine (omega3_le_conj C.hc).trans (Subgroup.closure_mono ?_)
    rintro y ⟨k, hk, w, hw, rfl⟩
    have hk' : k ∈ img8 D e (l32nH T V) := by rw [C.imgH]; exact omega3_le_gam C.hc hk
    exact ⟨k, hk', w, C.WW_le hw, rfl⟩

end Cert

end CFSG.Quasithin.H13.L1447
