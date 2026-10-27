module

public import CFSG.Quasithin.Vol2.GoldschmidtL128Wire
public import CFSG.Quasithin.H13.L32NLem14411b
public import CFSG.Quasithin.H13.L32NLem1447a
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace L1447

theorem sub_eq_add_vec {n : ℕ} (a b : Fin n → ZMod 2) : a - b = a + b :=
  funext fun i => CharTwo.sub_eq_add (a i) (b i)

theorem lt_card_of_coords {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {ψ : M ≃ₗ[ZMod 2] M} {γ : GL (Fin n) (ZMod 2)}
    (hγ : ∀ v, (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) = e (ψ v))
    (h : 4 < (Finset.univ.image fun w : Fin n → ZMod 2 =>
      (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w).card)
    (S : Finset M) (hS : ∀ v, ψ v - v ∈ S) : 4 < S.card := by
  refine h.trans_le ((Finset.card_le_card fun w hw => ?_).trans_eq
    (S.card_map e.toEquiv.toEmbedding))
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
  refine Finset.mem_map.mpr ⟨ψ (e.symm x) - e.symm x, hS _, ?_⟩
  show e (ψ (e.symm x) - e.symm x) = _
  rw [map_sub, ← hγ, LinearEquiv.apply_symm_apply]
  exact sub_eq_add_vec _ _

theorem ne_of_coords {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {ψ : M ≃ₗ[ZMod 2] M} {γ : GL (Fin n) (ZMod 2)}
    (hγ : ∀ v, (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) = e (ψ v)) {p : M}
    (h : ∀ w, (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w ≠ e p) (v : M) :
    ψ v - v ≠ p := by
  intro hv
  apply h (e v)
  rw [hγ, ← hv, map_sub]
  exact (sub_eq_add_vec _ _).symm

theorem card_range_le {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ψ : M ≃ₗ[ZMod 2] M) (S : Finset M) (hS : ∀ v, ψ v - v ∈ S) :
    Nat.card ↥(LinearMap.range (ψ.toLinearMap - LinearMap.id)) ≤ S.card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_mono (Set.toFinite _) fun w hw => ?_
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
  exact hS v

theorem exists_ker {M : Type*} [AddCommGroup M] (f : M →+ M) (φ : M →+ ZMod 2) (p : M)
    (h : ∀ S : Finset M, (∀ v, f v ∈ S) → 4 < S.card) : ∃ v, φ v = 0 ∧ f v ≠ 0 ∧ f v ≠ p := by
  classical
  by_contra hne
  push Not at hne
  by_cases hu : ∃ u, φ u ≠ 0
  · obtain ⟨u, hu⟩ := hu
    refine absurd (h {0, p, f u, f u + p} fun v => ?_) (not_lt.mpr Finset.card_le_four)
    by_cases hv : φ v = 0
    · by_cases h0 : f v = 0
      · rw [h0]; simp
      · rw [hne v hv h0]; simp
    · have hφ : φ (v - u) = 0 := by
        rw [map_sub]
        exact (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a - b = 0) _ _ hv hu
      have hf : f v = f u + f (v - u) := by rw [map_sub]; abel
      by_cases h0 : f (v - u) = 0
      · rw [hf, h0, add_zero]; simp
      · rw [hf, hne _ hφ h0]; simp
  · push Not at hu
    refine absurd (h {0, p} fun v => ?_) (not_lt.mpr (Finset.card_le_two.trans (by norm_num)))
    by_cases h0 : f v = 0
    · rw [h0]; simp
    · rw [hne v (hu v) h0]; simp

end L1447

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
variable (C : Base G T L V V₂ g)
include C

theorem pi_V2 (D : HatModelU (fsuU T V)) {a c : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hc : c ∈ V₂) : D.π c = 0 ∨ D.π c = D.π a := by
  obtain ⟨_, S⟩ := C.set14
  rcases S.mem_V2 ha haV hc with h | h
  · refine Or.inl ((L128A.HatU.π_eq_zero_iff D (C.V2U hc)).mpr ?_)
    rw [C.zU]
    exact h
  · refine Or.inr ((D.π_eq_iff _ (C.V2U ha) _ (C.V2U hc)).mpr ?_).symm
    rw [C.zU, inv_eq_of_mul_eq_one_right (S.mul_self_V (C.plane.1.1 ha))]
    exact h

theorem F1_of_vec (D : HatModelU (fsuU T V)) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (h : ∀ x (hx : x ∈ l32nH T V), x ∉ pCoreOf 2 (l32nH T V) →
      x * x ∈ pCoreOf 2 (l32nH T V) → ∃ v, D.B v (D.π a) = 0 ∧
        D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩ v - v ≠ 0 ∧
        D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩ v - v ≠ D.π a) :
    F1 T V V₂ := by
  obtain ⟨_, S⟩ := C.set14
  intro x hx hxQ hxx
  obtain ⟨v, hvB, hv0, hva⟩ := h x hx hxQ hxx
  obtain ⟨w, hw, rfl⟩ := D.π_surj v
  have haU := C.V2U ha
  have hwa : w * a = a * w := by
    have h1 := (D.B_spec w hw a haU).mp hvB
    calc w * a = w * a * w⁻¹ * a⁻¹ * (a * w) := by group
      _ = a * w := by rw [h1, one_mul]
  have hwa' : a⁻¹ * w = w * a⁻¹ := by
    calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * w) * a⁻¹ := by rw [hwa]
      _ = w * a⁻¹ := by group
  have hZ : ∀ z ∈ fsuV1 T V, z * w = w * z := fun z hz => by
    have hz' : z ∈ centerOf (fsuU T V) := by rw [C.zU]; exact hz
    exact (Subgroup.mem_centralizer_iff.mp hz'.2 w hw).symm
  have hwW : w ∈ l32nW T V V₂ := by
    refine ⟨hw, Subgroup.mem_centralizer_iff.mpr fun c hc => ?_⟩
    rcases S.mem_V2 ha haV hc with h1 | h1
    · exact hZ c h1
    · have hd := hZ _ h1
      calc c * w = a⁻¹ * ((a * c) * w) := by group
        _ = a⁻¹ * (w * (a * c)) := by rw [hd]
        _ = (a⁻¹ * w) * (a * c) := by group
        _ = (w * a⁻¹) * (a * c) := by rw [hwa']
        _ = w * c := by group
  refine ⟨w, hwW, fun hc => ?_⟩
  have hc' : x * w * x⁻¹ * w⁻¹ ∈ V₂ := by
    have := V₂.inv_mem hc
    rwa [show (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ by group] at this
  rw [L128A.HatU.rho_sub_π D _ hw] at hv0 hva
  rcases C.pi_V2 D ha haV hc' with h1 | h1
  · exact hv0 h1
  · exact hva h1

theorem F1_of_small (D : HatModelU (fsuU T V))
    (h : ∀ x (hx : x ∈ l32nH T V), x ∉ pCoreOf 2 (l32nH T V) →
      x * x ∈ pCoreOf 2 (l32nH T V) → ∀ S : Finset D.V,
        (∀ v, D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩ v - v ∈ S) → 4 < S.card) :
    F1 T V V₂ := by
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  refine C.F1_of_vec D ha haV fun x hx hxQ hxx => ?_
  set ψ := D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩ with hψ
  let f : D.V →+ D.V :=
    { toFun := fun v => ψ v - v
      map_zero' := by simp
      map_add' := fun v w => by simp only [map_add]; abel }
  let φ : D.V →+ ZMod 2 :=
    { toFun := fun v => D.B v (D.π a)
      map_zero' := by simp
      map_add' := fun v w => by simp }
  obtain ⟨v, hv, hv0, hva⟩ := exists_ker f φ (D.π a) (h x hx hxQ hxx)
  exact ⟨v, hv, hv0, hva⟩

theorem img_Wg_sq' (D : HatModelU (fsuU T V)) {x : D.V ≃ₗ[ZMod 2] D.V}
    (hx : x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g)) : x * x = 1 := by
  obtain ⟨w, hw, hwN, rfl⟩ := (L128A.HatU.mem_img D).mp hx
  have hww := C.WgH (Subgroup.mul_mem _ hw hw)
  rw [← map_mul]
  have e1 : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨w, hwN⟩ =
      ⟨w * w, L14332.l32nH_le_normalizer_fsuU T V hww⟩ := rfl
  rw [e1, L14332.rho_eq_one_iff_mem hww, C.cHat]
  exact C.sq_mem_Q D hw

theorem F2_of_fix (D : HatModelU (fsuU T V)) {a : G} (ha : a ∈ V₂)
    (h : ∀ v, (∀ x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), x v = v) → v = 0 ∨ v = D.π a) :
    F2 T V V₂ g := by
  intro u hu hcomm
  have hfix : ∀ x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), x (D.π u) = D.π u := by
    intro x hx
    obtain ⟨w, hw, hwN, rfl⟩ := (L128A.HatU.mem_img D).mp hx
    rw [D.ρ_π _ u hu]
    congr 1
    show w * u * w⁻¹ = u
    rw [← hcomm w hw]
    group
  rcases h _ hfix with h0 | h0
  · rw [L128A.HatU.π_eq_zero_iff D hu, C.zU] at h0
    exact C.plane.2 h0
  · have h1 := (D.π_eq_iff _ (C.V2U ha) _ hu).mp h0.symm
    rw [C.zU] at h1
    have e1 : u = a * (a⁻¹ * u) := by group
    rw [e1]
    exact V₂.mul_mem ha (C.plane.2 h1)

theorem F2_of_small (h12213 : Stmt12_2_13) (D : HatModelU (fsuU T V)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V)
    (h : ∀ x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), x ≠ 1 → x * x = 1 →
      (∀ S : Finset D.V, (∀ v, x v - v ∈ S) → 4 < S.card) ∨ ∀ v, x v - v ≠ D.π a) :
    F2 T V V₂ g := by
  refine C.F2_of_fix D ha fun v hv => ?_
  by_contra hne
  push Not at hne
  obtain ⟨x, hx, hx1, hrk, hxa⟩ := (lemma12_8_11_hat_of C.h1222 h12213 G T L V 3 (fsuV1 T V) V₂
    C.s1282 g C.gP C.gH a ha haV D).2.2 ⟨v, hv, hne.1, hne.2⟩
  rcases h x hx hx1 (C.img_Wg_sq' D hx) with h1 | h1
  · have : Module.Finite (ZMod 2) ↥(LinearMap.range (x.toLinearMap - LinearMap.id)) :=
      Module.Finite.of_finite
    have hcard : Nat.card ↥(LinearMap.range (x.toLinearMap - LinearMap.id)) ≤ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      calc 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.range (x.toLinearMap - LinearMap.id))
          ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrk
        _ = 4 := by norm_num
    have hfin := Set.toFinite (LinearMap.range (x.toLinearMap - LinearMap.id) : Set D.V)
    have h2 := h1 hfin.toFinset fun w =>
      (Set.Finite.mem_toFinset hfin).mpr (LinearMap.mem_range.mpr ⟨w, rfl⟩)
    have h3 : hfin.toFinset.card =
        Nat.card ↥(LinearMap.range (x.toLinearMap - LinearMap.id)) :=
      (Nat.card_eq_card_finite_toFinset hfin).symm
    omega
  · obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hxa
    exact h1 w hw

theorem F3_of_map {M : Type*} [Group M] (D : HatModelU (fsuU T V))
    (μ : (D.V ≃ₗ[ZMod 2] D.V) →* M) (hμ : Function.Injective μ)
    (h : oTwoUpper ((D.img (l32nH T V)).map μ) ≤ Subgroup.closure
      {y | ∃ k ∈ (D.img (l32nH T V)).map μ,
        ∃ w ∈ (D.img (CFSG.conjugate (l32nW T V V₂) g)).map μ, y = k * w * k⁻¹}) :
    F3 T V V₂ g := by
  have hHN := L14332.l32nH_le_normalizer_fsuU T V
  set N : Subgroup G := Subgroup.closure {y | ∃ h ∈ l32nH T V,
    ∃ w ∈ CFSG.conjugate (l32nW T V V₂) g, y = h * w * h⁻¹} with hN
  have hNH : N ≤ l32nH T V := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨k, hk, w, hw, rfl⟩
    exact (l32nH T V).mul_mem ((l32nH T V).mul_mem hk (C.WgH hw)) ((l32nH T V).inv_mem hk)
  have himg : Subgroup.closure {y | ∃ k ∈ (D.img (l32nH T V)).map μ,
      ∃ w ∈ (D.img (CFSG.conjugate (l32nW T V V₂) g)).map μ, y = k * w * k⁻¹} ≤
        (D.img N).map μ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨k', hk', w', hw', rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hk'
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hφ
    obtain ⟨φ', hφ', rfl⟩ := Subgroup.mem_map.mp hw'
    obtain ⟨w, hw, hwN, rfl⟩ := (L128A.HatU.mem_img D).mp hφ'
    have hmem : k * w * k⁻¹ ∈ N := Subgroup.subset_closure ⟨k, hk, w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨D.ρ ⟨k * w * k⁻¹, hHN (hNH hmem)⟩,
      L128A.HatU.rho_mem_img D hmem _, ?_⟩
    have e1 : (⟨k * w * k⁻¹, hHN (hNH hmem)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨k, hkN⟩ * ⟨w, hwN⟩ * ⟨k, hkN⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  show oTwoUpper (l32nH T V) ≤ N ⊔ pCoreOf 2 (l32nH T V)
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  obtain ⟨hyH, hodd⟩ := hy
  have hd : orderOf (μ (D.ρ ⟨y, hHN hyH⟩)) ∣ orderOf y := by
    have := orderOf_map_dvd (μ.comp D.ρ) ⟨y, hHN hyH⟩
    rwa [Subgroup.orderOf_mk] at this
  have h1 : μ (D.ρ ⟨y, hHN hyH⟩) ∈ oTwoUpper ((D.img (l32nH T V)).map μ) :=
    Subgroup.subset_closure ⟨Subgroup.mem_map.mpr ⟨_, L128A.HatU.rho_mem_img D hyH _, rfl⟩,
      hodd.of_dvd_nat hd⟩
  obtain ⟨φ, hφ, hφe⟩ := Subgroup.mem_map.mp (himg (h h1))
  obtain ⟨n, hn, hnN, rfl⟩ := (L128A.HatU.mem_img D).mp hφ
  have hnyH : n⁻¹ * y ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).inv_mem (hNH hn)) hyH
  have hρ : D.ρ ⟨n⁻¹ * y, hHN hnyH⟩ = 1 := by
    have e1 : (⟨n⁻¹ * y, hHN hnyH⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨n, hnN⟩⁻¹ * ⟨y, hHN hyH⟩ := rfl
    rw [e1, map_mul, map_inv, hμ hφe, inv_mul_cancel]
  have hQ : n⁻¹ * y ∈ pCoreOf 2 (l32nH T V) := by
    rw [← C.cHat]
    exact (L14332.rho_eq_one_iff_mem hnyH _).mp hρ
  have e2 : y = n * (n⁻¹ * y) := by group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hQ)

section Coords

variable (D : HatModelU (fsuU T V)) {n : ℕ} (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
  (μ : (D.V ≃ₗ[ZMod 2] D.V) →* GL (Fin n) (ZMod 2))

omit C [Finite G] in
theorem eq_one_of_coords
    (hμ : ∀ ψ v, ((μ ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) =
      e (ψ v)) {ψ : D.V ≃ₗ[ZMod 2] D.V} (h : μ ψ = 1) : ψ = 1 := by
  ext v
  apply e.injective
  rw [← hμ, h]
  simp

theorem invol_of_coords
    (hμ : ∀ ψ v, ((μ ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) =
      e (ψ v)) {x : G} (hx : x ∈ l32nH T V) (hxQ : x ∉ pCoreOf 2 (l32nH T V))
    (hxx : x * x ∈ pCoreOf 2 (l32nH T V)) :
    μ (D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩) ≠ 1 ∧
      μ (D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩) *
        μ (D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hx⟩) = 1 := by
  have hxN := L14332.l32nH_le_normalizer_fsuU T V hx
  have hxxH : x * x ∈ l32nH T V := (l32nH T V).mul_mem hx hx
  refine ⟨fun h1 => hxQ ?_, ?_⟩
  · rw [← C.cHat, ← L14332.rho_eq_one_iff_mem hx hxN]
    exact eq_one_of_coords D e μ hμ h1
  · rw [← map_mul, ← map_mul]
    have e1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨x, hxN⟩ =
        ⟨x * x, L14332.l32nH_le_normalizer_fsuU T V hxxH⟩ := rfl
    have h1 : D.ρ ⟨x * x, L14332.l32nH_le_normalizer_fsuU T V hxxH⟩ = 1 := by
      rw [L14332.rho_eq_one_iff_mem hxxH, C.cHat]
      exact hxx
    rw [e1, h1, map_one]

theorem F1_of_coords
    (hμ : ∀ ψ v, ((μ ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) =
      e (ψ v))
    (h : ∀ γ ∈ (D.img (l32nH T V)).map μ, γ ≠ 1 → γ * γ = 1 →
      4 < (Finset.univ.image fun w : Fin n → ZMod 2 =>
        (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w).card) :
    F1 T V V₂ := by
  refine C.F1_of_small D fun x hx hxQ hxx S hS => ?_
  have hxN := L14332.l32nH_le_normalizer_fsuU T V hx
  obtain ⟨h1, h2⟩ := C.invol_of_coords D e μ hμ hx hxQ hxx
  exact lt_card_of_coords e (hμ _)
    (h _ (Subgroup.mem_map.mpr ⟨_, L128A.HatU.rho_mem_img D hx hxN, rfl⟩) h1 h2) S hS

theorem F1_of_coords_vec
    (hμ : ∀ ψ v, ((μ ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) =
      e (ψ v)) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    {F : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2} (hform : ∀ x y, D.B x y = F (e x) (e y))
    (h : ∀ γ ∈ (D.img (l32nH T V)).map μ, γ ≠ 1 → γ * γ = 1 → ∃ w, F w (e (D.π a)) = 0 ∧
      (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w ≠ 0 ∧
      (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w ≠ e (D.π a)) :
    F1 T V V₂ := by
  refine C.F1_of_vec D ha haV fun x hx hxQ hxx => ?_
  have hxN := L14332.l32nH_le_normalizer_fsuU T V hx
  obtain ⟨h1, h2⟩ := C.invol_of_coords D e μ hμ hx hxQ hxx
  obtain ⟨w, hw, hw0, hwa⟩ :=
    h _ (Subgroup.mem_map.mpr ⟨_, L128A.HatU.rho_mem_img D hx hxN, rfl⟩) h1 h2
  have he : ∀ y : D.V, e (D.ρ ⟨x, hxN⟩ y - y) =
      ((μ (D.ρ ⟨x, hxN⟩) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        (e y) + e y := fun y => by
    rw [map_sub, hμ]
    exact sub_eq_add_vec _ _
  refine ⟨e.symm w, ?_, fun h0 => hw0 ?_, fun h0 => hwa ?_⟩
  · rw [hform, LinearEquiv.apply_symm_apply]
    exact hw
  · have := he (e.symm w)
    rwa [h0, map_zero, LinearEquiv.apply_symm_apply, eq_comm] at this
  · have := he (e.symm w)
    rwa [h0, LinearEquiv.apply_symm_apply, eq_comm] at this

theorem F2_of_coords (h12213 : Stmt12_2_13)
    (hμ : ∀ ψ v, ((μ ψ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v) =
      e (ψ v)) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (h : ∀ γ ∈ (D.img (CFSG.conjugate (l32nW T V V₂) g)).map μ, γ ≠ 1 → γ * γ = 1 →
      4 < (Finset.univ.image fun w : Fin n → ZMod 2 =>
        (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w).card ∨
      ∀ w, (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w ≠ e (D.π a)) :
    F2 T V V₂ g := by
  refine C.F2_of_small h12213 D ha haV fun x hx hx1 hxx => ?_
  have hμ1 : μ x ≠ 1 := fun h1 => hx1 (eq_one_of_coords D e μ hμ h1)
  rcases h (μ x) (Subgroup.mem_map_of_mem μ hx) hμ1 (by rw [← map_mul, hxx, map_one])
    with h1 | h1
  · exact Or.inl (lt_card_of_coords e (hμ x) h1)
  · exact Or.inr (ne_of_coords e (hμ x) h1)

end Coords

theorem Wg_le_T : CFSG.conjugate (l32nW T V V₂) g ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := C.hyp.fsu.sylow.1
  have hW2 : IsPGroup 2 ↥(CFSG.conjugate (l32nW T V V₂) g) :=
    (hT2.to_le (inf_le_left.trans C.UT)).map (MulAut.conj g⁻¹).toMonoidHom
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (l32nH T V)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hQN : CFSG.conjugate (l32nW T V V₂) g ≤
      Subgroup.normalizer (pCoreOf 2 (l32nH T V) : Set G) :=
    C.WgH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hX : IsPGroup 2 ↥(CFSG.conjugate (l32nW T V V₂) g ⊔ pCoreOf 2 (l32nH T V)) :=
    hW2.to_sup_of_normal_right' hQ2 hQN
  have hXH : CFSG.conjugate (l32nW T V V₂) g ⊔ pCoreOf 2 (l32nH T V) ≤ l32nH T V :=
    sup_le C.WgH (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hTX : T ≤ Subgroup.normalizer
      ((CFSG.conjugate (l32nW T V V₂) g ⊔ pCoreOf 2 (l32nH T V) : Subgroup G) : Set G) := by
    rw [← C.cHat]
    exact fun t ht => C.nWg ⟨C.TH ht, C.plane.1.2.2 ht⟩
  exact le_sup_left.trans (L14411.le_of_normalizes
    (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH) hX hXH hTX)

end L144B.Base

end CFSG.Quasithin.H13
