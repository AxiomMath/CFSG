module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSigma

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld CFSG.LieType.Steinberg.Adjoint

section Congr

variable {A B : Type} [Group A] [Group B]

theorem congr_conj (e : A ≃* B) (a : A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  refine MulEquiv.ext fun b => ?_
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply,
    MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem isInnerAut_congr_iff (e : A ≃* B) (φ : MulAut A) :
    IsInnerAut (MulAut.congr e φ) ↔ IsInnerAut φ := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨e.symm b, (MulAut.congr e).injective ?_⟩
    rw [hb, congr_conj, MulEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    exact ⟨e a, congr_conj e a⟩

theorem out_le_two_congr (e : A ≃* B)
    (h : ∀ φ₁ φ₂ : MulAut A, ¬ IsInnerAut φ₁ → ¬ IsInnerAut φ₂ → IsInnerAut (φ₁⁻¹ * φ₂)) :
    ∀ φ₁ φ₂ : MulAut B, ¬ IsInnerAut φ₁ → ¬ IsInnerAut φ₂ → IsInnerAut (φ₁⁻¹ * φ₂) := by
  intro φ₁ φ₂ h₁ h₂
  obtain ⟨χ₁, rfl⟩ := (MulAut.congr e).surjective φ₁
  obtain ⟨χ₂, rfl⟩ := (MulAut.congr e).surjective φ₂
  rw [isInnerAut_congr_iff] at h₁ h₂
  rw [← map_inv (MulAut.congr e), ← map_mul (MulAut.congr e), isInnerAut_congr_iff]
  exact h _ _ h₁ h₂

end Congr

variable {G : Type} [Group G] {K : Subgroup G}

theorem conj_inv_mem_of_map {X Y : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom = Y) {y : G} (hy : y ∈ Y) : g⁻¹ * y * g ∈ X := by
  rw [← h] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have e : g⁻¹ * (MulAut.conj g).toMonoidHom x * g = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hx

theorem map_conj_congr {X : Subgroup G} {g h : G}
    (hgh : ∀ x ∈ X, g * x * g⁻¹ = h * x * h⁻¹) :
    X.map (MulAut.conj g).toMonoidHom = X.map (MulAut.conj h).toMonoidHom := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (hgh x hx).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hgh x hx

theorem tr_injective (ψ : ↥L7 ≃* ↥K) {X Y : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7)
    (hY : Y ≤ L7) (h : tr ψ X = tr ψ Y) : X = Y := by
  ext x
  constructor
  · intro hx
    have hm := (coe_mem_tr_iff ψ (X := X) (⟨x, hX hx⟩ : ↥L7)).mpr hx
    rw [h] at hm
    exact (coe_mem_tr_iff ψ (X := Y) _).mp hm
  · intro hx
    have hm := (coe_mem_tr_iff ψ (X := Y) (⟨x, hY hx⟩ : ↥L7)).mpr hx
    rw [← h] at hm
    exact (coe_mem_tr_iff ψ (X := X) _).mp hm

theorem conjAut_mul_psi (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7)
    (g : G) (hg : (tr ψ X).map (MulAut.conj g).toMonoidHom = tr ψ X) (m : ↥X)
    (hgm : (tr ψ X).map (MulAut.conj (g * ((ψ ⟨m, hX m.2⟩ : ↥K) : G))).toMonoidHom = tr ψ X) :
    conjAut ψ hX (g * ((ψ ⟨m, hX m.2⟩ : ↥K) : G)) hgm = conjAut ψ hX g hg * MulAut.conj m := by
  refine MulEquiv.ext fun x => (trEquiv ψ hX).injective (Subtype.ext ?_)
  rw [trEquiv_conjAut, MulAut.mul_apply, trEquiv_conjAut, MulAut.conj_apply, map_mul, map_mul,
    map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_trEquiv ψ hX m]
  group

section M6


theorem m0_map_conj {k : ModGL .E7 (ZMod 2)} (hk : k ∈ L7)
    (hk6 : (Jn 0).map (MulAut.conj k).toMonoidHom = Jn 6) :
    M0.map (MulAut.conj k).toMonoidHom = M6 := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyL, hyC⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨L7.mul_mem (L7.mul_mem hk hyL) (L7.inv_mem hk),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    rw [← hk6] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hu' : u * y = y * u := Subgroup.mem_centralizer_iff.mp hyC u hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * u * k⁻¹ * (k * y * k⁻¹) = k * (u * y) * k⁻¹ := by group
      _ = k * (y * u) * k⁻¹ := by rw [hu']
      _ = k * y * k⁻¹ * (k * u * k⁻¹) := by group
  · rintro ⟨hxL, hxC⟩
    refine ⟨k⁻¹ * x * k, Subgroup.mem_inf.mpr ⟨L7.mul_mem (L7.mul_mem (L7.inv_mem hk) hxL) hk,
      Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
    · intro u hu
      have hku : k * u * k⁻¹ ∈ Jn 6 := by
        rw [← hk6]
        exact ⟨u, hu, rfl⟩
      have h := Subgroup.mem_centralizer_iff.mp hxC _ hku
      calc u * (k⁻¹ * x * k) = k⁻¹ * (k * u * k⁻¹ * x) * k := by group
        _ = k⁻¹ * (x * (k * u * k⁻¹)) * k := by rw [h]
        _ = k⁻¹ * x * k * u := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

def conjM6 {k : ModGL .E7 (ZMod 2)} (hkM : M0.map (MulAut.conj k).toMonoidHom = M6) :
    ↥M0 ≃* ↥M6 :=
  ((MulAut.conj k).subgroupMap M0).trans (MulEquiv.subgroupCongr hkM)

theorem coe_conjM6 {k : ModGL .E7 (ZMod 2)} (hkM : M0.map (MulAut.conj k).toMonoidHom = M6)
    (x : ↥M0) : ((conjM6 hkM x : ↥M6) : ModGL .E7 (ZMod 2)) = k * x * k⁻¹ := by
  change (((MulAut.conj k).subgroupMap M0 x : ↥(M0.map (MulAut.conj k).toMonoidHom)) :
    ModGL .E7 (ZMod 2)) = _
  rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

theorem coe_trEquiv_conjM6 (ψ : ↥L7 ≃* ↥K) {k : ModGL .E7 (ZMod 2)} (hkL : k ∈ L7)
    (hkM : M0.map (MulAut.conj k).toMonoidHom = M6) (y : ↥M0) :
    ((trEquiv ψ (inf_le_left : M6 ≤ L7) (conjM6 hkM y) : ↥(tr ψ M6)) : G) =
      ((ψ ⟨k, hkL⟩ : ↥K) : G) * ((trEquiv ψ (inf_le_left : M0 ≤ L7) y : ↥(tr ψ M0)) : G) *
        ((ψ ⟨k, hkL⟩ : ↥K) : G)⁻¹ := by
  rw [coe_trEquiv, coe_trEquiv]
  have h : (⟨((conjM6 hkM y : ↥M6) : ModGL .E7 (ZMod 2)), (conjM6 hkM y).2.1⟩ : ↥L7) =
      ⟨k, hkL⟩ * ⟨y, y.2.1⟩ * (⟨k, hkL⟩ : ↥L7)⁻¹ := Subtype.ext (coe_conjM6 hkM y)
  rw [h, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem conjAut_m6 (ψ : ↥L7 ≃* ↥K) {k : ModGL .E7 (ZMod 2)} (hkL : k ∈ L7)
    (hkM : M0.map (MulAut.conj k).toMonoidHom = M6) (σ : G)
    (hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0)
    (hσ₆ : (tr ψ M6).map (MulAut.conj (((ψ ⟨k, hkL⟩ : ↥K) : G) * σ *
      ((ψ ⟨k, hkL⟩ : ↥K) : G)⁻¹)).toMonoidHom = tr ψ M6) :
    conjAut ψ (inf_le_left : M6 ≤ L7) (((ψ ⟨k, hkL⟩ : ↥K) : G) * σ * ((ψ ⟨k, hkL⟩ : ↥K) : G)⁻¹)
      hσ₆ = MulAut.congr (conjM6 hkM) (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM) := by
  refine MulEquiv.ext fun x => (trEquiv ψ (inf_le_left : M6 ≤ L7)).injective (Subtype.ext ?_)
  obtain ⟨y, rfl⟩ := (conjM6 hkM).surjective x
  rw [trEquiv_conjAut, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, coe_trEquiv_conjM6 ψ hkL hkM y,
    coe_trEquiv_conjM6 ψ hkL hkM, trEquiv_conjAut]
  group

theorem out_m6 (hC : E7NatCent) (hW : E7NatWeyl) :
    ∀ φ₁ φ₂ : MulAut ↥M6, ¬ IsInnerAut φ₁ → ¬ IsInnerAut φ₂ → IsInnerAut (φ₁⁻¹ * φ₂) := by
  obtain ⟨-, k, hkL, hk6⟩ := hW
  exact out_le_two_congr (conjM6 (m0_map_conj hkL hk6)) hC.2.2.2.2.2

theorem exists_sigma6 (hW : E7NatWeyl) (ψ : ↥L7 ≃* ↥K) (σ : G)
    (hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0)
    (hout : ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM)) :
    ∃ k₆ ∈ K, (tr ψ (Jn 0)).map (MulAut.conj k₆).toMonoidHom = tr ψ (Jn 6) ∧
      ∃ hσ₆ : (tr ψ M6).map (MulAut.conj (k₆ * σ * k₆⁻¹)).toMonoidHom = tr ψ M6,
        ¬ IsInnerAut (conjAut ψ (inf_le_left : M6 ≤ L7) (k₆ * σ * k₆⁻¹) hσ₆) := by
  obtain ⟨-, k, hkL, hk6⟩ := hW
  have hkM := m0_map_conj hkL hk6
  have hM6 : tr ψ M6 = (tr ψ M0).map (MulAut.conj ((ψ ⟨k, hkL⟩ : ↥K) : G)).toMonoidHom := by
    rw [tr_map_conj, hkM]
  have hσ₆ : (tr ψ M6).map (MulAut.conj (((ψ ⟨k, hkL⟩ : ↥K) : G) * σ *
      ((ψ ⟨k, hkL⟩ : ↥K) : G)⁻¹)).toMonoidHom = tr ψ M6 := by
    rw [hM6, map_conj_map_conj, inv_mul_cancel_right, ← map_conj_map_conj, hσM]
  refine ⟨_, (ψ ⟨k, hkL⟩).2, by rw [tr_map_conj, hk6], hσ₆, ?_⟩
  rw [conjAut_m6 ψ hkL hkM σ hσM hσ₆, isInnerAut_congr_iff]
  exact hout

end M6

section Seven


theorem j_le_m6 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (h6 : iform β (Pi.single (6 : Fin 7) 1) = 0) : J β ≤ M6 :=
  le_inf (j_le_l7 hβ) (j_le_centralizer_of_orthogonal hβ (isRoot_single .E7 6) h6)

theorem le_m6 : Jn 0 ≤ M6 ∧ Jn 1 ≤ M6 ∧ Jn 2 ≤ M6 ∧ Jn 3 ≤ M6 ∧ J lam ≤ M6 :=
  ⟨j_le_m6 (isRoot_single .E7 0) (by decide +kernel),
    j_le_m6 (isRoot_single .E7 1) (by decide +kernel),
    j_le_m6 (isRoot_single .E7 2) (by decide +kernel),
    j_le_m6 (isRoot_single .E7 3) (by decide +kernel), j_le_m6 isRoot_lam (by decide +kernel)⟩

theorem exists_sigma' (hC : E7NatCent) (hT : E7NatTau) (hW : E7NatWeyl) (ψ : ↥L7 ≃* ↥K) (σ : G)
    {K₀ : Subgroup G} (hK₀ : K₀ ≤ Subgroup.centralizer (K : Set G))
    (hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0)
    (hout : ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM))
    (h0' : K₀.map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 0)) :
    ∃ σ' : G, (∀ x : G, (x ∈ tr ψ (Jn 0) ∨ x ∈ tr ψ (Jn 1) ∨ x ∈ tr ψ (Jn 2) ∨
        x ∈ tr ψ (Jn 3) ∨ x ∈ tr ψ (J lam)) → σ' * x = x * σ') ∧
      K₀.map (MulAut.conj σ').toMonoidHom = tr ψ (Jn 6) := by
  obtain ⟨k₆, hk₆K, hk₆, hσ₆, hout₆⟩ := exists_sigma6 hW ψ σ hσM hout
  obtain ⟨τ, hτ, hτfix⟩ := hT
  obtain ⟨m₆, hm₆⟩ := out_m6 hC hW _ _ hout₆ hτ
  have hpM : (tr ψ M6).map (MulAut.conj ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) :
      G)).toMonoidHom = tr ψ M6 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((coe_mem_tr_iff ψ _).mpr m₆.2))
  have hσ'M : (tr ψ M6).map (MulAut.conj (k₆ * σ * k₆⁻¹ *
      ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G))).toMonoidHom = tr ψ M6 := by
    rw [← map_conj_map_conj, hpM, hσ₆]
  have hσ' : conjAut ψ (inf_le_left : M6 ≤ L7) (k₆ * σ * k₆⁻¹ *
      ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G)) hσ'M = τ := by
    rw [conjAut_mul_psi ψ inf_le_left _ hσ₆ m₆ hσ'M, ← hm₆, mul_inv_cancel_left]
  refine ⟨k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G), fun x hx => ?_, ?_⟩
  ·
    have hxK : x ∈ K := by
      rcases hx with h | h | h | h | h <;> exact tr_le_K ψ _ h
    obtain ⟨y, rfl⟩ := exists_eq_psi ψ hxK
    simp only [coe_mem_tr_iff] at hx
    have hyM : (y : ModGL .E7 (ZMod 2)) ∈ M6 := by
      obtain ⟨hJ0, hJ1, hJ2, hJ3, hJl⟩ := le_m6
      rcases hx with h | h | h | h | h
      exacts [hJ0 h, hJ1 h, hJ2 h, hJ3 h, hJl h]
    have hfix : τ ⟨y, hyM⟩ = ⟨y, hyM⟩ := hτfix _ hx
    have h := trEquiv_conjAut ψ (inf_le_left : M6 ≤ L7) _ hσ'M ⟨y, hyM⟩
    rw [hσ', hfix, coe_trEquiv] at h
    have h' : ((ψ y : ↥K) : G) = k₆ * σ * k₆⁻¹ *
        ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G) * ((ψ y : ↥K) : G) *
          (k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G))⁻¹ := h
    calc k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G) * ((ψ y : ↥K) : G) =
        k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G) * ((ψ y : ↥K) : G) *
          (k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G))⁻¹ *
          (k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G)) := by group
      _ = ((ψ y : ↥K) : G) *
          (k₆ * σ * k₆⁻¹ * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G)) := by rw [← h']
  ·
    have hp : ∀ x ∈ K₀, ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G) * x =
        x * ((ψ ⟨m₆, (inf_le_left : M6 ≤ L7) m₆.2⟩ : ↥K) : G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mp (hK₀ hx) _ (ψ _).2
    have hk : ∀ x ∈ K₀, k₆⁻¹ * x = x * k₆⁻¹ := fun x hx =>
      Subgroup.mem_centralizer_iff.mp (hK₀ hx) _ (K.inv_mem hk₆K)
    rw [← map_conj_map_conj, map_conj_eq_of_forall_commute hp, ← map_conj_map_conj,
      map_conj_eq_of_forall_commute hk, ← map_conj_map_conj, h0', hk₆]

theorem root_of_mem_tr_jn0 (hW : E7NatWeyl) (ψ : ↥L7 ≃* ↥K) {x : G} (hx : x ∈ tr ψ (Jn 0)) :
    ∃ (ψ' : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) (r : ↥(adjointGroup .E7 (ZMod 2))),
      (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
        ((ψ' r : ↥K) : G) = x := by
  have hJθ : J theta = CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) :=
    (exceptional_Lang_root_rank_one_torus_transport .E7 (ZMod 2)
      (CFSG.SeitzReduction.isRoot_highRoot .E7)).1
  have hθL : J theta ≤ L7 := j_le_l7 isRoot_theta
  obtain ⟨y, hy, hψy⟩ := mem_tr.mp hx
  obtain ⟨⟨w, hwL, hw⟩, -⟩ := hW
  rw [← hw] at hy
  obtain ⟨x', hx', hxy⟩ := hy
  have hxy' : MulAut.conj (⟨w, hwL⟩ : ↥L7) ⟨x', hθL hx'⟩ = y := Subtype.ext hxy
  refine ⟨(MulAut.conj (⟨w, hwL⟩ : ↥L7)).trans ψ, ⟨x', hθL hx'⟩, hJθ ▸ hx', ?_⟩
  rw [MulEquiv.trans_apply, hxy', hψy]

theorem h77_of_sigma [Finite G] {b₀ : G} (hF : E7NatFrame) (hC : E7NatCent) (hT : E7NatTau)
    (hA5 : E7NatA5) (hW : E7NatWeyl) (ψ : ↥L7 ≃* ↥K) (σ : G) {K₀ : Subgroup G}
    (hK₀ : K₀ ≤ Subgroup.centralizer (K : Set G)) (hb₀ : b₀ ∈ K₀) (hb₀3 : orderOf b₀ = 3)
    {R : Subgroup G} (hRb : R ≤ Subgroup.centralizer ({b₀} : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hRK : R ≤ Subgroup.centralizer (K : Set G))
    (hCR : ∀ x ∈ Subgroup.centralizer ({b₀} : Set G),
      (tr ψ (Jn 0)).map (MulAut.conj x).toMonoidHom = tr ψ (J mu) →
        x ∈ R ⊔ (Subgroup.zpowers b₀ ⊔ K))
    (hRσ : R ≤ Subgroup.centralizer (K.map (MulAut.conj σ).toMonoidHom : Set G))
    (hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0)
    (hout : ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM))
    (h0 : (tr ψ (Jn 0)).map (MulAut.conj σ).toMonoidHom = K₀)
    (h0' : K₀.map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 0))
    (h1 : (tr ψ (Jn 1)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 6))
    (h3 : (tr ψ (Jn 3)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 5))
    (h5 : (tr ψ (Jn 5)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 3))
    (h6 : (tr ψ (Jn 6)).map (MulAut.conj σ).toMonoidHom = tr ψ (J mu))
    (hlam : (tr ψ (J lam)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 1)) :
    ∀ u ∈ (tr ψ (J theta)).map (MulAut.conj σ⁻¹).toMonoidHom, ∀ w ∈ tr ψ (Jn 2),
      u * w = w * u := by
  obtain ⟨σ', hσ'fix, hσ'K₀⟩ := exists_sigma' hC hT hW ψ σ hK₀ hσM hout h0'
  have hJ2K : tr ψ (Jn 2) ≤ K := tr_le_K ψ _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G, ρ = σ * σ' * σ⁻¹ := ⟨_, rfl⟩
  have hρfix : ∀ y : G, σ' * (σ⁻¹ * y * σ) = σ⁻¹ * y * σ * σ' → ρ * y = y * ρ := by
    intro y hy
    calc ρ * y = σ * (σ' * (σ⁻¹ * y * σ)) * σ⁻¹ := by rw [hρ]; group
      _ = σ * (σ⁻¹ * y * σ * σ') * σ⁻¹ := by rw [hy]
      _ = y * ρ := by rw [hρ]; group
  have hρK₀ : ∀ y ∈ K₀, ρ * y = y * ρ := fun y hy =>
    hρfix y (hσ'fix _ (Or.inl (conj_inv_mem_of_map h0 hy)))
  have hρ5 : ∀ y ∈ tr ψ (Jn 5), ρ * y = y * ρ := fun y hy =>
    hρfix y (hσ'fix _ (Or.inr (Or.inr (Or.inr (Or.inl (conj_inv_mem_of_map h3 hy))))))
  have hρ6 : ∀ y ∈ tr ψ (Jn 6), ρ * y = y * ρ := fun y hy =>
    hρfix y (hσ'fix _ (Or.inr (Or.inl (conj_inv_mem_of_map h1 hy))))
  have hρ1 : ∀ y ∈ tr ψ (Jn 1), ρ * y = y * ρ := fun y hy =>
    hρfix y (hσ'fix _ (Or.inr (Or.inr (Or.inr (Or.inr (conj_inv_mem_of_map hlam hy))))))
  have hρ0 : (tr ψ (Jn 0)).map (MulAut.conj ρ).toMonoidHom = tr ψ (J mu) := by
    have hσinv : (tr ψ (Jn 0)).map (MulAut.conj σ⁻¹).toMonoidHom = K₀ := by
      rw [← h0', map_conj_inv_map_conj]
    rw [hρ, ← map_conj_map_conj, ← map_conj_map_conj, hσinv, hσ'K₀, h6]
  have hρC : ρ ∈ Subgroup.centralizer ({b₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hρK₀ b₀ hb₀)
  have hRbK : R ⊔ Subgroup.zpowers b₀ ≤ Subgroup.centralizer (K : Set G) :=
    sup_le hRK (Subgroup.zpowers_le.mpr (hK₀ hb₀))
  have hρmem : ρ ∈ (R ⊔ Subgroup.zpowers b₀) ⊔ K := by
    rw [sup_assoc]
    exact hCR ρ hρC hρ0
  obtain ⟨c, hc, a, ha, hca⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun c hc a ha => (Subgroup.mem_centralizer_iff.mp (hRbK hc) a ha).symm) hρmem
  have hcK : ∀ x ∈ K, c * x = x * c := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hRbK hc) x hx).symm
  have hρa : ∀ x ∈ K, ρ * x * ρ⁻¹ = a * x * a⁻¹ := by
    intro x hx
    have h := hcK _ (K.mul_mem (K.mul_mem ha hx) (K.inv_mem ha))
    rw [← hca]
    calc c * a * x * (c * a)⁻¹ = c * (a * x * a⁻¹) * c⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [h]; group
  have hcomm_a : ∀ y ∈ K, ρ * y = y * ρ → a * y = y * a := by
    intro y hy h
    have h' := hρa y hy
    rw [show ρ * y * ρ⁻¹ = y by rw [h]; group] at h'
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [← h']
  obtain ⟨t₀, ht₀, ht₀b⟩ : ∃ t₀ ∈ K₀, t₀ * b₀ * t₀⁻¹ = b₀⁻¹ := by
    have hy : σ * b₀ * σ⁻¹ ∈ tr ψ (Jn 0) := by
      rw [← h0']
      exact ⟨b₀, hb₀, rfl⟩
    obtain ⟨y, hyJ, hψy⟩ := mem_tr.mp hy
    have hy3 : orderOf (y : ModGL .E7 (ZMod 2)) = 3 := by
      rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψy,
        ← MulAut.conj_apply, MulEquiv.orderOf_eq, hb₀3]
    obtain ⟨t, htJ, ht⟩ := jn0_exists_inv hF hyJ hy3
    obtain ⟨t', rfl⟩ : ∃ t' : ↥L7, (t' : ModGL .E7 (ZMod 2)) = t := ⟨⟨t, hF.1 0 htJ⟩, rfl⟩
    have hty : t' * y * t'⁻¹ = y⁻¹ := Subtype.ext ht
    have hψt := congrArg (fun v : ↥L7 => ((ψ v : ↥K) : G)) hty
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψy] at hψt
    refine ⟨σ⁻¹ * ((ψ t' : ↥K) : G) * σ,
      conj_inv_mem_of_map h0' (mem_tr.mpr ⟨t', htJ, rfl⟩), ?_⟩
    calc σ⁻¹ * ((ψ t' : ↥K) : G) * σ * b₀ * (σ⁻¹ * ((ψ t' : ↥K) : G) * σ)⁻¹ =
        σ⁻¹ * (((ψ t' : ↥K) : G) * (σ * b₀ * σ⁻¹) * ((ψ t' : ↥K) : G)⁻¹) * σ := by group
      _ = σ⁻¹ * (σ * b₀ * σ⁻¹)⁻¹ * σ := by rw [hψt]
      _ = b₀⁻¹ := by group
  have hct : t₀ * c = c * t₀ := by
    have h1 : Commute ρ t₀ := hρK₀ t₀ ht₀
    have h2 : Commute a t₀ := Subgroup.mem_centralizer_iff.mp (hK₀ ht₀) a ha
    have h3 : c = ρ * a⁻¹ := by rw [← hca]; group
    rw [h3]
    exact (h1.mul_left h2.inv_left).eq.symm
  have hcR : c ∈ R := CFSG.GroupTheory.mem_of_mem_sup_zpowers hRb hR3 hb₀3 hc hct ht₀b
  have hcσ : ∀ x ∈ K, σ⁻¹ * c * σ * x = x * (σ⁻¹ * c * σ) := by
    intro x hx
    have h := Subgroup.mem_centralizer_iff.mp (hRσ hcR) (σ * x * σ⁻¹) ⟨x, hx, rfl⟩
    calc σ⁻¹ * c * σ * x = σ⁻¹ * (c * (σ * x * σ⁻¹)) * σ := by group
      _ = σ⁻¹ * (σ * x * σ⁻¹ * c) * σ := by rw [← h]
      _ = x * (σ⁻¹ * c * σ) := by group
  have haσ : ∀ x ∈ tr ψ (Jn 2), σ⁻¹ * a⁻¹ * σ * x = x * (σ⁻¹ * a⁻¹ * σ) := by
    intro x hx
    have he : σ⁻¹ * a⁻¹ * σ = σ'⁻¹ * (σ⁻¹ * c * σ) := by
      have h : a = c⁻¹ * ρ := by rw [← hca]; group
      rw [h, hρ]
      group
    rw [he]
    have h1 : Commute σ' x := hσ'fix x (Or.inr (Or.inr (Or.inl hx)))
    have h2 : Commute (σ⁻¹ * c * σ) x := hcσ x (hJ2K hx)
    exact (h1.inv_left.mul_left h2).eq
  obtain ⟨α, hα⟩ := exists_eq_psi ψ ha
  have hnat : ∀ {i : Fin 7}, (∀ y ∈ tr ψ (Jn i), ρ * y = y * ρ) → ∀ x ∈ Jn i,
      ((α⁻¹ : ↥L7) : ModGL .E7 (ZMod 2)) * x = x * ((α⁻¹ : ↥L7) : ModGL .E7 (ZMod 2)) := by
    intro i hi x hx
    have hxL : x ∈ L7 := hF.1 i hx
    have hy : ((ψ ⟨x, hxL⟩ : ↥K) : G) ∈ tr ψ (Jn i) := (coe_mem_tr_iff ψ _).mpr hx
    have h := hcomm_a _ (ψ ⟨x, hxL⟩).2 (hi _ hy)
    rw [← hα] at h
    have h' : (α : ModGL .E7 (ZMod 2)) * x = x * α := (psi_commute_iff ψ α ⟨x, hxL⟩).mp h
    rw [Subgroup.coe_inv]
    calc (α : ModGL .E7 (ZMod 2))⁻¹ * x =
        (α : ModGL .E7 (ZMod 2))⁻¹ * (x * α) * (α : ModGL .E7 (ZMod 2))⁻¹ := by group
      _ = (α : ModGL .E7 (ZMod 2))⁻¹ * (α * x) * (α : ModGL .E7 (ZMod 2))⁻¹ := by rw [h']
      _ = x * (α : ModGL .E7 (ZMod 2))⁻¹ := by group
  have hμL : J mu ≤ L7 := j_le_l7 isRoot_mu
  have hθL : J theta ≤ L7 := j_le_l7 isRoot_theta
  have hmu0 : (J mu).map (MulAut.conj ((α⁻¹ : ↥L7) : ModGL .E7 (ZMod 2))).toMonoidHom =
      Jn 0 := by
    have h1 : (tr ψ (Jn 0)).map (MulAut.conj a).toMonoidHom = tr ψ (J mu) := by
      rw [← hρ0]
      exact map_conj_congr fun x hx => (hρa x (tr_le_K ψ _ hx)).symm
    rw [← hα, tr_map_conj] at h1
    have hmapL : (Jn 0).map (MulAut.conj (α : ModGL .E7 (ZMod 2))).toMonoidHom ≤ L7 := by
      rintro _ ⟨x, hx, rfl⟩
      exact L7.mul_mem (L7.mul_mem α.2 (hF.1 0 hx)) (L7.inv_mem α.2)
    have h2 := tr_injective ψ hmapL hμL h1
    rw [Subgroup.coe_inv, ← h2, map_conj_inv_map_conj]
  have hle : ∀ {X : Subgroup (ModGL .E7 (ZMod 2))}, X ≤ L7 →
      (∀ y ∈ tr ψ X, ∀ x ∈ tr ψ (Jn 2), x * (σ⁻¹ * y * σ) = σ⁻¹ * y * σ * x) →
      X ≤ pull ψ ((Subgroup.centralizer (tr ψ (Jn 2) : Set G)).comap
        (MulAut.conj σ⁻¹).toMonoidHom) := by
    intro X hX h
    rw [le_pull_iff ψ hX]
    intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact h y hy x hx
  have hθ := hA5 _ (α⁻¹).2 (hnat hρ5) (hnat hρ6) (hnat hρ1) hmu0 _
    (hle (hF.1 0) fun y hy x hx =>
      Subgroup.mem_centralizer_iff.mp (hK₀ (conj_inv_mem_of_map h0' hy)) x (hJ2K hx))
    (hle hμL fun y hy x hx =>
      tr_commute ψ (hF.2.1 2 6 (by decide) (by decide) (by decide)) x hx _
        (conj_inv_mem_of_map h6 hy))
    (hle (hF.1 3) fun y hy x hx =>
      tr_commute ψ (hF.2.1 2 5 (by decide) (by decide) (by decide)) x hx _
        (conj_inv_mem_of_map h5 hy))
    ⟨α⁻¹, by
      show ((ψ α⁻¹ : ↥K) : G) ∈ (Subgroup.centralizer (tr ψ (Jn 2) : Set G)).comap
        (MulAut.conj σ⁻¹).toMonoidHom
      rw [map_inv ψ α, Subgroup.coe_inv, hα, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro x hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact (haσ x hx).symm, rfl⟩
  intro u hu w hw
  obtain ⟨y, hy, rfl⟩ := hu
  have hmem := (le_pull_iff ψ hθL _).mp hθ hy
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hmem
  exact (hmem w hw).symm

theorem hCR_of_conj_mem_zpowers {b₀ : G} (hF : E7NatFrame) (ψ : ↥L7 ≃* ↥K)
    (hKb : K ≤ Subgroup.centralizer ({b₀} : Set G)) {R : Subgroup G}
    (hμ : ∃ m ∈ L7, (J mu).map (MulAut.conj m).toMonoidHom = Jn 0) {z : G}
    (hz : z ∈ tr ψ (Jn 0)) (hz3 : orderOf z = 3)
    (hN : ∀ x ∈ Subgroup.centralizer ({b₀} : Set G), x * z * x⁻¹ ∈ Subgroup.zpowers z →
      x ∈ R ⊔ (Subgroup.zpowers b₀ ⊔ K)) :
    ∀ x ∈ Subgroup.centralizer ({b₀} : Set G),
      (tr ψ (Jn 0)).map (MulAut.conj x).toMonoidHom = tr ψ (J mu) →
        x ∈ R ⊔ (Subgroup.zpowers b₀ ⊔ K) := by
  intro x hx hxμ
  obtain ⟨m, hmL, hm⟩ := hμ
  have hjK : ((ψ ⟨m, hmL⟩ : ↥K) : G) ∈ K := (ψ ⟨m, hmL⟩).2
  have hjx : (tr ψ (Jn 0)).map (MulAut.conj (((ψ ⟨m, hmL⟩ : ↥K) : G) * x)).toMonoidHom =
      tr ψ (Jn 0) := by
    rw [← map_conj_map_conj, hxμ, tr_map_conj]
    exact congrArg (tr ψ) hm
  have hw : (((ψ ⟨m, hmL⟩ : ↥K) : G) * x) * z * (((ψ ⟨m, hmL⟩ : ↥K) : G) * x)⁻¹ ∈
      tr ψ (Jn 0) := by
    rw [← hjx]
    exact ⟨z, hz, rfl⟩
  obtain ⟨w, hwJ, hψw⟩ := mem_tr.mp hw
  obtain ⟨z', hz'J, hψz⟩ := mem_tr.mp hz
  have hz'3 : orderOf (z' : ModGL .E7 (ZMod 2)) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψz, hz3]
  have hw3 : (w : ModGL .E7 (ZMod 2)) ^ 3 = 1 := by
    have h1 : ((ψ (w ^ 3) : ↥K) : G) = 1 := by
      rw [map_pow, Subgroup.coe_pow, hψw, conj_pow, ← hz3, pow_orderOf_eq_one, mul_one,
        mul_inv_cancel]
    have h2 : w ^ 3 = 1 := ψ.injective (Subtype.ext (by rw [h1, map_one, Subgroup.coe_one]))
    rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (jn0_mem_zpowers hF hz'J hz'3 hwJ hw3)
  have hk' : z' ^ k = w := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
  have hconj : (((ψ ⟨m, hmL⟩ : ↥K) : G) * x) * z * (((ψ ⟨m, hmL⟩ : ↥K) : G) * x)⁻¹ ∈
      Subgroup.zpowers z := by
    rw [← hψw, ← hk', map_zpow, Subgroup.coe_zpow, hψz]
    exact Subgroup.zpow_mem_zpowers z k
  have h := hN _ (mul_mem (hKb hjK) hx) hconj
  rw [show x = ((ψ ⟨m, hmL⟩ : ↥K) : G)⁻¹ * (((ψ ⟨m, hmL⟩ : ↥K) : G) * x) by group]
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right (inv_mem hjK))) h

end Seven

end CFSG.StandardType.FrameRoute.FS81.E7Frame
