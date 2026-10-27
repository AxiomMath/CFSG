module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81E5Gen
public import CFSG.RankThree.GF2n.Smith81.S81E7Conj
public import CFSG.RankThree.GF2n.Smith81.S81E7Form
public import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas
public import CFSG.RankThree.GF2n.Smith81.S81CS8
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model

@[expose] def E5RootEltStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE5 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
            EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K) →
              ∀ z ∈ Z, z ≠ 1 → ∀ t : G, IsConj z t → t ∈ M → t ∉ Q →
                ∃ s : Lgen M (LB M Q B), (s : G) * t⁻¹ ∈ Q ∧ IsRootElt ((vAut K).symm (φ s))

@[expose] def Smith24E5FormStatement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE5 M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∀ (ψ : M₀.E ≃ₗ[K] V K) (φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)),
            EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K) →
              ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * beta (ψ e) (ψ f)

end CFSG.RankThree.GF2n.Smith81

namespace CFSG.RankThree.GF2n.Smith81.E5Tr

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.GF2n.Smith81.E7Model

section Transport

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {V : Type} [AddCommGroup V] [Module K V]

@[expose] def tr (ψ : M₀.E ≃ₗ[K] V) : (M₀.E ≃ₗ[K] M₀.E) →* (V ≃ₗ[K] V) where
  toFun T := ψ.symm.trans (T.trans ψ)
  map_one' := by
    ext x
    simp
  map_mul' T₁ T₂ := by
    ext x
    simp

theorem tr_apply (ψ : M₀.E ≃ₗ[K] V) (T : M₀.E ≃ₗ[K] M₀.E) (e : M₀.E) :
    tr ψ T (ψ e) = ψ (T e) := by
  simp [tr]

theorem tr_eq_one_iff (ψ : M₀.E ≃ₗ[K] V) (T : M₀.E ≃ₗ[K] M₀.E) : tr ψ T = 1 ↔ T = 1 := by
  constructor
  · intro h
    ext e
    have := congrArg (fun S : V ≃ₗ[K] V => S (ψ e)) h
    simp only [tr_apply] at this
    exact ψ.injective this
  · rintro rfl
    exact map_one _

theorem exists_psi_pi (ψ : M₀.E ≃ₗ[K] V) (ξ : V) : ∃ x ∈ Q, ψ (M₀.π x) = ξ := by
  obtain ⟨x, hx, hxe⟩ := M₀.π_surj (ψ.symm ξ)
  exact ⟨x, hx, by rw [hxe]; simp⟩

theorem eq_of_psi_pi {ψ : M₀.E ≃ₗ[K] V} {A B : V ≃ₗ[K] V}
    (h : ∀ x ∈ Q, A (ψ (M₀.π x)) = B (ψ (M₀.π x))) : A = B := by
  ext ξ
  obtain ⟨x, hx, rfl⟩ := exists_psi_pi (M₀ := M₀) ψ ξ
  exact h x hx

end Transport

section Act

variable
  {G : Type} [Group G] {M Q Z B : Subgroup G} {K : Type} [Field K] {γ : G → K}

structure E5Act (hL : Lgen M (LB M Q B) ≤ H0 M Z) (M₀ : Tim79.QuadModel Q Z K γ)
    (ψ : M₀.E ≃ₗ[K] V K) (Θ : ↥(H0 M Z) →* (Module.End K (V K))ˣ) : Prop where
  equivariant : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
    (Θ m : Module.End K (V K)) (ψ (M₀.π x)) = ψ (M₀.π ((m : G) * x * (m : G)⁻¹))
  ker : ∀ m : ↥(H0 M Z), Θ m = 1 ↔ (m : G) ∈ Q
  range : (Θ.comp (Subgroup.inclusion hL)).range = EGrp K

variable {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_E5Act [Finite G] [Finite K] (Hs : StrothHyp M Q Z)
    (hL : Lgen M (LB M Q B) ≤ H0 M Z) (hg : GlobalModelData M Q Z γ M₀) {ψ : M₀.E ≃ₗ[K] V K}
    {φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)}
    (d : EUniData M Q Z B M₀ ψ φ (EAut K) (w0 : V K) (rootRad7 K)) :
    ∃ Θ : ↥(H0 M Z) →* (Module.End K (V K))ˣ, E5Act hL M₀ ψ Θ ∧
      ∀ s : Lgen M (LB M Q B), vAut K (Θ (Subgroup.inclusion hL s)) = φ s := by
  obtain ⟨θ, hθπ, hθker, -⟩ := exists_actionHom_H0 Hs hg
  let Θ : ↥(H0 M Z) →* (Module.End K (V K))ˣ :=
    ((vAut K).symm : (V K ≃ₗ[K] V K) ≃* _).toMonoidHom.comp ((tr ψ).comp θ)
  have hvΘ : ∀ m, vAut K (Θ m) = tr ψ (θ m) := fun m => by
    simp [Θ]
  have hrel : ∀ s : Lgen M (LB M Q B), vAut K (Θ (Subgroup.inclusion hL s)) = φ s := by
    intro s
    rw [hvΘ]
    refine eq_of_psi_pi (M₀ := M₀) (ψ := ψ) fun x hx => ?_
    rw [tr_apply, ← d.equivariant s x hx, ← hθπ _ x hx]
    rfl
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, hrel⟩
  · intro m x hx
    show vAut K (Θ m) (ψ (M₀.π x)) = _
    rw [hvΘ, tr_apply, ← hθπ m x hx]
  · intro m
    rw [← hθker m, ← tr_eq_one_iff ψ, ← hvΘ m]
    exact (map_eq_one_iff _ (vAut K).injective).symm
  · ext g
    constructor
    · rintro ⟨s, rfl⟩
      have h1 : φ s ∈ EAut K := by rw [← d.range]; exact ⟨s, rfl⟩
      have h2 := mem_EAut_iff.mp h1
      rw [← hrel s] at h2
      simpa using h2
    · intro hg'
      have h1 : vAut K g ∈ φ.range := by
        rw [d.range]
        exact Subgroup.mem_map.mpr ⟨g, hg', rfl⟩
      obtain ⟨s, hs⟩ := h1
      refine ⟨s, ?_⟩
      apply (vAut K).injective
      show vAut K (Θ (Subgroup.inclusion hL s)) = vAut K g
      rw [hrel s, hs]

variable {hL : Lgen M (LB M Q B) ≤ H0 M Z} {ψ : M₀.E ≃ₗ[K] V K}
  {Θ : ↥(H0 M Z) →* (Module.End K (V K))ˣ}

theorem E5Act.changeFrame (h : E5Act hL M₀ ψ Θ) {a : (Module.End K (V K))ˣ} (ha : a ∈ EGrp K) :
    E5Act hL M₀ (ψ.trans (vAut K a)) ((MulAut.conj a).toMonoidHom.comp Θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m x hx
    have hinv : ((a⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
        ((a : Module.End K (V K)) (ψ (M₀.π x))) = ψ (M₀.π x) := by
      have h1 := LinearMap.congr_fun (Units.inv_mul a) (ψ (M₀.π x))
      simp only [Module.End.mul_apply, Module.End.one_apply] at h1
      exact h1
    have e1 := h.equivariant m x hx
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      LinearEquiv.trans_apply, Units.val_mul, Module.End.mul_apply, vAut_apply]
    rw [hinv, e1]
  · intro m
    show MulAut.conj a (Θ m) = 1 ↔ _
    rw [map_eq_one_iff _ (MulAut.conj a).injective]
    exact h.ker m
  · ext g
    constructor
    · rintro ⟨s, rfl⟩
      have hs : Θ (Subgroup.inclusion hL s) ∈ EGrp K := by
        rw [← h.range]
        exact ⟨s, rfl⟩
      exact mul_mem (mul_mem ha hs) (inv_mem ha)
    · intro hg'
      have h1 : a⁻¹ * g * a ∈ EGrp K := mul_mem (mul_mem (inv_mem ha) hg') ha
      rw [← h.range] at h1
      obtain ⟨s, hs⟩ := h1
      refine ⟨s, ?_⟩
      show a * Θ (Subgroup.inclusion hL s) * a⁻¹ = g
      have hs' : Θ (Subgroup.inclusion hL s) = a⁻¹ * g * a := hs
      rw [hs']
      group

theorem E5Act.eq_of_mul_inv_mem (h : E5Act hL M₀ ψ Θ) {s : Lgen M (LB M Q B)} {t : G}
    (ht : t ∈ H0 M Z) (hst : (s : G) * t⁻¹ ∈ Q) : Θ (Subgroup.inclusion hL s) = Θ ⟨t, ht⟩ := by
  have h1 : Θ (Subgroup.inclusion hL s * (⟨t, ht⟩ : ↥(H0 M Z))⁻¹) = 1 := (h.ker _).mpr hst
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem E5Act.isRootElt (h : E5Act hL M₀ ψ Θ) {φ : Lgen M (LB M Q B) →* (V K ≃ₗ[K] V K)}
    (hrel : ∀ s : Lgen M (LB M Q B), vAut K (Θ (Subgroup.inclusion hL s)) = φ s) {t : G}
    (ht : t ∈ H0 M Z)
    (hF : ∃ s : Lgen M (LB M Q B), (s : G) * t⁻¹ ∈ Q ∧ IsRootElt ((vAut K).symm (φ s))) :
    IsRootElt (Θ ⟨t, ht⟩) := by
  obtain ⟨s, hsQ, hs⟩ := hF
  have e1 : Θ (Subgroup.inclusion hL s) = (vAut K).symm (φ s) := by
    rw [← hrel s]
    simp
  rw [← h.eq_of_mul_inv_mem ht hsQ, e1]
  exact hs

theorem orderOf_conj_mul_inv {H : Type*} [Group H] (a x : H) : orderOf (a * x * a⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective x
  have e : (MulAut.conj a).toMonoidHom x = a * x * a⁻¹ := by
    simp [MulAut.conj_apply]
  rw [e] at h
  exact h

theorem orderOf_image_eq [Finite G] (Hs : StrothHyp M Q Z) {A : Type*}
    [Group A] (Θ : ↥(H0 M Z) →* A) (hΘ : ∀ m : ↥(H0 M Z), Θ m = 1 ↔ (m : G) ∈ Q) {v : G}
    (hvH : v ∈ H0 M Z) (hv : Odd (orderOf v)) : orderOf (Θ ⟨v, hvH⟩) = orderOf v := by
  apply Nat.dvd_antisymm
  · have h1 : orderOf (Θ ⟨v, hvH⟩) ∣ orderOf (⟨v, hvH⟩ : ↥(H0 M Z)) := orderOf_map_dvd Θ _
    rwa [Subgroup.orderOf_mk] at h1
  · set k := orderOf (Θ ⟨v, hvH⟩) with hk
    have h1 : Θ ((⟨v, hvH⟩ : ↥(H0 M Z)) ^ k) = 1 := by
      rw [map_pow]
      exact pow_orderOf_eq_one _
    have hvk : v ^ k ∈ Q := by
      have := (hΘ _).mp h1
      simpa using this
    have h2 : v ^ k = 1 :=
      eq_one_of_mem_of_orderOf_dvd_odd (isPGroup_Q' Hs) hvk hv (orderOf_pow_dvd k)
    exact orderOf_dvd_of_pow_eq_one h2

theorem E5Act.exists_vform [Finite G] [CharP K 2]
    (h : E5Act hL M₀ ψ Θ) (Hs : StrothHyp M Q Z) {x y v : G} (hx : x ∈ H0 M Z) (hy : y ∈ H0 M Z)
    (hvH : v ∈ H0 M Z) (hv : v = x * y) (hrx : IsRootElt (Θ ⟨x, hx⟩)) (hry : IsRootElt (Θ ⟨y, hy⟩))
    (hodd : Odd (orderOf v)) (hv1 : v ≠ 1) :
    ∃ a ∈ EGrp K, ∃ s t : K, s ≠ 0 ∧ t ≠ 0 ∧
      a * Θ ⟨v, hvH⟩ * a⁻¹ = jHom (MinData.Valid.slLower K s * MinData.Valid.slUpper K t) := by
  have hΘv : Θ ⟨v, hvH⟩ = Θ ⟨x, hx⟩ * Θ ⟨y, hy⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hv
  have hord := orderOf_image_eq Hs Θ h.ker hvH hodd
  have hne : Θ ⟨v, hvH⟩ ≠ 1 := by
    intro h1
    exact hv1 (eq_one_of_mem_of_orderOf_dvd_odd (isPGroup_Q' Hs) ((h.ker _).mp h1) hodd dvd_rfl)
  obtain ⟨a, ha, s, t, hs, ht, hax, hay⟩ := fe3_conj hrx hry
    (by rw [← hΘv, hord]; exact hodd) (by rw [← hΘv]; exact hne)
  refine ⟨a, ha, s, t, hs, ht, ?_⟩
  rw [hΘv]
  calc a * (Θ ⟨x, hx⟩ * Θ ⟨y, hy⟩) * a⁻¹
      = (a * Θ ⟨x, hx⟩ * a⁻¹) * (a * Θ ⟨y, hy⟩ * a⁻¹) := by group
    _ = e7Data_valid.xu K theta s * e7Data_valid.xu K (-theta) t := by rw [hax, hay]
    _ = jHom (MinData.Valid.slLower K s * MinData.Valid.slUpper K t) := by
        rw [map_mul, ← xu_theta, ← xu_neg_theta]

structure VFrame (Θ : ↥(H0 M Z) →* (Module.End K (V K))ˣ) (v : G) (hvH : v ∈ H0 M Z) : Prop where
  mem : Θ ⟨v, hvH⟩ ∈ Jgrp K
  ne : Θ ⟨v, hvH⟩ ≠ 1
  odd : Odd (orderOf (Θ ⟨v, hvH⟩))

theorem E5Act.exists_vframe [Finite G] [CharP K 2]
    (h : E5Act hL M₀ ψ Θ) (Hs : StrothHyp M Q Z) {x y v : G} (hx : x ∈ H0 M Z) (hy : y ∈ H0 M Z)
    (hvH : v ∈ H0 M Z) (hv : v = x * y) (hrx : IsRootElt (Θ ⟨x, hx⟩)) (hry : IsRootElt (Θ ⟨y, hy⟩))
    (hodd : Odd (orderOf v)) (hv1 : v ≠ 1) :
    ∃ a ∈ EGrp K, VFrame ((MulAut.conj a).toMonoidHom.comp Θ) v hvH := by
  obtain ⟨a, ha, s, t, hs, ht, hform⟩ := h.exists_vform Hs hx hy hvH hv hrx hry hodd hv1
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · show a * Θ ⟨v, hvH⟩ * a⁻¹ ∈ Jgrp K
    rw [hform, Jgrp_eq_range]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · show a * Θ ⟨v, hvH⟩ * a⁻¹ ≠ 1
    intro h1
    have h2 : Θ ⟨v, hvH⟩ = 1 := by
      have : a * Θ ⟨v, hvH⟩ * a⁻¹ = 1 := h1
      rw [mul_inv_eq_one] at this
      exact mul_eq_left.mp this
    exact hv1 (eq_one_of_mem_of_orderOf_dvd_odd (isPGroup_Q' Hs) ((h.ker _).mp h2) hodd dvd_rfl)
  · show Odd (orderOf (a * Θ ⟨v, hvH⟩ * a⁻¹))
    rw [orderOf_conj_mul_inv, orderOf_image_eq Hs Θ h.ker hvH hodd]
    exact hodd

theorem E5Act.mem_Cv_iff [Finite G] [CharP K 2] (h : E5Act hL M₀ ψ Θ)
    (Hs : StrothHyp M Q Z) {v : G} (hvH : v ∈ H0 M Z) (hv : Odd (orderOf v))
    (hj : Θ ⟨v, hvH⟩ ∈ Jgrp K) (hj1 : Θ ⟨v, hvH⟩ ≠ 1) (hjo : Odd (orderOf (Θ ⟨v, hvH⟩))) {x : G}
    (hx : x ∈ Q) : v * x = x * v ↔ ψ (M₀.π x) ∈ V0 K := by
  have hfix := fixed_eq_V0 hj hj1 hjo
  have hE := h.equivariant ⟨v, hvH⟩ x hx
  constructor
  · intro hc
    have e : v * x * v⁻¹ = x := by rw [hc]; group
    have : ψ (M₀.π x) ∈ {w : V K | ((Θ ⟨v, hvH⟩ : (Module.End K (V K))ˣ) : Module.End K (V K)) w = w} := by
      show _ = _
      rw [hE]
      show ψ (M₀.π (v * x * v⁻¹)) = _
      rw [e]
    rw [hfix] at this
    exact this
  · intro hV
    have hmem : ψ (M₀.π x) ∈ {w : V K | ((Θ ⟨v, hvH⟩ : (Module.End K (V K))ˣ) : Module.End K (V K)) w = w} := by
      rw [hfix]
      exact hV
    have h1 : ψ (M₀.π (v * x * v⁻¹)) = ψ (M₀.π x) := by
      have := hE
      rw [← this]
      exact hmem
    have h2 : M₀.π (v * x * v⁻¹) = M₀.π x := ψ.injective h1
    exact mem_Cv_of_pi_fixed Hs M₀ hvH.1 hv
      (fun w hw => (Subgroup.mem_centralizer_iff.mp hvH.2 w hw).symm) hx h2

end Act

section World

variable
  {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {z v : G}

theorem E3L45World.factors (hW : E3L45World M Q Z B z v) :
    ∃ x y : G, IsConj z x ∧ IsConj z y ∧ x ∈ H0 M Z ∧ y ∈ H0 M Z ∧ x ∉ Q ∧ y ∉ Q ∧ v = x * y := by
  have Hs : StrothHyp M Q Z := hW.hStroth
  have hQ2 : IsPGroup 2 Q := isPGroup_Q' Hs
  obtain ⟨⟨x₀, y₀, hx₀, hy₀, hx₀z, hy₀z, hv⟩, hv_odd, hv1⟩ := hW.hv
  have hv1' : orderOf v ≠ 1 := by omega
  have hvM : v ∈ M := hW.v_mem_H0.1
  have hvN : v ∈ Subgroup.normalizer (Q : Set G) := Hs.Q_normal.2 hvM
  have hx₀H : x₀ ∈ H0 M Z := mem_H0_of_isConj_commute Hs hW.hz hW.hz1 hx₀ hx₀z
  have hy₀H : y₀ ∈ H0 M Z := mem_H0_of_isConj_commute Hs hW.hz hW.hz1 hy₀ hy₀z
  have hx₀2 : x₀ * x₀ = 1 := mul_self_eq_one_of_isConj_Z Hs hW.hz hx₀
  have hy₀2 : y₀ * y₀ = 1 := mul_self_eq_one_of_isConj_Z Hs hW.hz hy₀
  have hx₀inv : x₀ * v * x₀ = v⁻¹ := by
    rw [hv]
    calc x₀ * (x₀ * y₀) * x₀ = (x₀ * x₀) * y₀ * x₀ := by group
      _ = y₀ * x₀ := by rw [hx₀2, one_mul]
      _ = (x₀ * y₀)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hy₀2, inv_eq_of_mul_eq_one_right hx₀2]
  have hy₀inv : y₀ * v * y₀ = v⁻¹ := by
    rw [hv]
    calc y₀ * (x₀ * y₀) * y₀ = y₀ * x₀ * (y₀ * y₀) := by group
      _ = y₀ * x₀ := by rw [hy₀2, mul_one]
      _ = (x₀ * y₀)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hy₀2, inv_eq_of_mul_eq_one_right hx₀2]
  exact ⟨x₀, y₀, hx₀, hy₀, hx₀H, hy₀H,
    not_mem_of_inv_odd_normalizer hQ2 hvN hv_odd hv1' hx₀2 hx₀inv,
    not_mem_of_inv_odd_normalizer hQ2 hvN hv_odd hv1' hy₀2 hy₀inv, hv⟩

end World

end CFSG.RankThree.GF2n.Smith81.E5Tr
