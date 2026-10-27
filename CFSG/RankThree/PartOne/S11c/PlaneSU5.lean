module

public import CFSG.RankThree.PartOne.S11c.SuFive

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)

section Abstract

theorem cyclic_quotient_false {A U T : Type} [Group A] [Finite A] [Group U] [Group T] [IsCyclic T]
    (hcomm : ∀ a b : A, a * b = b * a) (c : A) (hA5 : ∀ a : A, a ^ 5 = 1)
    (hAcard : Nat.card A = 5 ^ 3) (R : Subgroup (A × U)) (hR : ∀ a : A, ∃ u : U, (a, u) ∈ R)
    (d : R →* T) (hd : ∀ r : R, d r = 1 → r.1.1 ∈ Subgroup.zpowers c) : False := by
  classical
  have hC : (Subgroup.zpowers c).Normal :=
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by rw [hcomm g n, mul_inv_cancel_right]
      rw [this]
      exact hn⟩
  let Φ : R →* A ⧸ Subgroup.zpowers c :=
    (QuotientGroup.mk' (Subgroup.zpowers c)).comp ((MonoidHom.fst A U).comp R.subtype)
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := hR a
    exact ⟨⟨(a, u), hu⟩, rfl⟩
  have hker : d.ker ≤ Φ.ker := by
    intro r hr
    rw [MonoidHom.mem_ker] at hr ⊢
    show (QuotientGroup.mk r.1.1 : A ⧸ Subgroup.zpowers c) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hd r hr
  let Ψ : (R ⧸ d.ker) →* A ⧸ Subgroup.zpowers c := QuotientGroup.lift d.ker Φ hker
  have hΨ : Function.Surjective Ψ := by
    intro q
    obtain ⟨r, rfl⟩ := hΦ q
    exact ⟨QuotientGroup.mk r, rfl⟩
  have hcyc : IsCyclic (R ⧸ d.ker) := by
    have : IsCyclic d.range := inferInstance
    exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange d).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivRange d).symm.surjective
  have hQcyc : IsCyclic (A ⧸ Subgroup.zpowers c) := isCyclic_of_surjective Ψ hΨ
  have hexp : Monoid.exponent (A ⧸ Subgroup.zpowers c) ∣ 5 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hA5, QuotientGroup.mk_one]
  have hc5 : Nat.card (Subgroup.zpowers c) ≤ 5 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA5 c))
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers c)
  have hQ25 : 25 ≤ Nat.card (A ⧸ Subgroup.zpowers c) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card A < 125 := by
      rw [hmul]
      calc Nat.card (A ⧸ Subgroup.zpowers c) * Nat.card (Subgroup.zpowers c)
          ≤ 24 * 5 := Nat.mul_le_mul (by omega) hc5
        _ < 125 := by norm_num
    omega
  have hexpcard := IsCyclic.exponent_eq_card (α := A ⧸ Subgroup.zpowers c)
  have := Nat.le_of_dvd (by norm_num) (hexpcard ▸ hexp)
  omega

end Abstract

section Frame

open scoped Pointwise

theorem four_le_localRank_of_frame {H : Type} [Group H] [Finite H] {L : Subgroup H} {Γ : Type}
    [Group Γ] (ψ : Γ ≃* L) {A : Subgroup Γ} (hA : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 3) {r : Γ} (hr : orderOf r = 2) (hrA : ∀ a ∈ A, a * r = r * a)
    {y : H} (hy5 : y ^ 5 = 1) (hyL : y ∉ L)
    (hyA : ∀ a ∈ A, y * ((ψ a : L) : H) = ((ψ a : L) : H) * y)
    (hyr : y * ((ψ r : L) : H) = ((ψ r : L) : H) * y) : 4 ≤ localRank 5 H := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set φ : Γ →* H := L.subtype.comp ψ.toMonoidHom with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp ψ.injective
  set AL : Subgroup H := A.map φ with hAL
  set S : Subgroup H := Subgroup.zpowers (φ r) with hS
  have hALel : IsElementaryAbelian 5 AL := IsElementaryAbelian.map φ
  have hALcard : Nat.card AL = 5 ^ 3 := by
    rw [hAL, Subgroup.card_map_of_injective hφinj]
    exact hAcard
  have hALL : AL ≤ L := by
    rintro _ ⟨a, -, rfl⟩
    exact (ψ a).2
  have hord : orderOf (φ r) = 2 := by
    rw [orderOf_injective φ hφinj r]
    exact hr
  have hScard : Nat.card S = 2 := by
    rw [hS, Nat.card_zpowers, hord]
  have hSne : S ≠ ⊥ := by
    intro hbot
    have := Subgroup.card_bot (G := H)
    rw [← hbot, hScard] at this
    omega
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 1) (by rw [hScard]; norm_num)
  have hloc : IsTwoLocal (Subgroup.normalizer (S : Set H)) := ⟨S, hSne, hS2, rfl⟩
  have hy1 : y ≠ 1 := fun h1 => hyL (h1 ▸ L.one_mem)
  have hyord : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  set Y : Subgroup H := Subgroup.zpowers y with hY
  have hYcard : Nat.card Y = 5 ^ 1 := by
    rw [hY, Nat.card_zpowers, hyord, pow_one]
  have hYel : IsElementaryAbelian 5 Y := IsElementaryAbelian.zpowers_of_pow_eq_one hy5
  have hnorm : ∀ v : H, Commute (φ r) v → v ∈ Subgroup.normalizer (S : Set H) := by
    intro v hv
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [hS, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hv.zpow_left k).eq
  have hALN : AL ≤ Subgroup.normalizer (S : Set H) := by
    rintro _ ⟨a, ha, rfl⟩
    refine hnorm _ ?_
    have := congrArg φ (hrA a ha)
    rw [map_mul, map_mul] at this
    exact this.symm
  have hYN : Y ≤ Subgroup.normalizer (S : Set H) :=
    Subgroup.zpowers_le.mpr (hnorm y hyr.symm)
  have hcomm : ∀ x ∈ AL, ∀ z ∈ Y, Commute x z := by
    rintro _ ⟨a, ha, rfl⟩ z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (show Commute (φ a) y from (hyA a ha).symm).zpow_right k
  have hinf : AL ⊓ Y = ⊥ := by
    have hL : L ⊓ Y = ⊥ := Sec12Two.inf_zpowers_eq_bot Nat.prime_five hy5 hyL
    rw [eq_bot_iff, ← hL]
    exact inf_le_inf_right Y hALL
  have h1 := Sec12Two.le_pRank_of_commute_of_inf_eq_bot (p := 5) Nat.prime_five
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 _).mp hALel)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 5 _).mp hYel) hcomm hinf hALcard
    hYcard hALN hYN
  exact (show 3 + 1 ≤ _ from h1).trans (Sec12Two.pRank_le_localRank_of_isTwoLocal Nat.prime_five
    hloc)

end Frame

section Contradiction

variable {f : ℕ} {K : Type} [Field K]

theorem frame_contradiction_loc {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L) {x : H}
    (hx5 : x ^ 5 = 1) (hxL : x ∉ L) (θ : gamma5 h ≃* gamma5 h)
    (hθ : ∀ g, ((ψ (θ g) : L) : H) = x * ((ψ g : L) : H) * x⁻¹) (P : unit5 h) {i j : Fin 5}
    (hij : i ≠ j) (hA : ∀ a ∈ frameA h P i j, θ a = a) (hr : θ (frameR h P i j) = frameR h P i j) :
    4 ≤ localRank 5 H := by
  have hcomm : ∀ g : gamma5 h, θ g = g → x * ((ψ g : L) : H) = ((ψ g : L) : H) * x := by
    intro g hg
    have := hθ g
    rw [hg] at this
    calc x * ((ψ g : L) : H) = x * ((ψ g : L) : H) * x⁻¹ * x := by group
      _ = ((ψ g : L) : H) * x := by rw [← this]
  exact four_le_localRank_of_frame ψ (isElementaryAbelian_frameA h h5 P i j)
    (card_frameA h h5 P hij) (orderOf_frameR h P hij) (fun a ha => frameR_comm h P ha) hx5 hxL
    (fun a ha => hcomm a (hA a ha)) (hcomm _ hr)

theorem su5_fcase_loc {H : Type} [Group H] [Finite H] {L : Subgroup H} (h : UnitaryFieldData 2 f K)
    (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L) {x : H} (hx5 : x ^ 5 = 1) (hxL : x ∉ L)
    (hxN : x ∈ Subgroup.normalizer (L : Set H)) (φ : K ≃+* K) (M : unit5 h) (hφ5 : φ ^ 5 = 1)
    (hconj : ∀ g : gamma5 h, ((inducedAut ψ x hxN g : gamma5 h) : GL (Fin 5) K) =
      (M : GL (Fin 5) K) * glAut φ ((M : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) *
        (M : GL (Fin 5) K)) * (M : GL (Fin 5) K)⁻¹) : 4 ≤ localRank 5 H := by
  refine frame_contradiction_loc h h5 ψ hx5 hxL (inducedAut ψ x hxN) (coe_inducedAut ψ x hxN) M
    (i := 0) (j := 1) (by decide) ?_ ?_
  · intro a ha
    obtain ⟨t, ht, hat⟩ := exists_of_mem_frameA ha
    apply Subtype.ext
    rw [hconj, hat]
    have h1 : (M : GL (Fin 5) K)⁻¹ * ((M : GL (Fin 5) K) * t * (M : GL (Fin 5) K)⁻¹) *
        (M : GL (Fin 5) K) = t := by group
    have hφt : glAut φ t = t := Units.ext (Matrix.ext fun r s => by
      rw [coe_glAut]
      exact apply_eq_of_mem_torusEq φ hφ5 ht r s)
    rw [h1, hφt]
  · apply Subtype.ext
    rw [hconj, coe_frameR]
    have h1 : (M : GL (Fin 5) K)⁻¹ * ((M : GL (Fin 5) K) * KFSU5.swapUnit K (0 : Fin 5) 1 *
        (M : GL (Fin 5) K)⁻¹) * (M : GL (Fin 5) K) = KFSU5.swapUnit K (0 : Fin 5) 1 := by group
    have hφs : glAut φ (KFSU5.swapUnit K (0 : Fin 5) 1) = KFSU5.swapUnit K (0 : Fin 5) 1 :=
      Units.ext (by
        rw [coe_glAut, KFSU5.swapUnit_val]
        exact KFSU5.swapMatrix_map φ.toRingHom (0 : Fin 5) 1)
    rw [h1, hφs]

end Contradiction

section Diag

variable {f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def conjHom5 (h : UnitaryFieldData 2 f K) :
    unit5 h →* (gamma5 h ≃* gamma5 h) where
  toFun P := primeFormConjSU h _ P
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    show ((1 : unit5 h) : GL (Fin 5) K) * (g : GL (Fin 5) K) * ((1 : unit5 h) : GL (Fin 5) K)⁻¹ = g
    simp)
  map_mul' P Q := MulEquiv.ext fun g => Subtype.ext (by
    show ((P * Q : unit5 h) : GL (Fin 5) K) * (g : GL (Fin 5) K) *
        ((P * Q : unit5 h) : GL (Fin 5) K)⁻¹ =
      (P : GL (Fin 5) K) * ((Q : GL (Fin 5) K) * (g : GL (Fin 5) K) * (Q : GL (Fin 5) K)⁻¹) *
        (P : GL (Fin 5) K)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem coe_conjHom5 (h : UnitaryFieldData 2 f K) (P : unit5 h) (g : gamma5 h) :
    ((conjHom5 h P g : gamma5 h) : GL (Fin 5) K) =
      (P : GL (Fin 5) K) * (g : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹ := rfl

@[expose] noncomputable def inducedAutHom {H : Type} [Group H] {L : Subgroup H} {Γ : Type}
    [Group Γ] (ψ : Γ ≃* L) : Subgroup.normalizer (L : Set H) →* (Γ ≃* Γ) :=
  (MulAut.congr ψ.symm).toMonoidHom.comp L.normalizerMonoidHom

theorem inducedAutHom_apply {H : Type} [Group H] {L : Subgroup H} {Γ : Type} [Group Γ]
    (ψ : Γ ≃* L) (x : H) (hx : x ∈ Subgroup.normalizer (L : Set H)) :
    inducedAutHom ψ ⟨x, hx⟩ = inducedAut ψ x hx := rfl

theorem det_scalar5 (κ : Kˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 5) κ) = κ ^ 5 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, det_diagonal]
  simp

end Diag

section DiagPlane

variable {f : ℕ} {K : Type} [Field K]

theorem su5_diag_plane_false {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L) {A : Subgroup H} {c : H}
    (hAN : A ≤ Subgroup.normalizer (L : Set H)) (hAe : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 3) (hcA : c ∈ A)
    (hmain : ∀ x ∈ A, x ∈ L ⊔ Subgroup.centralizer (L : Set H) → x ∈ Subgroup.zpowers c)
    (hdiag : ∀ (x : H) (hx : x ∈ A), ∃ P : unit5 h, ∀ g : gamma5 h,
      ((inducedAut ψ x (hAN hx) g : gamma5 h) : GL (Fin 5) K) =
        (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹) : False := by
  classical
  have hfin : Finite K := h.finite
  let θA : ↥A →* (gamma5 h ≃* gamma5 h) := (inducedAutHom ψ).comp (Subgroup.inclusion hAN)
  let R : Subgroup (↥A × unit5 h) :=
    MonoidHom.eqLocus (θA.comp (MonoidHom.fst _ _)) ((conjHom5 h).comp (MonoidHom.snd _ _))
  let F : Subgroup Kˣ := (powMonoidHom 5 : Kˣ →* Kˣ).range
  let d : R →* Kˣ ⧸ F :=
    (QuotientGroup.mk' F).comp ((Matrix.GeneralLinearGroup.det).comp
      ((unit5 h).subtype.comp ((MonoidHom.snd _ _).comp R.subtype)))
  refine cyclic_quotient_false (A := ↥A) (U := unit5 h) (T := Kˣ ⧸ F)
    (fun a b => (IsMulCommutative.is_comm (M := ↥A)).comm a b) ⟨c, hcA⟩
    (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 5 ↥A) a) hAcard R ?_ d ?_
  · intro a
    obtain ⟨P, hP⟩ := hdiag a.1 a.2
    refine ⟨P, ?_⟩
    refine MulEquiv.ext fun g => Subtype.ext ?_
    exact hP g
  · rintro ⟨⟨a, P⟩, hrR⟩ hr
    have hθP : θA a = conjHom5 h P := hrR
    have hdet : Matrix.GeneralLinearGroup.det (P : GL (Fin 5) K) ∈ F :=
      (QuotientGroup.eq_one_iff _).mp hr
    obtain ⟨w, hw5⟩ := hdet
    have hw5' : w ^ 5 = Matrix.GeneralLinearGroup.det (P : GL (Fin 5) K) := hw5
    have hNdet : h.norm (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det) = 1 :=
      norm_det_eq_one h (1 : GL (Fin 5) K) P.2
    have hNw : h.norm (w : K) = 1 := by
      refine norm_eq_one_of_norm_pow_five_eq_one h h5 ?_
      rw [← Units.val_pow_eq_pow_val, hw5', Matrix.GeneralLinearGroup.val_det_apply]
      exact hNdet
    have hNwi : h.norm ((w⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hNw, inv_one]
    set s : GL (Fin 5) K := Matrix.GeneralLinearGroup.scalar (Fin 5) w⁻¹ with hs
    have hsU : s ∈ unit5 h := scalar_mem_primeFormUnitary_one h hNwi
    have hP'U : s * (P : GL (Fin 5) K) ∈ unit5 h := mul_mem hsU P.2
    have hP'det :
        (((s * (P : GL (Fin 5) K) : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (s * (P : GL (Fin 5) K)) = 1 := by
        rw [map_mul, hs, det_scalar5, ← hw5', inv_pow, inv_mul_cancel]
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
    have hP'g : s * (P : GL (Fin 5) K) ∈ gamma5 h := (mem_gramSU_iff_unitary h).mpr ⟨hP'U, hP'det⟩
    set ℓ : gamma5 h := ⟨s * (P : GL (Fin 5) K), hP'g⟩ with hℓ
    have hsc : ∀ M : GL (Fin 5) K, s * M = M * s := fun M => by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hs, GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq
    have hcen : ∀ M : GL (Fin 5) K, s * M * s⁻¹ = M := fun M => by
      rw [hsc M, mul_inv_cancel_right]
    have hθℓ : ∀ g : gamma5 h, (θA a g : gamma5 h) = ℓ * g * ℓ⁻¹ := by
      intro g
      apply Subtype.ext
      have h1 := congrArg (fun e : gamma5 h ≃* gamma5 h => ((e g : gamma5 h) : GL (Fin 5) K))
        hθP
      simp only [coe_conjHom5] at h1
      rw [h1]
      calc (P : GL (Fin 5) K) * (g : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹
          = s * ((P : GL (Fin 5) K) * (g : GL (Fin 5) K) * (P : GL (Fin 5) K)⁻¹) * s⁻¹ :=
            (hcen _).symm
        _ = ((ℓ * g * ℓ⁻¹ : gamma5 h) : GL (Fin 5) K) := by
          simp only [hℓ, Subgroup.coe_mul, Subgroup.coe_inv]
          group
    set j : H := ((ψ ℓ : L) : H) with hj
    have hjL : j ∈ L := (ψ ℓ).2
    have hconj : ∀ g : gamma5 h,
        (a : H) * ((ψ g : L) : H) * (a : H)⁻¹ = j * ((ψ g : L) : H) * j⁻¹ := by
      intro g
      have h1 := coe_inducedAut ψ (a : H) (hAN a.2) g
      have h2 : inducedAut ψ (a : H) (hAN a.2) g = ℓ * g * ℓ⁻¹ := hθℓ g
      rw [h2, map_mul, map_mul, map_inv] at h1
      simpa [hj] using h1.symm
    have hcent : j⁻¹ * (a : H) ∈ Subgroup.centralizer (L : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨g, rfl⟩ : ∃ g : gamma5 h, ((ψ g : L) : H) = l :=
        ⟨ψ.symm ⟨l, hl⟩, by simp⟩
      have := hconj g
      calc ((ψ g : L) : H) * (j⁻¹ * (a : H))
          = j⁻¹ * (j * ((ψ g : L) : H) * j⁻¹) * (a : H) := by group
        _ = j⁻¹ * ((a : H) * ((ψ g : L) : H) * (a : H)⁻¹) * (a : H) := by rw [this]
        _ = (j⁻¹ * (a : H)) * ((ψ g : L) : H) := by group
    have haLC : (a : H) ∈ L ⊔ Subgroup.centralizer (L : Set H) := by
      have : (a : H) = j * (j⁻¹ * (a : H)) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hjL hcent
    have hc := hmain (a : H) a.2 haLC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

end DiagPlane

section Core

variable {f : ℕ} {K : Type} [Field K]

theorem su5_plane_core {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L)
    (hperf : Group.IsPerfect (gamma5 h)) (hcen : Nat.card (Subgroup.center L) = 5)
    {A : Subgroup H} {c : H} (hAN : A ≤ Subgroup.normalizer (L : Set H))
    (hAe : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 3) (hcA : c ∈ A)
    (hcC : c ∈ Subgroup.centralizer (L : Set H))
    (hmain : ∀ x ∈ A, x ∈ L ⊔ Subgroup.centralizer (L : Set H) → x ∈ Subgroup.zpowers c) :
    4 ≤ localRank 5 H := by
  classical
  by_contra hlt
  have hx5 : ∀ x ∈ A, x ^ 5 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hcenΓ : Nat.card (Subgroup.center (gamma5 h)) = 5 := by
    calc Nat.card (Subgroup.center (gamma5 h)) =
        Nat.card ((Subgroup.center (gamma5 h)).map ψ.toMonoidHom) :=
          (Subgroup.card_map_of_injective ψ.injective).symm
      _ = Nat.card (Subgroup.center L) := by
          rw [CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ψ]
      _ = 5 := hcen
  refine su5_diag_plane_false h h5 ψ hAN hAe hAcard hcA hmain ?_
  intro x hx
  by_cases hxc : x ∈ Subgroup.zpowers c
  · refine ⟨1, fun g => ?_⟩
    have hxC : x ∈ Subgroup.centralizer (L : Set H) := (Subgroup.zpowers_le.mpr hcC) hxc
    have h1 := coe_inducedAut ψ x (hAN hx) g
    have h2 : x * ((ψ g : L) : H) * x⁻¹ = ((ψ g : L) : H) := by
      rw [← (Subgroup.mem_centralizer_iff.mp hxC) ((ψ g : L) : H) (ψ g).2, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 : inducedAut ψ x (hAN hx) g = g := ψ.injective (Subtype.ext h1)
    rw [h3]
    simp
  · rcases su5_aut_classification h h5 hperf hcenΓ (inducedAut ψ x (hAN hx))
        (inducedAut_pow ψ x (hAN hx) (hx5 x hx)) with
      ⟨P, c', -, -, hconj⟩ | ⟨φ, M, hφ5, -, hconj⟩
    · exact ⟨P, hconj⟩
    · exfalso
      have hxL : x ∉ L := fun hxL => hxc (hmain x hx (Subgroup.mem_sup_left hxL))
      have := su5_fcase_loc h h5 ψ (hx5 x hx) hxL (hAN hx) φ M hφ5 hconj
      omega

end Core

section Final

open CFSG.Blueprint (Catalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem planeCenterSU5
    {H : Type} [Group H] [Finite H] {p : ℕ} {J A : Subgroup H}
    {c : H} (hrank : localRank p H ≤ 3) (hJq : CFSG.IsQuasisimple ↥J)
    (h68 : p = 5 ∧ Nat.card (Subgroup.center ↥J) = 5 ∧
      ∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU 5 2 n)
    (hAN : A ≤ Subgroup.normalizer (J : Set H)) (hAe : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (hcA : c ∈ A) (hcC : c ∈ Subgroup.centralizer (J : Set H))
    (hmain : ∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) :
    False := by
  obtain ⟨rfl, hZ, n, hn, hmodel⟩ := h68
  have : Group.IsPerfect ↥J := hJq.1
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hmodel
  obtain ⟨h5, ⟨ψ0⟩⟩ := KFSU5.exists_su5_iso hZ hn hKcard e
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have heq : unitarySU 2 n K 5 = gamma5 hU := unitarySU_eq_gramSU hU 5
  let ψ : gamma5 hU ≃* J := (MulEquiv.subgroupCongr heq.symm).trans ψ0
  have hperf : Group.IsPerfect (gamma5 hU) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one hU (by norm_num) (fun hh => absurd hh.1
      (by norm_num))
  have := su5_plane_core hU h5 ψ hperf hZ hAN hAe hAcard hcA hcC hmain
  omega

end Final

end CFSG.RankThree.PartOne
