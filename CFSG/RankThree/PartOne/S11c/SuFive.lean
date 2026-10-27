module

public import CFSG.RankThree.PartOne.S11.SecTenEight
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.S11c.SuFiveGroup

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

section Induced

variable {H : Type} [Group H] {L : Subgroup H} {Γ : Type} [Group Γ]

@[expose] noncomputable def inducedAut (ψ : Γ ≃* L) (x : H)
    (hx : x ∈ Subgroup.normalizer (L : Set H)) : Γ ≃* Γ :=
  MulAut.congr ψ.symm (L.normalizerMonoidHom ⟨x, hx⟩)

theorem coe_inducedAut (ψ : Γ ≃* L) (x : H) (hx : x ∈ Subgroup.normalizer (L : Set H)) (g : Γ) :
    ((ψ (inducedAut ψ x hx g) : L) : H) = x * ((ψ g : L) : H) * x⁻¹ := by
  have h1 : inducedAut ψ x hx g = ψ.symm (L.normalizerMonoidHom ⟨x, hx⟩ (ψ g)) := rfl
  rw [h1, MulEquiv.apply_symm_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ (ψ g)

theorem inducedAut_pow (ψ : Γ ≃* L) (x : H) (hx : x ∈ Subgroup.normalizer (L : Set H)) {n : ℕ}
    (hn : x ^ n = 1) : inducedAut ψ x hx ^ n = 1 := by
  have h1 : (⟨x, hx⟩ : Subgroup.normalizer (L : Set H)) ^ n = 1 := Subtype.ext hn
  have : inducedAut ψ x hx = (MulAut.congr ψ.symm).toMonoidHom
      (L.normalizerMonoidHom ⟨x, hx⟩) := rfl
  rw [this, ← map_pow, ← map_pow, h1, map_one, map_one]

end Induced

section FCase

variable {f : ℕ} {K : Type} [Field K]

theorem su5_fcase {H : Type} [Group H] [Finite H] {L : Subgroup H} (h : UnitaryFieldData 2 f K)
    (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L) {x : H} (hx5 : x ^ 5 = 1) (hxL : x ∉ L)
    (hxN : x ∈ Subgroup.normalizer (L : Set H)) (φ : K ≃+* K) (M : unit5 h) (hφ5 : φ ^ 5 = 1)
    (hconj : ∀ g : gamma5 h, ((inducedAut ψ x hxN g : gamma5 h) : GL (Fin 5) K) =
      (M : GL (Fin 5) K) * glAut φ ((M : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) *
        (M : GL (Fin 5) K)) * (M : GL (Fin 5) K)⁻¹) : 3 < evenRank H := by
  refine frame_contradiction h h5 ψ hx5 hxL (inducedAut ψ x hxN) (coe_inducedAut ψ x hxN) M
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

end FCase

section DCase

variable {f : ℕ} {K : Type} [Field K]

theorem su5_dcase {H : Type} [Group H] [Finite H] {L : Subgroup H} (h : UnitaryFieldData 2 f K)
    (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L) {x : H} (hx5 : x ^ 5 = 1) (hxL : x ∉ L)
    (hxN : x ∈ Subgroup.normalizer (L : Set H)) {S : Subgroup H} (hSne : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hSL : S ≤ L) (hxS : x ∈ Subgroup.normalizer (S : Set H)) (P : unit5 h)
    (c : Kˣ) (hc : h.norm (c : K) = 1)
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hconj : ∀ g : gamma5 h, ((inducedAut ψ x hxN g : gamma5 h) : GL (Fin 5) K) =
      (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹) : 3 < evenRank H := by
  classical
  have hfin : Finite K := h.finite
  have hθ := coe_inducedAut ψ x hxN
  set θ := inducedAut ψ x hxN with hθdef
  set S0 : Subgroup (gamma5 h) := (S.subgroupOf L).map ψ.symm.toMonoidHom with hS0
  set S1 : Subgroup (GL (Fin 5) K) := S0.map (gamma5 h).subtype with hS1
  have hS1p : IsPGroup 2 S1 :=
    ((hS2.comap_subtype (K := L)).map ψ.symm.toMonoidHom).map (gamma5 h).subtype
  have hS1ne : S1 ≠ ⊥ := by
    obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
    have hsL : s ∈ L := hSL hs
    have hmem : ψ.symm ⟨s, hsL⟩ ∈ S0 := ⟨⟨s, hsL⟩, hs, rfl⟩
    intro hbot
    have h1 : ((ψ.symm ⟨s, hsL⟩ : gamma5 h) : GL (Fin 5) K) ∈ S1 := ⟨_, hmem, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : ψ.symm ⟨s, hsL⟩ = 1 := Subtype.ext h1
    have h3 : (⟨s, hsL⟩ : L) = 1 := by simpa using congrArg ψ h2
    have h4 : s = 1 := congrArg Subtype.val h3
    exact hs1 (Subtype.ext h4)
  have hS1P : ∀ s ∈ S1, (P : GL (Fin 5) K)⁻¹ * s * (P : GL (Fin 5) K) ∈ S1 := by
    rintro _ ⟨g0, ⟨y, hy, rfl⟩, rfl⟩
    set g0 : gamma5 h := ψ.symm y with hg0
    set g1 : gamma5 h := ⟨(P : GL (Fin 5) K)⁻¹ * (g0 : GL (Fin 5) K) * (P : GL (Fin 5) K),
      conj_mem_gramSU h _ (inv_mem P.2) g0.2⟩ with hg1
    have hθg1 : θ g1 = g0 := by
      apply Subtype.ext
      rw [hconj g1]
      change (P : GL (Fin 5) K) * ((P : GL (Fin 5) K)⁻¹ * (g0 : GL (Fin 5) K) *
        (P : GL (Fin 5) K)) * (P : GL (Fin 5) K)⁻¹ = (g0 : GL (Fin 5) K)
      group
    have h2 := hθ g1
    rw [hθg1, hg0, ψ.apply_symm_apply] at h2
    have h3 : ((ψ g1 : L) : H) = x⁻¹ * (y : H) * x := by
      calc ((ψ g1 : L) : H) = x⁻¹ * (x * ((ψ g1 : L) : H) * x⁻¹) * x := by group
        _ = x⁻¹ * (y : H) * x := by rw [← h2]
    have h4 : ((ψ g1 : L) : H) ∈ S := by
      rw [h3]
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxS) (y : H)).mp hy
      simpa using this
    exact ⟨g1, ⟨ψ g1, h4, ψ.symm_apply_apply g1⟩, rfl⟩
  obtain ⟨P', hP'5, hP'conj⟩ := exists_pow_five_eq_one_conj h h5 hc hP5 hS1p hS1ne hS1P
  have hP'5u : P' ^ 5 = 1 := Subtype.ext hP'5
  obtain ⟨P0, hP0⟩ := KFU.exists_unitary_conj_diag h Nat.prime_five h5 (Subgroup.zpowers P')
    (by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact (Commute.zpow_zpow_self P' m n).eq)
    (by
      rintro _ ⟨m, rfl⟩
      show (P' ^ m) ^ 5 = 1
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hP'5u,
        _root_.one_zpow])
  have hDdiag : (((P0⁻¹ * P' * P0 : unit5 h) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).IsDiag := hP0 P' (Subgroup.mem_zpowers P')
  set Dg : GL (Fin 5) K := ((P0⁻¹ * P' * P0 : unit5 h) : GL (Fin 5) K) with hDg
  have hP'eq : (P' : GL (Fin 5) K) = (P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹ := by
    rw [hDg]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  by_cases hrep : ∃ i j : Fin 5, i ≠ j ∧ ((Dg : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
      ((Dg : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) j j
  · obtain ⟨i, j, hij, hDij⟩ := hrep
    refine frame_contradiction h h5 ψ hx5 hxL θ hθ P0 hij ?_ ?_
    · intro a ha
      obtain ⟨t, ht, hat⟩ := exists_of_mem_frameA ha
      apply Subtype.ext
      rw [hconj, ← hP'conj, hat, hP'eq]
      have hc := isDiag_comm hDdiag (isDiag_of_mem_torusEq ht)
      calc (P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹ *
            ((P0 : GL (Fin 5) K) * t * (P0 : GL (Fin 5) K)⁻¹) *
            ((P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹)⁻¹ =
          (P0 : GL (Fin 5) K) * (Dg * t * Dg⁻¹) * (P0 : GL (Fin 5) K)⁻¹ := by group
        _ = (P0 : GL (Fin 5) K) * t * (P0 : GL (Fin 5) K)⁻¹ := by
          rw [hc]
          group
    · apply Subtype.ext
      rw [hconj, ← hP'conj, coe_frameR, hP'eq]
      have hc := KFSU5.swapUnit_mul_comm (K := K) (i := i) (j := j) Dg hDdiag hDij
      calc (P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹ *
            ((P0 : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P0 : GL (Fin 5) K)⁻¹) *
            ((P0 : GL (Fin 5) K) * Dg * (P0 : GL (Fin 5) K)⁻¹)⁻¹ =
          (P0 : GL (Fin 5) K) * (Dg * KFSU5.swapUnit K i j * Dg⁻¹) * (P0 : GL (Fin 5) K)⁻¹ := by
            group
        _ = (P0 : GL (Fin 5) K) * KFSU5.swapUnit K i j * (P0 : GL (Fin 5) K)⁻¹ := by
          rw [← hc]
          group
  · push Not at hrep
    obtain ⟨d, hd⟩ := KFU.exists_diagU_of_isDiag hDdiag
    have hDg5 : Dg ^ 5 = 1 := by
      have h1 : (P0⁻¹ * P' * P0) ^ 5 = 1 := by
        rw [show P0⁻¹ * P' * P0 = P0⁻¹ * P' * P0⁻¹⁻¹ by simp, conj_pow, hP'5u]
        group
      have := congrArg Subtype.val h1
      rw [hDg]
      simpa using this
    have hd5 : ∀ k, d k ^ 5 = 1 := by
      have h1 := hDg5
      rw [← hd, KFU.diagU_pow, ← KFU.diagU_one] at h1
      intro k
      exact congrFun (KFU.diagU_injective h1) k
    have hdinj : Function.Injective d := by
      intro i j hij
      by_contra hne
      apply hrep i j hne
      rw [← hd, KFU.diagU_apply_same, KFU.diagU_apply_same, hij]
    obtain ⟨ζ0, hζ0⟩ := KFU.exists_isPrimitiveRoot h Nat.prime_five h5
    obtain ⟨z, hz⟩ := hζ0.isUnit (by norm_num)
    have hzp : IsPrimitiveRoot z 5 := IsPrimitiveRoot.coe_units_iff.mp (hz ▸ hζ0)
    have hprod : ∏ k, d k = 1 := prod_eq_one_of_injective_pow_five ⟨z, hzp⟩ hd5 hdinj
    have hdet : ((P' : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (P' : GL (Fin 5) K) =
          Matrix.GeneralLinearGroup.det Dg := by
        rw [hP'eq, map_mul, map_mul, map_inv]
        simp
      have h2 := congrArg (fun u : Kˣ => (u : K)) h1
      simp only [Matrix.GeneralLinearGroup.val_det_apply] at h2
      rw [h2, ← hd, KFU.det_diagU, ← Units.coe_prod, hprod, Units.val_one]
    have hPg : (P' : GL (Fin 5) K) ∈ gamma5 h := mem_gramSU.mpr ⟨P'.2, hdet⟩
    set ℓ : gamma5 h := ⟨P', hPg⟩ with hℓ
    obtain ⟨ℓH, hℓH⟩ : ∃ ℓH : H, ℓH = ((ψ ℓ : L) : H) := ⟨_, rfl⟩
    have hθg : ∀ g : gamma5 h, θ g = ℓ * g * ℓ⁻¹ := fun g => by
      apply Subtype.ext
      rw [hconj g, ← hP'conj]
      rfl
    have hxℓ : x * ℓH * x⁻¹ = ℓH := by
      rw [hℓH, ← hθ ℓ, hθg ℓ, mul_inv_cancel_right]
    have hcg : ∀ g : gamma5 h, (ℓH⁻¹ * x) * ((ψ g : L) : H) = ((ψ g : L) : H) * (ℓH⁻¹ * x) := by
      intro g
      have h1 := hθ g
      rw [hθg g, map_mul, map_mul, map_inv] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← hℓH] at h1
      calc ℓH⁻¹ * x * ((ψ g : L) : H) = ℓH⁻¹ * (x * ((ψ g : L) : H) * x⁻¹) * x := by group
        _ = ((ψ g : L) : H) * (ℓH⁻¹ * x) := by
          rw [← h1]
          group
    have hℓ5 : ℓH ^ 5 = 1 := by
      have : ℓ ^ 5 = 1 := Subtype.ext hP'5
      rw [hℓH, ← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
    have hc5 : (ℓH⁻¹ * x) ^ 5 = 1 := by
      have hcomm : Commute ℓH⁻¹ x := by
        have : x * ℓH = ℓH * x := by
          calc x * ℓH = x * ℓH * x⁻¹ * x := by group
            _ = ℓH * x := by rw [hxℓ]
        exact (Commute.inv_left (show Commute ℓH x from this.symm)).symm.symm
      rw [hcomm.mul_pow, inv_pow, hℓ5, hx5]
      simp
    have hcL : ℓH⁻¹ * x ∉ L := by
      intro hcL
      apply hxL
      have : x = ℓH * (ℓH⁻¹ * x) := by group
      rw [this]
      exact L.mul_mem (hℓH ▸ (ψ ℓ).2) hcL
    exact three_lt_evenRank_of_frame ψ (isElementaryAbelian_frameA h h5 1 0 1)
      (card_frameA h h5 1 (by decide)) (orderOf_frameR h 1 (by decide))
      (fun a ha => frameR_comm h 1 ha) hc5 hcL (fun a _ => hcg a) (hcg _)

end DCase

section Final

theorem su5_core {H : Type} [Group H] [Finite H] {L : Subgroup H} {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (ψ : gamma5 h ≃* L)
    (hperf : Group.IsPerfect (gamma5 h)) (hcen : Nat.card (Subgroup.center L) = 5) {x : H}
    (hx5 : x ^ 5 = 1) (hxL : x ∉ L) (hxN : x ∈ Subgroup.normalizer (L : Set H)) {S : Subgroup H}
    (hSne : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hSL : S ≤ L)
    (hxS : x ∈ Subgroup.normalizer (S : Set H)) : 3 < evenRank H := by
  have hcenΓ : Nat.card (Subgroup.center (gamma5 h)) = 5 := by
    calc Nat.card (Subgroup.center (gamma5 h)) =
        Nat.card ((Subgroup.center (gamma5 h)).map ψ.toMonoidHom) :=
          (Subgroup.card_map_of_injective ψ.injective).symm
      _ = Nat.card (Subgroup.center L) := by
          rw [CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ψ]
      _ = 5 := hcen
  have hθ5 := inducedAut_pow ψ x hxN hx5
  rcases su5_aut_classification h h5 hperf hcenΓ (inducedAut ψ x hxN) hθ5 with
    ⟨P, c, hc, hP5, hconj⟩ | ⟨φ, M, hφ5, -, hconj⟩
  · exact su5_dcase h h5 ψ hx5 hxL hxN hSne hS2 hSL hxS P c hc hP5 hconj
  · exact su5_fcase h h5 ψ hx5 hxL hxN φ M hφ5 hconj

theorem suFiveNormalizingSubgroupsContained :
    SUFiveNormalizingSubgroupsContained := by
  intro H _ _ he L n hn hqs hZ hmodel X hXN hXcard ⟨S, hSne, hS2, hSL, hXS⟩
  by_contra hXL
  obtain ⟨x, hxX, hxL⟩ := Set.not_subset.mp hXL
  have : Group.IsPerfect L := hqs.1
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hmodel
  obtain ⟨h5, ⟨ψ0⟩⟩ := KFSU5.exists_su5_iso hZ hn hKcard e
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have heq : unitarySU 2 n K 5 = gamma5 hU := unitarySU_eq_gramSU hU 5
  let ψ : gamma5 hU ≃* L := (MulEquiv.subgroupCongr heq.symm).trans ψ0
  have hperf : Group.IsPerfect (gamma5 hU) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one hU (by norm_num) (fun hh => absurd hh.1
      (by norm_num))
  have hx5 : x ^ 5 = 1 := by
    have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hxX⟩)
    rw [hXcard] at this
    exact congrArg Subtype.val this
  have h3 := su5_core hU h5 ψ hperf hZ hx5 hxL (hXN hxX) hSne hS2 hSL (hXS hxX)
  have h4 := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank H
  omega

end Final

end CFSG.RankThree.PartOne
