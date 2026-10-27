module

public import CFSG.Timmesfeld.Transvection.ModelSUPerp
public import CFSG.Timmesfeld.Transvection.ModelSUNormal
public import CFSG.LinearAlgebra.LinearGroups.QuadraticFrobenius

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ARS

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem natCard_perpPair_mul_eq [Finite F] (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) :
    Nat.card (perpPair σ a d) * (Nat.card F * Nat.card F) = Nat.card F ^ m := by
  have hda := uForm_swap_eq_one hσ had
  let e : (Fin m → F) ≃ perpPair σ a d × F × F :=
    { toFun := fun x =>
        (⟨projPair σ a d x, projPair_mem hσ haa hdd had x⟩, uForm σ d x, uForm σ a x)
      invFun := fun p => (p.1 : Fin m → F) + p.2.1 • a + p.2.2 • d
      left_inv := fun x => by
        change projPair σ a d x + uForm σ d x • a + uForm σ a x • d = x
        simp only [projPair]
        abel
      right_inv := fun p => by
        obtain ⟨⟨w, hw⟩, α, β⟩ := p
        refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
        · change projPair σ a d (w + α • a + β • d) = w
          rw [projPair_add, projPair_add, projPair_smul, projPair_smul, projPair_a hσ haa had,
            projPair_d hdd had, projPair_of_mem hw, smul_zero, smul_zero, add_zero, add_zero]
        · change uForm σ d (w + α • a + β • d) = α
          rw [uForm_add_right, uForm_add_right, uForm_smul_right, uForm_smul_right, hw.2, hda,
            hdd]
          ring
        · change uForm σ a (w + α • a + β • d) = β
          rw [uForm_add_right, uForm_add_right, uForm_smul_right, uForm_smul_right, hw.1, haa,
            had]
          ring }
  rw [← Nat.card_prod, ← Nat.card_prod, ← Nat.card_congr e, Nat.card_fun, Nat.card_fin]

theorem natCard_perpPair [Finite F] (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) (hm : 2 ≤ m) :
    Nat.card (perpPair σ a d) = Nat.card F ^ (m - 2) := by
  have h := natCard_perpPair_mul_eq hσ haa hdd had
  have hF : 0 < Nat.card F := Nat.card_pos
  have h2 : Nat.card F ^ m = Nat.card F ^ (m - 2) * (Nat.card F * Nat.card F) := by
    rw [← sq, ← pow_add, Nat.sub_add_cancel hm]
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hF hF) h

theorem natCard_add_unitaryInvolution_eq [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {y : F} (hy : unitaryInvolution F 2 f y = y) :
    Nat.card {c : F // c + unitaryInvolution F 2 f c = y} = 2 ^ f := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨c₀, hc₀⟩ := exists_add_unitaryInvolution_eq hF hy
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hf : f ≠ 0 := by
    rintro rfl
    rw [hF] at h1
    norm_num at h1
  have hq : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf)
  have hK : Fintype.card F = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have hcount := CFSG.LinearGroups.card_pow_eq_self_of_card_eq_sq hq hK
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : {c : F // c + unitaryInvolution F 2 f c = y} ≃ {c : F // c ^ 2 ^ f = c} := by
    refine Equiv.subtypeEquiv (Equiv.addRight c₀) fun c => ?_
    rw [Equiv.coe_addRight, ← unitaryInvolution_apply F 2 f, map_add]
    constructor
    · intro h
      linear_combination h + hc₀ + (y - c - c₀) * h2
    · intro h
      linear_combination h - hc₀ + (c + c₀ - y) * h2
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  convert hcount

theorem natCard_isoPairs [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (hm : 2 ≤ m) {a d : Fin m → F} (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    (hdd : uForm (unitaryInvolution F 2 f) d d = 0)
    (had : uForm (unitaryInvolution F 2 f) a d = 1) :
    Nat.card {p : perpPair (unitaryInvolution F 2 f) a d × F //
      p.2 + unitaryInvolution F 2 f p.2 =
        uForm (unitaryInvolution F 2 f) (p.1 : Fin m → F) p.1} = (2 ^ f) ^ (2 * m - 3) := by
  have hσ := unitaryInvolution_involutive hF
  have := Fintype.ofFinite (perpPair (unitaryInvolution F 2 f) a d)
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun
      (w : perpPair (unitaryInvolution F 2 f) a d) (c : F) =>
      c + unitaryInvolution F 2 f c = uForm (unitaryInvolution F 2 f) (w : Fin m → F) w),
    Nat.card_sigma, Finset.sum_congr rfl fun (w : perpPair (unitaryInvolution F 2 f) a d) _ =>
      natCard_add_unitaryInvolution_eq hF (uForm_conj _ hσ (w : Fin m → F) w),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    natCard_perpPair hσ haa hdd had hm, hF, ← pow_mul, ← pow_succ]
  congr 1
  omega

theorem exists_finset_injOn_conjSub_map [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {K : Type} [Group K] {Φ : SU σ m →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {a d : Fin m → F} {T : Subgroup (SU σ m)}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (hT : IsUTransGroup σ a T) :
    ∃ S : Finset K,
      Nat.card {p : perpPair σ a d × F // p.2 + σ p.2 = uForm σ (p.1 : Fin m → F) p.1} ≤
        S.card ∧ Set.InjOn (fun g => conjSub (T.map Φ) g) (S : Set K) := by
  classical
  have hda := uForm_swap_eq_one hσ had
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let vec : {p : perpPair σ a d × F // p.2 + σ p.2 = uForm σ (p.1 : Fin m → F) p.1} →
      Fin m → F := fun p => (p.1.1 : Fin m → F) + p.1.2 • a + d
  have hvec1 : ∀ p, uForm σ a (vec p) = 1 := by
    rintro ⟨⟨⟨w, hw⟩, α⟩, hα⟩
    change uForm σ a (w + α • a + d) = 1
    rw [uForm_add_right, uForm_add_right, uForm_smul_right, hw.1, haa, had]
    ring
  have hvec0 : ∀ p, uForm σ (vec p) (vec p) = 0 := by
    rintro ⟨⟨⟨w, hw⟩, α⟩, hα⟩
    change α + σ α = uForm σ w w at hα
    change uForm σ (w + α • a + d) (w + α • a + d) = 0
    have hwa : uForm σ w a = 0 := uForm_eq_zero_comm hσ hw.1
    have hwd : uForm σ w d = 0 := uForm_eq_zero_comm hσ hw.2
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hw.1, hw.2,
      hwa, hwd, haa, hdd, had, hda]
    linear_combination hα + uForm σ w w * h2
  have hvec_ne : ∀ p, vec p ≠ 0 := fun p h0 => by
    have h := hvec1 p
    rw [h0, uForm_zero_right] at h
    exact zero_ne_one h
  have hvec_inj : ∀ p q, vec p = vec q → p = q := by
    rintro ⟨⟨⟨w, hw⟩, α⟩, hα⟩ ⟨⟨⟨w', hw'⟩, α'⟩, hα'⟩ h
    change w + α • a + d = w' + α' • a + d at h
    have hαα : α = α' := by
      have h' := congrArg (uForm σ d) h
      simp only [uForm_add_right, uForm_smul_right, hw.2, hw'.2, hda, hdd] at h'
      linear_combination h'
    subst hαα
    have hww : w = w' := add_right_cancel (add_right_cancel h)
    subst hww
    rfl
  have hγ : ∀ p, ∃ γ : SU σ m, suMat σ m γ *ᵥ a = vec p := fun p =>
    exists_suMat_mulVec_eq hσ haa (hvec0 p) (by rw [hvec1 p]; exact one_ne_zero)
      (by rw [hvec1 p, map_one]; exact CharTwo.add_self_eq_zero 1)
  choose γ hγ using hγ
  have key : ∀ p q, conjSub (T.map Φ) (Φ (γ p)) = conjSub (T.map Φ) (Φ (γ q)) → p = q := by
    intro p q h
    rw [conjSub_map, conjSub_map] at h
    have hTp := hT.conjSub (γ p)
    have hTq := hT.conjSub (γ q)
    rw [hγ p] at hTp
    rw [hγ q] at hTq
    obtain ⟨l, hl⟩ := suMapEqStmt_holds hσ htr hker hTp hTq (hvec_ne p) (hvec_ne q) (hvec0 p)
      (hvec0 q) h
    have hl1 : l = 1 := by
      have h' := congrArg (uForm σ a) hl
      rw [uForm_smul_right, hvec1, hvec1, mul_one] at h'
      exact h'.symm
    rw [hl1, one_smul] at hl
    exact hvec_inj p q hl.symm
  have := Fintype.ofFinite
    {p : perpPair σ a d × F // p.2 + σ p.2 = uForm σ (p.1 : Fin m → F) p.1}
  refine ⟨Finset.univ.image fun p => Φ (γ p), le_of_eq ?_, ?_⟩
  · rw [Finset.card_image_of_injective _
      fun p q h => key p q (congrArg (fun g => conjSub (T.map Φ) g) h), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  · intro x hx y hy hxy
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [key p q hxy]

end ModelRank

end CFSG.Timmesfeld.Transvection
