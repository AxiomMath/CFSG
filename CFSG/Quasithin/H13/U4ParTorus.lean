module

public import CFSG.Quasithin.H13.U4ParModule

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ} {K : Type} [Field K]

@[expose] noncomputable def torDiag (a : K) (i : Ix) : K := if i = ie1 ∨ i = if1 then a else a⁻¹

@[expose] noncomputable def torMat (a : K) : Matrix Ix Ix K := diagonal (torDiag a)

theorem torMat_mul (a b : K) : torMat a * torMat b = torMat (a * b) := by
  rw [torMat, torMat, torMat, diagonal_mul_diagonal]
  congr 1
  funext i
  unfold torDiag
  split_ifs <;> simp [mul_comm]

theorem torMat_one : torMat (1 : K) = 1 := by
  rw [torMat, ← diagonal_one]
  congr 1
  funext i
  unfold torDiag
  split_ifs <;> simp

theorem det_torMat {a : K} (ha : a ≠ 0) : (torMat a).det = 1 := by
  rw [torMat, det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_two,
    Fin.prod_univ_two]
  simp [torDiag, ie1, if1, ha]

variable (h : UnitaryFieldData 2 m K)

theorem ne_zero_of_bar_mul {a : K} (ha : h.bar a * a = 1) : a ≠ 0 := by
  rintro rfl
  simp at ha

theorem bar_eq_inv_of_bar_mul {a : K} (ha : h.bar a * a = 1) : h.bar a = a⁻¹ :=
  eq_inv_of_mul_eq_one_left ha

theorem torMat_gram {a : K} (ha : h.bar a * a = 1) :
    ((torMat a).map h.bar)ᵀ * hypGram 2 0 K * torMat a = hypGram 2 0 K := by
  have ha0 := ne_zero_of_bar_mul h ha
  have hb : h.bar a = a⁻¹ := bar_eq_inv_of_bar_mul h ha
  ext i j
  rw [mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [torMat, torDiag, hypGram_apply, hypPartner, ie1, ie2, if1, if2, hb, map_inv₀, ha0]

@[expose] noncomputable def torElt {a : K} (ha : h.bar a * a = 1) : hypSU h 2 0 :=
  ⟨⟨torMat a, torMat a⁻¹,
    by rw [torMat_mul, mul_inv_cancel₀ (ne_zero_of_bar_mul h ha), torMat_one],
    by rw [torMat_mul, inv_mul_cancel₀ (ne_zero_of_bar_mul h ha), torMat_one]⟩,
    mem_gramSU.mpr ⟨torMat_gram h ha, det_torMat (ne_zero_of_bar_mul h ha)⟩⟩

theorem coe_torElt {a : K} (ha : h.bar a * a = 1) :
    (((torElt h ha : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = torMat a :=
  rfl

theorem coe_torElt_inv {a : K} (ha : h.bar a * a = 1) :
    ((((torElt h ha)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = torMat a⁻¹ :=
  rfl

theorem torElt_mem_parP {a : K} (ha : h.bar a * a = 1) : torElt h ha ∈ parP h := by
  rw [mem_parP_iff]
  intro b hb
  rw [coe_torElt, torMat, diagonal_apply_ne _ hb]

theorem torMat_mul_sMat {a : K} (ha : h.bar a * a = 1) (x y c : K) :
    torMat a * sMat h x y c = sMat h (a⁻¹ * a⁻¹ * x) (a⁻¹ * a⁻¹ * y) c * torMat a := by
  have ha0 := ne_zero_of_bar_mul h ha
  have hb : h.bar a = a⁻¹ := bar_eq_inv_of_bar_mul h ha
  ext i j
  rw [torMat, diagonal_mul, mul_diagonal]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, torDiag, ie1, ie2, if1, if2, map_mul, map_inv₀, hb] <;>
    field_simp

theorem coe_conj_torElt {a : K} (ha : h.bar a * a = 1) {g : hypSU h 2 0} {x y c : K}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) :
    (((torElt h ha * g * (torElt h ha)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h (a⁻¹ * a⁻¹ * x) (a⁻¹ * a⁻¹ * y) c := by
  rw [coe_mul_hypSU, coe_mul_hypSU, coe_torElt, hg, coe_torElt_inv, torMat_mul_sMat h ha,
    mul_assoc, torMat_mul, mul_inv_cancel₀ (ne_zero_of_bar_mul h ha), torMat_one, mul_one]

omit [Field K] in
theorem eq_one_of_mul_self_eq_one {F : Type} [Field F] [CharP F 2] {x : F} (hx : x * x = 1) :
    x = 1 := by
  have h0 : (x + 1) * (x + 1) = 0 := by
    have e : (x + 1) * (x + 1) = x * x + (x + x) + 1 := by ring
    rw [e, hx, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h1 : x + 1 = 0 := mul_self_eq_zero.mp h0
  rw [← CharTwo.neg_eq (1 : F)]
  exact eq_neg_of_add_eq_zero_left h1

theorem exists_torus_scalar :
    ∃ a : K, h.bar a * a = 1 ∧ h.bar (a⁻¹ * a⁻¹) ≠ a⁻¹ * a⁻¹ := by
  have := h.charP
  obtain ⟨z, hz⟩ := h.exists_bar_ne
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz (map_zero _)
  have hbz0 : h.bar z ≠ 0 := fun e => hz0 (by rw [← h.bar_bar z, e, map_zero])
  have hb : h.bar (z * (h.bar z)⁻¹) = (z * (h.bar z)⁻¹)⁻¹ := by
    rw [map_mul, map_inv₀, h.bar_bar, mul_inv, inv_inv, mul_comm]
  refine ⟨z * (h.bar z)⁻¹, ?_, fun heq => ?_⟩
  · rw [hb]
    exact inv_mul_cancel₀ (mul_ne_zero hz0 (inv_ne_zero hbz0))
  · set a := z * (h.bar z)⁻¹ with ha
    have ha0 : a ≠ 0 := mul_ne_zero hz0 (inv_ne_zero hbz0)
    rw [map_mul, map_inv₀, hb, inv_inv] at heq
    have h4 : (a * a) * (a * a) = 1 := by
      have e : (a * a) * (a * a) = (a * a) * (a⁻¹ * a⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
      rw [e, ← heq, mul_inv_cancel₀ (mul_ne_zero ha0 ha0)]
    have h1 : a = 1 := eq_one_of_mul_self_eq_one (eq_one_of_mul_self_eq_one h4)
    apply hz
    rw [ha] at h1
    have e := congrArg (· * h.bar z) h1
    simp only [one_mul, mul_assoc, inv_mul_cancel₀ hbz0, mul_one] at e
    exact e.symm

theorem eq_bot_or_eq_top_of_mul_mem {L : Submodule h.fixedField K} {μ : K} (hμ : h.bar μ ≠ μ)
    (hL : ∀ x ∈ L, μ * x ∈ L) : L = ⊥ ∨ L = ⊤ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, htop⟩ := hcon
  have := h.finite
  have hcard := card_submodule_eq h h0 htop
  obtain ⟨ℓ, hℓ, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  let φ : h.fixedField × h.fixedField → L := fun p =>
    ⟨(p.1 : K) * ℓ + (p.2 : K) * (μ * ℓ),
      L.add_mem (L.smul_mem p.1 hℓ) (L.smul_mem p.2 (hL ℓ hℓ))⟩
  have hφ : Function.Injective φ := by
    rintro ⟨c₀, c₁⟩ ⟨d₀, d₁⟩ he
    have he' : ((c₀ : K) - d₀ + ((c₁ : K) - d₁) * μ) * ℓ = 0 := by
      have := congrArg Subtype.val he
      simp only [φ] at this
      linear_combination this
    have hcd : (c₀ : K) - d₀ + ((c₁ : K) - d₁) * μ = 0 :=
      (mul_eq_zero.mp he').resolve_right hℓ0
    have h1 : (c₁ : K) = d₁ := by
      by_contra hne
      have hne' : (c₁ : K) - d₁ ≠ 0 := sub_ne_zero.mpr hne
      have hμe : μ = -((c₀ : K) - d₀) / ((c₁ : K) - d₁) := by
        field_simp
        linear_combination hcd
      apply hμ
      have hc₀ := (h.mem_fixedField).mp c₀.2
      have hc₁ := (h.mem_fixedField).mp c₁.2
      have hd₀ := (h.mem_fixedField).mp d₀.2
      have hd₁ := (h.mem_fixedField).mp d₁.2
      rw [hμe, map_div₀, map_neg, map_sub, map_sub, hc₀, hc₁, hd₀, hd₁]
    have h0' : (c₀ : K) = d₀ := by
      rw [h1, sub_self, zero_mul, add_zero] at hcd
      exact sub_eq_zero.mp hcd
    exact Prod.ext (Subtype.ext h0') (Subtype.ext h1)
  have : Finite L := Subtype.finite
  have hle := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, h.card_fixedField, hcard] at hle
  have h2m : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.one_le
  nlinarith

theorem RImg.tor {R : Subgroup (hypSU h 2 0)} {a : K} (ha : h.bar a * a = 1)
    (hR : torElt h ha ∈ Subgroup.normalizer (R : Set (hypSU h 2 0))) {x y : K}
    (h1 : RImg h R x y) : RImg h R (a⁻¹ * a⁻¹ * x) (a⁻¹ * a⁻¹ * y) := by
  obtain ⟨g, hg, c, hgc⟩ := h1
  exact ⟨torElt h ha * g * (torElt h ha)⁻¹, (Subgroup.mem_normalizer_iff.mp hR g).mp hg, c,
    coe_conj_torElt h ha hgc⟩

theorem eq_zRad_or_eq_radQ {W : Subgroup (hypSU h 2 0)} (hZW : zRad h ≤ W) (hWQ : W ≤ radQ h)
    (hN : (levHom h).range ≤ Subgroup.normalizer (W : Set (hypSU h 2 0))) {a : K}
    (ha : h.bar a * a = 1) (hμ : h.bar (a⁻¹ * a⁻¹) ≠ a⁻¹ * a⁻¹)
    (hT : torElt h ha ∈ Subgroup.normalizer (W : Set (hypSU h 2 0))) :
    W = zRad h ∨ W = radQ h := by
  have hWS : W = radS h (lineL W hN) := by rw [← sup_eq_radS hWQ hN, sup_eq_left.mpr hZW]
  have hL : ∀ x ∈ lineL W hN, a⁻¹ * a⁻¹ * x ∈ lineL W hN := fun x hx =>
    mem_lineL.mpr ((RImg.tor h ha hT (mem_lineL.mp hx)).congr rfl (mul_zero _))
  rcases eq_bot_or_eq_top_of_mul_mem h hμ hL with hbot | htop
  · refine Or.inl (le_antisymm (fun g hg => ?_) hZW)
    rw [hWS] at hg
    obtain ⟨hgQ, hx, hy⟩ := mem_radS.mp hg
    rw [hbot, Submodule.mem_bot] at hx hy
    have hG := coe_eq_sMat_coord hgQ
    rw [hx, hy] at hG
    exact ⟨_, (sAdm_zero_zero_iff h).mp (sAdm_of_mem_radQ hgQ hG), hG⟩
  · refine Or.inr (le_antisymm hWQ fun g hg => ?_)
    rw [hWS, htop]
    exact mem_radS.mpr ⟨hg, Submodule.mem_top, Submodule.mem_top⟩

theorem eq_zRad_or_eq_radQ_of_parP {W : Subgroup (hypSU h 2 0)} (hZW : zRad h ≤ W)
    (hWQ : W ≤ radQ h) (hP : parP h ≤ Subgroup.normalizer (W : Set (hypSU h 2 0))) :
    W = zRad h ∨ W = radQ h := by
  obtain ⟨a, ha, hμ⟩ := exists_torus_scalar h
  exact eq_zRad_or_eq_radQ h hZW hWQ ((levHom_le_parP h).trans hP) ha hμ
    (hP (torElt_mem_parP h ha))

theorem parabolic_irred_full {Y : Type} [Group Y] {m : ℕ} (hm : 2 ≤ m) {T M₁ M : Subgroup Y}
    (hY : IsLieOverTwo .PSU 4 m Y ∨ ∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y),
      IsLieOverTwo .PSU 4 m Y₀ ∧ Function.Injective ι ∧ ι.range.index = 2)
    (hpair : IsYAmalgamPair T M₁ M)
    (hsp : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore M))) :
    ∀ W : Subgroup Y, centerOf (pCoreOf 2 (perfectCore M)) ≤ W →
      W ≤ pCoreOf 2 (perfectCore M) → M ≤ Subgroup.normalizer (W : Set Y) →
        W = centerOf (pCoreOf 2 (perfectCore M)) ∨ W = pCoreOf 2 (perfectCore M) := by
  intro W hZW hWQ hMW
  obtain ⟨-, K, _, h, ψ, hψ, -, -, hMψ, -, hO⟩ := recog_of hm hY hpair hsp
  have hZ : centerOf (pCoreOf 2 (perfectCore M)) = (zRad h).map ψ := by
    rw [hO, centerOf_map_of_inj hψ, centerOf_radQ]
  rw [hZ] at hZW
  rw [hO] at hWQ
  rw [hZ, hO]
  have hW : (W.comap ψ).map ψ = W :=
    Subgroup.map_comap_eq_self (hWQ.trans (Subgroup.map_le_range ψ _))
  have hW₀Q : W.comap ψ ≤ radQ h := fun g hg => (Subgroup.mem_map_iff_mem hψ).mp (hWQ hg)
  have hZW₀ : zRad h ≤ W.comap ψ := fun g hg => hZW ⟨g, hg, rfl⟩
  have hPN : parP h ≤ Subgroup.normalizer ((W.comap ψ : Subgroup _) : Set (hypSU h 2 0)) := by
    intro g hg
    have hgM : ψ g ∈ M := by
      have : ψ g ∈ M ⊓ ψ.range := by
        rw [hMψ]
        exact Subgroup.mem_map_of_mem ψ hg
      exact (Subgroup.mem_inf.mp this).1
    have hA := hMW hgM
    rw [Subgroup.mem_normalizer_iff] at hA ⊢
    intro x
    have := hA (ψ x)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  rcases eq_zRad_or_eq_radQ_of_parP h hZW₀ hW₀Q hPN with e | e
  · left
    rw [← hW, e]
  · right
    rw [← hW, e]

end CFSG.Quasithin.H13.U4Par
