module

public import CFSG.CGT.Timmesfeld75.L2AutInvol
public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.Quasithin.Background.F7TwoInvL2Model

public section

namespace CFSG.Quasithin.F7Two

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75

section Sl2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem isSimpleGroup_sl2_of_charTwo (hF : 4 ≤ Nat.card F) : IsSimpleGroup SL(2, F) := by
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  exact pslMulEquivSL.symm.isSimpleGroup

omit [Finite F] in
theorem sl2_nonabelian : ∃ x y : SL(2, F), x * y ≠ y * x := by
  refine ⟨utriElt 1, ltriElt 1, fun h => ?_⟩
  have h00 := congrArg (fun g : SL(2, F) => g 0 0) h
  simp only [mul_apply_00, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10, ltriElt_apply_00,
    ltriElt_apply_01, ltriElt_apply_10, mul_one, zero_mul, add_zero] at h00
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [h2] at h00
  exact zero_ne_one h00

theorem comm_of_isPGroup_sl2 (P : Subgroup SL(2, F)) (hP : IsPGroup 2 ↥P) {x y : SL(2, F)}
    (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSubgroup_utri_eq_of_sylow Q
  have hx' : x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup a (utri F) := ha ▸ hQ hx
  have hy' : y ∈ CFSG.CGT.Timmesfeld75.conjSubgroup a (utri F) := ha ▸ hQ hy
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx' hy'
  obtain ⟨s, hs⟩ := mem_utri_iff.mp hx'
  obtain ⟨t, ht⟩ := mem_utri_iff.mp hy'
  have h : a⁻¹ * (x * y) * a = a⁻¹ * (y * x) * a :=
    calc a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
      _ = utriElt s * utriElt t := by rw [hs, ht]
      _ = utriElt t * utriElt s := by rw [← utriElt_add, ← utriElt_add, add_comm]
      _ = (a⁻¹ * y * a) * (a⁻¹ * x * a) := by rw [hs, ht]
      _ = a⁻¹ * (y * x) * a := by group
  exact mul_left_cancel (mul_right_cancel h)

theorem invAutGen_sl2_conj_involution {g : SL(2, F)} (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hF : 4 ≤ Nat.card F) : InvAutGen SL(2, F) (MulAut.conj g) :=
  invAutGen_conj_of_abelian_two_subgroups (isSimpleGroup_sl2_of_charTwo hF) sl2_nonabelian hg2 hg1
    fun P hP _ hx _ hy => comm_of_isPGroup_sl2 P hP hx hy

theorem invAutGen_sl2FieldAut {σ : F ≃+* F}
    (hσ2 : (sl2FieldAut σ : MulAut SL(2, F)) * sl2FieldAut σ = 1)
    (hσ : σ ≠ RingEquiv.refl F) (hF : 4 ≤ Nat.card F) : InvAutGen SL(2, F) (sl2FieldAut σ) := by
  obtain ⟨t₀, ht₀⟩ : ∃ t : F, σ t ≠ t := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  have hφ1 : (sl2FieldAut σ : MulAut SL(2, F)) ≠ 1 := by
    intro h
    apply ht₀
    have h1 := MulEquiv.congr_fun h (utriElt t₀)
    rw [MulAut.one_apply, sl2FieldAut_utriElt] at h1
    exact utriElt_injective h1
  set φ : MulAut SL(2, F) := sl2FieldAut σ with hφ
  let U : ↥(fixSubgroup φ) → Subgroup SL(2, F) := fun c =>
    CFSG.CGT.Timmesfeld75.conjSubgroup (c : SL(2, F)) (torus F)
  have hodd : ∀ c, Odd (Nat.card (U c)) := by
    intro c
    have h1 : Nat.card (U c) = Nat.card (torus F) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj (c : SL(2, F))).toMonoidHom)
        (MulAut.conj (c : SL(2, F))).injective
    rw [h1, card_torus]
    obtain ⟨n, hn, hcard⟩ := exists_natCard_eq_two_pow (F := F)
    rw [hcard]
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
    have h3 : 0 < 2 ^ n := by positivity
    exact Nat.odd_iff.mpr (by omega)
  have hT : ∀ y ∈ torus F, φ y ∈ torus F := by
    intro y hy
    obtain ⟨a, rfl⟩ := mem_torus_iff.mp hy
    rw [hφ, sl2FieldAut_torusElt]
    exact torusElt_mem_torus _
  have hinv : ∀ c, ∀ x ∈ U c, φ x ∈ U c := by
    intro c x hx
    have hc : φ (c : SL(2, F)) = c := mem_fixSubgroup_iff.mp c.2
    simp only [U] at hx ⊢
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx ⊢
    have e : (c : SL(2, F))⁻¹ * φ x * c = φ ((c : SL(2, F))⁻¹ * x * c) := by
      rw [map_mul, map_mul, map_inv, hc]
    rw [e]
    exact hT _ hx
  set S : Subgroup SL(2, F) := ⨆ c, U c with hS
  have hu1 : φ (utriElt 1) = utriElt 1 := by rw [hφ, sl2FieldAut_utriElt, map_one]
  have hw : φ wElt = wElt := by
    apply sl2_ext
    · rw [hφ, sl2FieldAut_apply_00, wElt_apply_00, map_zero]
    · rw [hφ, sl2FieldAut_apply_01, wElt_apply_01, map_neg, map_one]
    · rw [hφ, sl2FieldAut_apply_10, wElt_apply_10, map_one]
    · rw [hφ, sl2FieldAut_apply_11, wElt_apply_11, map_zero]
  have hT0 : ∀ a : Fˣ, torusElt a ∈ S := fun a => by
    refine Subgroup.mem_iSup_of_mem (1 : ↥(fixSubgroup φ)) ?_
    show torusElt a ∈ CFSG.CGT.Timmesfeld75.conjSubgroup 1 (torus F)
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_one]
    exact torusElt_mem_torus a
  have hT1 : ∀ a : Fˣ, utriElt 1 * torusElt a * (utriElt 1)⁻¹ ∈ S := fun a =>
    Subgroup.mem_iSup_of_mem (⟨utriElt 1, mem_fixSubgroup_iff.mpr hu1⟩ : ↥(fixSubgroup φ))
      (CFSG.CGT.Timmesfeld75.conj_mem_conjSubgroup (utriElt 1) (torusElt_mem_torus a))
  have hcomm : ∀ a : Fˣ, utriElt (1 - (a : F) ^ 2) ∈ S := fun a => by
    have h1 := Subgroup.mul_mem S (hT1 a) (Subgroup.inv_mem S (hT0 a))
    have e : utriElt 1 * torusElt a * (utriElt 1)⁻¹ * (torusElt a)⁻¹ =
        utriElt (1 - (a : F) ^ 2) :=
      calc utriElt 1 * torusElt a * (utriElt 1)⁻¹ * (torusElt a)⁻¹
          = utriElt 1 * (torusElt a * (utriElt 1)⁻¹ * (torusElt a)⁻¹) := by group
        _ = utriElt 1 * utriElt ((a : F) ^ 2 * (-1)) := by
          rw [utriElt_inv, torusElt_mul_utriElt_mul_inv]
        _ = utriElt (1 + (a : F) ^ 2 * (-1)) := (utriElt_add _ _).symm
        _ = utriElt (1 - (a : F) ^ 2) := by congr 1; ring
    rwa [e] at h1
  have hne : ∀ s : F, s ≠ 1 → utriElt s ∈ S := by
    intro s hs
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (1 - s)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hs (by linear_combination -hr)
    have h1 := hcomm (Units.mk0 r hr0)
    rwa [show 1 - ((Units.mk0 r hr0 : Fˣ) : F) ^ 2 = s by
      rw [Units.val_mk0, sq, ← hr]; ring] at h1
  have hutri : ∀ s : F, utriElt s ∈ S := by
    intro s
    by_cases hs : s = 1
    · subst hs
      have ht1 : t₀ ≠ 1 := fun h => ht₀ (by rw [h, map_one])
      have ht0 : t₀ ≠ 0 := fun h => ht₀ (by rw [h, map_zero])
      have ht2 : 1 + t₀ ≠ 1 := fun h => ht0 (by linear_combination h)
      have h1 := Subgroup.mul_mem S (hne t₀ ht1) (hne (1 + t₀) ht2)
      rwa [← utriElt_add, show t₀ + (1 + t₀) = 1 by
        linear_combination CharTwo.add_self_eq_zero t₀] at h1
    · exact hne s hs
  have hutri_le : utri F ≤ S := fun x hx => by
    obtain ⟨s, rfl⟩ := mem_utri_iff.mp hx
    exact hutri s
  have hwS : ∀ y ∈ S, (wElt : SL(2, F)) * y * (wElt : SL(2, F))⁻¹ ∈ S := by
    have hle : S ≤ S.comap (MulAut.conj (wElt : SL(2, F))).toMonoidHom := by
      refine iSup_le fun c y hy => ?_
      show (wElt : SL(2, F)) * y * (wElt : SL(2, F))⁻¹ ∈ S
      have hwc : (wElt : SL(2, F)) * (c : SL(2, F)) ∈ fixSubgroup φ :=
        Subgroup.mul_mem _ (mem_fixSubgroup_iff.mpr hw) c.2
      refine Subgroup.mem_iSup_of_mem
        (⟨(wElt : SL(2, F)) * (c : SL(2, F)), hwc⟩ : ↥(fixSubgroup φ)) ?_
      simp only [U] at hy ⊢
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hy ⊢
      have e : ((wElt : SL(2, F)) * (c : SL(2, F)))⁻¹ *
          ((wElt : SL(2, F)) * y * (wElt : SL(2, F))⁻¹) * ((wElt : SL(2, F)) * (c : SL(2, F))) =
          (c : SL(2, F))⁻¹ * y * (c : SL(2, F)) := by group
      rw [e]
      exact hy
    exact fun y hy => hle hy
  have hltri_le : ltri F ≤ S := by
    rw [← conjSubgroup_wElt_utri]
    intro x hx
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
    obtain ⟨s, hs⟩ := mem_utri_iff.mp hx
    have h1 := hwS _ (hutri s)
    rwa [← hs, show (wElt : SL(2, F)) * ((wElt : SL(2, F))⁻¹ * x * wElt) * (wElt : SL(2, F))⁻¹ =
      x by group] at h1
  refine invAutGen_of_odd_iSup (isSimpleGroup_sl2_of_charTwo hF) sl2_nonabelian hσ2 hφ1 hodd
    hinv ?_
  show S = ⊤
  rw [eq_top_iff, ← utri_sup_ltri]
  exact sup_le hutri_le hltri_le

end Sl2

theorem invAutGen_psl2_even {K : Type} [Field K] [Finite K]
    (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    ∀ φ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) φ := by
  obtain ⟨f, hf, hKf⟩ := hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hKf
  have : CharP K 2 := charP_of_card_eq_prime_pow hcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hKf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine invAutGen_of_mulEquiv_forall (pslMulEquivSL (F := K)) ?_
  intro φ hφ2 hφ1
  have hφ : ∀ x, φ (φ x) = x := fun x => by simpa using MulEquiv.congr_fun hφ2 x
  rcases autInvol_inner_or_field φ hφ with ⟨g, hg2, hg⟩ | ⟨k, σ, hσ, hk⟩
  · have hφg : φ = MulAut.conj g := MulEquiv.ext fun x => by rw [hg x]; rfl
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hφ1 (by rw [hφg]; exact map_one MulAut.conj)
    rw [hφg]
    exact invAutGen_sl2_conj_involution hg2 hg1 h4
  · have hconj : MulAut.conj k * φ * (MulAut.conj k)⁻¹ = sl2FieldAut σ := by
      refine MulEquiv.ext fun y => ?_
      have h1 := hk (k⁻¹ * y * k)
      rw [show k * (k⁻¹ * y * k) * k⁻¹ = y by group, ← sl2FieldAut_eq_map] at h1
      rw [← h1]
      simp [MulAut.conj_apply]
    have h2 : (sl2FieldAut σ : MulAut SL(2, K)) * sl2FieldAut σ = 1 := by
      rw [← hconj]
      calc MulAut.conj k * φ * (MulAut.conj k)⁻¹ * (MulAut.conj k * φ * (MulAut.conj k)⁻¹)
          = MulAut.conj k * (φ * φ) * (MulAut.conj k)⁻¹ := by group
        _ = 1 := by rw [hφ2]; group
    have h3 := invAutGen_sl2FieldAut h2 hσ h4
    rw [← hconj] at h3
    exact (InvAutGen.conj_iff _ _).2 h3

theorem invAutGen_of_statedPSL2_two {L : Type} [Group L] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 2 f) :
    ∀ φ : MulAut L, φ * φ = 1 → φ ≠ 1 → InvAutGen L φ := by
  obtain ⟨-, -, h4, K, _, _, hK, ⟨e⟩⟩ := exists_psl2_of_statedClassicalModel h
  exact invAutGen_of_mulEquiv_forall e
    (invAutGen_psl2_even ⟨f, two_le_of_four_le_two_pow h4, hK⟩)

end CFSG.Quasithin.F7Two
