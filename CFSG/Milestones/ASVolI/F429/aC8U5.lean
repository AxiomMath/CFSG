module

public import CFSG.Milestones.ASVolI.F429.aC3
public import CFSG.LocalAnalysis.EvenBN.U5.ModelFiveTwo

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section U5Line

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def burnsideF429a_lev : HypIndex 2 1 → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem burnsideF429a_mat_eq_zero_of_mem_u5LnStab {g : hypSU h 2 1} (hg : g ∈ u5LnStab h)
    (a c : HypIndex 2 1) (hac : burnsideF429a_lev c < burnsideF429a_lev a) : mat g a c = 0 := by
  have hG := (mem_u5LnStab_iff g).1 hg
  have hGi := (mem_u5LnStab_iff g⁻¹).1 (inv_mem hg)
  have hz1 : mat g ιf₁ ιz = 0 := by
    have h1 := hGi ιz ιe₁ (Or.inl rfl) (Or.inl rfl)
    rw [mat_inv_apply] at h1
    simpa using h1
  have hz2 : mat g ιf₂ ιz = 0 := by
    have h1 := hGi ιz ιe₂ (Or.inr rfl) (Or.inl rfl)
    rw [mat_inv_apply] at h1
    simpa using h1
  rcases H13.Sec53F.Unit.hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases H13.Sec53F.Unit.hypIndex_cases c with rfl | rfl | rfl | rfl | rfl <;>
    simp [burnsideF429a_lev] at hac <;>
    first
    | exact hz1
    | exact hz2
    | exact hG _ _ (Or.inl rfl) (Or.inl rfl)
    | exact hG _ _ (Or.inl rfl) (Or.inr (Or.inl rfl))
    | exact hG _ _ (Or.inl rfl) (Or.inr (Or.inr rfl))
    | exact hG _ _ (Or.inr rfl) (Or.inl rfl)
    | exact hG _ _ (Or.inr rfl) (Or.inr (Or.inl rfl))
    | exact hG _ _ (Or.inr rfl) (Or.inr (Or.inr rfl))

theorem burnsideF429a_mat_Ssub_apply {s : hypSU h 2 1} (hs : s ∈ Ssub h) (c d : HypIndex 2 1)
    (hcd : ¬ burnsideF429a_lev c < burnsideF429a_lev d) :
    mat s c d = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) c d := by
  obtain ⟨hsU, a1, a2⟩ := mem_Ssub'.1 hs
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hsU
  rcases H13.Sec53F.Unit.hypIndex_cases c with rfl | rfl | rfl | rfl | rfl <;>
    rcases H13.Sec53F.Unit.hypIndex_cases d with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [burnsideF429a_lev, ιe₁, ιe₂, ιz, ιf₁, ιf₂]

theorem burnsideF429a_fullPos_lt_of_lev_lt :
    ∀ a b : HypIndex 2 1, burnsideF429a_lev a < burnsideF429a_lev b → fullPos a < fullPos b := by
  decide

theorem burnsideF429a_conj_mem_Ssub {g s : hypSU h 2 1} (hg : g ∈ u5LnStab h) (hs : s ∈ Ssub h) :
    g * s * g⁻¹ ∈ Ssub h := by
  have hG := burnsideF429a_mat_eq_zero_of_mem_u5LnStab hg
  have hGi := burnsideF429a_mat_eq_zero_of_mem_u5LnStab (inv_mem hg)
  set E := mat s - 1 with hE
  have hEs : mat s = 1 + E := by rw [hE]; abel
  have hconj : mat (g * s * g⁻¹) = 1 + mat g * E * mat g⁻¹ := by
    rw [mat_mul, mat_mul, hEs, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← mat_mul,
      mul_inv_cancel, mat_one]
  have hEz : ∀ c d, ¬ burnsideF429a_lev c < burnsideF429a_lev d → E c d = 0 := by
    intro c d hcd
    rw [hE, Matrix.sub_apply, burnsideF429a_mat_Ssub_apply hs c d hcd, sub_self]
  have hent : ∀ a b, ¬ burnsideF429a_lev a < burnsideF429a_lev b →
      mat (g * s * g⁻¹) a b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
    intro a b hab
    rw [hconj, Matrix.add_apply]
    suffices (mat g * E * mat g⁻¹) a b = 0 by rw [this, add_zero]
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hcd : burnsideF429a_lev c < burnsideF429a_lev d
    · by_cases hac : burnsideF429a_lev c < burnsideF429a_lev a
      · rw [hG a c hac, zero_mul, zero_mul]
      · have hdb : burnsideF429a_lev b < burnsideF429a_lev d := by omega
        rw [hGi d b hdb, mul_zero]
    · rw [hEz c d hcd]
      simp
  have hU : g * s * g⁻¹ ∈ hypUnitriangular h 2 1 := by
    rw [mem_hypUnitriangular]
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · have hna : ¬ burnsideF429a_lev a < burnsideF429a_lev b := fun hlt =>
        (lt_asymm hab) (burnsideF429a_fullPos_lt_of_lev_lt a b hlt)
      change mat (g * s * g⁻¹) a b = 0
      rw [hent a b hna, one_apply_ne]
      rintro rfl
      exact (lt_irrefl _) hab
    · change mat (g * s * g⁻¹) a a = 1
      rw [hent a a (lt_irrefl _), one_apply_eq]
  refine mem_Ssub'.2 ⟨hU, ?_, ?_⟩
  · rw [hent _ _ (by simp [burnsideF429a_lev]), one_apply_ne (by decide)]
  · rw [hent _ _ (by simp [burnsideF429a_lev]), one_apply_ne (by decide)]

theorem burnsideF429a_leviDual_eq {ω : K} {d : SpecialLinearGroup (Fin 2) K}
    (hd : (d : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, ω]) :
    UnitaryHigher.leviDual h (SpecialLinearGroup.toGL d) = !![h.bar ω, 1; 1, 0] := by
  have := h.charP
  have hL := UnitaryHigher.bar_map_mul_inv h (SpecialLinearGroup.toGL d)
  rw [SpecialLinearGroup.coe_GL_coe_matrix, hd] at hL
  have hN : !![h.bar ω, 1; 1, 0] *
      ((!![0, 1; 1, ω] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  calc UnitaryHigher.leviDual h (SpecialLinearGroup.toGL d)
      = (!![h.bar ω, 1; 1, 0] * ((!![0, 1; 1, ω] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ) *
          UnitaryHigher.leviDual h (SpecialLinearGroup.toGL d) := by rw [hN, Matrix.one_mul]
    _ = !![h.bar ω, 1; 1, 0] * (((!![0, 1; 1, ω] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
          UnitaryHigher.leviDual h (SpecialLinearGroup.toGL d)) := by rw [Matrix.mul_assoc]
    _ = !![h.bar ω, 1; 1, 0] := by rw [hL, Matrix.mul_one]

theorem burnsideF429a_U5_eq_one_of_comm {ω : K} (hω : h.bar ω ≠ ω)
    {d : SpecialLinearGroup (Fin 2) K} (hd : (d : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, ω])
    {x : hypSU h 2 1} (hx : x ∈ Ssub h)
    (hcomm : x * UnitaryHigher.leviSU h 1 d = UnitaryHigher.leviSU h 1 d * x) : x = 1 := by
  have := h.charP
  obtain ⟨hxU, a1, a2⟩ := mem_Ssub'.1 hx
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hxU
  have hM : mat x * mat (UnitaryHigher.leviSU h 1 d) =
      mat (UnitaryHigher.leviSU h 1 d) * mat x := by
    rw [← mat_mul, ← mat_mul, hcomm]
  rw [mat_leviSU, burnsideF429a_leviDual_eq hd, hd] at hM
  have e1 := congrFun (congrFun hM ιe₁) ιz
  have e2 := congrFun (congrFun hM ιe₂) ιz
  have e3 := congrFun (congrFun hM ιz) ιf₁
  have e4 := congrFun (congrFun hM ιz) ιf₂
  have e5 := congrFun (congrFun hM ιe₁) ιf₁
  have e6 := congrFun (congrFun hM ιe₁) ιf₂
  have e7 := congrFun (congrFun hM ιe₂) ιf₁
  have e8 := congrFun (congrFun hM ιe₂) ιf₂
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.univ_unique,
    Finset.sum_singleton] at e1 e2 e3 e4 e5 e6 e7 e8
  simp [a1, a2, d1, d2, d3, d4, d5, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10] at e1 e2 e3 e4 e5 e6 e7 e8
  have hω0 : ω ≠ 0 := fun h0 => hω (by rw [h0, map_zero])
  have hβ0 : h.bar ω ≠ 0 := (map_ne_zero h.bar).2 hω0
  have hne : h.bar ω - ω ≠ 0 := sub_ne_zero.2 hω
  have zv2 : mat x ιe₂ ιz = 0 := by
    have : ω * mat x ιe₂ ιz = 0 := by linear_combination -e2 - e1
    exact (mul_eq_zero.1 this).resolve_left hω0
  have zv1 : mat x ιe₁ ιz = 0 := by linear_combination e1 + zv2
  have zw1 : mat x ιz ιf₁ = 0 := by
    have : h.bar ω * mat x ιz ιf₁ = 0 := by linear_combination e3 + e4
    exact (mul_eq_zero.1 this).resolve_left hβ0
  have zw2 : mat x ιz ιf₂ = 0 := by linear_combination -e4 + zw1
  have z21 : mat x ιe₂ ιf₁ = 0 := by
    have : mat x ιe₂ ιf₁ * (h.bar ω - ω) = 0 := by linear_combination e7 + e6
    exact (mul_eq_zero.1 this).resolve_right hne
  have z11 : mat x ιe₁ ιf₁ = 0 := by
    have : mat x ιe₁ ιf₁ * (h.bar ω - ω) = 0 := by linear_combination e5 + e8 - ω * e6
    exact (mul_eq_zero.1 this).resolve_right hne
  have z22 : mat x ιe₂ ιf₂ = 0 := by linear_combination -e6 + z11
  have z12 : mat x ιe₁ ιf₂ = 0 := by linear_combination e5 - h.bar ω * z11 + z21
  refine eq_of_U_entries hxU (one_mem _) (forall_upper.2 ?_)
  simp [mat_one, Matrix.one_apply, a1, a2, zv1, zv2, zw1, zw2, z11, z12, z21, z22]

theorem burnsideF429a_U5_Ssub_le_perfectCore : Ssub h ≤ perfectCore (u5LnStab h) := by
  have : Finite (hypSU h 2 1) := by have := h.finite; infer_instance
  have := h.charP
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  set d : SpecialLinearGroup (Fin 2) K :=
    ⟨!![0, 1; 1, ω], by simp [det_fin_two_of, CharTwo.neg_eq]⟩ with hd
  set t := UnitaryHigher.leviSU h 1 d with ht
  have htN : t ∈ N₁sub h := MonoidHom.mem_range.2 ⟨d, rfl⟩
  have htC : t ∈ perfectCore (u5LnStab h) := N₁sub_le_perfectCore_u5LnStab htN
  have htP : t ∈ u5LnStab h := N₁sub_le_u5LnStab htN
  have hSP : Ssub h ≤ u5LnStab h := Ssub_le_Usub.trans
    ((hypUnitriangular_le_hypBorel h).trans (hypBorel_le_isoStabilizer h (by norm_num) le_rfl))
  have hmaps : ∀ x ∈ Ssub h, x * t * x⁻¹ * t⁻¹ ∈ Ssub h := fun x hx => by
    have h1 : t * x⁻¹ * t⁻¹ ∈ Ssub h := burnsideF429a_conj_mem_Ssub htP (inv_mem hx)
    have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
    rw [e]
    exact mul_mem hx h1
  let φ : ↥(Ssub h) → ↥(Ssub h) := fun x =>
    ⟨(x : hypSU h 2 1) * t * (x : hypSU h 2 1)⁻¹ * t⁻¹, hmaps x x.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hxy
    have e : a * t * a⁻¹ * t⁻¹ = b * t * b⁻¹ * t⁻¹ := congrArg Subtype.val hxy
    have hz : b⁻¹ * a ∈ Ssub h := mul_mem (inv_mem hb) ha
    have hc : b⁻¹ * a * t = t * (b⁻¹ * a) := by
      calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹ * t⁻¹) * t * a := by group
        _ = b⁻¹ * (b * t * b⁻¹ * t⁻¹) * t * a := by rw [e]
        _ = t * (b⁻¹ * a) := by group
    have h1 := burnsideF429a_U5_eq_one_of_comm hω (d := d) rfl hz hc
    apply Subtype.ext
    show a = b
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  intro z hz
  obtain ⟨⟨a, ha⟩, hx⟩ := Finite.surjective_of_injective hφ ⟨z, hz⟩
  have e : z = a * t * a⁻¹ * t⁻¹ := (congrArg Subtype.val hx).symm
  rw [e]
  have hxN : a ∈ Subgroup.normalizer (perfectCore (u5LnStab h) : Set (hypSU h 2 1)) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (u5LnStab h))) (hSP ha)
  exact (perfectCore (u5LnStab h)).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN t).mp htC)
    ((perfectCore (u5LnStab h)).inv_mem htC)

theorem burnsideF429a_U5_U_le_perfectCore_u5LnStab :
    hypUnitriangular h 2 1 ≤ perfectCore (u5LnStab h) := by
  rw [U_eq_sup_Ssub_I₁.1]
  exact sup_le burnsideF429a_U5_Ssub_le_perfectCore
    (patSub_sI₁_le_N₁sub.trans N₁sub_le_perfectCore_u5LnStab)

theorem burnsideF429a_U5_U_le_perfectCore_u5LnP :
    hypProjUnitriangular h 2 1 ≤ perfectCore (u5LnP h) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [u5LnP, projIsoStabilizer, ← map_perfectCore]
  exact Subgroup.map_mono burnsideF429a_U5_U_le_perfectCore_u5LnStab

end U5Line

section U5Two

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF429a_U5_line {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) ∧
      oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, -, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨Ψ, -, e2⟩ := burnsideF429a_U5_equiv marking
  obtain ⟨hS2, -, hS⟩ := burnsideF429a_sbar Gp M₁ M₂
  obtain ⟨k, e⟩ := burnsideF429a_of_model Ψ (h2.trans e2) (u5_sylow _)
    burnsideF429a_U5_U_le_perfectCore_u5LnP
  exact ⟨k _ hS hS2, e⟩

theorem burnsideF429a_c8_U5two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∨
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  Or.inr (burnsideF429a_U5_line hyp).1

end U5Two

end CFSG.ASVolI
