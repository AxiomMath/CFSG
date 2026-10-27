module

public import CFSG.Quasithin.Background.SimsG4OrthURefl
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.Quasithin.Background.SimsG4OrthMinus
import CFSG.Quasithin.Background.SimsG4OrthPlusOmega
import CFSG.Quasithin.Background.SimsG49FStar
import CFSG.Quasithin.Background.SimsG49Pre
import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.Quasithin.SimsG4.G49

open Module

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem finrank_le_one_of_not_plus (Q : QuadraticForm K W) (hdim : finrank K W = 4)
    (hplus : ¬ ∃ U : Submodule K W, finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → finrank K U ≤ 1 := by
  intro U hU
  by_contra hlt
  push Not at hlt
  apply hplus
  haveI : FiniteDimensional K W := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  let b := Module.finBasis K U
  have h2 : 2 ≤ finrank K U := hlt
  let i₀ : Fin (finrank K U) := ⟨0, by omega⟩
  let i₁ : Fin (finrank K U) := ⟨1, by omega⟩
  let v : Fin 2 → W := ![(b i₀ : W), (b i₁ : W)]
  have hv : LinearIndependent K v := by
    have hb : LinearIndependent K (fun i => (b i : W)) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have hinj : Function.Injective ![i₀, i₁] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [i₀, i₁, Fin.ext_iff]
    have := hb.comp ![i₀, i₁] hinj
    convert this using 1
    ext x
    fin_cases x <;> rfl
  refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hv]
    simp
  · intro u hu
    have hle : Submodule.span K (Set.range v) ≤ U := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      fin_cases x
      · exact (b i₀).2
      · exact (b i₁).2
    exact hU u (hle hu)

theorem exists_orth_unit [Finite K] [CharP K 2] (Q : QuadraticForm K W) (hdim : 2 < finrank K W)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) {r : W} (hr : Q r = 1) :
    ∃ s : W, Q s = 1 ∧ QuadraticMap.polar Q s r = 0 ∧ LinearIndependent K ![s, r] := by
  classical
  haveI : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hr
    exact zero_ne_one hr
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, QuadraticMap.polar Q r y₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hr0 (hnd r hcon)
  set y := (QuadraticMap.polar Q r y₀)⁻¹ • y₀ with hy
  have hyr : QuadraticMap.polar Q y r = 1 := by
    rw [QuadraticMap.polar_comm, hy, QuadraticMap.polar_smul_right, smul_eq_mul,
      inv_mul_cancel₀ hy₀]
  obtain ⟨x, hx⟩ : ∃ x, x + QuadraticMap.polar Q x r • y ∉ K ∙ r := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Submodule K W) ≤ Submodule.span K (({r, y} : Finset W) : Set W) := by
      intro v _
      have hv : v = (v + QuadraticMap.polar Q v r • y) - QuadraticMap.polar Q v r • y := by
        abel
      rw [hv]
      refine Submodule.sub_mem _ (Submodule.span_mono ?_ (hcon v))
        (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      · simp
      · simp
    have h1 := Submodule.finrank_mono htop
    rw [finrank_top] at h1
    have h2 : (({r, y} : Finset W) : Set W).finrank K ≤ ({r, y} : Finset W).card :=
      finrank_span_finset_le_card _
    have h3 : ({r, y} : Finset W).card ≤ 2 := Finset.card_le_two
    have h4 : finrank K (Submodule.span K (({r, y} : Finset W) : Set W)) ≤ 2 := h2.trans h3
    omega
  set s₀ := x + QuadraticMap.polar Q x r • y with hs₀
  have hs₀r : QuadraticMap.polar Q s₀ r = 0 := by
    rw [hs₀, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hyr, smul_eq_mul,
      mul_one, CharTwo.add_self_eq_zero]
  by_cases hQ0 : Q s₀ = 0
  · refine ⟨s₀ + r, ?_, ?_, linearIndependent_fin2.mpr ⟨?_, fun a ha => hx ?_⟩⟩
    · rw [QuadraticMap.map_add (⇑Q) s₀ r, hQ0, hr, hs₀r, zero_add, add_zero]
    · rw [QuadraticMap.polar_add_left, hs₀r, polar_self_eq_zero, add_zero]
    · simpa using hr0
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at ha
      have e : s₀ = (a - 1) • r := by
        rw [sub_smul, one_smul, ha, add_sub_cancel_right]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)
  · obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q s₀)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hQ0 (by rw [hc, mul_zero])
    refine ⟨c⁻¹ • s₀, ?_, ?_, linearIndependent_fin2.mpr ⟨?_, fun a ha => hx ?_⟩⟩
    · rw [QuadraticMap.map_smul, hc, smul_eq_mul]
      field_simp
    · rw [QuadraticMap.polar_smul_left, hs₀r, smul_zero]
    · simpa using hr0
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at ha
      have e : s₀ = (c * a) • r := by
        rw [mul_smul, ha, smul_inv_smul₀ hc0]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)

variable {Γ : Type*} [Group Γ] {G₀ : Subgroup Γ}

theorem orth_minus_core [Finite G₀] [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : finrank K W = 4) (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hminus : ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → finrank K U ≤ 1)
    (f : ↥G₀ →* (W ≃ₗ[K] W)) (hf : Function.Injective f)
    (hrange : f.range = TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ N : Subgroup Γ, fStarOf G₀ = N ∧ (∀ g ∈ G₀, ∀ m ∈ N, g * m * g⁻¹ ∈ N) ∧
      IsSimpleGroup ↥N ∧ (∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) ∧
      (∀ (a b : Γ) (ha : a ∈ G₀) (hb : b ∈ G₀) (r s : W), Q r = 1 → Q s = 1 →
        f ⟨a, ha⟩ = reflK Q r → f ⟨b, hb⟩ = reflK Q s → a * b ∈ N) ∧
      (∀ (t : Γ) (ht : t ∈ G₀) (r : W), r ≠ 0 → f ⟨t, ht⟩ = reflK Q r →
        ∀ h ∈ G₀, h ∈ N ∨ h * t ∈ N) := by
  obtain ⟨L, _, _, ρ, hL, hρinj, hρrange, hidx, hrefl, hrefl2, -, hcent⟩ :=
    omega4minus_structure Q hdim hnd hminus
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hΩO : ⁅O, O⁆ ≤ O := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem hx hy) (O.inv_mem hx)) (O.inv_mem hy)
  have hΩf : ⁅O, O⁆ ≤ f.range := hrange ▸ hΩO
  have hidx' : ((⁅O, O⁆).subgroupOf f.range).index = 2 := by
    rw [hrange]
    exact hidx
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite L
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hLcard : Fintype.card L = 2 ^ (2 * (m : ℕ)) := by
    rw [Fintype.card_eq_nat_card, hL, Nat.card_eq_fintype_card, hm, ← pow_mul, mul_comm]
  haveI : CharP L 2 := charP_of_card_eq_prime_pow hLcard
  have hL4 : 4 ≤ Nat.card L := by
    rw [Nat.card_eq_fintype_card, hLcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (m : ℕ)) := Nat.pow_le_pow_right (by norm_num) (by have := m.pos; omega)
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) L) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup hL4
  obtain ⟨e₁⟩ := nonempty_mulEquiv_pre hf hΩf
  have e : ↥(pre f ⁅O, O⁆) ≃* Matrix.SpecialLinearGroup (Fin 2) L :=
    e₁.trans ((MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)).symm
  have hNs : IsSimpleGroup ↥(pre f ⁅O, O⁆) := e.isSimpleGroup
  have hnab := nonabelian_of_mulEquiv e (exists_sl2_ne_comm L)
  have hNn := conj_mem_pre (conj_mem_of_index_two hΩf hidx')
  have hC := eq_one_of_commute_pre hf hΩf fun y hy hys => hcent y (hrange ▸ hy) hys
  refine ⟨pre f ⁅O, O⁆, fStarOf_eq_of_simple_normal (pre_le f _) hNn hNs hnab hC, hNn, hNs,
    hnab, ?_, ?_⟩
  · intro a b ha hb r s hr hs hfa hfb
    refine mem_pre.mpr ⟨G₀.mul_mem ha hb, ?_⟩
    have e2 : f ⟨a * b, G₀.mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := by
      rw [← map_mul]
      rfl
    rw [e2, hfa, hfb]
    exact hrefl2 r s hr hs
  · intro t ht r hr hft
    exact mem_pre_or_mul_mem_pre hΩf hidx' ht (by rw [hft]; exact hrefl r hr)

theorem orth_plus_core [Finite G₀] [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : finrank K W = 4) (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hplus : ∃ U : Submodule K W, finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0) (h4 : 4 ≤ Nat.card K)
    (f : ↥G₀ →* (W ≃ₗ[K] W)) (hf : Function.Injective f)
    (hrange : f.range = TauCeti.QuadraticMap.orthogonalGroup Q) :
    Nonempty (↥(fStarOf G₀) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨ρ, hρinj, hρO, hidx, -, -, -, -, -, -, -, hcent⟩ :=
    OrthPlus.exists_omega_plus hdim hnd hplus
  set ρ₁ := ρ.comp (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
    (Matrix.SpecialLinearGroup (Fin 2) K)) with hρ₁
  set ρ₂ := ρ.comp (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
    (Matrix.SpecialLinearGroup (Fin 2) K)) with hρ₂
  have hρf : ρ.range ≤ f.range := hrange ▸ hρO
  have hρ₁le : ρ₁.range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hρ₂le : ρ₂.range ≤ ρ.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hS₁f : ρ₁.range ≤ f.range := hρ₁le.trans hρf
  have hS₂f : ρ₂.range ≤ f.range := hρ₂le.trans hρf
  have hsplit : ∀ x y, ρ (x, y) = ρ₁ x * ρ₂ y := fun x y => by
    rw [hρ₁, hρ₂, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hsplit' : ∀ x y, ρ (x, y) = ρ₂ y * ρ₁ x := fun x y => by
    rw [hρ₁, hρ₂, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hsup : ρ₁.range ⊔ ρ₂.range = ρ.range := by
    refine le_antisymm (sup_le hρ₁le hρ₂le) ?_
    rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hsplit]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ ⟨y, rfl⟩
  have hcomm : ∀ x ∈ ρ₁.range, ∀ y ∈ ρ₂.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← hsplit, ← hsplit']
  have hdisj : ρ₁.range ⊓ ρ₂.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Subgroup.mem_inf.mp hx
    have hab' : ρ (a, 1) = ρ (1, b) := ha.trans hb.symm
    have hab := hρinj hab'
    have ha1 : a = 1 := congrArg Prod.fst hab
    rw [Subgroup.mem_bot, ← ha, ha1, map_one]
  have hinj₁ : Function.Injective ρ₁ := fun x y h => by
    have h' : ρ (x, 1) = ρ (y, 1) := h
    exact congrArg Prod.fst (hρinj h')
  have hinj₂ : Function.Injective ρ₂ := fun x y h => by
    have h' : ρ (1, x) = ρ (1, y) := h
    exact congrArg Prod.snd (hρinj h')
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
  obtain ⟨e₁⟩ := nonempty_mulEquiv_pre hf hS₁f
  obtain ⟨e₂⟩ := nonempty_mulEquiv_pre hf hS₂f
  have ε₁ : ↥(pre f ρ₁.range) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e₁.trans (MonoidHom.ofInjective hinj₁).symm
  have ε₂ : ↥(pre f ρ₂.range) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e₂.trans (MonoidHom.ofInjective hinj₂).symm
  have hN : pre f ρ₁.range ⊔ pre f ρ₂.range = pre f ρ.range := by
    rw [← pre_sup hS₁f hS₂f, hsup]
  have hidx' : (ρ.range.subgroupOf f.range).index = 2 := by
    rw [hrange]
    exact hidx
  have hNn : ∀ g ∈ G₀, ∀ n ∈ pre f ρ₁.range ⊔ pre f ρ₂.range,
      g * n * g⁻¹ ∈ pre f ρ₁.range ⊔ pre f ρ₂.range := by
    rw [hN]
    exact conj_mem_pre (conj_mem_of_index_two hρf hidx')
  have hC : ∀ g ∈ G₀, (∀ n ∈ pre f ρ₁.range ⊔ pre f ρ₂.range, g * n = n * g) → g = 1 := by
    rw [hN]
    refine eq_one_of_commute_pre hf hρf fun y hy hys => hcent y ?_ fun z => hys _ ⟨z, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hrange ▸ hy)
  obtain ⟨hF, ⟨e⟩⟩ := fStarOf_eq_of_two_simple (sup_le (pre_le f _) (pre_le f _)) hNn
    (commute_pre hf hcomm) (pre_inf_eq_bot hf hdisj) ε₁.isSimpleGroup ε₂.isSimpleGroup
    (nonabelian_of_mulEquiv ε₁ (exists_sl2_ne_comm K))
    (nonabelian_of_mulEquiv ε₂ (exists_sl2_ne_comm K)) hC
  rw [hF]
  exact ⟨e.trans (ε₁.prodCongr ε₂)⟩

end CFSG.Quasithin.SimsG4.G49
