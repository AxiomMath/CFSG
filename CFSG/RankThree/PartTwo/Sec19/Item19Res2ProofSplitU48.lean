module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofFlag
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Outer
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Descent
import CFSG.RankThree.PartTwo.Sec19.KS1919U48

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK)

section U48

theorem conj_injective_SU4 : Function.Injective (MulAut.conj : SU4 →* MulAut SU4) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcen : g ∈ Subgroup.center SU4 := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut SU4 => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rw [center_SU4, Subgroup.mem_bot] at hcen
  exact hcen

theorem exists_fixed_E27_of_fieldFactor_ne_one {α : MulAut SU4} (hα3 : α ^ 3 = 1)
    (hα1 : fieldFactor4 α ≠ 1) :
    ∃ B : Subgroup SU4, CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 27 ∧
      ∀ y ∈ B, α y = y := by
  set φ : K ≃+* K := fieldFactor4 α with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hα3, map_one]
  obtain ⟨g₀, hg₀⟩ := exists_conj_field4 α
  have hα : ∀ x, α x = g₀ * fieldSU4 φ x * g₀⁻¹ := fun x => Subtype.ext (by rw [hg₀ x]; rfl)
  have hN : g₀ * fieldSU4 φ g₀ * fieldSU4 φ (fieldSU4 φ g₀) = 1 :=
    mul_apply_apply_eq_one center_SU4 g₀ hα (by rw [fieldSU4_pow, hφ3, fieldSU4_one]) hα3
  have hN' : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *
      (((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ).map φ = 1 := by
    have := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hN
    simpa [coe_fieldSU4, coe_glAut] using this
  obtain ⟨H, hH, hgH, -⟩ := exists_fixed_orthonormal_eigenbasis
    (unitary_of_mem_SU4 g₀) hφ3 hα1 hN' (p := 1) (by simp) (by simp) (by simp)
  let Hu : GL (Fin 4) K := ⟨H, (H.map hK.bar)ᵀ, mul_eq_one_comm.mp hH, hH⟩
  have hHu : Hu ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary]
    simpa using hH
  obtain ⟨h₀, hh₀⟩ := exists_SU4_conj_eq hHu
  refine ⟨Dstd.map (MulAut.conj h₀).toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ Dstd isElemAbelian_Dstd,
    by rw [Subgroup.card_map_of_injective (MulAut.conj h₀).injective, card_Dstd], ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply Subtype.ext
  rw [hg₀]
  have e1 : (((MulAut.conj h₀) x : SU4) : GL (Fin 4) K) = Hu * (x : GL (Fin 4) K) * Hu⁻¹ :=
    (hh₀ (x : GL (Fin 4) K)).symm
  have e2 : glAut φ (x : GL (Fin 4) K) = x := by
    have := congrArg (fun y : SU4 => (y : GL (Fin 4) K)) (fieldSU4_apply_of_mem_Dstd hφ3 hx)
    simpa [coe_fieldSU4] using this
  have e3 : (g₀ : GL (Fin 4) K) * glAut φ Hu = Hu := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut]
    exact hgH
  change (g₀ : GL (Fin 4) K) * glAut φ (((MulAut.conj h₀) x : SU4) : GL (Fin 4) K) *
    (g₀ : GL (Fin 4) K)⁻¹ = (((MulAut.conj h₀) x : SU4) : GL (Fin 4) K)
  rw [e1, map_mul, map_mul, map_inv, e2]
  calc (g₀ : GL (Fin 4) K) * (glAut φ Hu * x * (glAut φ Hu)⁻¹) * (g₀ : GL (Fin 4) K)⁻¹ =
      ((g₀ : GL (Fin 4) K) * glAut φ Hu) * x * ((g₀ : GL (Fin 4) K) * glAut φ Hu)⁻¹ := by
        group
    _ = Hu * x * Hu⁻¹ := by rw [e3]

theorem ks1919SplitAut_u48 {Y : Type} [Group Y] [Finite Y]
    (ψ : Y ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 3) (E : Subgroup (MulAut Y))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (F : Subgroup (MulAut Y))
    (hFE : F ≤ E) (hFinn : F ≤ (MulAut.conj : Y →* MulAut Y).range) (hF9 : Nat.card F = 9)
    (c : MulAut Y) (hcE : c ∈ E) (hcF : c ∉ F) (P : Subgroup Y) (hP : IsProperParabolic P) :
    ¬ ∀ y : Y, c y = y → y ∈ P := by
  intro hfixP
  set Ψ : Y ≃* SU4 := ψ.trans equivSU4 with hΨ
  set Γ : MulAut Y ≃* MulAut SU4 := MulAut.congr Ψ with hΓ
  set α := Γ c with hα
  have hc3 : c ^ 3 = 1 := hE.2 c hcE
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hc3, map_one]
  set E₁ := E.map Γ.toMonoidHom with hE₁
  have hcommE₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpE₁ : ∀ x ∈ E₁, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hαE₁ : α ∈ E₁ := ⟨c, hcE, rfl⟩
  obtain ⟨B, hBe, hB27, hBfix⟩ : ∃ B : Subgroup SU4, CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 27 ∧ ∀ y ∈ B, α y = y := by
    by_cases hφ : fieldFactor4 α = 1
    · set I := (MulAut.conj : SU4 →* MulAut SU4).range with hI
      have hαI : α ∈ I := mem_range_conj_of_fieldFactor4_eq_one hφ
      set F₁ := F.map Γ.toMonoidHom with hF₁
      set E' := E₁ ⊓ I with hE'
      have hF₁I : F₁ ≤ I := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨y, rfl⟩ := hFinn hx
        change Γ (MulAut.conj y) ∈ I
        rw [hΓ, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]
        exact ⟨Ψ y, rfl⟩
      have hF₁E' : F₁ ≤ E' := le_inf (Subgroup.map_mono hFE) hF₁I
      have hαE' : α ∈ E' := ⟨hαE₁, hαI⟩
      have hαF₁ : α ∉ F₁ := by
        rintro ⟨x, hx, hxc⟩
        exact hcF (Γ.injective hxc ▸ hx)
      have hcardF₁ : Nat.card F₁ = 9 := by
        rw [hF₁, Subgroup.card_map_of_injective Γ.injective, hF9]
      have hcardE₁ : Nat.card E₁ = 27 := by
        rw [hE₁, Subgroup.card_map_of_injective Γ.injective, hE27]
      have hdvd1 : Nat.card E' ∣ 27 := hcardE₁ ▸ Subgroup.card_dvd_of_le inf_le_left
      have hdvd2 : 9 ∣ Nat.card E' := hcardF₁ ▸ Subgroup.card_dvd_of_le hF₁E'
      have hne9 : Nat.card E' ≠ 9 := by
        intro h9
        have : F₁ = E' := Subgroup.eq_of_le_of_card_ge hF₁E' (by rw [h9, hcardF₁])
        exact hαF₁ (this ▸ hαE')
      have h27 : Nat.card E' = 27 := by
        obtain ⟨k, hk⟩ := hdvd2
        have hk27 : 9 * k ≤ 27 := hk ▸ Nat.le_of_dvd (by norm_num) hdvd1
        rw [hk] at hdvd1 hne9 ⊢
        have hk3 : k ≤ 3 := by omega
        interval_cases k <;> first | rfl | omega
      refine ⟨E'.comap MulAut.conj, ⟨⟨⟨fun a b => Subtype.ext (conj_injective_SU4 ?_)⟩⟩,
        fun a ha => conj_injective_SU4 ?_⟩, ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hcommE₁ _ a.2.1 _ b.2.1
      · rw [map_pow, map_one]
        exact hexpE₁ _ ha.1
      · have hmap := Subgroup.map_comap_eq_self
          (show E' ≤ (MulAut.conj : SU4 →* MulAut SU4).range from inf_le_right)
        rw [← h27]
        conv_rhs => rw [← hmap]
        rw [Subgroup.card_map_of_injective conj_injective_SU4]
      · intro y hy
        exact apply_eq_of_commute_conj center_SU4 (hcommE₁ α hαE₁ _ hy.1)
    · exact exists_fixed_E27_of_fieldFactor_ne_one hα3 hφ
  have hP' : IsProperParabolic (P.map Ψ.toMonoidHom) := isProperParabolic_map_equiv Ψ hP
  have hBP : B ≤ P.map Ψ.toMonoidHom := by
    intro y hy
    have hcy : c (Ψ.symm y) = Ψ.symm y := by
      have h1 : Ψ (c (Ψ.symm y)) = y := hBfix y hy
      have h2 := congrArg Ψ.symm h1
      rwa [MulEquiv.symm_apply_apply] at h2
    exact ⟨Ψ.symm y, hfixP _ hcy, by simp⟩
  have hle := ks1919U48 SU4 ⟨equivSU4.symm⟩ _ hP' B hBP
    (fun x hx y hy => congrArg Subtype.val (hBe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hBe.2
  omega

end U48

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
