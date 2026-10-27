module

public import CFSG.Timmesfeld.Transvection.OddSU3Chord
import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.ARS.CaseHAlign
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValField

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseH CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LocalAnalysis.UniquenessCase
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Timmesfeld.RankOne
  CFSG.SeitzReduction.F4Pilot Matrix Subgroup
open Pres

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

section Chord

variable (hζ0 : (1 : F) ≠ 0)
  (hζ : unitaryInvolution F 2 n (1 : F) = -(1 : F))

private theorem crd_two_inl :
    crd (Sum.inl (0 : Fin (2 / 2)) : Fin (2 / 2) ⊕ Fin (2 / 2)) = 0 := by
  rw [crd_inl]
  rfl

private theorem crd_two_inr :
    crd (Sum.inr (0 : Fin (2 / 2)) : Fin (2 / 2) ⊕ Fin (2 / 2)) = 1 := by
  rw [crd_inr]
  rfl

private theorem hypEquiv_upperElt (s : fixedSubfield F 2 n) :
    hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ
        (upperElt (fixedSubfield F 2 n) s) =
      suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) (s : F) := by
  apply mat_injective
  rw [hypEquiv_apply, mat_apply, coe_hypHom]
  have h0 : (s : F) + unitaryInvolution F 2 n (s : F) = 0 := by
    rw [(mem_fixedSubfield).1 s.2, CharTwo.add_self_eq_zero]
  rw [mat_suLong (σ := unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) h0,
    Sum.swap_inl, crd_two_inl, crd_two_inr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, upperElt]

private theorem hypEquiv_lowerElt (s : fixedSubfield F 2 n) :
    hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ
        (lowerElt (fixedSubfield F 2 n) s) =
      suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) (s : F) := by
  apply mat_injective
  rw [hypEquiv_apply, mat_apply, coe_hypHom]
  have h0 : (s : F) + unitaryInvolution F 2 n (s : F) = 0 := by
    rw [(mem_fixedSubfield).1 s.2, CharTwo.add_self_eq_zero]
  rw [mat_suLong (σ := unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) h0,
    Sum.swap_inr, crd_two_inl, crd_two_inr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, lowerElt]

private theorem hypEquiv_symm_suLong_inl {c : F} (hc : unitaryInvolution F 2 n c = c) :
    (hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ).symm
        (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c) =
      upperElt (fixedSubfield F 2 n) ⟨c, hc⟩ := by
  apply (hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ).injective
  rw [MulEquiv.apply_symm_apply, hypEquiv_upperElt hζ0 hζ]

private theorem hypEquiv_symm_suLong_inr {c : F} (hc : unitaryInvolution F 2 n c = c) :
    (hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ).symm
        (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c) =
      lowerElt (fixedSubfield F 2 n) ⟨c, hc⟩ := by
  apply (hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ).injective
  rw [MulEquiv.apply_symm_apply, hypEquiv_lowerElt hζ0 hζ]

end Chord

private theorem su2_mulAut_aligned_lift
    {α : MulAut (SU (unitaryInvolution F 2 n) 2)}
    {e : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 n) ≃*
      SU (unitaryInvolution F 2 n) 2}
    {α' : MulAut (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 n))}
    (hα_apply : ∀ A, e (α' A) = α (e A))
    (hup : ∀ s : fixedSubfield F 2 n,
      e (upperElt (fixedSubfield F 2 n) s) =
        suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) (s : F))
    (hlo : ∀ s : fixedSubfield F 2 n,
      e (lowerElt (fixedSubfield F 2 n) s) =
        suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) (s : F))
    {ε : fixedSubfield F 2 n} {τ : fixedSubfield F 2 n ≃+* fixedSubfield F 2 n}
    (hε : ε ≠ 0)
    (hαu : ∀ s, α' (upperElt (fixedSubfield F 2 n) s) =
      upperElt (fixedSubfield F 2 n) (ε * τ s))
    (hαl : ∀ s, α' (lowerElt (fixedSubfield F 2 n) s) =
      lowerElt (fixedSubfield F 2 n) (ε⁻¹ * τ s)) :
    ∃ ε' : F, ∃ τ' : F ≃+* F, ε' ≠ 0 ∧ unitaryInvolution F 2 n ε' = ε' ∧
      (∀ c, τ' (unitaryInvolution F 2 n c) = unitaryInvolution F 2 n (τ' c)) ∧
      (∀ c, unitaryInvolution F 2 n c = c →
        α (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c) =
          suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) (ε' * τ' c)) ∧
      ∀ c, unitaryInvolution F 2 n c = c →
        α (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c) =
          suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) (ε'⁻¹ * τ' c) := by
  let σ : F ≃+* F := unitaryInvolution F 2 n
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow τ
  let τF : F ≃+* F := iterateFrobeniusEquiv F 2 i
  have hτ_apply : ∀ x : fixedSubfield F 2 n, ((τ x : fixedSubfield F 2 n) : F) = τF (x : F) := by
    intro x
    rw [hi x, iterateFrobeniusEquiv_def]
    exact map_pow (fixedSubfield F 2 n).subtype x (2 ^ i)
  have hτ : ∀ c, τF (σ c) = σ (τF c) := by
    intro c
    have h1 : τF (σ c) = (σ c) ^ 2 ^ i := iterateFrobeniusEquiv_def F 2 i (σ c)
    have h2 : τF c = c ^ 2 ^ i := iterateFrobeniusEquiv_def F 2 i c
    rw [h1, h2, map_pow]
  refine ⟨(ε : F), τF, ?_, ?_, hτ, ?_, ?_⟩
  · intro h
    exact hε (by simpa using h)
  · exact ε.2
  · intro c hc
    have hu := congrArg e (hαu ⟨c, hc⟩)
    calc α (suLong σ (Sum.inl (0 : Fin (2 / 2))) c)
        = e (α' (upperElt (fixedSubfield F 2 n) ⟨c, hc⟩)) := by
          rw [hα_apply, hup ⟨c, hc⟩]
      _ = e (upperElt (fixedSubfield F 2 n) (ε * τ ⟨c, hc⟩)) := hu
      _ = suLong σ (Sum.inl (0 : Fin (2 / 2))) ((ε * τ ⟨c, hc⟩ : fixedSubfield F 2 n) : F) :=
          hup (ε * τ ⟨c, hc⟩)
      _ = suLong σ (Sum.inl (0 : Fin (2 / 2))) ((ε : F) * τF c) := by
          congr 1
          rw [Subfield.coe_mul, hτ_apply]
  · intro c hc
    have hl := congrArg e (hαl ⟨c, hc⟩)
    calc α (suLong σ (Sum.inr (0 : Fin (2 / 2))) c)
        = e (α' (lowerElt (fixedSubfield F 2 n) ⟨c, hc⟩)) := by
          rw [hα_apply, hlo ⟨c, hc⟩]
      _ = e (lowerElt (fixedSubfield F 2 n) (ε⁻¹ * τ ⟨c, hc⟩)) := hl
      _ = suLong σ (Sum.inr (0 : Fin (2 / 2))) ((ε⁻¹ * τ ⟨c, hc⟩ : fixedSubfield F 2 n) : F) :=
          hlo (ε⁻¹ * τ ⟨c, hc⟩)
      _ = suLong σ (Sum.inr (0 : Fin (2 / 2))) ((ε : F)⁻¹ * τF c) := by
          congr 1
          rw [Subfield.coe_mul, Subfield.coe_inv, hτ_apply]

theorem su2_mulAut_aligned (hFn : Nat.card F = (2 ^ n) ^ 2)
    (α : MulAut (SU (unitaryInvolution F 2 n) 2))
    (ht : (su2Top (unitaryInvolution F 2 n)).map α.toMonoidHom =
      su2Top (unitaryInvolution F 2 n))
    (hb : (su2Bot (unitaryInvolution F 2 n)).map α.toMonoidHom =
      su2Bot (unitaryInvolution F 2 n)) :
    ∃ ε : F, ∃ τ : F ≃+* F, ε ≠ 0 ∧ unitaryInvolution F 2 n ε = ε ∧
      (∀ c, τ (unitaryInvolution F 2 n c) = unitaryInvolution F 2 n (τ c)) ∧
      (∀ c, unitaryInvolution F 2 n c = c →
        α (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c) =
          suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) (ε * τ c)) ∧
      ∀ c, unitaryInvolution F 2 n c = c →
        α (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c) =
          suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) (ε⁻¹ * τ c) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  have hζ0 : (1 : F) ≠ 0 := one_ne_zero
  have hζ : σ (1 : F) = -(1 : F) := by
    dsimp only [σ]
    rw [unitaryInvolution_apply, one_pow, CharTwo.neg_eq]
  let K₀ : Subfield F := fixedSubfield F 2 n
  haveI : CharP K₀ 2 := inferInstance
  let e : Matrix.SpecialLinearGroup (Fin 2) K₀ ≃* SU σ 2 :=
    hypEquiv (p := 2) (f := n) (ζ := (1 : F)) hζ0 hζ
  let α' : MulAut (Matrix.SpecialLinearGroup (Fin 2) K₀) :=
    e.trans (α.trans e.symm)
  have hα_apply : ∀ A, e (α' A) = α (e A) := by
    intro A
    simp [α', MulEquiv.trans_apply]
  have hU : ∀ s : K₀, ∃ t, α' (upperElt K₀ s) = upperElt K₀ t := by
    intro s
    have hs : σ (s : F) = (s : F) := (mem_fixedSubfield).1 s.2
    have hmem : α (suLong σ (Sum.inl (0 : Fin (2 / 2))) (s : F)) ∈ su2Top σ := by
      rw [← ht]
      exact Subgroup.mem_map_of_mem _ ((mem_su2Top_iff (σ := σ)).2 ⟨(s : F), hs, rfl⟩)
    obtain ⟨c, hc, hcx⟩ := (mem_su2Top_iff (σ := σ)).1 hmem
    refine ⟨⟨c, hc⟩, ?_⟩
    show e.symm (α (e (upperElt K₀ s))) = upperElt K₀ ⟨c, hc⟩
    rw [hypEquiv_upperElt hζ0 hζ s, ← hcx]
    exact hypEquiv_symm_suLong_inl hζ0 hζ hc
  have hL : ∀ s : K₀, ∃ t, α' (lowerElt K₀ s) = lowerElt K₀ t := by
    intro s
    have hs : σ (s : F) = (s : F) := (mem_fixedSubfield).1 s.2
    have hmem : α (suLong σ (Sum.inr (0 : Fin (2 / 2))) (s : F)) ∈ su2Bot σ := by
      rw [← hb]
      exact Subgroup.mem_map_of_mem _ ((mem_su2Bot_iff (σ := σ)).2 ⟨(s : F), hs, rfl⟩)
    obtain ⟨c, hc, hcx⟩ := (mem_su2Bot_iff (σ := σ)).1 hmem
    refine ⟨⟨c, hc⟩, ?_⟩
    show e.symm (α (e (lowerElt K₀ s))) = lowerElt K₀ ⟨c, hc⟩
    rw [hypEquiv_lowerElt hζ0 hζ s, ← hcx]
    exact hypEquiv_symm_suLong_inr hζ0 hζ hc
  obtain ⟨ε, τ, hε, hαu, hαl⟩ :=
    exists_aligned_SL2 (E := K₀) α' hU hL
  exact su2_mulAut_aligned_lift hα_apply
    (fun s => hypEquiv_upperElt hζ0 hζ s) (fun s => hypEquiv_lowerElt hζ0 hζ s)
    hε hαu hαl

private theorem suCongr_suLong (τ : F ≃+* F) {σ : F ≃+* F}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) {m : ℕ} (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F}
    (hc : c + σ c = 0) :
    suCongr τ hτ m (suLong σ a c) = suLong σ a (τ c) := by
  have hc' : τ c + σ (τ c) = 0 := by
    rw [← hτ, ← map_add, hc, map_zero]
  apply mat_injective
  rw [mat_apply, coe_suCongr, ← mat_apply, mat_suLong a hc, mat_suLong a hc']
  rw [Matrix.map_add τ (map_add τ), Matrix.map_one τ (map_zero τ) (map_one τ)]
  simp [Matrix.map_single]


private theorem su3Conj_suCongr_suLong {σ : F ≃+* F} {h : SU σ 3} {d : Fin 3 → F}
    {τ : F ≃+* F} (hτ : ∀ c, τ (σ c) = σ (τ c))
    (hmatd : mat σ 3 h = diagonal d) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (a : Fin (3 / 2) ⊕ Fin (3 / 2)) {c : F} (hc : c + σ c = 0) :
    ((MulAut.conj h) * (suCongr τ hτ 3)) (suLong σ a c) =
      suLong σ a (d (crd a) * τ c * (d (crd (Sum.swap a)))⁻¹) := by
  have hcongr : suCongr τ hτ 3 (suLong σ a c) = suLong σ a (τ c) :=
    suCongr_suLong τ hτ a hc
  have hconj := conj_suLong_of_mat_diagonal hmatd hd a (τ c)
  calc ((MulAut.conj h) * (suCongr τ hτ 3)) (suLong σ a c)
      = h * suCongr τ hτ 3 (suLong σ a c) * h⁻¹ := by
        simp [MulAut.mul_apply, MulAut.conj_apply]
    _ = h * suLong σ a (τ c) * h⁻¹ := by rw [hcongr]
    _ = suLong σ a (d (crd a) * τ c * (d (crd (Sum.swap a)))⁻¹) := hconj

theorem exists_su3MulAut (hFn : Nat.card F = (2 ^ n) ^ 2) {ε : F} (hε : ε ≠ 0)
    (hεσ : unitaryInvolution F 2 n ε = ε) (τ : F ≃+* F)
    (hτ : ∀ c, τ (unitaryInvolution F 2 n c) = unitaryInvolution F 2 n (τ c)) :
    ∃ β : MulAut (SU (unitaryInvolution F 2 n) 3),
      (∀ c, unitaryInvolution F 2 n c = c →
        β (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
          suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (ε * τ c)) ∧
      ∀ c, unitaryInvolution F 2 n c = c →
        β (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) =
          suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) (ε⁻¹ * τ c) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  obtain ⟨t, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hFn hεσ hε
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at ht
    exact hε ht.symm
  have hHcard : Nat.card (uc22pwsu3H σ) = Nat.card Fˣ := by
    rw [card_levelTorus_three (p := 2) (f := n) hFn,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hFn]
  obtain ⟨h, hh, hmat⟩ := uc22pwsu3H_exists_entry hHcard (Units.mk0 t ht0)
  let d : Fin 3 → F := ![t, σ t / t, (σ t)⁻¹]
  have hmatd : mat σ 3 h = diagonal d := by
    simpa [d, Units.val_mk0] using hmat
  have hd : ∀ s, σ (d s) * d (Fin.rev s) = 1 := by
    intro s
    fin_cases s <;> simp [d, hσ, ht0]
  let β : MulAut (SU σ 3) := (MulAut.conj h) * (suCongr τ hτ 3)
  have hβ₁ : ∀ c, σ c = c →
      β (suLong σ (Sum.inl (0 : Fin (3 / 2))) c) =
        suLong σ (Sum.inl (0 : Fin (3 / 2))) (ε * τ c) := by
    intro c hc
    have hc0 : c + σ c = 0 := by rw [hc, CharTwo.add_self_eq_zero]
    change ((MulAut.conj h) * (suCongr τ hτ 3)) (suLong σ (Sum.inl (0 : Fin (3 / 2))) c) =
      suLong σ (Sum.inl (0 : Fin (3 / 2))) (ε * τ c)
    rw [su3Conj_suCongr_suLong hτ hmatd hd (Sum.inl (0 : Fin (3 / 2))) hc0]
    change suLong σ (Sum.inl (0 : Fin (3 / 2))) (d 0 * τ c * (d 2)⁻¹) =
      suLong σ (Sum.inl (0 : Fin (3 / 2))) (ε * τ c)
    congr 1
    calc d 0 * τ c * (d 2)⁻¹ = (σ t * t) * τ c := by simp [d]; ring
      _ = ε * τ c := by rw [ht]
  have hβ₂ : ∀ c, σ c = c →
      β (suLong σ (Sum.inr (0 : Fin (3 / 2))) c) =
        suLong σ (Sum.inr (0 : Fin (3 / 2))) (ε⁻¹ * τ c) := by
    intro c hc
    have hc0 : c + σ c = 0 := by rw [hc, CharTwo.add_self_eq_zero]
    change ((MulAut.conj h) * (suCongr τ hτ 3)) (suLong σ (Sum.inr (0 : Fin (3 / 2))) c) =
      suLong σ (Sum.inr (0 : Fin (3 / 2))) (ε⁻¹ * τ c)
    rw [su3Conj_suCongr_suLong hτ hmatd hd (Sum.inr (0 : Fin (3 / 2))) hc0]
    change suLong σ (Sum.inr (0 : Fin (3 / 2))) (d 2 * τ c * (d 0)⁻¹) =
      suLong σ (Sum.inr (0 : Fin (3 / 2))) (ε⁻¹ * τ c)
    congr 1
    calc d 2 * τ c * (d 0)⁻¹ = (σ t * t)⁻¹ * τ c := by simp [d]; field_simp
      _ = ε⁻¹ * τ c := by rw [ht]
  exact ⟨β, hβ₁, hβ₂⟩

theorem su3Chord_comp_of_aligned (hFn : Nat.card F = (2 ^ n) ^ 2)
    {α : MulAut (SU (unitaryInvolution F 2 n) 2)}
    {β : MulAut (SU (unitaryInvolution F 2 n) 3)} {ε : F} {τ : F ≃+* F}
    (hα₁ : ∀ c, unitaryInvolution F 2 n c = c →
      α (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) c) =
        suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (2 / 2))) (ε * τ c))
    (hα₂ : ∀ c, unitaryInvolution F 2 n c = c →
      α (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) c) =
        suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (2 / 2))) (ε⁻¹ * τ c))
    (hβ₁ : ∀ c, unitaryInvolution F 2 n c = c →
      β (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
        suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (ε * τ c))
    (hβ₂ : ∀ c, unitaryInvolution F 2 n c = c →
      β (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) =
        suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) (ε⁻¹ * τ c)) :
    β.toMonoidHom.comp (su3Chord (unitaryInvolution F 2 n)) =
      (su3Chord (unitaryInvolution F 2 n)).comp α.toMonoidHom := by
  let σ := unitaryInvolution F 2 n
  have htop : ∀ x ∈ su2Top σ,
      (β.toMonoidHom.comp (su3Chord σ)) x = ((su3Chord σ).comp α.toMonoidHom) x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := (mem_su2Top_iff (σ := σ)).1 hx
    show β (su3Chord σ (suLong σ (Sum.inl (0 : Fin (2 / 2))) c)) =
      su3Chord σ (α (suLong σ (Sum.inl (0 : Fin (2 / 2))) c))
    rw [su3Chord_suLong_inl, hβ₁ c hc, hα₁ c hc, su3Chord_suLong_inl]
  have hbot : ∀ x ∈ su2Bot σ,
      (β.toMonoidHom.comp (su3Chord σ)) x = ((su3Chord σ).comp α.toMonoidHom) x := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := (mem_su2Bot_iff (σ := σ)).1 hx
    show β (su3Chord σ (suLong σ (Sum.inr (0 : Fin (2 / 2))) c)) =
      su3Chord σ (α (suLong σ (Sum.inr (0 : Fin (2 / 2))) c))
    rw [su3Chord_suLong_inr, hβ₂ c hc, hα₂ c hc, su3Chord_suLong_inr]
  apply MonoidHom.eq_of_eqOn_dense
    (s := ((su2Top σ : Set (SU σ 2)) ∪ (su2Bot σ : Set (SU σ 2))))
  · rw [← Subgroup.sup_eq_closure, su2Top_sup_su2Bot hFn]
  · intro x hx
    rcases hx with hx | hx
    · exact htop x hx
    · exact hbot x hx

theorem map_su3Top_of_aligned {β : MulAut (SU (unitaryInvolution F 2 n) 3)} {ε : F}
    {τ : F ≃+* F} (hε : ε ≠ 0) (hεσ : unitaryInvolution F 2 n ε = ε)
    (hτ : ∀ c, τ (unitaryInvolution F 2 n c) = unitaryInvolution F 2 n (τ c))
    (hβ₁ : ∀ c, unitaryInvolution F 2 n c = c →
      β (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
        suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (ε * τ c))
    (hβ₂ : ∀ c, unitaryInvolution F 2 n c = c →
      β (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) =
        suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) (ε⁻¹ * τ c)) :
    (su3Top (unitaryInvolution F 2 n)).map β.toMonoidHom = su3Top (unitaryInvolution F 2 n) ∧
      (su3Bot (unitaryInvolution F 2 n)).map β.toMonoidHom =
        su3Bot (unitaryInvolution F 2 n) := by
  let σ := unitaryInvolution F 2 n
  have hτinv : ∀ c, σ (τ.symm c) = τ.symm (σ c) := by
    intro c
    apply τ.injective
    rw [hτ (τ.symm c), τ.apply_symm_apply, τ.apply_symm_apply]
  constructor
  · refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su3Top_iff (σ := σ)).1 hx
      exact (mem_su3Top_iff (σ := σ)).2
        ⟨ε * τ c, by rw [map_mul, hεσ, (hτ c).symm, hc], (hβ₁ c hc).symm⟩
    · intro y hy
      obtain ⟨c', hc', rfl⟩ := (mem_su3Top_iff (σ := σ)).1 hy
      set c : F := τ.symm (ε⁻¹ * c') with hcdef
      have hcfix : σ c = c := by
        rw [hcdef, hτinv, map_mul, map_inv₀, hεσ, hc']
      refine ⟨suLong σ (Sum.inl (0 : Fin (3 / 2))) c,
        (mem_su3Top_iff (σ := σ)).2 ⟨c, hcfix, rfl⟩, ?_⟩
      change β (suLong σ (Sum.inl (0 : Fin (3 / 2))) c) = suLong σ (Sum.inl (0 : Fin (3 / 2))) c'
      rw [hβ₁ c hcfix]
      congr 1
      rw [hcdef, τ.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  · refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su3Bot_iff (σ := σ)).1 hx
      exact (mem_su3Bot_iff (σ := σ)).2
        ⟨ε⁻¹ * τ c, by rw [map_mul, map_inv₀, hεσ, (hτ c).symm, hc], (hβ₂ c hc).symm⟩
    · intro y hy
      obtain ⟨c', hc', rfl⟩ := (mem_su3Bot_iff (σ := σ)).1 hy
      set c : F := τ.symm (ε * c') with hcdef
      have hcfix : σ c = c := by
        rw [hcdef, hτinv, map_mul, hεσ, hc']
      refine ⟨suLong σ (Sum.inr (0 : Fin (3 / 2))) c,
        (mem_su3Bot_iff (σ := σ)).2 ⟨c, hcfix, rfl⟩, ?_⟩
      change β (suLong σ (Sum.inr (0 : Fin (3 / 2))) c) = suLong σ (Sum.inr (0 : Fin (3 / 2))) c'
      rw [hβ₂ c hcfix]
      congr 1
      rw [hcdef, τ.apply_symm_apply, ← mul_assoc, inv_mul_cancel₀ hε, one_mul]

end CFSG.Timmesfeld.Transvection
