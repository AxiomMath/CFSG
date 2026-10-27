module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Field
public import CFSG.RankThree.PartOne.U5K.Hyp.Dlin
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

section Vocabulary

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

abbrev cj5 (s : hypPSU h 2 1) : MulAut (hypPSU h 2 1) := MulAut.conj s

abbrev fa5 (φ : K ≃+* K) : MulAut (hypPSU h 2 1) := fieldP h φ

@[expose] def FStab5 (B : Subgroup (hypPSU h 2 1)) : Prop :=
  ∀ (φ : K ≃+* K) (x : hypPSU h 2 1), fa5 h φ x ∈ B ↔ x ∈ B

theorem aut5_mul_cj5_mul_inv (β : MulAut (hypPSU h 2 1)) (s : hypPSU h 2 1) :
    β * cj5 h s * β⁻¹ = cj5 h (β s) := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem fa5_mul_cj5_mul_inv (φ : K ≃+* K) (s : hypPSU h 2 1) :
    fa5 h φ * cj5 h s * (fa5 h φ)⁻¹ = cj5 h (fa5 h φ s) :=
  aut5_mul_cj5_mul_inv h _ s

theorem fa5_mul (φ ψ : K ≃+* K) : fa5 h φ * fa5 h ψ = fa5 h (φ * ψ) :=
  ((fieldP h).map_mul φ ψ).symm

theorem fa5_one : fa5 h (1 : K ≃+* K) = 1 := (fieldP h).map_one

theorem fa5_inv (φ : K ≃+* K) : (fa5 h φ)⁻¹ = fa5 h φ⁻¹ := (map_inv (fieldP h) φ).symm

theorem cj5_mul (s t : hypPSU h 2 1) : cj5 h (s * t) = cj5 h s * cj5 h t :=
  map_mul (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)) s t

theorem cj5_one : cj5 h (1 : hypPSU h 2 1) = 1 :=
  map_one (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1))

theorem cj5_inv (s : hypPSU h 2 1) : cj5 h s⁻¹ = (cj5 h s)⁻¹ :=
  map_inv (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1)) s

theorem cj5_fa5_mul_cj5_fa5 (s t : hypPSU h 2 1) (φ ψ : K ≃+* K) :
    (cj5 h s * fa5 h φ) * (cj5 h t * fa5 h ψ) = cj5 h (s * fa5 h φ t) * fa5 h (φ * ψ) := by
  have e' : fa5 h φ * cj5 h t = cj5 h (fa5 h φ t) * fa5 h φ := by
    rw [← fa5_mul_cj5_mul_inv h φ t]
    group
  calc (cj5 h s * fa5 h φ) * (cj5 h t * fa5 h ψ) = cj5 h s * (fa5 h φ * cj5 h t) * fa5 h ψ := by
        simp only [mul_assoc]
    _ = cj5 h s * (cj5 h (fa5 h φ t) * fa5 h φ) * fa5 h ψ := by rw [e']
    _ = cj5 h s * cj5 h (fa5 h φ t) * (fa5 h φ * fa5 h ψ) := by simp only [mul_assoc]
    _ = cj5 h (s * fa5 h φ t) * fa5 h (φ * ψ) := by rw [fa5_mul, cj5_mul]

theorem inv_cj5_fa5 (s : hypPSU h 2 1) (φ : K ≃+* K) :
    (cj5 h s * fa5 h φ)⁻¹ = cj5 h (fa5 h φ⁻¹ s⁻¹) * fa5 h φ⁻¹ := by
  rw [_root_.mul_inv_rev, fa5_inv]
  have e := fa5_mul_cj5_mul_inv h φ⁻¹ s⁻¹
  rw [cj5_inv] at e
  rw [← e]
  simp

@[expose] def Ssd5 (B : Subgroup (hypPSU h 2 1)) (hB : FStab5 h B) (F : Subgroup (K ≃+* K)) :
    Subgroup (MulAut (hypPSU h 2 1)) where
  carrier := {α | ∃ s ∈ B, ∃ φ ∈ F, α = cj5 h s * fa5 h φ}
  mul_mem' := by
    rintro _ _ ⟨s, hs, φ, hφ, rfl⟩ ⟨t, ht, ψ, hψ, rfl⟩
    exact ⟨s * fa5 h φ t, B.mul_mem hs ((hB φ t).2 ht), φ * ψ, F.mul_mem hφ hψ,
      cj5_fa5_mul_cj5_fa5 h s t φ ψ⟩
  one_mem' := ⟨1, B.one_mem, 1, F.one_mem, by rw [cj5_one, fa5_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨s, hs, φ, hφ, rfl⟩
    exact ⟨fa5 h φ⁻¹ s⁻¹, (hB φ⁻¹ s⁻¹).2 (B.inv_mem hs), φ⁻¹, F.inv_mem hφ, inv_cj5_fa5 h s φ⟩

theorem Ssd5_mono {B B' : Subgroup (hypPSU h 2 1)} {hB : FStab5 h B} {hB' : FStab5 h B'}
    {F F' : Subgroup (K ≃+* K)} (hBB : B ≤ B') (hFF : F ≤ F') :
    Ssd5 h B hB F ≤ Ssd5 h B' hB' F' := by
  rintro _ ⟨s, hs, φ, hφ, rfl⟩
  exact ⟨s, hBB hs, φ, hFF hφ, rfl⟩

theorem cj5_mem_Ssd5 {B : Subgroup (hypPSU h 2 1)} {hB : FStab5 h B} {F : Subgroup (K ≃+* K)}
    {s : hypPSU h 2 1} (hs : s ∈ B) : cj5 h s ∈ Ssd5 h B hB F :=
  ⟨s, hs, 1, F.one_mem, by rw [fa5_one, mul_one]⟩

theorem fa5_mem_Ssd5 {B : Subgroup (hypPSU h 2 1)} {hB : FStab5 h B} {F : Subgroup (K ≃+* K)}
    {φ : K ≃+* K} (hφ : φ ∈ F) : fa5 h φ ∈ Ssd5 h B hB F :=
  ⟨1, B.one_mem, φ, hφ, by rw [cj5_one, one_mul]⟩

end Vocabulary

section Inj

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem fa5_mem_Dlin {φ : K ≃+* K} (hφ : fa5 h φ ∈ Dlin h) : φ = 1 := by
  have := (mem_Dlin_iff (hK := h) (x := inrGam h φ) rfl).1 hφ
  simpa [inrGam] using this

theorem cj5_mem_Dlin (s : hypPSU h 2 1) : cj5 h s ∈ Dlin h :=
  Pi_le_Dlin (by
    rw [Pi_eq_map]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top s))

theorem cj5_mul_fa5_inj (hZ : Subgroup.center (hypPSU h 2 1) = ⊥) {s t : hypPSU h 2 1}
    {φ ψ : K ≃+* K} (e : cj5 h s * fa5 h φ = cj5 h t * fa5 h ψ) : s = t ∧ φ = ψ := by
  have e1 : fa5 h φ = (cj5 h s)⁻¹ * (cj5 h t * fa5 h ψ) := by
    rw [← e]
    group
  have e2 : fa5 h (φ * ψ⁻¹) = cj5 h (s⁻¹ * t) := by
    rw [← fa5_mul, ← fa5_inv, e1, cj5_mul, cj5_inv]
    group
  have hφψ : φ * ψ⁻¹ = 1 := fa5_mem_Dlin h (e2 ▸ cj5_mem_Dlin h _)
  have hst : cj5 h (s⁻¹ * t) = 1 := by rw [← e2, hφψ, fa5_one]
  have hs : s⁻¹ * t = 1 := CFSG.RankThree.PartOne.U5K.Hyp.conj_injective hZ
    (hst.trans (map_one (MulAut.conj : hypPSU h 2 1 →* MulAut (hypPSU h 2 1))).symm)
  exact ⟨inv_mul_eq_one.1 hs, mul_inv_eq_one.1 hφψ⟩

theorem card_Ssd5 (hZ : Subgroup.center (hypPSU h 2 1) = ⊥) (B : Subgroup (hypPSU h 2 1))
    (hB : FStab5 h B) (F : Subgroup (K ≃+* K)) :
    Nat.card (Ssd5 h B hB F) = Nat.card B * Nat.card F := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : B × F => (⟨cj5 h (p.1 : hypPSU h 2 1) * fa5 h (p.2 : K ≃+* K),
      ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : Ssd5 h B hB F)) ⟨?_, ?_⟩)
  · rintro ⟨s, φ⟩ ⟨t, ψ⟩ e
    obtain ⟨e1, e2⟩ := cj5_mul_fa5_inj h hZ (congrArg Subtype.val e)
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · rintro ⟨_, s, hs, φ, hφ, rfl⟩
    exact ⟨(⟨s, hs⟩, ⟨φ, hφ⟩), rfl⟩

end Inj

end CFSG.Quasithin.H13.F431.Un.OL5
