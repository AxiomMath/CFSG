module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Aut

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

section Vocabulary

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

abbrev Xg : Type := ↥(gramSU h (miyamotoJ4 K))

abbrev cj (s : Xg h) : MulAut (Xg h) := MulAut.conj s

abbrev fa (φ : K ≃+* K) : MulAut (Xg h) := miyamotoFieldAut h φ

abbrev sg (M : Subgroup (GL (Fin 4) K)) : Subgroup (Xg h) :=
  M.subgroupOf (gramSU h (miyamotoJ4 K))

abbrev Psy : Subgroup (Xg h) := sg h (miyamotoP h)

abbrev A1X : Subgroup (Xg h) := sg h (miyamotoA1 h)

abbrev A2X : Subgroup (Xg h) := sg h (miyamotoA2 h)

abbrev ZX : Subgroup (Xg h) := sg h (miyamotoZ h)

@[expose] def Pt : Subgroup (Xg h) := Subgroup.normalizer (A2X h : Set (Xg h))

@[expose] def Ln : Subgroup (Xg h) := Subgroup.normalizer (A1X h : Set (Xg h))

@[expose] def FStab (B : Subgroup (Xg h)) : Prop :=
  ∀ (φ : K ≃+* K) (x : Xg h), fa h φ x ∈ B ↔ x ∈ B

theorem fa_mul_cj_mul_inv (φ : K ≃+* K) (s : Xg h) :
    fa h φ * cj h s * (fa h φ)⁻¹ = cj h (fa h φ s) :=
  miyamotoFieldAut_mul_conj_mul_inv h φ s

theorem fa_mul (φ ψ : K ≃+* K) : fa h φ * fa h ψ = fa h (φ * ψ) :=
  ((miyamotoFieldHom h).map_mul φ ψ).symm

theorem fa_one : fa h (1 : K ≃+* K) = 1 := (miyamotoFieldHom h).map_one

theorem fa_inv (φ : K ≃+* K) : (fa h φ)⁻¹ = fa h φ⁻¹ := (map_inv (miyamotoFieldHom h) φ).symm

theorem cj_mul (s t : Xg h) : cj h (s * t) = cj h s * cj h t :=
  map_mul (MulAut.conj : Xg h →* MulAut (Xg h)) s t

theorem cj_one : cj h (1 : Xg h) = 1 := map_one (MulAut.conj : Xg h →* MulAut (Xg h))

theorem cj_inv (s : Xg h) : cj h s⁻¹ = (cj h s)⁻¹ :=
  map_inv (MulAut.conj : Xg h →* MulAut (Xg h)) s

theorem cj_fa_mul_cj_fa (s t : Xg h) (φ ψ : K ≃+* K) :
    (cj h s * fa h φ) * (cj h t * fa h ψ) = cj h (s * fa h φ t) * fa h (φ * ψ) := by
  have e := fa_mul_cj_mul_inv h φ t
  have e' : fa h φ * cj h t = cj h (fa h φ t) * fa h φ := by
    rw [← e]
    group
  calc (cj h s * fa h φ) * (cj h t * fa h ψ) = cj h s * (fa h φ * cj h t) * fa h ψ := by
        simp only [mul_assoc]
    _ = cj h s * (cj h (fa h φ t) * fa h φ) * fa h ψ := by rw [e']
    _ = cj h s * cj h (fa h φ t) * (fa h φ * fa h ψ) := by simp only [mul_assoc]
    _ = cj h (s * fa h φ t) * fa h (φ * ψ) := by rw [fa_mul, cj_mul]

theorem inv_cj_fa (s : Xg h) (φ : K ≃+* K) :
    (cj h s * fa h φ)⁻¹ = cj h (fa h φ⁻¹ s⁻¹) * fa h φ⁻¹ := by
  rw [_root_.mul_inv_rev, fa_inv]
  have e := fa_mul_cj_mul_inv h φ⁻¹ s⁻¹
  rw [cj_inv] at e
  rw [← e]
  simp

@[expose] def Ssd (B : Subgroup (Xg h)) (hB : FStab h B) (F : Subgroup (K ≃+* K)) :
    Subgroup (MulAut (Xg h)) where
  carrier := {α | ∃ s ∈ B, ∃ φ ∈ F, α = cj h s * fa h φ}
  mul_mem' := by
    rintro _ _ ⟨s, hs, φ, hφ, rfl⟩ ⟨t, ht, ψ, hψ, rfl⟩
    exact ⟨s * fa h φ t, B.mul_mem hs ((hB φ t).2 ht), φ * ψ, F.mul_mem hφ hψ,
      cj_fa_mul_cj_fa h s t φ ψ⟩
  one_mem' := ⟨1, B.one_mem, 1, F.one_mem, by rw [cj_one, fa_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨s, hs, φ, hφ, rfl⟩
    exact ⟨fa h φ⁻¹ s⁻¹, (hB φ⁻¹ s⁻¹).2 (B.inv_mem hs), φ⁻¹, F.inv_mem hφ, inv_cj_fa h s φ⟩

theorem fStab_top : FStab h ⊤ := fun _ _ => by simp

theorem Ssd_mono {B B' : Subgroup (Xg h)} {hB : FStab h B} {hB' : FStab h B'}
    {F F' : Subgroup (K ≃+* K)} (hBB : B ≤ B') (hFF : F ≤ F') :
    Ssd h B hB F ≤ Ssd h B' hB' F' := by
  rintro _ ⟨s, hs, φ, hφ, rfl⟩
  exact ⟨s, hBB hs, φ, hFF hφ, rfl⟩

theorem cj_mem_Ssd {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)} {s : Xg h}
    (hs : s ∈ B) : cj h s ∈ Ssd h B hB F :=
  ⟨s, hs, 1, F.one_mem, by rw [fa_one, mul_one]⟩

theorem fa_mem_Ssd {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)}
    {φ : K ≃+* K} (hφ : φ ∈ F) : fa h φ ∈ Ssd h B hB F :=
  ⟨1, B.one_mem, φ, hφ, by rw [cj_one, one_mul]⟩

theorem cj_mul_fa_mem_Ssd_iff {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)}
    {s : Xg h} {φ : K ≃+* K} : cj h s * fa h φ ∈ Ssd h B hB F ↔ s ∈ B ∧ φ ∈ F := by
  constructor
  · rintro ⟨t, ht, ψ, hψ, e⟩
    obtain ⟨e1, e2⟩ := (conj_mul_fieldAut_inj h).1 e
    exact ⟨e1 ▸ ht, e2 ▸ hψ⟩
  · rintro ⟨hs, hφ⟩
    exact ⟨s, hs, φ, hφ, rfl⟩

theorem card_Ssd (B : Subgroup (Xg h)) (hB : FStab h B) (F : Subgroup (K ≃+* K)) :
    Nat.card (Ssd h B hB F) = Nat.card B * Nat.card F := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : B × F => (⟨cj h (p.1 : Xg h) * fa h (p.2 : K ≃+* K),
      ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : Ssd h B hB F)) ⟨?_, ?_⟩)
  · rintro ⟨s, φ⟩ ⟨t, ψ⟩ e
    obtain ⟨e1, e2⟩ := (conj_mul_fieldAut_inj h).1 (congrArg Subtype.val e)
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · rintro ⟨_, s, hs, φ, hφ, rfl⟩
    exact ⟨(⟨s, hs⟩, ⟨φ, hφ⟩), rfl⟩

@[expose] def FK (K₀ : Subgroup (MulAut (Xg h))) : Subgroup (K ≃+* K) :=
  K₀.comap (miyamotoFieldHom h)

theorem cj_mul_fa_mem_iff {K₀ : Subgroup (MulAut (Xg h))}
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) (s : Xg h) (φ : K ≃+* K) :
    cj h s * fa h φ ∈ K₀ ↔ φ ∈ FK h K₀ := by
  have hs : cj h s ∈ K₀ := hinn ⟨s, rfl⟩
  constructor
  · intro hm
    have := K₀.mul_mem (K₀.inv_mem hs) hm
    rwa [inv_mul_cancel_left] at this
  · intro hφ
    exact K₀.mul_mem hs hφ

theorem eq_Ssd_top {K₀ : Subgroup (MulAut (Xg h))}
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) :
    K₀ = Ssd h ⊤ (fStab_top h) (FK h K₀) := by
  ext α
  constructor
  · intro hα
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    refine ⟨s, Subgroup.mem_top _, miyamotoFieldFactor h α, ?_, hs⟩
    rw [← cj_mul_fa_mem_iff h hinn s, ← hs]
    exact hα
  · rintro ⟨s, -, φ, hφ, rfl⟩
    exact (cj_mul_fa_mem_iff h hinn s φ).2 hφ

theorem card_eq_mul_FK {K₀ : Subgroup (MulAut (Xg h))}
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) :
    Nat.card K₀ = Nat.card (Xg h) * Nat.card (FK h K₀) := by
  have e := card_Ssd h ⊤ (fStab_top h) (FK h K₀)
  rw [← eq_Ssd_top h hinn, Subgroup.card_top] at e
  exact e

theorem Ssd_le {K₀ : Subgroup (MulAut (Xg h))}
    (hinn : (MulAut.conj : Xg h →* MulAut (Xg h)).range ≤ K₀) {B : Subgroup (Xg h)}
    {hB : FStab h B} {F : Subgroup (K ≃+* K)} (hF : F ≤ FK h K₀) : Ssd h B hB F ≤ K₀ := by
  rintro _ ⟨s, -, φ, hφ, rfl⟩
  exact (cj_mul_fa_mem_iff h hinn s φ).2 (hF hφ)

end Vocabulary

end CFSG.Quasithin.H13.F431.Un.OL
