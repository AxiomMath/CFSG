module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly F4Model

theorem f4_swap23 :
    (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2) *
        CoxeterMatrix.F₄.simple 2 *
        (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2)⁻¹ =
      CoxeterMatrix.F₄.simple 3 ∧
    (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2) *
        CoxeterMatrix.F₄.simple 3 *
        (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2)⁻¹ =
      CoxeterMatrix.F₄.simple 2 := by
  set x := CoxeterMatrix.F₄.simple 2
  set y := CoxeterMatrix.F₄.simple 3
  have hxx : x * x = 1 := by
    have h := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_self 2
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at h
  have hyy : y * y = 1 := by
    have h := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_self 3
    rwa [CoxeterMatrix.toCoxeterSystem_simple] at h
  have hxy : (x * y) ^ 3 = 1 := by
    have h := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_pow 2 3
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    exact h
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have h5 : x * y * x * y * x = y := by
    have h6 : x * y * x * y * x * y = 1 := by rw [← hxy, pow_three]; group
    calc x * y * x * y * x = x * y * x * y * x * y * y⁻¹ := by group
      _ = y := by rw [h6, one_mul, hyi]
  have hc : (x * y * x)⁻¹ = x * y * x := by
    rw [mul_inv_rev, mul_inv_rev, hxi, hyi, mul_assoc]
  constructor
  · rw [hc]
    calc x * y * x * x * (x * y * x) = x * y * (x * x) * x * y * x := by group
      _ = y := by rw [hxx, mul_one, h5]
  · rw [hc]
    calc x * y * x * y * (x * y * x) = (x * y * x * y * x) * y * x := by group
      _ = x := by rw [h5, hyy, one_mul]

section Missed

variable {G : Type} [Group G]

theorem exists_missed_framePos {Bs : Subgroup G} {W : Subgroup (MulAut ↥Bs)} {p : ℕ}
    (e : CoxeterMatrix.F₄.Group ≃* ↥W)
    (he : ∀ i, GGIsReflection p ((e (CoxeterMatrix.F₄.simple i) : ↥W) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {AL AK : Subgroup (MulAut ↥Bs)} {a b : Fin 3 → CoxeterMatrix.F₄.Group}
    (haR : ∀ k, R.IsRefl (a k)) (ha01 : orderOf (a 0 * a 1) = 3)
    (ha12 : orderOf (a 1 * a 2) = 4) (ha02 : orderOf (a 0 * a 2) = 2)
    (hbR : ∀ k, R.IsRefl (b k)) (hb01 : orderOf (b 0 * b 1) = 3)
    (hb12 : orderOf (b 1 * b 2) = 4) (hb02 : orderOf (b 0 * b 2) = 2)
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) ↔ ((e z : ↥W) : MulAut ↥Bs) ∈ AL)
    (hbK : ∀ z, z ∈ Subgroup.closure (Set.range b) ↔ ((e z : ↥W) : MulAut ↥Bs) ∈ AK)
    (w : CoxeterMatrix.F₄.Group) {i j : Fin 4} (hij : CoxeterMatrix.F₄ i j = 3)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥W) : MulAut ↥Bs) ∈ AL)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥W) : MulAut ↥Bs) ∈ AK)
    (hmiss : ∀ (w' : CoxeterMatrix.F₄.Group) (Z : Subgroup (MulAut ↥Bs)), (Z = AL ∨ Z = AK) →
      ((e (w' * CoxeterMatrix.F₄.simple i * w'⁻¹) : ↥W) : MulAut ↥Bs) ∈ Z →
      ((e (w' * CoxeterMatrix.F₄.simple j * w'⁻¹) : ↥W) : MulAut ↥Bs) ∉ Z) :
    ∃ (e' : CoxeterMatrix.F₄.Group ≃* ↥W) (a' b' : Fin 3 → CoxeterMatrix.F₄.Group)
      (ga gb w₀ : CoxeterMatrix.F₄.Group),
      (∀ i, GGIsReflection p ((e' (CoxeterMatrix.F₄.simple i) : ↥W) : MulAut ↥Bs)) ∧
      (∀ z, z ∈ Subgroup.closure (Set.range a') ↔ ((e' z : ↥W) : MulAut ↥Bs) ∈ AL) ∧
      (∀ z, z ∈ Subgroup.closure (Set.range b') ↔ ((e' z : ↥W) : MulAut ↥Bs) ∈ AK) ∧
      (ga * a' 0 * ga⁻¹ = R.s 0 ∧ ga * a' 1 * ga⁻¹ = R.s 1 ∧ ga * a' 2 * ga⁻¹ = R.s 2) ∧
      (gb * b' 0 * gb⁻¹ = R.s 0 ∧ gb * b' 1 * gb⁻¹ = R.s 1 ∧ gb * b' 2 * gb⁻¹ = R.s 2) ∧
      e' (w₀ * R.s 2 * w₀⁻¹) = e (w * CoxeterMatrix.F₄.simple i * w⁻¹) ∧
      e' (w₀ * R.s 3 * w₀⁻¹) = e (w * CoxeterMatrix.F₄.simple j * w⁻¹) ∧
      ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥W) : MulAut ↥Bs) ∉ AK ∧
      ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥W) : MulAut ↥Bs) ∉ AL := by
  have hjL : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥W) : MulAut ↥Bs) ∉ AL :=
    hmiss w AL (Or.inl rfl) hi
  have hiK : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥W) : MulAut ↥Bs) ∉ AK :=
    fun h => hmiss w AK (Or.inr rfl) h hj
  have hnotB : ∀ {c : Fin 3 → CoxeterMatrix.F₄.Group} {g : CoxeterMatrix.F₄.Group}
      {Z : Subgroup (MulAut ↥Bs)}, (Z = AL ∨ Z = AK) →
      (∀ z, z ∈ Subgroup.closure (Set.range c) ↔ ((e z : ↥W) : MulAut ↥Bs) ∈ Z) →
      (g * c 0 * g⁻¹ = R.s 0 ∧ g * c 1 * g⁻¹ = R.s 1 ∧ g * c 2 * g⁻¹ = R.s 2) →
      ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) := by
    intro c g Z hZ hcZ hg
    by_contra hne
    obtain ⟨w', h1, h2⟩ := R.exists_conj_of_B hg hne
    rw [hRs] at h1 h2
    exact hmiss w' Z hZ ((hcZ _).1 h1) ((hcZ _).1 h2)
  have hnotC : ∀ {c : Fin 3 → CoxeterMatrix.F₄.Group} {g : CoxeterMatrix.F₄.Group}
      {Z : Subgroup (MulAut ↥Bs)}, (Z = AL ∨ Z = AK) →
      (∀ z, z ∈ Subgroup.closure (Set.range c) ↔ ((e z : ↥W) : MulAut ↥Bs) ∈ Z) →
      (g * c 0 * g⁻¹ = R.s 3 ∧ g * c 1 * g⁻¹ = R.s 2 ∧ g * c 2 * g⁻¹ = R.s 1) →
      ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
    intro c g Z hZ hcZ hg
    by_contra hne
    obtain ⟨w', h1, h2⟩ := R.exists_conj_of_C hg hne
    rw [hRs] at h1 h2
    exact hmiss w' Z hZ ((hcZ _).1 h1) ((hcZ _).1 h2)
  have hdisj : ¬ (((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))) := by
    rintro ⟨h1 | h1, h2 | h2⟩ <;> (obtain ⟨rfl, rfl⟩ := h1; simp at h2)
  obtain ⟨hsw2, hsw3⟩ := f4_swap23
  set c : CoxeterMatrix.F₄.Group :=
    CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2 with hcdef
  obtain ⟨ga, hga | hga⟩ := R.classify (haR 0) (haR 1) (haR 2) ha01 ha12 ha02 <;>
    obtain ⟨gb, hgb | hgb⟩ := R.classify (hbR 0) (hbR 1) (hbR 2) hb01 hb12 hb02
  ·
    have hp := hnotB (Or.inl rfl) haL hga
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨e, a, b, ga, gb, w, he, haL, hbK, hga, hgb, by rw [hRs], by rw [hRs], hiK, hjL⟩
    · refine ⟨e, a, b, ga, gb, w * c, he, haL, hbK, hga, hgb, ?_, ?_, hiK, hjL⟩
      · rw [hRs, show w * c * CoxeterMatrix.F₄.simple 2 * (w * c)⁻¹ =
          w * (c * CoxeterMatrix.F₄.simple 2 * c⁻¹) * w⁻¹ by group, hsw2]
      · rw [hRs, show w * c * CoxeterMatrix.F₄.simple 3 * (w * c)⁻¹ =
          w * (c * CoxeterMatrix.F₄.simple 3 * c⁻¹) * w⁻¹ by group, hsw3]
  ·
    exact absurd ⟨hnotB (Or.inl rfl) haL hga, hnotC (Or.inr rfl) hbK hgb⟩ hdisj
  · exact absurd ⟨hnotB (Or.inr rfl) hbK hgb, hnotC (Or.inl rfl) haL hga⟩ hdisj
  ·
    have hp := hnotC (Or.inl rfl) haL hga
    obtain ⟨ρ, hρ⟩ := exists_f4DiagramRev
    have hρs : ∀ k, ρ.symm (CoxeterMatrix.F₄.simple (Fin.rev k)) = CoxeterMatrix.F₄.simple k := by
      intro k
      rw [← hρ, MulEquiv.symm_apply_apply]
    have hmem : ∀ (c' : Fin 3 → CoxeterMatrix.F₄.Group) (Z : Subgroup (MulAut ↥Bs)),
        (∀ z, z ∈ Subgroup.closure (Set.range c') ↔ ((e z : ↥W) : MulAut ↥Bs) ∈ Z) →
        ∀ z, z ∈ Subgroup.closure (Set.range fun k => ρ.symm (c' k)) ↔
          (((ρ.trans e) z : ↥W) : MulAut ↥Bs) ∈ Z := by
      intro c' Z hcZ z
      have hcl : Subgroup.closure (Set.range fun k => ρ.symm (c' k)) =
          (Subgroup.closure (Set.range c')).map ρ.symm.toMonoidHom := by
        rw [MonoidHom.map_closure, ← Set.range_comp]
        rfl
      rw [hcl, MulEquiv.trans_apply, ← hcZ, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    have htrip : ∀ (c' : Fin 3 → CoxeterMatrix.F₄.Group) (g : CoxeterMatrix.F₄.Group),
        (g * c' 0 * g⁻¹ = R.s 3 ∧ g * c' 1 * g⁻¹ = R.s 2 ∧ g * c' 2 * g⁻¹ = R.s 1) →
        (ρ.symm g * ρ.symm (c' 0) * (ρ.symm g)⁻¹ = R.s 0 ∧
          ρ.symm g * ρ.symm (c' 1) * (ρ.symm g)⁻¹ = R.s 1 ∧
          ρ.symm g * ρ.symm (c' 2) * (ρ.symm g)⁻¹ = R.s 2) := by
      rintro c' g ⟨h0, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_inv, ← map_mul, ← map_mul, h0, hRs, hRs]; exact hρs 0
      · rw [← map_inv, ← map_mul, ← map_mul, h1, hRs, hRs]; exact hρs 1
      · rw [← map_inv, ← map_mul, ← map_mul, h2, hRs, hRs]; exact hρs 2
    have he' : ∀ k, GGIsReflection p
        (((ρ.trans e) (CoxeterMatrix.F₄.simple k) : ↥W) : MulAut ↥Bs) := by
      intro k
      rw [MulEquiv.trans_apply, hρ]
      exact he _
    have hconj : ∀ (v t : CoxeterMatrix.F₄.Group), (ρ.trans e) (ρ.symm v * t * (ρ.symm v)⁻¹) =
        e (v * ρ t * v⁻¹) := by
      intro v t
      rw [MulEquiv.trans_apply]
      congr 1
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨ρ.trans e, _, _, _, _, ρ.symm w * c, he', hmem a AL haL, hmem b AK hbK,
        htrip a ga hga, htrip b gb hgb, ?_, ?_, hiK, hjL⟩
      · rw [hRs, show ρ.symm w * c * CoxeterMatrix.F₄.simple 2 * (ρ.symm w * c)⁻¹ =
          ρ.symm w * (c * CoxeterMatrix.F₄.simple 2 * c⁻¹) * (ρ.symm w)⁻¹ by group, hsw2, hconj,
          hρ]
        rfl
      · rw [hRs, show ρ.symm w * c * CoxeterMatrix.F₄.simple 3 * (ρ.symm w * c)⁻¹ =
          ρ.symm w * (c * CoxeterMatrix.F₄.simple 3 * c⁻¹) * (ρ.symm w)⁻¹ by group, hsw3, hconj,
          hρ]
        rfl
    · refine ⟨ρ.trans e, _, _, _, _, ρ.symm w, he', hmem a AL haL, hmem b AK hbK,
        htrip a ga hga, htrip b gb hgb, ?_, ?_, hiK, hjL⟩
      · rw [hRs, hconj, hρ]
        rfl
      · rw [hRs, hconj, hρ]
        rfl

end Missed

end CFSG.StandardType

end
