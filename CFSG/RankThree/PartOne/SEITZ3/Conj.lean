module

public import CFSG.Timmesfeld.ARS.BasicRankOne
public import CFSG.LieType.Steinberg.PartB

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG.Timmesfeld.ARS CFSG.LieType.Steinberg

section ConjInv

variable {G : Type*} [Group G]

theorem conjSub_conjSub_inv' (X : Subgroup G) (g : G) : conjSub (conjSub X g) g⁻¹ = X := by
  rw [← conjSub_mul]; simp

theorem conjSub_inj {A B : Subgroup G} (g : G) (h : conjSub A g = conjSub B g) : A = B := by
  have := congrArg (fun X => conjSub X g⁻¹) h
  simpa [conjSub_conjSub_inv'] using this

theorem conjSub_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSub H g = H := by
  ext x
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e] at this
  exact this

theorem le_normalizer_of_commute {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : ∀ z ∈ B, x * z * x⁻¹ = z := fun z hz => (h x hx z hz).mul_inv_cancel
  have h2 : ∀ z ∈ B, x⁻¹ * z * x = z := fun z hz => by
    simpa using ((h x hx z hz).inv_left).mul_inv_cancel
  constructor
  · intro hy
    rw [h1 y hy]
    exact hy
  · intro hy
    have h3 : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := h2 _ hy
    have h4 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [h4] at h3
    rw [h3]
    exact hy

theorem commuting_conj {A B : Subgroup G} (h : Commuting A B) (g : G) :
    Commuting (conjSub A g) (conjSub B g) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact (h a ha b hb).map (MulAut.conj g).toMonoidHom

theorem opposite_conj {A B : Subgroup G} (h : Opposite A B) (g : G) :
    Opposite (conjSub A g) (conjSub B g) := by
  refine ⟨fun heq => h.1 (conjSub_inj g heq), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ ha1
    have ha1' : a ≠ 1 := fun h1 => ha1 (by simp [h1])
    obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha ha1'
    refine ⟨(MulAut.conj g).toMonoidHom b, ⟨b, hb, rfl⟩, fun h1 => hb1 ?_, ?_⟩
    · simpa using h1
    · have e1 : conjSub (conjSub A g) ((MulAut.conj g).toMonoidHom b) = conjSub A (g * b) := by
        rw [← conjSub_mul]; congr 1; simp [MulAut.conj_apply]
      have e2 : conjSub (conjSub B g) ((MulAut.conj g).toMonoidHom a) = conjSub B (g * a) := by
        rw [← conjSub_mul]; congr 1; simp [MulAut.conj_apply]
      rw [e1, e2, conjSub_mul, hab, ← conjSub_mul]
  · rintro _ ⟨b, hb, rfl⟩ hb1
    have hb1' : b ≠ 1 := fun h1 => hb1 (by simp [h1])
    obtain ⟨a, ha, ha1, hab⟩ := h.2.2 b hb hb1'
    refine ⟨(MulAut.conj g).toMonoidHom a, ⟨a, ha, rfl⟩, fun h1 => ha1 ?_, ?_⟩
    · simpa using h1
    · have e1 : conjSub (conjSub B g) ((MulAut.conj g).toMonoidHom a) = conjSub B (g * a) := by
        rw [← conjSub_mul]; congr 1; simp [MulAut.conj_apply]
      have e2 : conjSub (conjSub A g) ((MulAut.conj g).toMonoidHom b) = conjSub A (g * b) := by
        rw [← conjSub_mul]; congr 1; simp [MulAut.conj_apply]
      rw [e1, e2, conjSub_mul, hab, ← conjSub_mul]

theorem special_conj {R : Set (Subgroup G)} (hR : ∀ A ∈ R, ∀ g : G, conjSub A g ∈ R)
    {A B : Subgroup G} (h : Special R A B) (g : G) :
    Special R (conjSub A g) (conjSub B g) := by
  have hc : conjSub ⁅A, B⁆ g = ⁅conjSub A g, conjSub B g⁆ := Subgroup.map_commutator _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc]; exact hR _ h.1 g
  · rw [← hc]; exact commuting_conj h.2.1 g
  · rw [← hc]; exact commuting_conj h.2.2 g

end ConjInv

section SL2Opp

variable {F : Type*} [Field F] {H : Type*} [Group H]

theorem sl2_conj_eq {t d : F} (ht : t ≠ 0) :
    sl2Lower t⁻¹ * sl2Upper (-(t ^ 2) * d) * (sl2Lower t⁻¹)⁻¹ =
      sl2Upper t * sl2Lower d * (sl2Upper t)⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, sl2Lower, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem sl2Upper_zero : sl2Upper (0 : F) = 1 := by
  apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2Upper]

theorem sl2Lower_zero : sl2Lower (0 : F) = 1 := by
  apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2Lower]

theorem sl2Upper_ne_sl2Lower {c : F} (hc : c ≠ 0) (d : F) : sl2Upper c ≠ sl2Lower d := fun h => by
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [sl2Upper, sl2Lower] at this
  exact hc this

theorem opposite_of_sl2 (φ : Matrix.SpecialLinearGroup (Fin 2) F →* H)
    (hφ : Function.Injective φ) {A B : Subgroup H}
    (hA : ∀ x, x ∈ A ↔ ∃ c : F, φ (sl2Upper c) = x)
    (hB : ∀ x, x ∈ B ↔ ∃ c : F, φ (sl2Lower c) = x) : Opposite A B := by
  have key : ∀ {t : F}, t ≠ 0 →
      conjSub A (φ (sl2Lower t⁻¹)) = conjSub B (φ (sl2Upper t)) := by
    intro t ht
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := (hA y).1 hy
      refine ⟨φ (sl2Lower (-c / t ^ 2)), (hB _).2 ⟨_, rfl⟩, ?_⟩
      have h := sl2_conj_eq (F := F) (t := t) (d := -c / t ^ 2) ht
      have hc : -(t ^ 2) * (-c / t ^ 2) = c := by field_simp
      rw [hc] at h
      have h2 := congrArg φ h
      simp only [map_mul, map_inv] at h2
      simpa [MulAut.conj_apply] using h2.symm
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨d, rfl⟩ := (hB y).1 hy
      refine ⟨φ (sl2Upper (-(t ^ 2) * d)), (hA _).2 ⟨_, rfl⟩, ?_⟩
      have h := sl2_conj_eq (F := F) (t := t) (d := d) ht
      have h2 := congrArg φ h
      simp only [map_mul, map_inv] at h2
      simpa [MulAut.conj_apply] using h2
  refine ⟨?_, ?_, ?_⟩
  · intro hAB
    have h1 : φ (sl2Upper 1) ∈ A := (hA _).2 ⟨1, rfl⟩
    rw [hAB] at h1
    obtain ⟨c, hc⟩ := (hB _).1 h1
    exact sl2Upper_ne_sl2Lower one_ne_zero c (hφ hc).symm
  · intro a ha ha1
    obtain ⟨t, rfl⟩ := (hA a).1 ha
    have ht : t ≠ 0 := fun h0 => ha1 (by rw [h0, sl2Upper_zero, map_one])
    refine ⟨φ (sl2Lower t⁻¹), (hB _).2 ⟨_, rfl⟩, fun h1 => ?_, key ht⟩
    have : sl2Lower t⁻¹ = 1 := hφ (by rw [h1, map_one])
    have h0 : t⁻¹ = 0 := by
      have := congrArg
        (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 0) this
      simpa [sl2Lower] using this
    exact ht (inv_eq_zero.1 h0)
  · intro b hb hb1
    obtain ⟨d, rfl⟩ := (hB b).1 hb
    have hd : d ≠ 0 := fun h0 => hb1 (by rw [h0, sl2Lower_zero, map_one])
    refine ⟨φ (sl2Upper d⁻¹), (hA _).2 ⟨_, rfl⟩, fun h1 => ?_, ?_⟩
    · have : sl2Upper d⁻¹ = 1 := hφ (by rw [h1, map_one])
      have h0 : d⁻¹ = 0 := by
        have := congrArg
          (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) this
        simpa [sl2Upper] using this
      exact hd (inv_eq_zero.1 h0)
    · have := key (inv_ne_zero hd)
      simpa using this.symm

end SL2Opp

end CFSG.RankThree.PartOne.SEITZ3
