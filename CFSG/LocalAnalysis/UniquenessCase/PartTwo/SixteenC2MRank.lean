module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c2m_rkIdx_ge_swap {T : Type} [CommGroup T] [Finite T] {Ya Yb : Subgroup T}
    (hd : Disjoint Ya Yb) {φ : MulAut T} (hφa : Ya.map φ.toMonoidHom = Yb) :
    rk ↥Ya ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
  have h1 := rk_map_add_rk_inf_ker (commHom φ) Ya
  have h2 : Ya ⊓ (commHom φ).ker = ⊥ := by
    rw [ker_commHom, eq_bot_iff]
    rintro y ⟨hy, hyf⟩
    have hyfix : φ y = y := mem_fixV_zpowers_iff.1 hyf
    have hyb : y ∈ Yb := by
      rw [← hφa]
      exact ⟨y, hy, hyfix⟩
    have : y ∈ Ya ⊓ Yb := ⟨hy, hyb⟩
    rwa [disjoint_iff.1 hd] at this
  rw [h2, rk_bot, add_zero] at h1
  have h3 : Ya.map (commHom φ) ≤ commV (Subgroup.zpowers φ) := by
    rw [commV_zpowers_eq_map]
    exact Subgroup.map_mono le_top
  have h4 := rk_mono h3
  rw [rkIdx_fixV_zpowers]
  omega

private theorem s16c2m_rk_map {T : Type} [CommGroup T] (e : MulAut T) (U : Subgroup T) :
    rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective e.injective]

theorem s16c2m_zpowers_inv {T : Type} [CommGroup T] {A : Subgroup T} {φ : MulAut T}
    (hA : A.map φ.toMonoidHom = A) : ∀ x ∈ Subgroup.zpowers φ, ∀ w ∈ A, x w ∈ A := by
  have h1 : φ ∈ stabSub A := StabLat.mem_stabSub_of_map_eq hA
  have h2 : Subgroup.zpowers φ ≤ stabSub A := Subgroup.zpowers_le.2 h1
  intro x hx w hw
  exact ((mem_stabSub.1 (h2 hx)) w).2 hw

theorem s16c2m_commV_two {T : Type} [CommGroup T] [Finite T] {A : Subgroup T} {φ ζ : MulAut T}
    (hζφ : ζ * φ = φ * ζ) (hA : A.map φ.toMonoidHom = A)
    (hd : Disjoint A (A.map ζ.toMonoidHom)) (hsup : A ⊔ A.map ζ.toMonoidHom = ⊤) :
    rkIdx (fixV (Subgroup.zpowers φ)) = 2 * rk ↥(commSub A (Subgroup.zpowers φ)) ∧
      ∀ z ∈ commV (Subgroup.zpowers φ), ∃ a ∈ commSub A (Subgroup.zpowers φ),
        ∃ b ∈ commSub A (Subgroup.zpowers φ), z = a * ζ b := by
  have hcomm : ∀ x : T, φ (ζ x) = ζ (φ x) := by
    intro x
    have := congrArg (fun f : MulAut T => f x) hζφ
    simpa [MulAut.mul_apply] using this.symm
  have hcomm' : ∀ x : T, φ (ζ⁻¹ x) = ζ⁻¹ (φ x) := by
    intro x
    apply ζ.injective
    have h := hcomm (ζ⁻¹ x)
    simp only [MulAut.apply_inv_self] at h
    simp only [MulAut.apply_inv_self]
    exact h.symm
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup T, B = A.map ζ.toMonoidHom := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup T, C = fixV (Subgroup.zpowers φ) := ⟨_, rfl⟩
  rw [← hBdef] at hd hsup
  have hCmem : ∀ x : T, x ∈ C ↔ φ x = x := fun x => by
    rw [hCdef]; exact mem_fixV_zpowers_iff
  have hB : B.map φ.toMonoidHom = B := by
    rw [hBdef, Subgroup.map_map]
    have : φ.toMonoidHom.comp ζ.toMonoidHom = ζ.toMonoidHom.comp φ.toMonoidHom := by
      ext x; exact hcomm x
    rw [this, ← Subgroup.map_map, hA]
  have hinvA := s16c2m_zpowers_inv hA
  have hinvB := s16c2m_zpowers_inv hB
  have hrkB : rk ↥B = rk ↥A := by rw [hBdef]; exact s16c2m_rk_map ζ A
  have hAB : A ⊓ B = ⊥ := disjoint_iff.1 hd
  have hT : rk T = 2 * rk ↥A := by
    have h := rk_sup_add_rk_inf A B
    rw [hsup, hAB, rk_top, rk_bot] at h
    omega
  have hsplit : C = (A ⊓ C) ⊔ (B ⊓ C) := by
    apply le_antisymm
    · intro x hx
      have hx' : φ x = x := (hCmem x).1 hx
      have hxT : x ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top x
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hxT
      have hφa : φ a ∈ A := hinvA φ (Subgroup.mem_zpowers φ) a ha
      have hφb : φ b ∈ B := hinvB φ (Subgroup.mem_zpowers φ) b hb
      have hmul : φ a * φ b = a * b := by rw [← map_mul]; exact hx'
      have h2 : φ a * a⁻¹ = b * (φ b)⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]
        have h3 : φ a = a * b * (φ b)⁻¹ := eq_mul_inv_of_mul_eq hmul
        rw [h3]
        ac_rfl
      have h1 : φ a * a⁻¹ ∈ A ⊓ B :=
        ⟨A.mul_mem hφa (A.inv_mem ha), h2 ▸ B.mul_mem hb (B.inv_mem hφb)⟩
      rw [hAB, Subgroup.mem_bot, mul_inv_eq_one] at h1
      have h4 : φ b = b := by
        rw [h1] at hmul
        exact mul_left_cancel hmul
      exact Subgroup.mul_mem_sup ⟨ha, (hCmem a).2 h1⟩ ⟨hb, (hCmem b).2 h4⟩
    · exact sup_le inf_le_right inf_le_right
  have hAC_BC : (A ⊓ C) ⊓ (B ⊓ C) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ A ⊓ B := ⟨hx.1.1, hx.2.1⟩
    rwa [hAB] at this
  have hrkC : rk ↥C = rk ↥(A ⊓ C) + rk ↥(B ⊓ C) := by
    have h := rk_sup_add_rk_inf (A ⊓ C) (B ⊓ C)
    rw [hAC_BC, rk_bot, add_zero, ← hsplit] at h
    exact h
  have hle1 : rk ↥(A ⊓ C) ≤ rk ↥(B ⊓ C) := by
    have h : (A ⊓ C).map ζ.toMonoidHom ≤ B ⊓ C := by
      rintro _ ⟨a, ⟨ha, haC⟩, rfl⟩
      have hφa : φ a = a := (hCmem a).1 haC
      refine ⟨by rw [hBdef]; exact ⟨a, ha, rfl⟩, (hCmem _).2 ?_⟩
      show φ (ζ a) = ζ a
      rw [hcomm, hφa]
    have h2 := rk_mono h
    rw [s16c2m_rk_map] at h2
    exact h2
  have hle2 : rk ↥(B ⊓ C) ≤ rk ↥(A ⊓ C) := by
    have h : (B ⊓ C).map (ζ⁻¹).toMonoidHom ≤ A ⊓ C := by
      rintro _ ⟨b, ⟨hb, hbC⟩, rfl⟩
      rw [hBdef] at hb
      obtain ⟨a', ha', rfl⟩ := hb
      have hφ : φ (ζ a') = ζ a' := (hCmem _).1 hbC
      refine ⟨by simpa using ha', (hCmem _).2 ?_⟩
      show φ (ζ⁻¹ (ζ a')) = ζ⁻¹ (ζ a')
      rw [hcomm', hφ]
    have h2 := rk_mono h
    rw [s16c2m_rk_map] at h2
    exact h2
  have hcs := rk_commSub_add_rk_inf_fixV (g := φ) (W := A) hinvA
  have hCi := rk_add_rkIdx (fixV (Subgroup.zpowers φ))
  rw [← hCdef] at hcs hCi ⊢
  refine ⟨by omega, ?_⟩
  intro z hz
  rw [commV_zpowers_eq_map] at hz
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hz
  have hv : v ∈ A ⊔ B := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨a, ha, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [hBdef] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨φ a * a⁻¹, Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, a, ha, rfl⟩,
    φ b * b⁻¹, Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, b, hb, rfl⟩, ?_⟩
  show φ (a * ζ b) * (a * ζ b)⁻¹ = (φ a * a⁻¹) * ζ (φ b * b⁻¹)
  rw [map_mul, hcomm, map_mul, map_inv, mul_inv]
  simp only [mul_assoc, mul_comm, mul_left_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
