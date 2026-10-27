module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Counts

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem card_inv_R (hD : Nonempty (↥R ≃* DihedralGroup 4 × DihedralGroup 4)) :
    35 ≤ Set.ncard {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1} := by
  classical
  obtain ⟨e⟩ := hD
  let ψ : DihedralGroup 4 × DihedralGroup 4 → G := fun y => ((e.symm y : ↥R) : G)
  have hψ : Function.Injective ψ := fun a b hab => e.symm.injective (Subtype.ext hab)
  let T : Set (DihedralGroup 4 × DihedralGroup 4) := {y | y * y = 1 ∧ y ≠ 1}
  have hT : T.ncard = 35 := by
    have : T = ↑(Finset.univ.filter fun y : DihedralGroup 4 × DihedralGroup 4 =>
        y * y = 1 ∧ y ≠ 1) := by
      ext y
      simp [T]
    rw [this, Set.ncard_coe_finset]
    decide +kernel
  have hsub : ψ '' T ⊆ {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1} := by
    rintro _ ⟨y, ⟨hy2, hy1⟩, rfl⟩
    refine ⟨(e.symm y).2, ?_, ?_⟩
    · have : e.symm y * e.symm y = 1 := by rw [← map_mul, hy2, map_one]
      simpa using congrArg Subtype.val this
    · intro h1
      apply hy1
      have : e.symm y = 1 := Subtype.ext h1
      have h2 : y = 1 := by simpa using congrArg e this
      exact h2
  calc 35 = T.ncard := hT.symm
    _ = (ψ '' T).ncard := (Set.ncard_image_of_injective _ hψ).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem R_counts (h : F55Ctx c R) :
    17 ≤ Set.ncard {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} ∧
    18 ≤ Set.ncard {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x (c.iso.toG fhB)} := by
  obtain ⟨g, hgu, hgR⟩ := exists_gR c h
  set F := c.iso.toG fhB with hF
  have hFR : F ∈ R := F_mem_R c h
  have hFT : g * F * g⁻¹ ∈ c.iso.imgG That := hgR F hFR
  have hF2 : (g * F * g⁻¹) * (g * F * g⁻¹) = 1 := by
    calc (g * F * g⁻¹) * (g * F * g⁻¹) = g * (F * F) * g⁻¹ := by group
      _ = 1 := by rw [F_sq c.iso]; group
  have hFne : g * F * g⁻¹ ≠ 1 := by
    intro h1
    apply F_ne_one c.iso
    show F = 1
    have : F = g⁻¹ * (g * F * g⁻¹) * g := by group
    rw [this, h1]
    group
  obtain ⟨k₀, hk₀, hk₀F⟩ := exists_ivG c hFT hF2 hFne
  have hzk₀ : zt k₀ = false := by
    rw [← ivG_conj_F_iff c h hk₀, hk₀F]
    exact isConj_conj_self g F
  have hcommR : ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∃ j ∈ JC k₀, ivG c j = g * x * g⁻¹ := by
    intro x hx hx2 hx1
    have hxT := hgR x hx
    have hx2' : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
      calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hx1' : g * x * g⁻¹ ≠ 1 := by
      intro h1
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h1]
      group
    obtain ⟨j, hj, hjx⟩ := exists_ivG c hxT hx2' hx1'
    refine ⟨j, mem_JC.2 ⟨hj, ?_⟩, hjx⟩
    rw [← ivG_comm_iff c hj hk₀, hjx, hk₀F]
    have hxF : x * F = F * x := Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hx)
    calc g * x * g⁻¹ * (g * F * g⁻¹) = g * (x * F) * g⁻¹ := by group
      _ = g * (F * x) * g⁻¹ := by rw [hxF]
      _ = g * F * g⁻¹ * (g * x * g⁻¹) := by group
  have h35 : 35 ≤ (JC k₀).length := by
    have := ncard_le_of_idx c {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1} g (JC k₀) (JC_nodup k₀)
      (fun x hx => hcommR x hx.1 hx.2.1 hx.2.2)
    exact (card_inv_R h.hD).trans this
  obtain ⟨hZ, hP⟩ := count_R k₀ hk₀ hzk₀ h35
  have hback : ∀ j ∈ JC k₀, g⁻¹ * ivG c j * g ∈ R ∧ g⁻¹ * ivG c j * g * (g⁻¹ * ivG c j * g) = 1 ∧
      g⁻¹ * ivG c j * g ≠ 1 := by
    intro j hjC
    obtain ⟨hj43, hjcomm⟩ := mem_JC.1 hjC
    have hjF : ivG c j * (g * F * g⁻¹) = (g * F * g⁻¹) * ivG c j := by
      rw [← hk₀F]
      exact (ivG_comm_iff c hj43 hk₀).2 hjcomm
    refine ⟨mem_R_of_T₀ c h hgu (ivG_mem_T₀ c hj43) hjF, ?_, ?_⟩
    · calc g⁻¹ * ivG c j * g * (g⁻¹ * ivG c j * g) = g⁻¹ * (ivG c j * ivG c j) * g := by group
        _ = 1 := by rw [ivG_sq c hj43]; group
    · intro h1
      apply ivG_ne_one c hj43
      have : ivG c j = g * (g⁻¹ * ivG c j * g) * g⁻¹ := by group
      rw [this, h1]
      group
  have hconj : ∀ (w : G) (j : ℕ), IsConj (ivG c j) w → IsConj (g⁻¹ * ivG c j * g) w := by
    intro w j hw
    have := isConj_conj_self g⁻¹ (ivG c j)
    rw [inv_inv] at this
    exact this.trans hw
  constructor
  · refine hZ.trans (le_ncard_of_idx c _ g (JZ k₀) (JZ_nodup k₀)
      (fun j hj => (mem_JC.1 (mem_JZ.1 hj).1).1) ?_)
    intro j hj
    obtain ⟨hjC, hjz⟩ := mem_JZ.1 hj
    obtain ⟨h1, h2, h3⟩ := hback j hjC
    exact ⟨h1, h2, h3, hconj z j ((ivG_conj_z_iff c h (mem_JC.1 hjC).1).2 hjz)⟩
  · refine hP.trans (le_ncard_of_idx c _ g (JP k₀) (JP_nodup k₀)
      (fun j hj => (mem_JC.1 (mem_JP.1 hj).1).1) ?_)
    intro j hj
    obtain ⟨hjC, hjz⟩ := mem_JP.1 hj
    obtain ⟨h1, h2, h3⟩ := hback j hjC
    exact ⟨h1, h2, h3, hconj F j ((ivG_conj_F_iff c h (mem_JC.1 hjC).1).2 hjz)⟩

end Counts

end CFSG.Quasithin.H13.F431.U42Aut
