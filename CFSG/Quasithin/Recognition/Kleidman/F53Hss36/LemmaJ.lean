module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaI

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem Iv_le_stab {ν δ : Geo H M} (hδ : δ ∈ nbrs ν) (hvδ : vtype δ = false) :
    Iv ν ≤ stab ν := fun _ hx =>
  (Qv_le_inf C.hA (mem_nbrs_comm hδ) (C.Vn_le_Qv_self hvδ (Iv_le_Vn hδ hx))).2

theorem comm_Iv_Qv_eq {ν : Geo H M} (hν : vtype ν = true) (h8 : Nat.card (Iv ν) = 8) :
    ⁅Iv ν, Qv ν⁆ = Zv ν := by
  obtain ⟨δ, hδ⟩ := exists_adj ν
  have hδn : δ ∈ nbrs ν := hδ
  have hvδ := vtype_false_of_mem_nbrs_true hδn hν
  have hZI : Zv ν ≤ Iv ν := C.Zv_le_Iv
  have hrel : (Zv ν).relIndex (Iv ν) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := Zv ν) (K := Iv ν)
    rw [inf_of_le_left hZI, C.card_Zv_true hν, h8] at h
    omega
  have hIst := C.Iv_le_stab hδn hvδ
  have hIN := stab_le_normalizer_Iv (H := H) (M := M) ν
  have hqZ : ∀ y ∈ Iv ν, ∀ q ∈ Qv ν, y⁻¹ * q * y * q⁻¹ ∈ Zv ν := by
    intro y hy q hq
    have hqs : q ∈ stab ν := pCoreOf_le 2 (stab ν) hq
    have hqz := fun z hz => C.Qv_centralizes_Zv hν hq (z := z) hz
    have hqy : q * y * q⁻¹ ∈ Iv ν :=
      (Subgroup.mem_normalizer_iff.mp (hIN hqs) y).mp hy
    by_cases hyZ : y ∈ Zv ν
    · have h1 := hqz y hyZ
      have : y⁻¹ * q * y * q⁻¹ = 1 := by
        calc y⁻¹ * q * y * q⁻¹ = y⁻¹ * (q * y * q⁻¹) := by group
          _ = 1 := by rw [h1]; group
      rw [this]
      exact one_mem _
    · have hwZ : q * y * q⁻¹ ∉ Zv ν := by
        intro h
        have h1 := hqz _ h
        have h2 : y = q * y * q⁻¹ := by
          calc y = q⁻¹ * (q * y * q⁻¹) * q := by group
            _ = q⁻¹ * (q * (q * y * q⁻¹) * q⁻¹) * q := by rw [h1]
            _ = q * y * q⁻¹ := by group
        exact hyZ (h2 ▸ h)
      have := inv_mul_mem_of_relIndex_two hrel hy hqy hyZ hwZ
      have e : y⁻¹ * q * y * q⁻¹ = y⁻¹ * (q * y * q⁻¹) := by group
      rw [e]
      exact this
  have hBZ : ⁅Iv ν, Qv ν⁆ ≤ Zv ν := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    have := hqZ g₁⁻¹ (Subgroup.inv_mem _ hg₁) g₂ hg₂
    simpa [commutatorElement_def] using this
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = ⁅Iv ν, Qv ν⁆ := ⟨_, rfl⟩
  rw [← hB] at hBZ ⊢
  obtain ⟨d, hdst, hd3, hdQ⟩ := C.exists_cube hν
  have hdQN : ∀ g ∈ stab ν, g ∈ Subgroup.normalizer (Qv ν : Set G) := fun g hg =>
    le_normalizer_pCoreOf 2 (stab ν) hg
  have hBd : ∀ x ∈ B, d * x * d⁻¹ ∈ B := by
    have hle : B ≤ B.comap (MulAut.conj d).toMonoidHom := by
      rw [hB]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      show d * ⁅a, b⁆ * d⁻¹ ∈ ⁅Iv ν, Qv ν⁆
      have e : d * ⁅a, b⁆ * d⁻¹ = ⁅d * a * d⁻¹, d * b * d⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hIN hdst) a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp (hdQN d hdst) b).mp hb)
    intro x hx
    simpa using hle hx
  have hfix := C.cube_fixed_Zv hν hdst hd3 hdQ
  have hdvd : Nat.card ↥B ∣ 4 := by
    have := Subgroup.card_dvd_of_le hBZ
    rwa [C.card_Zv_true hν] at this
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  have hle4 : Nat.card ↥B ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : Nat.card ↥B = 1 ∨ Nat.card ↥B = 2 ∨
      Nat.card ↥B = 4 := by
    generalize Nat.card ↥B = c at hdvd hpos hle4 ⊢
    interval_cases c <;> omega
  rcases hcases with h1 | h2 | h4
  ·
    exfalso
    have hbot : B = ⊥ := Subgroup.card_eq_one.mp h1
    have hQI : ∀ q ∈ Qv ν, ∀ x ∈ Iv ν, q * x * q⁻¹ = x := by
      intro q hq x hx
      have hc : ⁅x⁻¹, q⁆ ∈ B := by
        rw [hB]; exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hx) hq
      rw [hbot, Subgroup.mem_bot] at hc
      have hc' : x⁻¹ * q * x * q⁻¹ = 1 := by simpa [commutatorElement_def] using hc
      calc q * x * q⁻¹ = x * (x⁻¹ * q * x * q⁻¹) := by group
        _ = x := by rw [hc']; group
    exact C.false_of_Qv_centralizes hν (C.isElemAbelian_Iv hδn) h8 hZI hIst hIN hQI
  ·
    exfalso
    obtain ⟨b₀, hb₀ne, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥B)).mp h2
    have hc1 : (⟨d * (b₀ : G) * d⁻¹, hBd _ b₀.2⟩ : ↥B) ≠ 1 := by
      intro h
      apply hb₀ne
      have h' : d * (b₀ : G) * d⁻¹ = 1 := congrArg Subtype.val h
      apply Subtype.ext
      calc (b₀ : G) = d⁻¹ * (d * (b₀ : G) * d⁻¹) * d := by group
        _ = 1 := by rw [h']; group
    have := congrArg Subtype.val (huniq _ hc1)
    exact hb₀ne (Subtype.ext (hfix b₀ (hBZ b₀.2) this))
  · exact (Subgroup.eq_of_le_of_card_ge hBZ (by rw [C.card_Zv_true hν]; omega)).symm ▸ rfl

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
