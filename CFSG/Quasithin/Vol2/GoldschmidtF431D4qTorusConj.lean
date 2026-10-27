module

public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qTorusCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qTorusRoot

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage4.Hex
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed

theorem r01_eq_hexPos : r01 = hexPos 1 := by
  funext i
  fin_cases i <;> decide

theorem r13_eq_hexPos : r13 = hexPos 2 := by
  funext i
  fin_cases i <;> decide

theorem r12_eq_hexPos : r12 = hexPos 3 := by
  funext i
  fin_cases i <;> decide

theorem r23_eq_hexPos : r23 = hexPos 4 := by
  funext i
  fin_cases i <;> decide

theorem r11_eq_hexPos : r11 = hexPos 5 := by
  funext i
  fin_cases i <;> decide

theorem r10_eq_hexPos : r10 = hexPos 6 := by
  funext i
  fin_cases i <;> decide


variable {K : Type} [Field K] {σ : K →+* K}

theorem torus_fix_hexGroup (hσ : ∀ c, σ (σ (σ c)) = c) (s : fixedUnits σ) (t : Kˣ)
    (hw : chi σ s t d01 ≠ 1 ∧ chi σ s t d13 ≠ 1 ∧ chi σ s t d12 ≠ 1 ∧ chi σ s t d23 ≠ 1 ∧
      chi σ s t d11 ≠ 1 ∧ chi σ s t d10 ≠ 1)
    {i : ℤ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) {x : twistedGroup σ}
    (hx : x ∈ hexGroup (twistedX σ) i) (hfix : tor hσ s t * x * (tor hσ s t)⁻¹ = x) : x = 1 := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
  interval_cases i
  · exact fix_short hσ isRoot_d01 rho_d01 (proj_d01.trans r01_eq_hexPos) s t w1 hx hfix
  · exact fix_long hσ isRoot_d13 rho_d13 (proj_d13.trans r13_eq_hexPos) s t w2 hx hfix
  · exact fix_short hσ isRoot_d12 rho_d12 (proj_d12.trans r12_eq_hexPos) s t w3 hx hfix
  · exact fix_long hσ isRoot_d23 rho_d23 (proj_d23.trans r23_eq_hexPos) s t w4 hx hfix
  · exact fix_short hσ isRoot_d11 rho_d11 (proj_d11.trans r11_eq_hexPos) s t w5 hx hfix
  · exact fix_long hσ isRoot_d10 rho_d10 (proj_d10.trans r10_eq_hexPos) s t w6 hx hfix


theorem fix_of_fix_proj (hσ : ∀ c, σ (σ (σ c)) = c) (s : fixedUnits σ) (t : Kˣ) {i : ℤ}
    (hi1 : 1 ≤ i) (hi6 : i ≤ 6) {x : twistedGroup σ} (hx : x ∈ hexGroup (twistedX σ) i)
    (h : hexProj (twistedGroup σ) (tor hσ s t) * hexProj (twistedGroup σ) x *
      (hexProj (twistedGroup σ) (tor hσ s t))⁻¹ = hexProj (twistedGroup σ) x) :
    tor hσ s t * x * (tor hσ s t)⁻¹ = x := by
  have hy : tor hσ s t * x * (tor hσ s t)⁻¹ ∈ hexGroup (twistedX σ) i :=
    (d4RGD2 σ hσ).invariant i (isRoot_of_pos_le hi1 hi6) _ (tor_mem_torus hσ s t) x hx
  have hU : x⁻¹ * (tor hσ s t * x * (tor hσ s t)⁻¹) ∈ posUnipotent (g2Shape (twistedX σ)) :=
    mul_mem (inv_mem (hexGroup_le_posUnipotent hi1 hi6 hx))
      (hexGroup_le_posUnipotent hi1 hi6 hy)
  have hker : x⁻¹ * (tor hσ s t * x * (tor hσ s t)⁻¹) ∈ (hexProj (twistedGroup σ)).ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [h, inv_mul_cancel]
  have h0 := posUnipotent_inf_ker_hexProj (twistedData σ hσ)
  have h1 : x⁻¹ * (tor hσ s t * x * (tor hσ s t)⁻¹) ∈ (⊥ : Subgroup (twistedGroup σ)) :=
    h0 ▸ ⟨hU, hker⟩
  exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 h1)).symm

variable [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)

theorem modelTor_mem_cartan (hσ : ∀ c, σ (σ (σ c)) = c) (s : fixedUnits σ) (t : Kˣ) :
    hexProj (twistedGroup σ) (tor hσ s t) ∈
      (d4ModelSystem σ hq hK hσq).B ⊓ (d4ModelSystem σ hq hK hσq).N :=
  ⟨Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (tor_mem_torus hσ s t)),
    (hexQuotRGD2 (twistedData σ hσ)).H_le_N (Subgroup.mem_map_of_mem _ (tor_mem_torus hσ s t))⟩

theorem modelTor_fix_root (hσ : ∀ c, σ (σ (σ c)) = c) (s : fixedUnits σ) (t : Kˣ)
    (hw : chi σ s t d01 ≠ 1 ∧ chi σ s t d13 ≠ 1 ∧ chi σ s t d12 ≠ 1 ∧ chi σ s t d23 ≠ 1 ∧
      chi σ s t d11 ≠ 1 ∧ chi σ s t d10 ≠ 1)
    {i : ℤ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) {x : twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)}
    (hx : x ∈ (d4ModelSystem σ hq hK hσq).root i)
    (hfix : hexProj (twistedGroup σ) (tor hσ s t) * x *
      (hexProj (twistedGroup σ) (tor hσ s t))⁻¹ = x) : x = 1 := by
  obtain ⟨x', hx', rfl⟩ := hx
  have h1 := fix_of_fix_proj hσ s t hi1 hi6 hx' hfix
  rw [torus_fix_hexGroup hσ s t hw hi1 hi6 hx' h1, map_one]

theorem modelTor_fix_U (hσ : ∀ c, σ (σ (σ c)) = c) (s : fixedUnits σ) (t : Kˣ)
    (hw : chi σ s t d01 ≠ 1 ∧ chi σ s t d13 ≠ 1 ∧ chi σ s t d12 ≠ 1 ∧ chi σ s t d23 ≠ 1 ∧
      chi σ s t d11 ≠ 1 ∧ chi σ s t d10 ≠ 1)
    {y : twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)} (hy : y ∈ (d4ModelSystem σ hq hK hσq).U)
    (hfix : hexProj (twistedGroup σ) (tor hσ s t) * y *
      (hexProj (twistedGroup σ) (tor hσ s t))⁻¹ = y) : y = 1 :=
  centralizer_U_trivial (d4ModelSystem σ hq hK hσq) (modelTor_mem_cartan hq hK hσq hσ s t)
    (fun _ hk1 hk6 _ hx hf => modelTor_fix_root hq hK hσq hσ s t hw hk1 hk6 hx hf) hy hfix

end CFSG.Quasithin.H13.F431.D4q.F48
