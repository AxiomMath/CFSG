module

public import CFSG.RankThree.PartOne.SEITZ5.UGen
public import CFSG.RankThree.PartOne.SEITZ5.UCoreFinal

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def normF (hσ : ∀ c, σ (σ c) = c) (a : K) : fixSub σ :=
  ⟨σ a * a, by rw [mem_fixSub, map_mul, hσ, mul_comm]⟩

@[expose] def traceF (hσ : ∀ c, σ (σ c) = c) (a : K) : fixSub σ :=
  ⟨a + σ a, by rw [mem_fixSub, map_add, hσ, add_comm]⟩

section FrameOf

variable [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {e w v : Fin n → K} (he : herm σ e e = 0)
  (hw : herm σ w w = 0) (hv : herm σ v v = 0) (hew : herm σ e w = 0) (hβ : herm σ e v ≠ 0)

include hσ he hw hv hew hβ in
theorem frameOf_w_eq :
    w = (σ (herm σ e v))⁻¹ • (frameOf hσ he hw hv hew hβ).z +
      σ (herm σ w v / herm σ e v) • (frameOf hσ he hw hv hew hβ).e := by
  have hσβ : σ (herm σ e v) ≠ 0 := (map_ne_zero σ).2 hβ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  show w = (σ (herm σ e v))⁻¹ • (σ (herm σ w v) • e + σ (herm σ e v) • w) +
    σ (herm σ w v / herm σ e v) • e
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_div₀]
  field_simp
  linear_combination (-(σ (herm σ w v) * e i)) * h2

include hσ he hw hv hew hβ in
theorem frameOf_hwu :
    herm σ w (frameOf hσ he hw hv hew hβ).u = herm σ w v / herm σ e v := by
  show herm σ w ((herm σ e v)⁻¹ • v) = _
  rw [herm_smul_right, div_eq_inv_mul]

include hσ he hw hv hew hβ in
theorem frameOf_hwe : herm σ w (frameOf hσ he hw hv hew hβ).e = 0 :=
  herm_eq_zero_comm σ hσ hew

include hσ he hw hv hew hβ in
theorem frameOf_hwz : herm σ w (frameOf hσ he hw hv hew hβ).z = 0 := by
  have hwe : herm σ w e = 0 := herm_eq_zero_comm σ hσ hew
  show herm σ w (σ (herm σ w v) • e + σ (herm σ e v) • w) = 0
  simp [herm_add_right, herm_smul_right, hwe, hw]

end FrameOf

theorem exists_isTv_z_rat [Finite K] [CharP K 2] {k : Subfield K}
    (hσ : ∀ c, σ (σ c) = c) (hk4 : Nat.card k = 4) (hr2 : Nat.card (ratFix σ k) = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    {e w v : Fin n → K} (he : herm σ e e = 0) (hw : herm σ w w = 0) (hv : herm σ v v = 0)
    (hew : herm σ e w = 0) (hβ : herm σ e v ≠ 0)
    (hz0 : σ (herm σ w v) • e + σ (herm σ e v) • w ≠ 0) {ω : K} (hωk : ω ∈ k)
    (hω : σ ω = ω ^ 2) (hω2 : ω ^ 2 + ω + 1 = 0) (hρ : herm σ w v / herm σ e v ∉ k)
    {H : Subgroup (SUid σ n)} (hTe : ∃ t ∈ H, IsTv σ t e 1) (hTw : ∃ t ∈ H, IsTv σ t w 1)
    (hTv : ∃ t ∈ H, IsTv σ t v 1)
    (hS1 : ∃ t ∈ H, ∀ x, t • x = x + ((1 : K) * herm σ e x) • w + (σ 1 * herm σ w x) • e)
    (hSω : ∃ t ∈ H, ∀ x, t • x = x + (ω * herm σ e x) • w + (σ ω * herm σ w x) • e) :
    ∀ c : fixSub σ, ∃ t ∈ H, IsTv σ t (σ (herm σ w v) • e + σ (herm σ e v) • w) (c : K) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P := frameOf hσ he hw hv hew hβ with hP
  set ρ : K := herm σ w v / herm σ e v with hρdef
  set ζ : K := (σ (herm σ e v))⁻¹ with hζdef
  have hσβ : σ (herm σ e v) ≠ 0 := (map_ne_zero σ).2 hβ
  have hζ : ζ ≠ 0 := inv_ne_zero hσβ
  have hw_eq : w = ζ • P.z + σ ρ • P.e := frameOf_w_eq hσ he hw hv hew hβ
  have hwe : herm σ w P.e = 0 := frameOf_hwe hσ he hw hv hew hβ
  have hwz : herm σ w P.z = 0 := frameOf_hwz hσ he hw hv hew hβ
  have hwu : herm σ w P.u = ρ := frameOf_hwu hσ he hw hv hew hβ
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω2
  have hσω2 : σ (ω ^ 2) = ω := by
    rw [map_pow, hω, ← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hω3, pow_one, mul_one]
  obtain ⟨y, hy⟩ : ∃ y : fixSub σ, (y : K) = ρ + σ ρ := ⟨traceF hσ ρ, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : fixSub σ, (x : K) = ω * ρ + ω ^ 2 * σ ρ :=
    ⟨⟨ω * ρ + ω ^ 2 * σ ρ, by
      rw [mem_fixSub, map_add, map_mul, map_mul, hω, hσω2, hσ]
      ring⟩, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : fixSub σ, (γ : K) = σ ρ * ρ := ⟨normF hσ ρ, rfl⟩
  have hρxy : ρ = x + ω ^ 2 * y := by
    rw [hx, hy]
    linear_combination (-ρ - 2 * σ ρ) * hω2 + (ρ + σ ρ * ω + σ ρ) * h2
  have hγxy : (γ : K) = (x : K) ^ 2 + x * y + (y : K) ^ 2 := by
    rw [hγ, hx, hy]
    linear_combination (-ρ ^ 2 + ρ * σ ρ - σ ρ ^ 2 * ω ^ 2 - σ ρ ^ 2 +
      ω * (-2 * ρ * σ ρ + σ ρ ^ 2)) * hω2 + (-(ρ * σ ρ)) * h2
  have hτ1 : ((y : fixSub σ) : K) = 1 * σ ρ + σ 1 * ρ := by
    rw [hy, map_one]
    ring
  have hτω : (((x + y : fixSub σ)) : K) = ω * σ ρ + σ ω * ρ := by
    rw [Subfield.coe_add, hx, hy, hω]
    linear_combination (-ρ + σ ρ) * hω2 + (ρ * ω + ρ - σ ρ * ω) * h2
  have hγP : (γ : K) = σ ρ * ρ := hγ
  obtain ⟨te, hteH, hte⟩ := hTe
  obtain ⟨tv, htvH, htv⟩ := hTv
  obtain ⟨tw, htwH, htw⟩ := hTw
  obtain ⟨t1, ht1H, ht1⟩ := hS1
  obtain ⟨tω, htωH, htω⟩ := hSω
  have hteP : IsTv σ te P.e ((1 : fixSub σ) : K) := hte
  have hvu : v = herm σ e v • P.u := by
    show v = herm σ e v • ((herm σ e v)⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hβ, one_smul]
  have htv' : IsTv σ tv P.u ((normF hσ (herm σ e v) : fixSub σ) : K) := by
    have := htv
    rw [hvu, isTv_smul_vec] at this
    simpa [normF] using this
  have hb₀ : normF hσ (herm σ e v) ≠ 0 := fun h => mul_ne_zero hσβ hβ (congrArg Subtype.val h)
  have hE : ∃ t ∈ affGroup P H, Aff P t (u2 (1 : fixSub σ)) 0 0 :=
    ⟨te, ⟨hteH, triv_tv_e P hteP, u2 1, 0, 0, aff_tv_e P hteP⟩, aff_tv_e P hteP⟩
  have hU : ∃ t ∈ affGroup P H, ∃ b₀ : fixSub σ, b₀ ≠ 0 ∧ Aff P t (l2 b₀) 0 0 :=
    ⟨tv, ⟨htvH, triv_tv_u P htv', l2 (normF hσ (herm σ e v)), 0, 0, aff_tv_u P hσ htv'⟩,
      normF hσ (herm σ e v), hb₀, aff_tv_u P hσ htv'⟩
  have hW : ∃ t ∈ affGroup P H, Aff P t (u2 γ) 0 (ρ * ζ) :=
    ⟨tw, ⟨htwH, triv_tv_w P hw_eq htw, u2 γ, 0, ρ * ζ, aff_tv_w P hγP hwe hwz hwu hw_eq htw⟩,
      aff_tv_w P hγP hwe hwz hwu hw_eq htw⟩
  have h1A : Aff P t1 (u2 y) 0 (1 * ζ) := aff_siegel P hτ1 hwe hwz hwu hw_eq ht1
  rw [one_mul] at h1A
  have h1 : ∃ t ∈ affGroup P H, Aff P t (u2 y) 0 ζ :=
    ⟨t1, ⟨ht1H, triv_siegel P hw_eq ht1, u2 y, 0, ζ, h1A⟩, h1A⟩
  have hωA : Aff P tω (u2 (x + y)) 0 (ω * ζ) := aff_siegel P hτω hwe hwz hwu hw_eq htω
  have hωg : ∃ t ∈ affGroup P H, Aff P t (u2 (x + y)) 0 (ω * ζ) :=
    ⟨tω, ⟨htωH, triv_siegel P hw_eq htω, u2 (x + y), 0, ω * ζ, hωA⟩, hωA⟩
  exact exists_isTv_z hσ hk4 hr2 hp hp2 hK (P := P) hz0 hωk hω hω2 hρ hζ hρxy hγxy hE hU hW h1
    hωg

end CFSG.RankThree.PartOne.SEITZ5
