module

public import CFSG.RankThree.PartOne.SEITZ5.UPlane
public import CFSG.RankThree.PartOne.SEITZ5.UConf
public import CFSG.RankThree.PartOne.SEITZ5.USiegel
public import CFSG.RankThree.PartOne.SEITZ5.UTransfer

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Subfield K} {σ : K ≃+* K} {N : ℕ}

theorem hfull_rank_one (hN : 4 ≤ N) (hσi : ∀ c, σ (σ c) = c) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    (hr2 : Nat.card (ratFix σ k) = 2) {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1)
    {M : Subgroup (SUid σ N)}
    (hM_rat : ∀ a : Fin N → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c)
    (hM_trans : ∀ x x' : Fin N → K, IsRat k x → IsRat k x' → x ≠ 0 → x' ≠ 0 →
      herm σ x x = 0 → herm σ x' x' = 0 → ∃ r ∈ M, r • x = x')
    {lam : K} (hNlam : σ lam * lam ∉ k) {w₀ : Fin N → K} (hw₀ : IsRat k w₀) (hw₀0 : w₀ ≠ 0)
    (hw₀iso : herm σ w₀ w₀ = 0) (hTy : ∃ t ∈ M, IsTv σ t (lam • w₀) 1) :
    ∃ e : Fin N → K, IsRat k e ∧ e ≠ 0 ∧ herm σ e e = 0 ∧
      ∀ b : fixSub σ, ∃ t ∈ M, IsTv σ t e (b : K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set i₁ : Fin N := ⟨0, by omega⟩ with hi₁
  set i₂ : Fin N := ⟨1, by omega⟩ with hi₂
  have hi12 : i₁ ≠ i₂ := by
    intro h
    have := congrArg Fin.val h
    simp [hi₁, hi₂] at this
  have h1ω : 1 + ω ≠ 0 := fun h => hω1 (by linear_combination h - h2)
  set c : K := (1 + ω)⁻¹ with hc
  have hck : c ∈ k := k.inv_mem (k.add_mem k.one_mem hωk)
  have hcc : c * (1 + ω) = 1 := inv_mul_cancel₀ h1ω
  set a₀ : Fin N → K := vec2 i₁ i₂ 1 1 with ha₀
  set b₀ : Fin N → K := vec2 i₁ i₂ c (c * ω) with hb₀
  have ha₀rat : IsRat k a₀ := isRat_vec2 _ _ k.one_mem k.one_mem
  have hb₀rat : IsRat k b₀ := isRat_vec2 _ _ hck (k.mul_mem hck hωk)
  have ha₀iso : herm σ a₀ a₀ = 0 := by
    rw [ha₀, herm_vec2_vec2_same hi12, map_one]
    linear_combination h2
  have hb₀iso : herm σ b₀ b₀ = 0 := by
    rw [hb₀, herm_vec2_vec2_same hi12]
    have : σ c * c + σ (c * ω) * (c * ω) = (σ c * c) * (1 + σ ω * ω) := by
      rw [map_mul]
      ring
    rw [this, hωn]
    linear_combination (σ c * c) * h2
  have hab₀ : herm σ a₀ b₀ = 1 := by
    rw [ha₀, hb₀, herm_vec2_vec2_same hi12, map_one]
    linear_combination hcc
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    have := congrFun h i₁
    rw [ha₀, vec2_apply_left hi12] at this
    exact one_ne_zero this
  obtain ⟨r, hrM, hr⟩ := hM_trans w₀ a₀ hw₀ ha₀rat hw₀0 ha₀0 hw₀iso ha₀iso
  obtain ⟨ty, htyM, hty⟩ := hTy
  have hty' : IsTv σ ty w₀ (1 * (σ lam * lam)) := isTv_smul_vec.1 hty
  have hconj : IsTv σ (r * ty * r⁻¹) a₀ (σ lam * lam) := by
    have := hty'.conj r
    rw [hr, one_mul] at this
    exact this
  refine ⟨a₀, ha₀rat, ha₀0, ha₀iso, ?_⟩
  exact hfull_of_plane hσi hp hp2 hK hr2 ha₀iso hb₀iso hab₀ (ν := normF hσi lam)
    (fun h => hNlam (mem_ratFix.1 h))
    (hM_rat a₀ ha₀rat ha₀iso 1 k.one_mem (map_one σ))
    ⟨r * ty * r⁻¹, M.mul_mem (M.mul_mem hrM htyM) (M.inv_mem hrM), hconj⟩
    (hM_rat b₀ hb₀rat hb₀iso 1 k.one_mem (map_one σ))

theorem hfull_rank_two (hN : 4 ≤ N) (hσi : ∀ c, σ (σ c) = c) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    (hr2 : Nat.card (ratFix σ k) = 2) (hk4 : Nat.card k = 4) {ω : K} (hωk : ω ∈ k)
    (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1) (hω : σ ω = ω ^ 2) (hω2 : ω ^ 2 + ω + 1 = 0)
    {M : Subgroup (SUid σ N)}
    (hM_rat : ∀ a : Fin N → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c)
    {y : Fin N → K} (hyiso : herm σ y y = 0) (hTy : ∃ t ∈ M, IsTv σ t y 1) {i j : Fin N}
    (hi : y i ≠ 0) (hj : ∀ c ∈ k, y j ≠ c * y i) :
    ∃ f : Fin N → K, IsRat k f ∧ f ≠ 0 ∧ herm σ f f = 0 ∧
      ∀ b : fixSub σ, ∃ t ∈ M, IsTv σ t f (b : K) := by
  obtain ⟨e, w, f, hre, hrw, hrf, hee, hww, hff, hew, hwf, hef, hβ, hρ⟩ :=
    exists_config hωk hω1 hω hω2 hωn hN hi hj
  have hσ1 : σ (1 : K) = 1 := map_one σ
  have hwe : herm σ w e = 0 := herm_eq_zero_comm σ hσi hew
  have hTe := hM_rat e hre hee 1 k.one_mem hσ1
  have hTw := hM_rat w hrw hww 1 k.one_mem hσ1
  have hTf := hM_rat f hrf hff 1 k.one_mem hσ1
  have hsieg : ∀ μ ∈ k, σ μ * μ = 1 → ∃ t ∈ M, ∀ x : Fin N → K,
      t • x = x + (μ * herm σ e x) • w + (σ μ * herm σ w x) • e := by
    intro μ hμk hμ
    have hr : IsRat k (e + μ • w) := fun r => k.add_mem (hre r) (k.mul_mem hμk (hrw r))
    have hiso : herm σ (e + μ • w) (e + μ • w) = 0 := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hee, hww, hew,
        hwe, mul_zero, add_zero]
    obtain ⟨t₁, ht₁M, ht₁⟩ := hM_rat _ hr hiso 1 k.one_mem hσ1
    obtain ⟨t₂, ht₂M, ht₂⟩ := hTe
    obtain ⟨t₃, ht₃M, ht₃⟩ := hTw
    exact ⟨t₁ * t₂ * t₃, M.mul_mem (M.mul_mem ht₁M ht₂M) ht₃M,
      siegel_of_three hσi hee hww hew hμ ht₁ ht₂ ht₃⟩
  have hS1 := hsieg 1 k.one_mem (by simp)
  have hSω := hsieg ω hωk hωn
  have hβ₂ : herm σ w y ≠ 0 := fun h => hρ (by rw [h, zero_div]; exact k.zero_mem)
  have hzf : herm σ (σ (herm σ w y) • e + σ (herm σ e y) • w) f ≠ 0 := by
    rw [herm_add_left, herm_smul_left, herm_smul_left, hwf, mul_zero, add_zero, hσi]
    exact mul_ne_zero hβ₂ hef
  have hz0 : σ (herm σ w y) • e + σ (herm σ e y) • w ≠ 0 := fun h => hzf (by rw [h, herm_zero_left])
  have hZ := exists_isTv_z_rat hσi hk4 hr2 hp hp2 hK hee hww hyiso hew hβ hz0 hωk hω hω2 hρ hTe
    hTw hTy hS1 hSω
  have hzz : herm σ (σ (herm σ w y) • e + σ (herm σ e y) • w)
      (σ (herm σ w y) • e + σ (herm σ e y) • w) = 0 :=
    (frameOf hσi hee hww hyiso hew hβ).hz
  exact ⟨f, hrf, fun h => hef (by rw [h, herm_zero_right]), hff,
    hfull_of_isTv_z hσi hzz hzf hTf hZ⟩

end CFSG.RankThree.PartOne.SEITZ5
