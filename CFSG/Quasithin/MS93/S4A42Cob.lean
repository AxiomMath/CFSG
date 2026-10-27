module

public import CFSG.Quasithin.MS93.S4A42Coc
public import CFSG.Quasithin.MS93.S4AH1

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

section Cob

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

omit hfull in
theorem zloc_le_dloc (δ : Vtx (puAmalgam h.le)) : Zloc h.le L δ ≤ Dloc h.le L δ :=
  puTrans_mono h.le (inf_le_inf_right _ (Xq_le_pCoreOf M)) δ

theorem exists_ltil_toSL3_eq {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {F : Type} [Field F]
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)} (hsurj : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1) (g : SL3 F) :
    ∃ l : ↥(stab (puAmalgam h.le) α), (l : (puAmalgam h.le).Universal) ∈ Ltil h.le L α ∧
      toSL3 ψ l = g := by
  obtain ⟨s, rfl⟩ := toSL3_surjective hsurj g
  have hs : (s : (puAmalgam h.le).Universal) ∈ ((Ltil h.le L α ⊔ Qv _ α : Subgroup _) : Set _) :=
    stab_eq_ltil_sup_qv h hfull hα ▸ s.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((ltil_le_stab h α).trans (stab_le_normalizer_qv _ α))] at hs
  obtain ⟨l, hl, q, hq, hlq⟩ := hs
  have hls : l ∈ stab (puAmalgam h.le) α := ltil_le_stab h α hl
  have hqs : q ∈ stab (puAmalgam h.le) α := qv_le_stab _ α hq
  refine ⟨⟨l, hls⟩, hl, ?_⟩
  have hq1 : toSL3 ψ ⟨q, hqs⟩ = 1 := by
    refine (toSL3_eq_one_iff hψ _).mpr fun v hv => ?_
    have hc := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hα
      (uloc_le_zm h hfull hα hv)) q hq
    show q * v * q⁻¹ = v
    rw [hc, mul_inv_cancel_right]
  have : s = ⟨l, hls⟩ * ⟨q, hqs⟩ := Subtype.ext hlq.symm
  rw [this, map_mul, hq1, mul_one]


end Cob

section Abstract

variable {S : Type*} [Group S] {F : Type} [Field F] {ρ : S →* SL3 F} {H Y P : Subgroup S}
  {f : S → (Fin 3 → F)}

omit [Group S] in
theorem cocycle_one [Group S] {ρ : S →* SL3 F} {H : Subgroup S} {f : S → (Fin 3 → F)}
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b) :
    f 1 = 0 := by
  have := hf 1 H.one_mem 1 H.one_mem
  rw [mul_one, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at this
  exact (add_eq_left.mp this.symm)

theorem cocycle_conj_ker
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b)
    {a k : S} (ha : a ∈ H) (hk : k ∈ H) (hk1 : ρ k = 1) :
    f (a * k * a⁻¹) = ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f k := by
  have hai : a⁻¹ ∈ H := H.inv_mem ha
  have h1 := hf a ha (k * a⁻¹) (H.mul_mem hk hai)
  have h2 := hf k hk a⁻¹ hai
  have h3 := hf a ha a⁻¹ hai
  rw [mul_inv_cancel, cocycle_one hf] at h3
  rw [mul_assoc, h1, h2, hk1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
    Matrix.mulVec_add, add_comm (_ *ᵥ f k), ← add_assoc, ← h3, zero_add]

theorem cocycle_pow_ker
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b)
    {k : S} (hk : k ∈ H) (hk1 : ρ k = 1) (n : ℕ) : f (k ^ n) = n • f k := by
  induction n with
  | zero => rw [pow_zero, cocycle_one hf, zero_nsmul]
  | succ n ih =>
    rw [pow_succ, hf _ (H.pow_mem hk n) k hk, ih, add_nsmul, one_nsmul, map_pow, hk1, one_pow,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem cocycle_eq_zero_of_ker [CharP F 2]
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b)
    (hYH : Y ≤ H) (hfY : ∀ y ∈ Y, f y = 0) (hρH : ∀ g : SL3 F, ∃ a ∈ H, ρ a = g)
    (hP : ∀ k ∈ H, ρ k = 1 → ∃ b : ℕ, Odd b ∧ k ^ b ∈ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set S)) (hYρ : Y.map ρ ≠ ⊥) {k : S} (hk : k ∈ H)
    (hk1 : ρ k = 1) : f k = 0 := by
  have hfixP : ∀ k ∈ H, ρ k = 1 → k ∈ P → f k ∈ fixN (Y.map ρ) := by
    intro k hk hk1 hkP
    rw [mem_fixN]
    rintro _ ⟨y, hyY, rfl⟩
    have hc : y * k * y⁻¹ * k⁻¹ ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hPY hkP) _).mp (Y.inv_mem hyY)
      have hmul := Y.mul_mem hyY this
      simpa [mul_assoc] using hmul
    have hck : y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
    have key := cocycle_conj_ker hf (hYH hyY) hk hk1
    rw [hck, hf _ (hYH hc) k hk, hfY _ hc, zero_add] at key
    have hρc : ρ (y * k * y⁻¹ * k⁻¹) = 1 := by
      simp only [map_mul, map_inv, hk1, mul_one, inv_one, mul_inv_cancel]
    rw [hρc, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at key
    exact key.symm
  have hfix : ∀ k ∈ H, ρ k = 1 → f k ∈ fixN (Y.map ρ) := by
    intro k hk hk1
    obtain ⟨b, hb, hkb⟩ := hP k hk hk1
    have h := hfixP (k ^ b) (H.pow_mem hk b) (by rw [map_pow, hk1, one_pow]) hkb
    rwa [cocycle_pow_ker hf hk hk1 b, odd_nsmul_eq hb] at h
  by_contra hne
  apply hYρ
  have htop : fixN (Y.map ρ) = ⊤ := by
    refine eq_top_of_forall_mulVec_mem hne fun g => ?_
    obtain ⟨a, ha, rfl⟩ := hρH g
    rw [← cocycle_conj_ker hf ha hk hk1]
    refine hfix _ (H.mul_mem (H.mul_mem ha hk) (H.inv_mem ha)) ?_
    simp only [map_mul, map_inv, hk1, mul_one, mul_inv_cancel]
  rw [eq_bot_iff]
  rintro _ ⟨y, hyY, rfl⟩
  rw [Subgroup.mem_bot]
  apply eq_one_of_mulVec_eq_self
  intro x
  have hx : x ∈ fixN (Y.map ρ) := htop ▸ Submodule.mem_top
  exact (mem_fixN.mp hx) _ ⟨y, hyY, rfl⟩

theorem exists_coboundary_of_cocycle [Finite F] [CharP F 2]
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b)
    (hYH : Y ≤ H) (hfY : ∀ y ∈ Y, f y = 0) (hρH : ∀ g : SL3 F, ∃ a ∈ H, ρ a = g)
    (hP : ∀ k ∈ H, ρ k = 1 → ∃ b : ℕ, Odd b ∧ k ^ b ∈ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set S)) (hYρ : Y.map ρ ≠ ⊥) (hY2 : IsPGroup 2 Y) :
    ∃ n : Fin 3 → F, ∀ a ∈ H, f a = ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  have hker : ∀ k ∈ H, ρ k = 1 → f k = 0 := fun k hk hk1 =>
    cocycle_eq_zero_of_ker hf hYH hfY hρH hP hPY hYρ hk hk1
  choose pre hpreH hpre using hρH
  have hfib : ∀ a ∈ H, f (pre (ρ a)) = f a := by
    intro a ha
    have hk : a⁻¹ * pre (ρ a) ∈ H := H.mul_mem (H.inv_mem ha) (hpreH _)
    have hk1 : ρ (a⁻¹ * pre (ρ a)) = 1 := by rw [map_mul, map_inv, hpre, inv_mul_cancel]
    have := hf a ha _ hk
    rw [mul_inv_cancel_left, hker _ hk hk1, Matrix.mulVec_zero, add_zero] at this
    exact this
  set fs : SL3 F → (Fin 3 → F) := fun g => f (pre g) with hfs
  have hcoc : IsCocycle3 fs := by
    intro g₁ g₂
    have h12 : pre g₁ * pre g₂ ∈ H := H.mul_mem (hpreH g₁) (hpreH g₂)
    have := hfib _ h12
    rw [map_mul, hpre, hpre] at this
    simp only [hfs]
    rw [this, hf _ (hpreH g₁) _ (hpreH g₂), hpre]
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, ρ y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hYρ
    rw [eq_bot_iff]
    rintro _ ⟨y, hyY, rfl⟩
    exact (Subgroup.mem_bot).mpr (hcon y hyY)
  obtain ⟨e, he⟩ := hY2 ⟨y, hyY⟩
  have hye : ρ y ^ 2 ^ e = 1 := by
    have : y ^ 2 ^ e = 1 := by
      have := congrArg Subtype.val he
      simpa using this
    rw [← map_pow, this, map_one]
  obtain ⟨j, hj2, hj1⟩ := exists_pow_involution hy1 hye
  have ht0 : fs (ρ y ^ 2 ^ j) = 0 := by
    simp only [hfs]
    rw [← map_pow, hfib _ (hYH (Y.pow_mem hyY _)), hfY _ (Y.pow_mem hyY _)]
  obtain ⟨n, hn⟩ := exists_coboundary hcoc hj2 hj1 ht0
  refine ⟨n, fun a ha => ?_⟩
  rw [← hfib a ha]
  exact hn _

end Abstract

end CFSG.Quasithin.MS93.S4A
