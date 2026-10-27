module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Main
public import CFSG.RankThree.PartOne.SEITZ2.SU3Stab
public import CFSG.RankThree.PartOne.CTP.SeitzMaxUnitary
public import CFSG.RankThree.PartOne.CTP.StdBlocks

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Frame

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}

omit [CharP K 2] in
theorem single_mem_of_mem {k : Subfield K} {n : ℕ} (j i : Fin n) {c : K} (hc : c ∈ k) :
    (Pi.single j c : Fin n → K) i ∈ k := by
  rcases eq_or_ne i j with rfl | h
  · simpa using hc
  · rw [Pi.single_eq_of_ne h]
    exact k.zero_mem

theorem exists_rational_frame {k : Subfield K} {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1)
    (hωn : σ ω * ω = 1) :
    ∃ a b : Fin 3 → K, herm σ a a = 0 ∧ herm σ b b = 0 ∧ herm σ a b = 1 ∧ IsRat k a ∧
      IsRat k b ∧ a 2 = 0 ∧ b 2 = 0 ∧ a 0 * b 1 - a 1 * b 0 ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu : σ (1 : K) * 1 = -1 := by
    rw [map_one, mul_one]
    linear_combination h2
  let W : WittData σ := ⟨1, ω, hu, hωn, hω1⟩
  have h1ω : (1 - ω) ≠ 0 := W.one_sub_ω_ne_zero
  refine ⟨W.hypA 1, W.hypB 1, W.herm_hypA_hypA, W.herm_hypB_hypB, W.herm_hypA_hypB, ?_, ?_,
    W.hypA_succ_succ 0, W.hypB_succ_succ 0, ?_⟩
  · intro i
    rw [WittData.hypA, Pi.add_apply]
    exact k.add_mem (single_mem_of_mem _ _ k.one_mem) (single_mem_of_mem _ _ k.one_mem)
  · intro i
    rw [WittData.hypB, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    exact k.mul_mem (k.inv_mem (k.sub_mem k.one_mem hωk))
      (k.add_mem (single_mem_of_mem _ _ k.one_mem)
        (single_mem_of_mem _ _ (k.mul_mem k.one_mem hωk)))
  · simp only [WittData.hypA_zero, WittData.hypA_one, WittData.hypB_zero, WittData.hypB_one]
    have : (1 : K) * ((1 - ω)⁻¹ * (W.u * ω)) - W.u * (1 - ω)⁻¹ = -W.u := by
      field_simp
      ring
    rw [this]
    exact neg_ne_zero.2 W.u_ne_zero

end Frame

section Bridge

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCUnitaryCoord
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

variable {f f₀ : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem SUid_eq_unitarySU (h : UnitaryFieldData 2 f K) (n : ℕ) :
    SUid (unitaryInvolution K 2 f) n = unitarySU 2 f K n :=
  SUid_eq_statedSU h.card_eq_sq n

theorem unitaryInvolution_eq_bar (h : UnitaryFieldData 2 f K) (c : K) :
    unitaryInvolution K 2 f c = h.bar c := by
  rw [unitaryInvolution_apply, h.bar_apply]

omit [Finite K] [CharP K 2] in
theorem coordEmbed_mulVec_single_two (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K (0 : Fin 3) 1 X *ᵥ (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
  have h1 : coordProj K (0 : Fin 3) 1 *ᵥ (Pi.single 2 1 : Fin 3 → K) = 0 := by
    funext a
    fin_cases a <;> simp [coordProj, coordIncl, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [coordEmbed, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, h1]
  simp

end Bridge

section Final

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

theorem subfieldPairSU_three : SubfieldPairSU 3 := by
  intro f f₀ K _ h k h₀ hbar p hp hp5 hf hnot A hne
  classical
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have : Finite k := h₀.finite
  have : CharP k 2 := h₀.charP
  have hf₀ : 2 ≤ f₀ := by
    have := h₀.one_le
    by_contra hlt
    exact hnot ⟨rfl, by omega⟩
  have hf2 : 2 ≤ f := by rw [hf]; nlinarith [hp.two_le]
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hσ₀ : IsUnitaryInvolution (unitaryInvolution k 2 f₀) :=
    isUnitaryInvolution_unitaryInvolution h₀.card_eq_sq
  set σ := unitaryInvolution K 2 f with hσdef
  set σ₀ := unitaryInvolution k 2 f₀ with hσ₀def
  have hσbar : ∀ c : K, σ c = h.bar c := fun c => unitaryInvolution_eq_bar h c
  have hσ₀bar : ∀ c : k, σ₀ c = h₀.bar c := fun c => unitaryInvolution_eq_bar h₀ c
  have hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K) := fun c => by
    rw [hσbar, ← hbar, hσ₀bar]
  have hfix : fixSub σ = h.fixedField := by
    ext c
    rw [mem_fixSub, UnitaryFieldData.mem_fixedField, hσbar]
  have hcardF : Nat.card (fixSub σ) = 2 ^ f := by
    rw [hfix]
    exact h.card_fixedField
  have hcardk0 : Nat.card (ratFix σ k) = 2 ^ f₀ := by
    rw [← h₀.card_fixedField]
    apply Nat.card_congr
    refine ⟨fun c => ⟨⟨c.1.1, c.2⟩, ?_⟩, fun d => ⟨⟨(d.1 : K), ?_⟩, d.1.2⟩, ?_, ?_⟩
    · apply Subtype.ext
      change ((h₀.bar ⟨c.1.1, c.2⟩ : k) : K) = c.1.1
      rw [hbar]
      have := c.1.2
      rw [mem_fixSub, hσbar] at this
      exact this
    · rw [mem_fixSub, hσbar, ← hbar]
      have := d.2
      rw [UnitaryFieldData.mem_fixedField] at this
      exact congrArg (fun z : k => (z : K)) this
    · intro c
      rfl
    · intro d
      rfl
  have hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p := by
    rw [hcardF, hcardk0, ← pow_mul, hf, mul_comm]
  have hk4 : 4 ∣ Nat.card (ratFix σ k) := by
    rw [hcardk0]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact pow_dvd_pow 2 hf₀
  have hq : ∃ s : k, s ≠ 0 ∧ σ₀ s * s ≠ 1 :=
    exists_norm_ne_one h₀.card_eq_sq (by
      have : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
      omega)
  obtain ⟨ω₀, hω₀n, hω₀1⟩ := hσ₀.exists_norm_one_ne_one
  have hωk : (ω₀ : K) ∈ k := ω₀.2
  have hω1 : (ω₀ : K) ≠ 1 := fun h1 => hω₀1 (Subtype.ext h1)
  have hωn : σ (ω₀ : K) * ω₀ = 1 := by
    rw [hσk]
    exact congrArg (fun z : k => (z : K)) hω₀n
  obtain ⟨a₀, b₀, ha, hb, hab, ha_rat, hb_rat, ha2, hb2, hP⟩ :=
    exists_rational_frame (σ := σ) hωk hω1 hωn
  obtain ⟨A', hA'⟩ := A
  have hfun : (⇑σ : K → K) = ⇑h.bar := funext hσbar
  have hA : conjTr σ (A' : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := mem_primeFormUnitary.1 hA'
    show ((A' : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * (A' : Matrix (Fin 3) (Fin 3) K) = 1
    rw [hfun]
    simpa using this
  have hUK : SUid σ 3 = unitarySU 2 f K 3 := SUid_eq_unitarySU h 3
  have hUk : SUid σ₀ 3 = unitarySU 2 f₀ k 3 := SUid_eq_unitarySU h₀ 3
  set N := gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hNdef
  set Rgl : Subgroup (GL (Fin 3) K) := (unitarySU 2 f₀ k 3).map (subfieldGL k 3) with hRgl
  have hS1 : (suSub h h₀ hbar 3).map N.subtype = Rgl := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g.1, ?_, rfl⟩
      rw [unitarySU_eq_gramSU h₀ 3]
      exact g.2
    · rintro ⟨g', hg', rfl⟩
      rw [unitarySU_eq_gramSU h₀ 3] at hg'
      exact ⟨_, ⟨⟨g', hg'⟩, rfl⟩, rfl⟩
  have hS2 : (phi hσk).range.map (SUid σ 3).subtype = Rgl := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g.1, ?_, rfl⟩
      rw [← hUk]
      exact g.2
    · rintro ⟨g', hg', rfl⟩
      rw [← hUk] at hg'
      exact ⟨_, ⟨⟨g', hg'⟩, rfl⟩, rfl⟩
  have hconjN : ∀ S : Subgroup N,
      (S.map (primeFormConjSU h _ ⟨A', hA'⟩).toMonoidHom).map N.subtype =
        (S.map N.subtype).map (MulAut.conj A').toMonoidHom := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hconjG : ∀ S : Subgroup (SUid σ 3),
      (S.map (conjU A' hA)).map (SUid σ 3).subtype =
        (S.map (SUid σ 3).subtype).map (MulAut.conj A').toMonoidHom := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hneG : (phi hσk).range.map (conjU A' hA) ≠ (phi hσk).range := by
    intro heq
    apply hne
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    rw [hconjN, hS1]
    have := congrArg (Subgroup.map (SUid σ 3).subtype) heq
    rwa [hconjG, hS2] at this
  have hplane := range_planeSU_le_sup hσ hσ₀ hσk hp (by omega) hK hk4 hq hωk hω1 hωn ha hb hab
    ha_rat hb_rat A' hA hneG
  have hab01 : (0 : Fin 3) ≠ 1 := by decide
  have hblk : blk h hab01 ≤ Rgl ⊔ Rgl.map (MulAut.conj A').toMonoidHom := by
    intro x hx
    obtain ⟨X, hX, hxX⟩ := (mem_blk_iff hab01).1 hx
    have hxU : x ∈ SUid σ 3 := by
      rw [hUK]
      exact blk_le_unitarySU hab01 hx
    let xG : SUid σ 3 := ⟨x, hxU⟩
    have hfix : xG • (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
      rw [smul_def]
      show (x : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
      rw [hxX]
      exact coordEmbed_mulVec_single_two _
    obtain ⟨M', hM'⟩ := exists_planeElt_of_fix hσ.invol ha hb hab ha2 hb2 hP xG hfix
    have h2 : xG ∈ (phi hσk).range ⊔ (phi hσk).range.map (conjU A' hA) := hplane ⟨M', hM'⟩
    have h3 : x ∈ ((phi hσk).range ⊔ (phi hσk).range.map (conjU A' hA)).map
        (SUid σ 3).subtype := ⟨xG, h2, rfl⟩
    rwa [Subgroup.map_sup, hS2, hconjG, hS2] at h3
  have hsupGL : Rgl ⊔ Rgl.map (MulAut.conj A').toMonoidHom = unitarySU 2 f K 3 := by
    apply le_antisymm
    · have hR : Rgl ≤ unitarySU 2 f K 3 := by
        rintro x ⟨g', hg', rfl⟩
        rw [unitarySU_eq_gramSU h₀ 3] at hg'
        rw [unitarySU_eq_gramSU h 3]
        exact subfieldGL_mem_gramSU h h₀ hbar 3 hg'
      refine sup_le hR ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [unitarySU_eq_gramSU h 3]
      exact conj_mem_gramSU h _ hA' (by
        have := hR hy
        rwa [unitarySU_eq_gramSU h 3] at this)
    · rw [← Kst_sup_blk_eq k h h₀ hbar hf2 hab01]
      exact sup_le le_sup_left hblk
  have htop : (⊤ : Subgroup N).map N.subtype = unitarySU 2 f K 3 := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, unitarySU_eq_gramSU h 3]
    rfl
  have hsup : suSub h h₀ hbar 3 ⊔
      (suSub h h₀ hbar 3).map (primeFormConjSU h _ ⟨A', hA'⟩).toMonoidHom = ⊤ := by
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    rw [Subgroup.map_sup, hconjN, hS1, htop]
    exact hsupGL
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  exact hsup

end Final

end CFSG.RankThree.PartOne.SEITZ2
