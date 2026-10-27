module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

section Small

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_mono' {p : ℕ} {X Y : Subgroup G} (hXY : X ≤ Y) :
    oPrimeResidualOf p X ≤ oPrimeResidualOf p Y := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure]
  exact Subgroup.closure_mono fun x ⟨hx, k, hk⟩ => ⟨hXY hx, k, hk⟩

theorem not_three_dvd_of_oPrimeResidualOf_eq_bot' {X : Subgroup G}
    (hX : oPrimeResidualOf 3 X = ⊥) : ¬ 3 ∣ Nat.card X := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  have hmem : (x : G) ∈ oPrimeResidualOf 3 X := by
    rw [oPrimeResidualOf_eq_closure]
    refine Subgroup.subset_closure ⟨x.2, 1, ?_⟩
    rw [pow_one, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  rw [hX, Subgroup.mem_bot] at hmem
  have : x = 1 := Subtype.ext hmem
  rw [this, orderOf_one] at hx
  omega

omit [Finite G] in
theorem bot_mem_scriptQPi {A : Subgroup G} {LB : Subgroup G → Subgroup G} (Y : Subgroup G)
    (π : Set Nat.Primes) : (⊥ : Subgroup G) ∈ scriptQPi A LB Y π := by
  have hπ : ∀ π' : Set Nat.Primes, IsPiSubgroup π' (⊥ : Subgroup G) := fun π' q hq => by
    rw [Subgroup.card_bot] at hq
    exact absurd (Nat.le_of_dvd one_pos hq) (by have := q.2.two_le; omega)
  refine ⟨⟨⟨⟨le_top, hπ _, fun a _ => ?_⟩, fun B _ => ?_⟩, bot_le⟩, hπ π⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h
      have := congrArg (fun y => a⁻¹ * y * a) h
      simpa [mul_assoc] using this
  · rw [bot_inf_eq]
    exact bot_le

theorem exists_mem_scriptQPiStar {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (Y : Subgroup G) (π : Set Nat.Primes) : ∃ S : Subgroup G, S ∈ scriptQPiStar A LB Y π := by
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A LB Y π))
    (bot_mem_scriptQPi Y π)
  exact ⟨S, hS⟩

omit [Finite G] in
theorem inf_le_pCoreOf_of_le_normalizer {P H : Subgroup G} (hP : IsPGroup 2 P)
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) : P ⊓ H ≤ CFSG.Open.pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    (hP.to_le inf_le_left)
  exact Late.le_normalizer_inf hHP Subgroup.le_normalizer

end Small

section Item179

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem delta_M_mem_scriptY3 (h : Sec17Std G A c L Y₀) {U : Subgroup G}
    (hU : U ∈ scriptQ A (lB A)) (hUM : U ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)))
    (hU1 : U ≠ ⊥) :
    delta A (lB A) (Subgroup.normalizer (Y₀ : Set G)) ∈ scriptY3 A (lB A) ∧
      U ≤ CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.normalizer (Y₀ : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set D := delta A (lB A) M with hD
  have hDM : D ≤ M := delta_le M
  have hUD : U ≤ D := le_delta hU (hUM.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hUO : U ≤ CFSG.Open.pCoreOf 2 D := by
    refine (le_inf hUM hUD).trans (inf_le_pCoreOf_of_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M) ?_)
    exact hDM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  refine ⟨⟨⟨⟨fun htop => M_ne_top h (eq_top_iff.mpr (htop ▸ hDM)),
    le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩, fun hbot => hU1 (le_bot_iff.mp (hbot ▸ hUO))⟩,
    (delta_delta M).symm⟩, hUO⟩

theorem rank3II_17_9_of (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h146 : Item146 A (lB A)) (h177 : Item177 A (lB A)) : Item179 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y₀' hY₀'
  obtain rfl : Y₀' = Y₀ := h.eq_of_mem_y0Star hY₀'
  set M := Subgroup.normalizer (Y₀' : Set G) with hM
  refine ⟨?_, fun U hU hUM Y hY => ?_⟩
  ·
    obtain ⟨V, -, hV⟩ := Finite.exists_le_maximal (p := fun V : Subgroup G => V ≤ M ∧
      M ≤ Subgroup.normalizer (V : Set G) ∧ CFSG.Assembly.IsElemAbelian 2 V) (a := ⊥)
      ⟨bot_le, by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top,
        ⟨⟨⟨fun a b => Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, (Subgroup.mem_bot).mp a.2,
            (Subgroup.mem_bot).mp b.2])⟩⟩,
          fun x hx => by rw [(Subgroup.mem_bot).mp hx, one_pow]⟩⟩
    obtain ⟨-, U, hU, hUV⟩ := h177 Y₀' hY₀' V hV
    have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.prop.2.2.2 x x.2)⟩
    have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.prop.1 hV.prop.2.1 hV2
    exact ⟨U, hU, hUV.1.1, hUV.1.2.trans hVO⟩
  · have hU1 : U ≠ ⊥ := by
      intro hb
      have := hU.1.2.2
      rw [hb, Subgroup.card_bot] at this
      omega
    by_cases hYM : Y ≤ M
    · obtain ⟨hD3, hUD⟩ := delta_M_mem_scriptY3 h hUM.1 hUM.2 hU1
      have hYD : Y ≤ delta A (lB A) M := hY.prop.2.le.trans (delta_mono hYM)
      have hDY : delta A (lB A) M ≤ Y := hY.2 hD3 hYD
      rw [le_antisymm hYD hDY]
      exact hUD
    · obtain ⟨hY1, hYs⟩ := mem_scriptY1_of_not_le_M h h166 hbot hY.prop hYM
      obtain ⟨S, hS⟩ := exists_mem_scriptQPiStar (A := A) (LB := lB A) Y (piOf 2)
      have hSG := mem_qStar_top_of_item168 h h166 hbot h168 hY.prop hYM
        (fun N hN hYN => le_antisymm (hY.2 hN.1 hYN) hYN) hS
      have hSM : S ≤ M := h.qStar_le S hSG
      have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
      have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
      set Z := S ⊔ CFSG.Open.pCoreOf 2 M with hZ
      have hZ2 : IsPGroup 2 Z := IsPGroup.to_sup_of_normal_right' hS2 hO2
        (hSM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
        le_normalizer_sup hS.prop.1.1.1.2.2 ((h.le_normalizer_y0.trans
          Subgroup.le_normalizer).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
            M))
      have hZ3 : IsPiSubgroup (piCompl 3) Z := (isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr
        fun h3 => by
          rcases hZ2.card_eq_or_dvd with h1 | h2
          · rw [h1] at h3
            omega
          · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
            rw [hk] at h3
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
              (Nat.prime_three.dvd_of_dvd_pow h3)
            omega
      have hΔZ : delta A (lB A) Z ∈ scriptQ A (lB A) :=
        delta_mem_scriptQ (isE27_of_std h) h146 ⟨le_top, hZ3, hAZ⟩
      have hSΔ : S ≤ delta A (lB A) Z := le_delta hS.prop.1.1 le_sup_left
      have hUΔ : U ≤ delta A (lB A) Z := le_delta hUM.1 (hUM.2.trans le_sup_right)
      have hΔ2 : delta A (lB A) Z ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
        ⟨⟨hΔZ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hZ2.to_le (delta_le Z))⟩
      have hΔS : delta A (lB A) Z ≤ S := hSG.2 hΔ2 hSΔ
      have hUY : U ≤ Y := (hUΔ.trans hΔS).trans hS.prop.1.2
      exact le_pCoreOf_two_of_fourGroupsMinus (fun a ha => pow_three_of_std h ha)
        hY.prop.1.1.2 hYs (card_le_sq_of_pCoreOf_ne_bot h.toTheoremFourHyp hY.prop.1.2
          (not_three_dvd_of_oPrimeResidualOf_eq_bot' hY1.2)) hU hUY

end Item179

section Item1710

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_17_10_of (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h179 : Item179 A (lB A)) : Item1710 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y₀' hY₀' Y hYeq hYM Y₁ hY₁ Y₂ hY₂ hYY₁ hYY₂
  obtain rfl : Y₀' = Y₀ := h.eq_of_mem_y0Star hY₀'
  set M := Subgroup.normalizer (Y₀' : Set G) with hM
  have hYΔ : Y = delta A (lB A) Y := by
    refine le_antisymm ?_ (delta_le Y)
    calc Y = inSubgroup (oResidual 2) (deltaZero A (lB A) Y) := hYeq
      _ ≤ deltaZero A (lB A) Y := inSubgroup_oResidual_le_self 2 _
      _ ≤ delta A (lB A) Y := deltaZero_le_delta Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    have hA0 : A ≤ Subgroup.normalizer (deltaZero A (lB A) Y : Set G) :=
      le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
    have := le_normalizer_inSubgroup_oResidual (p := 2) hA0
    rwa [← hYeq] at this
  have hYtop : Y ≠ ⊤ := fun htop => hY₁.prop.1.1.1 (eq_top_iff.mpr (htop ▸ hYY₁))
  have hYΩ : Y ∈ omega168 A (lB A) := ⟨hYeq, ⟨hYtop, hAY⟩, fun Y₃ hY₃ hYY₃ =>
    mem_scriptY1_of_not_le_M h h166 hbot hY₃ fun hle => hYM (hYY₃.trans hle)⟩
  obtain ⟨⟨U, hU, hUM⟩, hU2⟩ := h179 Y₀' hY₀'
  have hU1 : U ≠ ⊥ := by
    intro hb
    have := hU.1.2.2
    rw [hb, Subgroup.card_bot] at this
    omega
  have hUY₁ := hU2 U hU hUM Y₁ hY₁
  have hUY₂ := hU2 U hU hUM Y₂ hY₂
  set Y' := delta A (lB A) (Y₁ ⊓ Y₂) with hY'
  have hY'le : Y' ≤ Y₁ ⊓ Y₂ := delta_le _
  have hUY' : U ≤ Y' := le_delta hUM.1
    (le_inf (hUY₁.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₁))
      (hUY₂.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂)))
  have hUO : U ≤ CFSG.Open.pCoreOf 2 Y' := by
    refine (le_inf hUY₁ hUY').trans (inf_le_pCoreOf_of_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁) ?_)
    exact (hY'le.trans inf_le_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨fun htop => hY₁.prop.1.1.1 (eq_top_iff.mpr (htop ▸ hY'le.trans inf_le_left)),
      le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩, fun hb => hU1 (le_bot_iff.mp (hb ▸ hUO))⟩,
      (delta_delta _).symm⟩
  have hYY' : Y ≤ Y' := hYΔ.le.trans (delta_mono (le_inf hYY₁ hYY₂))
  obtain ⟨N, hN, hNY, -⟩ := h168 (item168_premise h) Y hYΩ Y' hY'3 hYY'
  have hY₁N : Y₁ ≤ N := hNY Y₁ hY₁.prop (hY'le.trans inf_le_left)
  have hY₂N : Y₂ ≤ N := hNY Y₂ hY₂.prop (hY'le.trans inf_le_right)
  have h1 : N = Y₁ := le_antisymm (hY₁.2 hN.prop.1 hY₁N) hY₁N
  have h2 : N = Y₂ := le_antisymm (hY₂.2 hN.prop.1 hY₂N) hY₂N
  exact h1.symm.trans h2

end Item1710

theorem item1718_of (hC : Claim1718) : Item1718 := by
  intro G _ _ A c L Y₀ Y₁ S p P h w hw hwS heq
  apply hC G A c L Y₀ Y₁ S p P h w hw hwS
  have hSY : S ≤ Y₁ := h.mem_qStar_two.prop.1.2
  have hJ : (S ⊓ Y₀) ⊔ (S ⊓ Y₀).map (MulAut.conj w).toMonoidHom ≤ Y₁ := by
    refine sup_le (inf_le_left.trans hSY) ?_
    calc (S ⊓ Y₀).map (MulAut.conj w).toMonoidHom ≤ Y₁.map (MulAut.conj w).toMonoidHom :=
          Subgroup.map_mono (inf_le_left.trans hSY)
      _ = Y₁ := heq
  rw [eq_bot_iff, ← h.mem_y1Star.prop.2]
  exact oPrimeResidualOf_mono' hJ

section Item1715

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_17_15_of (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (h1714 : Item1714 L) (hMeets : Claim1715Meets) (hPrime : Claim1715Prime)
    (hAY : Claim1715A) :
    (omegaA A = {Subgroup.zpowers c} ∧ Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
          Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
          ((∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
              Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))) ∨
        (A ⊔ L ≤ Y₀ ∧
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) ∧
          WStarS4 A ∧ TransOmegaThree A c) := by
  rcases h1514 Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
    ⟨hY, -, hΩ, hprod, hM12⟩ | ⟨hA7, hW, hT, -⟩ | ⟨-, -, -, -, hno, -⟩
  ·
    have hYL : Y₀ ⊓ L = L := inf_eq_right.mpr h.le_y0
    rw [hYL] at hY
    refine Or.inl ⟨hΩ, hY, hprod, ?_⟩
    rcases (h.hypR.2.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with hJ | hL3 | hA7 | hM22 | hM
    · exact Or.inr (Or.inr (Or.inr hJ))
    · obtain ⟨p, e, hp, he, hiso⟩ := hL3
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact h1714 e he hiso
      have hp3 : p ≠ 3 := by
        rintro rfl
        rcases hiso with ⟨hmod, -⟩ | ⟨hmod, -⟩ <;>
        · rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega)] at hmod
          omega
      have hp3' : 3 < p := by
        have := hp.out.two_le
        omega
      have he1 : e = 1 := hPrime G A c L Y₀ h p e hp3' he hiso
      subst he1
      exact Or.inl ⟨p, hp, hp3', hiso⟩
    · exact Or.inr (Or.inl hA7)
    · exact Or.inr (Or.inr (Or.inl hM22))
    · exact absurd hM (not_nonempty_iff.mpr hM12)
  ·
    have hA10 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) := by
      rcases h.a10_or_omega with h10 | hΩ
      · exact h10
      · exfalso
        have := hT.1
        rw [hΩ, Set.ncard_singleton] at this
        omega
    exact Or.inr ⟨sup_le (hAY G A c L Y₀ h hA10 hA7 hT) h.le_y0, hA7, hA10, hW, hT⟩
  ·
    exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

theorem rank3II_17_15_HJ_of (h : Sec17Std G A c L Y₀) (h1514 : Item1514 A (lB A) c L)
    (hMeets : MeetsY4 A (lB A) L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    omegaA A = {Subgroup.zpowers c} ∧ Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
  rcases h1514 Y₀ h.mem_y0Star hMeets with
    ⟨hY, -, hΩ, hprod, -⟩ | ⟨⟨hA7⟩, -⟩ | ⟨-, -, -, -, hno, -⟩
  · rw [inf_eq_right.mpr h.le_y0] at hY
    exact ⟨hΩ, hY, hprod⟩
  · obtain ⟨φ⟩ := hJ
    exact ((KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1).false (φ.symm.trans hA7)).elim
  · exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

theorem card_inf_eq_nine_of_prod (h : Sec17Std G A c L Y₀)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    Nat.card (A ⊓ L : Subgroup G) = 9 := by
  obtain ⟨φ⟩ := hprod
  have hperf : Group.IsPerfect (Sec12.lBar c L) := by
    obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_lA.1
    have := (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_lA.1).1
    exact Group.IsPerfect.ofSurjective (f := η.toMonoidHom) η.surjective
  exact card_inf_eq_nine h.toSec13Data hperf φ

theorem item1715_of
    (h1514 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1514 A (lB A) c L)
    (h1714 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1714 L)
    (hMeets : Claim1715Meets) (hPrime : Claim1715Prime) (hAY : Claim1715A) : Item1715 :=
  fun G _ _ A c L Y₀ h => rank3II_17_15_of h (h1514 G A c L Y₀ h) (h1714 G A c L Y₀ h) hMeets
    hPrime hAY

end Item1715

section Item1719

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
  {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}

omit [Finite G] in
theorem card_sup_mul_card_inf' {X N : Subgroup G} (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hXN Subgroup.le_normalizer)
  have : (N.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
      (Late.le_normalizer_inf hXN Subgroup.le_normalizer)
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem mem_scriptY3Star_of_not_le_M (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) (hM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    Y ∈ scriptY3Star A (lB A) := by
  refine ⟨hY.prop.1, fun Y' hY' hle => ?_⟩
  have hM' : ¬ Y' ≤ Subgroup.normalizer (Y₀ : Set G) := fun h' => hM (hle.trans h')
  exact hY.2 (mem_scriptY1_of_not_le_M h h166 hbot hY' hM').1 hle

theorem commutator_zpowers_mem_scriptQZero {LB : Subgroup G → Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hc3 : c ^ 3 = 1) (hcA : c ∈ A) {P : Subgroup G}
    (hP : P ∈ scriptQ A LB) (hP3 : ¬ 3 ∣ Nat.card P) :
    ⁅P, Subgroup.zpowers c⁆ ∈ scriptQZero A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hP.1.2.2
  have hcP : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans hAP
  have hc3' : IsPGroup 3 (Subgroup.zpowers c) := fun x => ⟨1, Subtype.ext (by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hc3, one_zpow, Subgroup.coe_one])⟩
  have hAc : A ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hac : a * c = c * a := hAab a ha c hcA
    have key : ∀ y : G, y ∈ Subgroup.zpowers c → a * y * a⁻¹ = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : Commute a (c ^ k) := (Commute.zpow_right hac k)
      rw [this.eq, mul_inv_cancel_right]
    constructor
    · intro hx
      rw [key x hx]
      exact hx
    · intro hx
      have h1 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = a * x * a⁻¹ := by
        have hinv := key (a * x * a⁻¹) hx
        calc a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * (a * (a * x * a⁻¹) * a⁻¹) * a := by
              rw [hinv, inv_inv]
          _ = a * x * a⁻¹ := by group
      have h2 : x = a * x * a⁻¹ := by
        calc x = a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ := by group
          _ = a * x * a⁻¹ := h1
      rw [h2]
      exact hx
  have hAX : A ≤ Subgroup.normalizer ((⁅P, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hAP hAc
  have hXP : ⁅P, Subgroup.zpowers c⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hcP
  refine ⟨mem_scriptQ_of_le hP hXP hAX, le_antisymm ?_
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hAX)⟩
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Subgroup.zpowers c) P hc3' hP3 hcP
  calc ⁅P, Subgroup.zpowers c⁆ = ⁅⁅P, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ := hidem.symm
    _ ≤ ⁅⁅P, Subgroup.zpowers c⁆, A⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)

theorem rank3II_17_19_of (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hW : Claim1719W)
    (h1712 : Item1712 A (lB A)) (h1710 : Item1710 A (lB A)) (h1718 : Item1718)
    (h166 : Item166 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A ⊓ L ≠ A ⊓ Subgroup.centralizer (P : Set G) := by
  have hs := h.toSec17Std
  have : Fact p.Prime := ⟨h.p_prime⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  intro heq
  obtain ⟨w, hwW, hwAL, hwS⟩ := hW G A c L Y₀ Y₁ S p P h
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hwW.1
  have hwM : w ∈ M := hs.normalizer_le hwA
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => hs.toSec13Data.commute ha hb
  have hALP : ∀ b ∈ A ⊓ L, ∀ x ∈ P, x * b = b * x := by
    intro b hb x hx
    rw [heq] at hb
    exact Subgroup.mem_centralizer_iff.mp hb.2 x hx
  have hALPw : ∀ b ∈ A ⊓ L, ∀ x ∈ P.map (MulAut.conj w).toMonoidHom, x * b = b * x := by
    rintro b hb _ ⟨x, hx, rfl⟩
    have hb' : w⁻¹ * b * w ∈ A ⊓ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwAL) b).mp hb
      simpa [mul_assoc] using this
    have h1 := hALP _ hb' x hx
    change w * x * w⁻¹ * b = b * (w * x * w⁻¹)
    calc w * x * w⁻¹ * b = w * (x * (w⁻¹ * b * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * b * w) * x) * w⁻¹ := by rw [h1]
      _ = b * (w * x * w⁻¹) := by group
  obtain ⟨B, hB, hBY, -⟩ := h1712
  have hBAL : B ⊓ (A ⊓ L) ≠ ⊥ := by
    intro hbot'
    have hA27 : Nat.card A = 27 := (isE27_of_std hs).2
    have hB9 : Nat.card B = 9 := by
      have := hB.2
      rw [hA27] at this
      omega
    have hBC : B ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hAab x (hB.1 hx) y hy.1).symm
    have hBN : B ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      hBC.trans (Subgroup.centralizer_le_normalizer _)
    have hprod := card_sup_mul_card_inf' hBN
    rw [hbot', Subgroup.card_bot, mul_one, hB9, h9] at hprod
    have hle := Subgroup.card_le_of_le (sup_le hB.1 inf_le_left : B ⊔ (A ⊓ L) ≤ A)
    rw [hprod, hA27] at hle
    omega
  obtain ⟨b, hbBAL, hb1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hBAL
  have hbAL : b ∈ A ⊓ L := hbBAL.2
  obtain ⟨Z, hΔZ, hZ⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A)))
    (hBY b hbBAL.1 hb1)
  have hp2 : p ≠ 2 := by have := h.three_lt_p; omega
  have hp3 : p ≠ 3 := by have := h.three_lt_p; omega
  have hPQ : P ∈ scriptQ A (lB A) := h.mem_qStar_p.prop.1.1
  have hPp : IsPGroup p P := (isPiSubgroup_piOf_iff h.p_prime P).mp h.mem_qStar_p.prop.2
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    rw [hk] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.p_prime).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  set X := ⁅P, Subgroup.zpowers c⁆ with hX
  have hX0 : X ∈ scriptQZero A (lB A) :=
    commutator_zpowers_mem_scriptQZero hAab (pow_three_of_std hs hs.toSec13Data.mem_A)
      hs.toSec13Data.mem_A hPQ hP3
  have hXP : X ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.zpowers_le.mpr hs.toSec13Data.mem_A).trans hPQ.1.2.2)
  have hXp : IsPGroup p X := hPp.to_le hXP
  have hXM : ¬ X ≤ M := h.commutator_not_le_M
  have hXeq := (mem_omega168_of hs h166 hbot h.p_prime hp2 hp3 hXp hX0 hXM).1
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hALP b hbAL x (hXP hx))
  have hXZ : X ≤ Z := (le_delta hX0.1 hXb).trans hΔZ
  have hY₁3 : Y₁ ∈ scriptY3Star A (lB A) :=
    mem_scriptY3Star_of_not_le_M hs h166 hbot h.mem_y1Star h.not_le_M
  have hXY₁ : X ≤ Y₁ := hXP.trans h.mem_qStar_p.prop.1.2
  have hY₁Z := h1710 Y₀ hs.mem_y0Star X hXeq hXM Y₁ hY₁3 Z hZ hXY₁ hXZ
  set Xw := X.map (MulAut.conj w).toMonoidHom with hXw
  have hXw0 : Xw ∈ scriptQZero A (lB A) := rank3II_14_4_5_zero_lB hwA hX0
  have hXwp : IsPGroup p Xw := hXp.map _
  have hXwM : ¬ Xw ≤ M := by
    intro hle
    apply hXM
    have := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hle
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one,
      Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (inv_mem hwM))] at this
  have hXweq := (mem_omega168_of hs h166 hbot h.p_prime hp2 hp3 hXwp hXw0 hXwM).1
  have hXwb : Xw ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hALPw b hbAL x (Subgroup.map_mono hXP hx))
  have hXwZ : Xw ≤ Z := (le_delta hXw0.1 hXwb).trans hΔZ
  have hY₁w3 := map_conj_mem_scriptY3Star hwA hY₁3
  have hXwY₁ : Xw ≤ Y₁.map (MulAut.conj w).toMonoidHom := Subgroup.map_mono hXY₁
  have hY₁wZ := h1710 Y₀ hs.mem_y0Star Xw hXweq hXwM _ hY₁w3 Z hZ hXwY₁ hXwZ
  exact h1718 G A c L Y₀ Y₁ S p P h w hwW hwS (hY₁wZ.trans hY₁Z.symm)

theorem item1719_of (hW : Claim1719W) (h1718 : Item1718)
    (h1712 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1712 A (lB A))
    (h1710 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1710 A (lB A))
    (h166 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item166 A (lB A))
    (hbot : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h9 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Nat.card (A ⊓ L : Subgroup G) = 9) : Item1719 :=
  fun G _ _ A c L Y₀ _ _ _ _ h =>
    rank3II_17_19_of h hW (h1712 G A c L Y₀ h.toSec17Std) (h1710 G A c L Y₀ h.toSec17Std) h1718
      (h166 G A c L Y₀ h.toSec17Std) (hbot G A c L Y₀ h.toSec17Std) (h9 G A c L Y₀ h.toSec17Std)

end Item1719

section Para1714

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem exists_sec17Y1_of (h : Sec17Std G A c L Y₀) (h1713 : Item1713 A (lB A))
    (h166 : Item166 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h168 : Item168 A (lB A) c L) (h1411 : Item1411_1 A (lB A)) :
    ∃ (Y₁ S : Subgroup G) (p : ℕ) (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  obtain ⟨Y, hY, hYM⟩ := h1713 Y₀ h.mem_y0Star
  obtain ⟨hY1, -⟩ := mem_scriptY1_of_not_le_M h h166 hbot hY hYM
  obtain ⟨Y₁', hYY₁', hY₁'⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY1 A (lB A))) hY1
  have hY₁'M : ¬ Y₁' ≤ M := fun hle => hYM (hYY₁'.trans hle)
  obtain ⟨S₀, hS₀⟩ := exists_mem_scriptQPiStar (A := A) (LB := lB A) Y₁' (piOf 2)
  have hS₀G := mem_qStar_top_of_item168 h h166 hbot h168 hY₁'.prop.1 hY₁'M
    (fun N hN hYN => le_antisymm (hY₁'.2 hN hYN) hYN) hS₀
  obtain ⟨TL, hTL⟩ := exists_mem_scriptQPiStar (A := A) (LB := lB A) L (piOf 2)
  obtain ⟨T, hTLT, hT⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) (a := TL) ⟨⟨hTL.prop.1.1, le_top⟩, hTL.prop.2⟩
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := h.toSec13Data.le_normalizer
  have hTL2 : T ⊓ L ∈ scriptQPi A (lB A) L (piOf 2) := by
    refine ⟨⟨mem_scriptQ_of_le hT.prop.1.1 inf_le_left
      (Late.le_normalizer_inf hT.prop.1.1.1.2.2 hAL), inf_le_right⟩, ?_⟩
    exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (((isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.prop.2).to_le inf_le_left)
  have hTLeq : T ⊓ L ∈ scriptQPiStar A (lB A) L (piOf 2) :=
    ⟨hTL2, fun R hR hle => (hTL.2 hR ((le_inf hTLT hTL.prop.1.2).trans hle)).trans
      (le_inf hTLT hTL.prop.1.2)⟩
  obtain ⟨w, hw, hTw⟩ := h1411 S₀ hS₀G T hT
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hw.1
  have hwM : w ∈ M := h.normalizer_le hwA
  set Y₁ := Y₁'.map (MulAut.conj w).toMonoidHom with hY₁
  have hY₁star : Y₁ ∈ scriptY1Star A (lB A) := map_conj_mem_scriptY1Star hwA hY₁'
  have hY₁M : ¬ Y₁ ≤ M := by
    intro hle
    apply hY₁'M
    have := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hle
    rwa [hY₁, map_conj_map_conj, inv_mul_cancel, map_conj_one,
      Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (inv_mem hwM))] at this
  have hS : T ∈ scriptQPiStar A (lB A) Y₁ (piOf 2) := hTw ▸ map_conj_mem_scriptQPiStar hwA hS₀
  have hY₁s : Group.IsSolvable Y₁ :=
    (mem_scriptY1_of_not_le_M h h166 hbot hY₁star.prop.1 hY₁M).2
  obtain ⟨Q, hQ, hQM⟩ : ∃ Q ∈ collectionIn (scriptQ A (lB A)) Y₁, ¬ Q ≤ M := by
    by_contra hall
    push Not at hall
    exact hY₁M (hY₁star.prop.1.2.le.trans (sSup_le hall))
  obtain ⟨r, hr, hr2, hr3, R, hRQ, hRr, hAR, hRM⟩ := exists_pGroup_not_le_M h hQ.1 hQM
  have : Fact r.Prime := ⟨hr⟩
  have hR : R ∈ scriptQPi A (lB A) Y₁ (piOf r) :=
    ⟨⟨mem_scriptQ_of_le hQ.1 hRQ hAR, hRQ.trans hQ.2⟩, (isPiSubgroup_piOf_iff hr R).mpr hRr⟩
  obtain ⟨P, hRP, hP⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) Y₁ (piOf r))) hR
  have hPM : ¬ P ≤ M := fun hle => hRM (hRP.trans hle)
  have hPr : IsPGroup r P := (isPiSubgroup_piOf_iff hr P).mp hP.prop.2
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPr
    rw [hk] at h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hc3 : IsPGroup 3 (Subgroup.zpowers c) := fun x => ⟨1, Subtype.ext (by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, pow_three_of_std h h.toSec13Data.mem_A, one_zpow, Subgroup.coe_one])⟩
  have hcP : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le.mpr h.toSec13Data.mem_A).trans hP.prop.1.1.1.2.2
  have hPc : ¬ ⁅P, Subgroup.zpowers c⁆ ≤ M := by
    intro hle
    refine hPM (le_of_commutator_le Nat.prime_three hc3 hP3 hcP hle ?_)
    exact inf_le_right.trans ((Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c))).trans (centralizer_c_le_M h))
  have hr3' : 3 < r := by
    have := hr.two_le
    omega
  exact ⟨Y₁, T, r, P, ⟨h, hY₁star, hY₁M, hS, hTw ▸ hTLeq, hY₁s, hr, hr3', hP, hPc⟩⟩

theorem para1714_of
    (h1713 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1713 A (lB A))
    (h166 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item166 A (lB A))
    (hbot : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h168 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item168 A (lB A) c L)
    (h1411 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item1411_1 A (lB A)) : Para1714 :=
  fun G _ _ A c L Y₀ h => exists_sec17Y1_of h (h1713 G A c L Y₀ h) (h166 G A c L Y₀ h)
    (hbot G A c L Y₀ h) (h168 G A c L Y₀ h) (h1411 G A c L Y₀ h)

end Para1714

end CFSG.RankThree.PartTwo.Sec17
