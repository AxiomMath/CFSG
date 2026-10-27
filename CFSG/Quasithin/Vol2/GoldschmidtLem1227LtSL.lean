module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.Quasithin.H13.Lem1227Lt

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace SL

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by simp

theorem isSylowTwoOf_unitriangular {n : ℕ} (hn : 1 ≤ n) :
    CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) hn
  exact hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P

theorem det_blkMon_flag {n : ℕ} (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) (g : ↥(flagStabilizer n (ZMod 2) I)) :
    (blkMon (flagStabilizer n (ZMod 2) I) a m h (blockLeft_of_cut m ha) (blockRight_of_cut hb)
      g).det = 1 := by
  set f := blkMon (flagStabilizer n (ZMod 2) I) a m h (blockLeft_of_cut m ha)
    (blockRight_of_cut hb) with hf
  have h1 : f g * f g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : (f g).det * (f g⁻¹).det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  rcases eq_zero_or_eq_one_of_card_two card_zmod_two (f g).det with h0 | h0
  · rw [h0, zero_mul] at h2
    exact absurd h2 zero_ne_one
  · exact h0

@[expose] noncomputable def blockHom {n : ℕ} (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) :
    ↥(flagStabilizer n (ZMod 2) I) →* SpecialLinearGroup (Fin m) (ZMod 2) where
  toFun g := ⟨blkMon (flagStabilizer n (ZMod 2) I) a m h (blockLeft_of_cut m ha)
    (blockRight_of_cut hb) g, det_blkMon_flag I a m h ha hb g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g g' := Subtype.ext (map_mul _ g g')

theorem blockHom_eq_bigBlockHom {n : ℕ} (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (x : ↥(perfectCore (flagStabilizer n (ZMod 2) I))) :
    blockHom I a m h ha hb ⟨(x : SpecialLinearGroup (Fin n) (ZMod 2)), perfectCore_le _ x.2⟩ =
      bigBlockHom I a m h ha hb x := rfl

theorem sl_model {n : ℕ} (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    {B : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))} (hperf : ⁅B, B⁆ = B) (hbot : B ≠ ⊥)
    (htop : B ≠ ⊤)
    (hU : unitriangular n (ZMod 2) ≤ Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n)
      (ZMod 2)))) :
    ∃ m : ℕ, (m = 3 ∨ (m = 4 ∧ n = 5)) ∧
      (n = 4 → ∃ d : ℕ, (d = 1 ∨ d = 3) ∧
        Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
          stabilizer (flagSpace n (ZMod 2) d)) ∧
      ∃ Θ : ↥(Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2)))) →*
          SpecialLinearGroup (Fin m) (ZMod 2),
        ∀ s, ∃ b : ↥B, Θ ⟨(b : SpecialLinearGroup (Fin n) (ZMod 2)), Subgroup.le_normalizer b.2⟩ =
          s := by
  classical
  have hK : Nat.card (ZMod 2) = 2 := card_zmod_two
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : B ≤ Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2))) :=
    Subgroup.le_normalizer
  have hUN : upperTriangular n (ZMod 2) ≤
      Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2))) :=
    (upperTriangular_le_unitriangular hK).trans hU
  have hsimple : IsSimpleGroup (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    sl_isSimple_of_card_two hK (by omega)
  have hNne : Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2))) ≠ ⊤ := by
    intro h
    have hn : B.Normal := ⟨fun x hx g => by
      have hg : g ∈ Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
        rw [h]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.1 hg x).1 hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h0 | h1
    · exact hbot h0
    · exact htop h1
  have hBperf : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  have hBP : B ≤ perfectCore (Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n)
      (ZMod 2)))) := le_perfectCore_of_perfect hBN hperf
  obtain ⟨hNQ, -⟩ := borel_overgroups
    (Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2)))) hUN
  have hIcuts : ∀ c ∈ borelOvergroupCuts (Subgroup.normalizer (B : Set (SpecialLinearGroup
      (Fin n) (ZMod 2)))), 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  generalize borelOvergroupCuts (Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n)
    (ZMod 2)))) = I at hNQ hIcuts
  rw [hNQ] at hBP hNne
  rcases exists_big_or_small (n := n) (I := I) with hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    have h0 : perfectCore (flagStabilizer n (ZMod 2) I) = ⊥ :=
      perfectCore_eq_bot_of_small hK (by omega) hsmall
    rw [h0] at hBP
    exact hbot (le_bot_iff.1 hBP)
  · have hmn : m < n := by
      by_contra hmn
      have hmn' : m = n ∧ a = 0 := by omega
      have hIempty : I = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hc
        obtain ⟨h1, h2⟩ := hIcuts c hc
        exact hno c hc ⟨by omega, by omega⟩
      apply hNne
      rw [hIempty, flagStabilizer_empty]
    have hm : m = 3 ∨ (m = 4 ∧ n = 5) := by omega
    refine ⟨m, hm, ?_, ?_⟩
    · intro hn4'
      subst hn4'
      have hm3' : m = 3 := by omega
      subst hm3'
      have hIeq : (a = 0 ∧ I = {3}) ∨ (a = 1 ∧ I = {1}) := by
        have ha01 : a = 0 ∨ a = 1 := by omega
        rcases ha01 with rfl | rfl
        · left
          refine ⟨rfl, ?_⟩
          have h3 : 3 ∈ I := hb.resolve_left (by omega)
          ext c
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hc
            obtain ⟨h1, h2⟩ := hIcuts c hc
            have := hno c hc
            omega
          · rintro rfl
            exact h3
        · right
          refine ⟨rfl, ?_⟩
          have h1 : 1 ∈ I := ha.resolve_left (by omega)
          ext c
          simp only [Set.mem_singleton_iff]
          constructor
          · intro hc
            obtain ⟨h1', h2⟩ := hIcuts c hc
            have := hno c hc
            omega
          · rintro rfl
            exact h1
      rcases hIeq with ⟨-, hI⟩ | ⟨-, hI⟩
      · refine ⟨3, Or.inr rfl, ?_⟩
        rw [hNQ, hI, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer_singleton]
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [hNQ, hI, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer_singleton]
    ·
      let Θ₀ := blockHom (n := n) I a m h ha hb
      refine ⟨Θ₀.comp (Subgroup.inclusion hNQ.le), ?_⟩
      have hbig := bigBlockHom_surjective (K := ZMod 2) hK h hm3 ha hb hno
      let ΘB : ↥B →* SpecialLinearGroup (Fin m) (ZMod 2) :=
        Θ₀.comp (Subgroup.inclusion (hBN.trans hNQ.le))
      have hnorm : ΘB.range.Normal := by
        refine ⟨fun c hc s => ?_⟩
        obtain ⟨b, rfl⟩ := hc
        obtain ⟨p, rfl⟩ := hbig s
        have hpQ : (p : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
            Subgroup.normalizer (B : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
          rw [hNQ]
          exact perfectCore_le _ p.2
        have hpb : (p : SpecialLinearGroup (Fin n) (ZMod 2)) * (b : SpecialLinearGroup (Fin n)
            (ZMod 2)) * (p : SpecialLinearGroup (Fin n) (ZMod 2))⁻¹ ∈ B :=
          (Subgroup.mem_normalizer_iff.1 hpQ b).1 b.2
        refine ⟨⟨_, hpb⟩, ?_⟩
        have hpQ' : (p : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
            flagStabilizer n (ZMod 2) I := perfectCore_le _ p.2
        have hbQ' : (b : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
            flagStabilizer n (ZMod 2) I := hNQ ▸ hBN b.2
        have e1 : ΘB ⟨_, hpb⟩ = Θ₀ (⟨(p : SpecialLinearGroup (Fin n) (ZMod 2)), hpQ'⟩ *
            ⟨(b : SpecialLinearGroup (Fin n) (ZMod 2)), hbQ'⟩ *
            ⟨(p : SpecialLinearGroup (Fin n) (ZMod 2)), hpQ'⟩⁻¹) := rfl
        rw [e1, map_mul, map_mul, map_inv]
        rfl
      have : IsSimpleGroup (SpecialLinearGroup (Fin m) (ZMod 2)) :=
        sl_isSimple_of_card_two hK hm3
      have hC : ΘB.range = ⊥ ∨ ΘB.range = ⊤ := IsSimpleGroup.eq_bot_or_eq_top_of_normal _
      rcases hC with hC | hC
      · exfalso
        have hle : B ≤ unitriangular n (ZMod 2) := by
          intro b hb'
          have hb1 : ΘB ⟨b, hb'⟩ = 1 := by
            have : ΘB ⟨b, hb'⟩ ∈ ΘB.range := ⟨_, rfl⟩
            rw [hC] at this
            exact Subgroup.mem_bot.1 this
          refine unitriangular_of_bigBlockHom hK hn5 h hm3 ha hb hno
            ⟨b, hBP hb'⟩ ?_
          rw [← blockHom_eq_bigBlockHom]
          exact hb1
        have hsolv : Group.IsSolvable ↥B := by
          have := (isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) (by omega)).isNilpotent
          exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
            (Subgroup.inclusion_injective hle)
        have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).2 hbot
        exact Group.IsPerfect.not_isSolvable ↥B hsolv
      · intro s
        have : s ∈ ΘB.range := by rw [hC]; exact Subgroup.mem_top s
        obtain ⟨b, hb'⟩ := this
        exact ⟨b, hb'⟩

end SL

end CFSG.Quasithin.H13.Lem1227Lt
