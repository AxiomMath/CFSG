module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem etaSet_one : etaSet 1 = ∅ := by
  ext p
  simp only [etaSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hdvd
  rw [show 2 ^ 1 - 1 = 1 by norm_num] at hdvd
  exact hp.ne_one (Nat.dvd_one.mp hdvd)

private theorem etaSet_nonempty_of_ne_one {n : ℕ} (hn : n ≠ 1) : (etaSet n).Nonempty := by
  have hne : 2 ^ n - 1 ≠ 1 := by
    rcases n with _ | _ | k
    · norm_num
    · exact absurd rfl hn
    · have h4 : 4 ≤ 2 ^ (k + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨p, hp, hpd⟩

private theorem eq_zero_of_etaSet_zero_eq {m : ℕ} (h : etaSet 0 = etaSet m) : m = 0 := by
  by_contra hm
  have h2 : 2 ∈ etaSet m := h ▸ ⟨Nat.prime_two, by norm_num⟩
  obtain ⟨-, hdvd⟩ := h2
  have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 hm
  have hsub : 2 ∣ 2 ^ m - (2 ^ m - 1) := Nat.dvd_sub h2m hdvd
  have h1 : 2 ^ m - (2 ^ m - 1) = 1 := by
    have := Nat.one_le_two_pow (n := m)
    omega
  rw [h1] at hsub
  norm_num at hsub

private theorem etaSet_six : etaSet 6 = {3, 7} := by
  ext p
  simp only [etaSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hdvd⟩
    have h63 : 2 ^ 6 - 1 = 3 ^ 2 * 7 := by norm_num
    rw [h63] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h)
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
  · rintro (rfl | rfl) <;> norm_num

private theorem orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  have h2 : orderOf (2 : ZMod 3) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
  have hne : orderOf (2 : ZMod 3) ≠ 1 := by
    intro h
    have h1 : (2 : ZMod 3) = 1 := by simpa [h] using pow_orderOf_eq_one (2 : ZMod 3)
    exact (by decide : (2 : ZMod 3) ≠ 1) h1
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact absurd h hne
  · exact h

private theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  have h3 : orderOf (2 : ZMod 7) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 7) ^ 3 = 1)
  have hne : orderOf (2 : ZMod 7) ≠ 1 := by
    intro h
    have h1 : (2 : ZMod 7) = 1 := by simpa [h] using pow_orderOf_eq_one (2 : ZMod 7)
    exact (by decide : (2 : ZMod 7) ≠ 1) h1
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact absurd h hne
  · exact h

private theorem orderOf_two_dvd_of_dvd {p n : ℕ} (h : p ∣ 2 ^ n - 1) :
    orderOf (2 : ZMod p) ∣ n :=
  orderOf_dvd_of_pow_eq_one ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff n).mp h)

private theorem two_dvd_of_three_dvd {m : ℕ} (h : 3 ∣ 2 ^ m - 1) : 2 ∣ m := by
  rw [← orderOf_two_zmod_three]
  exact orderOf_two_dvd_of_dvd h

private theorem three_dvd_of_seven_dvd {m : ℕ} (h : 7 ∣ 2 ^ m - 1) : 3 ∣ m := by
  rw [← orderOf_two_zmod_seven]
  exact orderOf_two_dvd_of_dvd h

private theorem eq_six_of_etaSet_eq_six {m : ℕ} (hm0 : m ≠ 0) (h : etaSet 6 = etaSet m) :
    m = 6 := by
  have h3mem : 3 ∈ etaSet 6 := by rw [etaSet_six]; norm_num
  have h7mem : 7 ∈ etaSet 6 := by rw [etaSet_six]; norm_num
  have h3 : 3 ∣ 2 ^ m - 1 := (h ▸ h3mem).2
  have h7 : 7 ∣ 2 ^ m - 1 := (h ▸ h7mem).2
  have h2 : 2 ∣ m := two_dvd_of_three_dvd h3
  have h3dvd : 3 ∣ m := three_dvd_of_seven_dvd h7
  have h6 : 6 ∣ m := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3dvd
    simpa using this
  by_contra hm6
  have hm12 : 12 ≤ m := by
    obtain ⟨k, hk⟩ := h6
    omega
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := m) (by omega) hm6
  have hp6 : p ∈ etaSet 6 := h.symm ▸ ⟨hp.prime, hp.dvd⟩
  rw [etaSet_six] at hp6
  have hp37 : p = 3 ∨ p = 7 := by simpa using hp6
  rcases hp37 with rfl | rfl
  · exact hp.2.2 2 (by norm_num) (by omega) (by norm_num)
  · exact hp.2.2 3 (by norm_num) (by omega) (by norm_num)

private theorem dvd_of_etaSet_eq {n m : ℕ} (hn2 : 2 ≤ n) (hn6 : n ≠ 6)
    (h : etaSet n = etaSet m) : n ∣ m := by
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor hn2 hn6
  have hpm : p ∣ 2 ^ m - 1 := by
    have hpη : p ∈ etaSet n := ⟨hp.prime, hp.dvd⟩
    rw [h] at hpη
    exact hpη.2
  exact (hp.dvd_sub_one_iff (by omega) m).mp hpm

theorem etaSet_injective : Function.Injective etaSet := by
  intro n m h
  rcases eq_or_ne n 0 with rfl | hn0
  · exact (eq_zero_of_etaSet_zero_eq h).symm
  rcases eq_or_ne m 0 with rfl | hm0
  · exact absurd (eq_zero_of_etaSet_zero_eq h.symm) hn0
  rcases eq_or_ne n 1 with rfl | hn1
  · by_contra hm1
    obtain ⟨p, hp⟩ := etaSet_nonempty_of_ne_one (n := m) (fun h => hm1 h.symm)
    have hp1 : p ∈ etaSet 1 := h.symm ▸ hp
    rw [etaSet_one] at hp1
    exact hp1
  rcases eq_or_ne m 1 with rfl | hm1
  · exfalso
    obtain ⟨p, hp⟩ := etaSet_nonempty_of_ne_one hn1
    have hp1 : p ∈ etaSet 1 := h ▸ hp
    rw [etaSet_one] at hp1
    exact hp1
  rcases eq_or_ne n 6 with rfl | hn6
  · exact (eq_six_of_etaSet_eq_six hm0 h).symm
  rcases eq_or_ne m 6 with rfl | hm6
  · exact eq_six_of_etaSet_eq_six hn0 h.symm
  · have hn2 : 2 ≤ n := by
      have := Nat.pos_of_ne_zero hn0
      omega
    have hm2 : 2 ≤ m := by
      have := Nat.pos_of_ne_zero hm0
      omega
    exact Nat.dvd_antisymm (dvd_of_etaSet_eq hn2 hn6 h)
      (dvd_of_etaSet_eq hm2 hm6 h.symm)

@[expose] def Choice2011Out (D : Data G) (L0 B0 : Subgroup G) (n : ℕ) : Prop :=
  B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧ AlphaCond D.T B0 n ∧ B0 ≤ D.M

@[expose] def ChoiceZ (D : Data G) : Choice2011 G := fun L0 B0 =>
  Choice214U D L0 B0 ∧
    (Choice2011Out D L0 B0 (CFSG.Open.pRank 2 D.Z) →
      (∃ B' : Subgroup G, Choice214U D L0 B' ∧
        Choice2011Out D L0 B' (CFSG.Open.pRank 2 D.Z) ∧
          B' ⊓ centralizer (D.Z : Set G) = ⊥) →
      B0 ⊓ centralizer (D.Z : Set G) = ⊥)

theorem choiceZ_le {D : Data G} {L0 B0 : Subgroup G} (h : ChoiceZ D L0 B0) :
    Choice214U D L0 B0 := h.1

theorem choiceExists2011_choiceZ {D : Data G} (h : ChoiceExists2011 D (Choice214U D)) :
    ChoiceExists2011 D (ChoiceZ D) := by
  intro L0 hL0 n hn
  obtain ⟨B0, hB0ch, hB0, hpi, hα, hBM⟩ := h L0 hL0 n hn
  by_cases hnZ : n = CFSG.Open.pRank 2 D.Z
  · subst hnZ
    by_cases hex : ∃ B' : Subgroup G, Choice214U D L0 B' ∧
        Choice2011Out D L0 B' (CFSG.Open.pRank 2 D.Z) ∧
          B' ⊓ centralizer (D.Z : Set G) = ⊥
    · obtain ⟨B', hB'ch, hB'out, hB'bot⟩ := hex
      exact ⟨B', ⟨hB'ch, fun _ _ => hB'bot⟩, hB'out.1, hB'out.2.1, hB'out.2.2.1,
        hB'out.2.2.2⟩
    · exact ⟨B0, ⟨hB0ch, fun _ hex' => absurd hex' hex⟩, hB0, hpi, hα, hBM⟩
  · refine ⟨B0, ⟨hB0ch, ?_⟩, hB0, hpi, hα, hBM⟩
    intro hout _
    exact absurd (etaSet_injective (hpi.symm.trans hout.2.1)) hnZ

theorem choice2011ZRepair_choiceZ_of {D : Data G}
    (h : H1930 D → ∀ c : Ctx23L D (ChoiceZ D), c.n = CFSG.Open.pRank 2 D.Z →
      c.B0 ⊓ centralizer (D.Z : Set G) = ⊥ ∨
        ∃ B' : Subgroup G, Choice214U D c.L0 B' ∧
          Choice2011Out D c.L0 B' (CFSG.Open.pRank 2 D.Z) ∧
            B' ⊓ centralizer (D.Z : Set G) = ⊥) :
    Choice2011ZRepair D (ChoiceZ D) := by
  intro hH c hn
  rcases h hH c hn with hbot | ⟨B', hB'ch, hB'out, hB'bot⟩
  · exact hbot
  · refine c.hch.2 ?_ ⟨B', hB'ch, hB'out, hB'bot⟩
    exact ⟨c.hB0, by simpa [hn] using c.hpi, by simpa [hn] using c.hα, c.hBM⟩

@[expose] def Ctx22.mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx22 D Ch') : Ctx22 D Ch :=
  { c with hch := h c.L0 c.B0 c.hch }

@[simp] theorem Ctx22.mono_L0 {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx22 D Ch') :
    (c.mono h).L0 = c.L0 := rfl

@[simp] theorem Ctx22.mono_B0 {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx22 D Ch') :
    (c.mono h).B0 = c.B0 := rfl

@[simp] theorem Ctx22.mono_B {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx22 D Ch') :
    (c.mono h).B = c.B := rfl

@[simp] theorem Ctx22.mono_n {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx22 D Ch') :
    (c.mono h).n = c.n := rfl

@[expose] def Ctx23.mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23 D Ch') : Ctx23 D Ch :=
  { c with hch := h c.L0 c.B0 c.hch }

@[simp] theorem Ctx23.mono_L0 {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23 D Ch') :
    (c.mono h).L0 = c.L0 := rfl

@[simp] theorem Ctx23.mono_B0 {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23 D Ch') :
    (c.mono h).B0 = c.B0 := rfl

@[simp] theorem Ctx23.mono_B {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23 D Ch') :
    (c.mono h).B = c.B := rfl

@[simp] theorem Ctx23.mono_n {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23 D Ch') :
    (c.mono h).n = c.n := rfl

@[expose] def Ctx23L.mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') : Ctx23L D Ch :=
  { c with hch := h c.L0 c.B0 c.hch }

@[simp] theorem Ctx23L.mono_L0 {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') :
    (c.mono h).L0 = c.L0 := rfl

@[simp] theorem Ctx23L.mono_B0 {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') :
    (c.mono h).B0 = c.B0 := rfl

@[simp] theorem Ctx23L.mono_B {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') :
    (c.mono h).B = c.B := rfl

@[simp] theorem Ctx23L.mono_n {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') :
    (c.mono h).n = c.n := rfl

@[simp] theorem Ctx23L.mono_L {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') :
    (c.mono h).L = c.L := rfl

@[simp] theorem Ctx23L.mono_N {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx23L D Ch') :
    (c.mono h).N = c.N := rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
