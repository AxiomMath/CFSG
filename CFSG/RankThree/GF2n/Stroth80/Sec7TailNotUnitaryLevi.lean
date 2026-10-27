module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNotUnitaryBase
import CFSG.LieType.BorelTits.LeviSU6

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

def ParabolicLeviData {G : Type*} [Group G] (U A P O : Subgroup G) (d₁ d₂ d₃ : ℕ) : Prop :=
  P ≤ U ∧ O ≤ P ∧ A ≤ O ∧ IsPGroup 2 O ∧
    (∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O) ∧
    (∀ g ∈ U, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ P) ∧
    ∀ S : Subgroup G, S ≤ P → commutator ↥S = ⊤ →
      Nat.card S ∣ Nat.card ↥(S ⊓ O) * d₁ ∨
      Nat.card S ∣ Nat.card ↥(S ⊓ O) * d₂ ∨
      Nat.card S ∣ Nat.card ↥(S ⊓ O) * d₃

theorem ParabolicLeviData.map_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {U A P O : Subgroup G} {d₁ d₂ d₃ : ℕ}
    (h : ParabolicLeviData U A P O d₁ d₂ d₃) :
    ParabolicLeviData (U.map f) (A.map f) (P.map f) (O.map f) d₁ d₂ d₃ := by
  unfold ParabolicLeviData at h
  obtain ⟨hPU, hOP, hAO, hO2, hnorm, hnrm, hdisj⟩ := h
  refine ⟨Subgroup.map_mono hPU, Subgroup.map_mono hOP, Subgroup.map_mono hAO,
    hO2.map f, ?_, ?_, ?_⟩
  · intro p hp o ho
    obtain ⟨p₀, hp₀, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨o₀, ho₀, rfl⟩ := Subgroup.mem_map.mp ho
    exact Subgroup.mem_map.mpr ⟨p₀ * o₀ * p₀⁻¹, hnorm p₀ hp₀ o₀ ho₀, by simp⟩
  · intro g hg hgn
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg
    refine Subgroup.mem_map.mpr ⟨g₀, hnrm g₀ hg₀ ?_, rfl⟩
    intro a ha
    exact (Subgroup.mem_map_iff_mem hf).1
      (by simpa using hgn (f a) (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
  · intro S hSP hSperf
    have hSrange : S ≤ f.range := hSP.trans (Subgroup.map_le_range f P)
    have hmapS : (S.comap f).map f = S := Subgroup.map_comap_eq_self hSrange
    have hS₀P : S.comap f ≤ P := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]
      exact Subgroup.comap_mono hSP
    have eS : ↥S ≃* ↥(S.comap f) :=
      (MulEquiv.subgroupCongr hmapS).symm.trans
        (Subgroup.equivMapOfInjective (S.comap f) f hf).symm
    have hS₀perf : commutator ↥(S.comap f) = ⊤ := by
      haveI : Group.IsPerfect ↥S := Group.IsPerfect.mk hSperf
      haveI : Group.IsPerfect ↥(S.comap f) :=
        Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective
      exact Group.IsPerfect.commutator_eq_top
    have hcardS : Nat.card ↥(S.comap f) = Nat.card ↥S := by
      calc Nat.card ↥(S.comap f)
          = Nat.card ↥((S.comap f).map f) := (Subgroup.card_map_of_injective hf).symm
        _ = Nat.card ↥S := Nat.card_congr (MulEquiv.subgroupCongr hmapS).toEquiv
    have hmapSO : (S.comap f ⊓ O).map f = S ⊓ O.map f := by
      rw [Subgroup.map_inf (S.comap f) O f hf, hmapS]
    have hcardSO : Nat.card ↥(S.comap f ⊓ O) = Nat.card ↥(S ⊓ O.map f) := by
      calc Nat.card ↥(S.comap f ⊓ O)
          = Nat.card ↥((S.comap f ⊓ O).map f) := (Subgroup.card_map_of_injective hf).symm
        _ = Nat.card ↥(S ⊓ O.map f) := Nat.card_congr (MulEquiv.subgroupCongr hmapSO).toEquiv
    rcases hdisj (S.comap f) hS₀P hS₀perf with h1 | h2 | h3
    · left; rwa [hcardS, hcardSO] at h1
    · right; left; rwa [hcardS, hcardSO] at h2
    · right; right; rwa [hcardS, hcardSO] at h3

theorem unitarySixLevi_of_model
    (h : ∀ (f : ℕ), 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (2 ^ f) ^ 2 →
      ∀ A : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)), A ≠ ⊥ → IsPGroup 2 A →
        ∃ P O : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)),
          O ≤ P ∧ A ≤ O ∧ IsPGroup 2 O ∧
          (∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O) ∧
          (∀ g, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ P) ∧
          ∀ S : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)), S ≤ P →
            commutator ↥S = ⊤ →
            Nat.card S ∣ Nat.card ↥(S ⊓ O) *
                ((2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) *
                  ((2 ^ f) ^ 4 - 1)) ∨
            Nat.card S ∣ Nat.card ↥(S ⊓ O) *
                ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) ∨
            Nat.card S ∣ Nat.card ↥(S ⊓ O) *
                ((2 ^ f) ^ 6 * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1))) :
    UnitarySixLeviStatement := by
  intro q hq2 Y _ _ U hU A hAU hAne hA2
  obtain ⟨f, hf, rfl⟩ := hq2
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hU
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  let A' : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)) :=
    (A.subgroupOf U).map e.toMonoidHom
  have hA'ne : A' ≠ ⊥ := by
    change (A.subgroupOf U).map e.toMonoidHom ≠ ⊥
    intro hbot
    have hbot' : A.subgroupOf U = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (A.subgroupOf U) e.injective).1 hbot
    exact hAne (by rw [← Subgroup.map_subgroupOf_eq_of_le hAU, hbot', Subgroup.map_bot])
  have hA'2 : IsPGroup 2 A' := by
    have hmap := (hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAU).symm).map e.toMonoidHom
    simpa [A'] using hmap
  obtain ⟨P', O', hOP, hAO, hO2, hnorm, hnrm, hdisj⟩ :=
    h f hf K hKcard A' hA'ne hA'2
  let d₁ : ℕ := (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1)
  let d₂ : ℕ := (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)
  let d₃ : ℕ := (2 ^ f) ^ 6 * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)
  have hdata : ParabolicLeviData ⊤ A' P' O' d₁ d₂ d₃ :=
    ⟨le_top, hOP, hAO, hO2, hnorm, fun g _ => hnrm g, hdisj⟩
  let φ : StatedProj (StatedSU 6 (2 ^ f) K) →* Y := U.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := U.subtype_injective.comp e.symm.injective
  have htop : (⊤ : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K))).map φ = U := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hy
      rw [← hx]
      exact (e.symm x).2
    · intro hy
      refine Subgroup.mem_map.mpr ⟨e ⟨y, hy⟩, Subgroup.mem_top _, ?_⟩
      simp [φ]
  have hAφ : A'.map φ = A := by
    change ((A.subgroupOf U).map e.toMonoidHom).map φ = A
    rw [Subgroup.map_map]
    have hcomp : φ.comp e.toMonoidHom = U.subtype := by
      ext x
      simp [φ]
    rw [hcomp, Subgroup.map_subgroupOf_eq_of_le hAU]
  have htrans := hdata.map_injective hφ
  rw [htop, hAφ] at htrans
  unfold ParabolicLeviData at htrans
  obtain ⟨hPU, hOPY, hAO', hO2Y, hnormY, hnrmY, hdisjY⟩ := htrans
  refine ⟨P'.map φ, O'.map φ, hPU, hOPY, hAO', hO2Y, hnormY, hnrmY, ?_⟩
  simpa [d₁, d₂, d₃] using hdisjY

theorem unitarySixLevi_holds : UnitarySixLeviStatement :=
  unitarySixLevi_of_model fun f hf K _ _ hK A hA hA2 =>
    CFSG.LieType.BorelTits.exists_levi_statedProj_su6 hf hK hA hA2

end CFSG.RankThree.GF2n.Stroth80
