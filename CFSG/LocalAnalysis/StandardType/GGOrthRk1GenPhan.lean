module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
import CFSG.GH74.L5U5.IdentUnitary
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal

theorem phanD_system_central_quotient (hD : PhanDInput2) {G : Type} [Group G] {r : ℕ} (hr : 4 ≤ r)
    {f : ℕ} (hq : 4 ≤ 2 ^ f) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (S : Fin r → Subgroup G)
    (hiso : ∀ i, Nonempty (Su K' 2 f 2 ≃* S i))
    (hcomm : ∀ i j, CFSG.StandardType.ggCoxeterMatrixD r i j = 2 → ∀ x ∈ S i, ∀ y ∈ S j,
      x * y = y * x)
    (hpair : ∀ i j, CFSG.StandardType.ggCoxeterMatrixD r i j = 3 →
      ∃ W : Subgroup G, UnitaryBlockStandardPair K' 2 f W (S i) (S j)) :
    (Even r → ∃ θ : (lieUniversal .POmegaPlus r 2 f Nat.prime_two).K →* G,
        θ.range = ⨆ i, S i ∧ θ.ker ≤ Subgroup.center (lieUniversal .POmegaPlus r 2 f
          Nat.prime_two).K) ∧
    (Odd r → ∃ θ : (lieUniversal .POmegaMinus r 2 f Nat.prime_two).K →* G,
        θ.range = ⨆ i, S i ∧ θ.ker ≤ Subgroup.center (lieUniversal .POmegaMinus r 2 f
          Nat.prime_two).K) := by
  let H : Subgroup G := ⨆ i, S i
  have hSH : ∀ i, S i ≤ H := fun i => le_iSup S i
  have hq2 : (2 : ℕ) ^ f ≠ 2 := by omega
  let U : Fin r → Subgroup ↥H := fun k => (S k).subgroupOf H
  let W : Fin r → Fin r → Subgroup ↥H := fun k l => U k ⊔ U l
  have hsys : WeakPhanSL K' 2 f (ggCoxeterMatrixD r) U W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k
      obtain ⟨φ⟩ := hiso k
      exact ⟨φ.trans (Subgroup.subgroupOfEquivOfLe (hSH k)).symm⟩
    · intro k l _
      rfl
    · intro k l hkl a ha b hb
      exact Subtype.ext (hcomm k l hkl (a : G) ha (b : G) hb)
    · intro k l hkl
      obtain ⟨W₀, hW₀⟩ := hpair k l hkl
      have h1 := CFSG.GH74.L5U5.unitaryBlockStandardPair_subgroupOf hK' hq2 hW₀ H
        (hSH k) (hSH l)
      have h2 := CFSG.GH74.L5U5.unitaryBlockStandardPair_eq_sup hK' hq2 h1
      rw [h2] at h1
      exact h1
    · apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
      have hU : ∀ k, (U k).map H.subtype = S k := fun k =>
        (Subgroup.subgroupOf_map_subtype (S k) H).trans (inf_eq_left.mpr (hSH k))
      simp only [hU]
      rfl
  obtain ⟨hEven, hOdd⟩ := hD K' f hK' hq r hr U W hsys
  have hrangeH : ∀ {Y : Type} [Group Y] (θ : Y →* ↥H), Function.Surjective θ →
      (H.subtype.comp θ).range = ⨆ i, S i := by
    intro Y _ θ hθ
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hθ, Subgroup.map_top,
      Subgroup.range_subtype]
  have hkerH : ∀ {Y : Type} [Group Y] (θ : Y →* ↥H), (H.subtype.comp θ).ker = θ.ker := by
    intro Y _ θ
    exact MonoidHom.ker_comp_of_injective θ H.subtype H.subtype_injective
  refine ⟨fun hev => ?_, fun hodd => ?_⟩
  · obtain ⟨θ, hθ, hker⟩ := hEven hev
    exact ⟨H.subtype.comp θ, hrangeH θ hθ, (hkerH θ).le.trans hker⟩
  · obtain ⟨θ, hθ, hker⟩ := hOdd hodd
    exact ⟨H.subtype.comp θ, hrangeH θ hθ, (hkerH θ).le.trans hker⟩

theorem center_lieUniversal_POmegaPlus {r : ℕ} (hr : 3 ≤ r) (f : ℕ) :
    Subgroup.center (lieUniversal .POmegaPlus r 2 f Nat.prime_two).K = ⊥ := by
  rw [show (lieUniversal .POmegaPlus r 2 f Nat.prime_two) =
      ⟨spinGroup (Spin.quadPlus r (GaloisField 2 f)),
        Spin.plusDatum r (GaloisField 2 f) hr⟩ from dite_eq_left hr]
  exact RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hr

theorem center_lieUniversal_POmegaMinus {r : ℕ} (hr : 4 ≤ r) (f : ℕ) :
    Subgroup.center (lieUniversal .POmegaMinus r 2 f Nat.prime_two).K = ⊥ := by
  rw [show (lieUniversal .POmegaMinus r 2 f Nat.prime_two) =
      ⟨spinGroup (Spin.quadMinus r (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2), Spin.Twisted.minusDatum r (minusCoeffs_irr 2 f)⟩ from rfl]
  exact CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hr (minusCoeffs_irr 2 f)

theorem iSup_eq_of_phanD (hD : PhanDInput2) {G : Type} [Group G] {Ω : Subgroup G} [Finite Ω]
    {r : ℕ} (hr : 4 ≤ r) {f : ℕ} (hq : 4 ≤ 2 ^ f) (K' : Type) [Field K'] [Finite K']
    [CharP K' 2] (hK' : Nat.card K' = (2 ^ f) ^ 2) (S : Fin r → Subgroup G)
    (hS : ∀ i, S i ≤ Ω) (hiso : ∀ i, Nonempty (Su K' 2 f 2 ≃* S i))
    (hcomm : ∀ i j, CFSG.StandardType.ggCoxeterMatrixD r i j = 2 → ∀ x ∈ S i, ∀ y ∈ S j,
      x * y = y * x)
    (hpair : ∀ i j, CFSG.StandardType.ggCoxeterMatrixD r i j = 3 →
      ∃ W : Subgroup G, UnitaryBlockStandardPair K' 2 f W (S i) (S j))
    (hUPlus : Even r →
      Nonempty ((lieUniversal .POmegaPlus r 2 f Nat.prime_two).K ≃* ↥Ω))
    (hUMinus : Odd r →
      Nonempty ((lieUniversal .POmegaMinus r 2 f Nat.prime_two).K ≃* ↥Ω)) :
    ⨆ i, S i = Ω := by
  have hle : ⨆ i, S i ≤ Ω := iSup_le hS
  have hcard : Nat.card ↥Ω ≤ Nat.card ↥(⨆ i, S i) := by
    obtain ⟨hEven, hOdd⟩ := phanD_system_central_quotient hD hr hq K' hK' S hiso hcomm hpair
    rcases Nat.even_or_odd r with hev | hodd
    · obtain ⟨θ, hrange, hker⟩ := hEven hev
      have hbot : Subgroup.center (lieUniversal .POmegaPlus r 2 f Nat.prime_two).K = ⊥ :=
        center_lieUniversal_POmegaPlus (by omega) f
      have hkerbot : θ.ker = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' := hker hx
        rwa [hbot] at hx'
      have hinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hkerbot
      have hcardY : Nat.card (lieUniversal .POmegaPlus r 2 f Nat.prime_two).K =
          Nat.card ↥(⨆ i, S i) := by
        rw [← hrange]
        exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      obtain ⟨e⟩ := hUPlus hev
      have hcardΩ : Nat.card (lieUniversal .POmegaPlus r 2 f Nat.prime_two).K =
          Nat.card ↥Ω := Nat.card_congr e.toEquiv
      exact (hcardΩ.symm.trans hcardY).le
    · obtain ⟨θ, hrange, hker⟩ := hOdd hodd
      have hbot : Subgroup.center (lieUniversal .POmegaMinus r 2 f Nat.prime_two).K = ⊥ :=
        center_lieUniversal_POmegaMinus (by omega) f
      have hkerbot : θ.ker = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' := hker hx
        rwa [hbot] at hx'
      have hinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).mp hkerbot
      have hcardY : Nat.card (lieUniversal .POmegaMinus r 2 f Nat.prime_two).K =
          Nat.card ↥(⨆ i, S i) := by
        rw [← hrange]
        exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      obtain ⟨e⟩ := hUMinus hodd
      have hcardΩ : Nat.card (lieUniversal .POmegaMinus r 2 f Nat.prime_two).K =
          Nat.card ↥Ω := Nat.card_congr e.toEquiv
      exact (hcardΩ.symm.trans hcardY).le
  exact Subgroup.eq_of_le_of_card_ge hle hcard

end OrthTorus

end CFSG.StandardType

end
