module

public import CFSG.RankThree.PartTwo.KFacts.KS116Lin
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG

section Pure

variable {X : Type} [Group X] [Finite X]

theorem eq_bot_of_perfect_isPGroup {Y : Type*} [Group Y] {r : ℕ} [Fact r.Prime] [Finite Y]
    {B : Subgroup Y} (hBp : IsPGroup r B) (hB : ⁅B, B⁆ = B) : B = ⊥ := by
  by_contra hne
  have hnil : Group.IsNilpotent B := hBp.isNilpotent
  have hsol : Group.IsSolvable B := inferInstance
  have htop : (⊤ : Subgroup B) ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have := (Subgroup.eq_bot_iff_forall _).mp h ⟨x, hx⟩ (Subgroup.mem_top _)
    simpa using congrArg Subtype.val this
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot (G := B) (H := (⊤ : Subgroup B)) htop
  have hcomm : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hB
  rw [hcomm] at hlt
  exact lt_irrefl _ hlt

theorem pCore_fixed_of_ndc (hLin : KFacts.NoDoubleComponentGL) (hXs : Group.IsSolvable X)
    (hX3 : ¬ 3 ∣ Nat.card X) {r : ℕ} [hr : Fact r.Prime] (hr5 : 5 ≤ r)
    (h3gen : ∀ P : Subgroup X, IsPGroup r P →
      ∃ s : Finset P, s.card ≤ 3 ∧ Subgroup.closure (s : Set P) = ⊤)
    {Γ : Type} [Group Γ] (φ : Γ →* MulAut X) (K T : Subgroup Γ) (n : Γ) [T.Normal]
    (hKperf : ⁅K, K⁆ = K)
    (hTinn : ∀ t ∈ T, ∃ x : X, ∀ y, φ t y = x * y * x⁻¹)
    (hKT : ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ T) :
    ∀ k ∈ K, ∀ f ∈ CFSG.pCore r X, φ k f = f := by
  classical
  set P := CFSG.pCore r X with hP
  have hPp : IsPGroup r P := BaerSuzuki.Helpers.pCore_isPGroup r
  haveI : P.Characteristic := BaerSuzuki.Helpers.pCore_characteristic r
  obtain ⟨-, hcomm, hpow⟩ := SectionRank.Ccomm.frattini_quotient_elementary hPp
  obtain ⟨s, hs3, hs⟩ := h3gen P hPp
  have hgen : ∃ s : Finset (P ⧸ frattini P), s.card ≤ 3 ∧
      Subgroup.closure (s : Set (P ⧸ frattini P)) = ⊤ := by
    refine ⟨s.image (QuotientGroup.mk' (frattini P)), Finset.card_image_le.trans hs3, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure, hs, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  let ρ : Γ →* MulAut (P ⧸ frattini P) := (SectionRank.Ccomm.frattiniAction P).comp φ
  let ρX : X →* MulAut (P ⧸ frattini P) :=
    (SectionRank.Ccomm.frattiniAction P).comp (MulAut.conj : X →* MulAut X)
  have hnorm : ∀ g ∈ ρ.range, ∀ t ∈ T.map ρ, g * t * g⁻¹ ∈ T.map ρ := by
    rintro g ⟨γ, rfl⟩ t ⟨t₀, ht₀, rfl⟩
    refine ⟨γ * t₀ * γ⁻¹, (inferInstance : T.Normal).conj_mem t₀ ht₀ γ, ?_⟩
    simp [map_mul, map_inv]
  have hle : T.map ρ ≤ ρX.range := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hTinn t ht
    refine ⟨x, ?_⟩
    have : φ t = MulAut.conj x := by
      ext y
      simpa using hx y
    simp [ρ, ρX, this]
  haveI : Group.IsSolvable ρX.range :=
    Group.isSolvable_of_surjective (f := ρX.rangeRestrict) ρX.rangeRestrict_surjective
  have hsolv : Group.IsSolvable (T.map ρ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have h3T : ¬ 3 ∣ Nat.card (T.map ρ) := fun h3 =>
    hX3 (h3.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd ρX)))
  have hperf : ⁅K.map ρ, K.map ρ⁆ = K.map ρ := by
    rw [← Subgroup.map_commutator, hKperf]
  have hconj : ⁅K.map ρ, (K.map ρ).map (MulAut.conj (ρ n)).toMonoidHom⁆ ≤ T.map ρ := by
    have h1 : (K.map ρ).map (MulAut.conj (ρ n)).toMonoidHom =
        (K.map (MulAut.conj n).toMonoidHom).map ρ := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [h1, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hKT
  have hK0 := hLin r hr5 (P ⧸ frattini P) hcomm hpow hgen ρ.range (T.map ρ) (K.map ρ) (ρ n)
    ⟨n, rfl⟩ (Subgroup.map_le_range ρ K) (Subgroup.map_le_range ρ T) hnorm hsolv h3T hperf hconj
  have hker : ∀ k ∈ K, ρ k = 1 := fun k hk =>
    ((Subgroup.map_eq_bot_iff _).mp hK0) hk
  let β : Γ →* MulAut P := (MulAut.characteristic P).comp φ
  have hBle : K.map β ≤ (SectionRank.Ccomm.autQuotient (frattini P)).ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact hker k hk
  have hBp : IsPGroup r (K.map β) :=
    (SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hPp).to_le hBle
  have hBperf : ⁅K.map β, K.map β⁆ = K.map β := by
    rw [← Subgroup.map_commutator, hKperf]
  have hB0 : K.map β = ⊥ := eq_bot_of_perfect_isPGroup hBp hBperf
  intro k hk f hf
  have hk1 : β k = 1 := ((Subgroup.map_eq_bot_iff _).mp hB0) hk
  have := congrArg (fun α : MulAut P => (α ⟨f, hf⟩ : P).1) hk1
  simpa [β] using this

theorem fitting_fixed_of_ndc (hLin : KFacts.NoDoubleComponentGL) (hXs : Group.IsSolvable X)
    (hX3 : ¬ 3 ∣ Nat.card X) (hlow : ∀ p : ℕ, p.Prime → p < 5 → CFSG.pCore p X = ⊥)
    (h3gen : ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r → ∀ P : Subgroup X, IsPGroup r P →
      ∃ s : Finset P, s.card ≤ 3 ∧ Subgroup.closure (s : Set P) = ⊤)
    {Γ : Type} [Group Γ] (φ : Γ →* MulAut X) (K T : Subgroup Γ) (n : Γ) [T.Normal]
    (hKperf : ⁅K, K⁆ = K)
    (hTinn : ∀ t ∈ T, ∃ x : X, ∀ y, φ t y = x * y * x⁻¹)
    (hKT : ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ T) :
    ∀ k ∈ K, ∀ f ∈ CFSG.fittingSubgroup X, φ k f = f := by
  intro k hk f hf
  have hle : CFSG.fittingSubgroup X ≤ (φ k).toMonoidHom.eqLocus (MonoidHom.id X) := by
    rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (p : ℕ).Prime := ⟨hp⟩
    by_cases h5 : (p : ℕ) < 5
    · rw [hlow p hp h5]
      exact bot_le
    · intro g hg
      exact pCore_fixed_of_ndc hLin hXs hX3 (not_lt.mp h5) (h3gen p (not_lt.mp h5)) φ K T n
        hKperf hTinn hKT k hk g hg
  exact hle hf

end Pure

end CFSG.RankThree.PartTwo.Sec11

end
