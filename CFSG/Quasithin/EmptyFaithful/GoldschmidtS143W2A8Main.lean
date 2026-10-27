module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2A8Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2A8K
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2A8Three

import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Equiv

namespace S143

namespace InspW2

theorem false_of_perm8 {L Gc : Type} [Group L] [Group Gc] [Finite Gc] {ρ : Gc →* MulAut L}
    {ž : Gc} {Ŝ Kh : Subgroup Gc} (hin : InspInput ρ ž Ŝ Kh) (ψ : Gc →* Perm (Fin 8))
    (hψ : Function.Injective ψ) (hA : ∀ a : Perm (Fin 8), Perm.sign a = 1 → ∃ g, ψ g = a)
    (hσ2 : ψ ž * ψ ž = 1) (hσ1 : ψ ž ≠ 1) (hσs : Perm.sign (ψ ž) = 1) : False := by
  have hrange : Nat.card ψ.range = Nat.card Gc := Nat.card_range_of_injective hψ
  have hdvd : Nat.card Gc ∣ 40320 := by
    have h1 : Nat.card ψ.range ∣ Nat.card (Perm (Fin 8)) :=
      Subgroup.card_subgroup_dvd_card ψ.range
    have h2 : Nat.card (Perm (Fin 8)) = 40320 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rwa [hrange, h2] at h1
  have hAlt : alternatingGroup (Fin 8) ≤ ψ.range := fun a ha =>
    hA a (Equiv.Perm.mem_alternatingGroup.mp ha)
  have hAcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hdvd2 : 20160 ∣ Nat.card Gc := by
    have := Subgroup.card_dvd_of_le hAlt
    rwa [hAcard, hrange] at this
  have hSi := Subgroup.card_mul_index Ŝ
  have hodd : ¬ 2 ∣ Ŝ.index := hin.sylow.2
  have h64 : Nat.card Ŝ = 64 ∧ Nat.card Gc = 20160 := by
    have hle : Nat.card Gc ≤ 40320 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨t, ht⟩ := hdvd2
    have hpos : 0 < Nat.card Gc := Nat.card_pos
    rcases hin.card_S with hS | hS <;> rw [hS] at hSi <;> omega
  have hrangeAlt : alternatingGroup (Fin 8) = ψ.range :=
    Subgroup.eq_of_le_of_card_ge hAlt (by rw [hrange, h64.2, hAcard])
  have hsign : ∀ g : Gc, Perm.sign (ψ g) = 1 := by
    intro g
    have : ψ g ∈ ψ.range := ⟨g, rfl⟩
    rw [← hrangeAlt] at this
    exact Equiv.Perm.mem_alternatingGroup.mp this
  set C : Subgroup Gc := Subgroup.centralizer ({ž} : Set Gc) with hC
  have hCcard : Nat.card C = 192 := by rw [hC, hin.card_C, h64.1]
  have hKcard : Nat.card Kh = 48 := hin.K_shape.1
  have hidx : Kh.relIndex C = 4 := by
    have h1 := Subgroup.card_mul_index (Kh.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hin.K_le).toEquiv, hKcard, hCcard] at h1
    have : (Kh.subgroupOf C).index = 4 := by omega
    exact this
  rcases involution_cycleType8 (ψ ž) hσ2 hσ1 hσs with hcyc | hcyc
  ·
    obtain ⟨τ, hτσ, hτs⟩ := exists_odd_centralizer8 (ψ ž) hcyc
    set Cσ := Subgroup.centralizer ({ψ ž} : Set (Perm (Fin 8))) with hCσ
    have hCσcard : Nat.card Cσ = 192 := card_centralizer8_two _ hcyc
    set H : Subgroup (Perm (Fin 8)) := alternatingGroup (Fin 8) ⊓ Cσ with hH
    have hmap : C.map ψ ≤ H := by
      rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨Equiv.Perm.mem_alternatingGroup.mpr (hsign g), ?_⟩
      rw [hCσ, Subgroup.mem_centralizer_singleton_iff]
      have hg' : g * ž = ž * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [← map_mul, ← map_mul, hg']
    have hCH : Nat.card C ≤ Nat.card H := by
      have h1 := Subgroup.card_le_of_le hmap
      rwa [← Nat.card_congr (Subgroup.equivMapOfInjective C ψ hψ).toEquiv] at h1
    have hHdvd : Nat.card H ∣ 192 := hCσcard ▸ Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card H ≠ 192 := by
      intro h192
      have heq : H = Cσ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hCσcard, h192])
      have hτ : τ ∈ H := by
        rw [heq, hCσ, Subgroup.mem_centralizer_singleton_iff]
        exact hτσ
      have := Equiv.Perm.mem_alternatingGroup.mp hτ.1
      rw [hτs] at this
      exact absurd this (by decide)
    have hd : ∀ d ∈ Nat.divisors 192, d ≠ 192 → d ≤ 96 := by decide +kernel
    have := hd _ (Nat.mem_divisors.mpr ⟨hHdvd, by norm_num⟩) hne
    omega
  ·
    obtain ⟨f, hfinj, hf⟩ := exists_nine_order_three (ψ ž) hcyc
    have hfs : ∀ i, Perm.sign (f i) = 1 := by
      intro i
      have h3 := congrArg Perm.sign (hf i).1
      rw [map_pow, map_one] at h3
      rcases Int.units_eq_one_or (Perm.sign (f i)) with h | h
      · exact h
      · rw [h] at h3
        exact absurd h3 (by decide)
    choose g hg using fun i => hA (f i) (hfs i)
    have hgC : ∀ i, g i ∈ C := by
      intro i
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      apply hψ
      rw [map_mul, map_mul, hg i]
      exact (hf i).2.2
    have hg3 : ∀ i, g i ^ 3 = 1 := by
      intro i
      apply hψ
      rw [map_pow, hg i, map_one]
      exact (hf i).1
    have hg1 : ∀ i, g i ≠ 1 := by
      intro i h
      apply (hf i).2.1
      rw [← hg i, h, map_one]
    have hginj : Function.Injective g := by
      intro i j h
      apply hfinj
      rw [← hg i, ← hg j, h]
    have hgK : ∀ i, g i ∈ Kh := fun i => mem_of_pow_three hin.K_norm hidx (hgC i) (hg3 i)
    exact no_nine_order_three hin.K_shape (fun i => (⟨g i, hgK i⟩ : Kh))
      (fun i j h => hginj (congrArg Subtype.val h))
      (fun i => ⟨Subtype.ext (by simpa using hg3 i), fun h => hg1 i (congrArg Subtype.val h)⟩)

theorem resW_a8 : ResW (fun L _ => StatedClassicalModel L .PSL 4 2 1) := by
  intro L _ _ _ hF Gc _ _ ρ ž Ŝ Kh hin ⟨z, hz2, hž⟩
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff L).mp
    (Or.inl ⟨by decide, hF⟩)
  obtain ⟨ψ, hψ, hψc⟩ := a8_embedding e ρ hin.inj
  have hψž : ψ ž = ((e z : alternatingGroup (Fin 8)) : Perm (Fin 8)) := hψc z ž hž
  have hz1 : z ≠ 1 := by
    intro h
    apply hin.ne
    apply hin.inj
    rw [hž, h, map_one, map_one]
  refine false_of_perm8 hin ψ hψ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨g, hg⟩ := hin.inn (e.symm ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩)
    refine ⟨g, ?_⟩
    rw [hψc _ g hg]
    simp
  · rw [hψž]
    have h : e z * e z = 1 := by rw [← map_mul, hz2, map_one]
    simpa using congrArg (fun a : alternatingGroup (Fin 8) => (a : Perm (Fin 8))) h
  · rw [hψž]
    intro h
    apply hz1
    apply e.injective
    apply Subtype.ext
    simpa using h
  · rw [hψž]
    exact Equiv.Perm.mem_alternatingGroup.mp (e z).2

end InspW2

end S143

end CFSG.Quasithin
