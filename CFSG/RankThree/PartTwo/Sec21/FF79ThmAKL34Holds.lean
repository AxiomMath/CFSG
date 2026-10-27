module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmADefs
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKL34Aut
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKL34Spec
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.ComponentClassification.PSL3Four CFSG.RankThree.PartTwo.Sec21.FF79.KL34

theorem ff79KL34b_holds :
    FF79KL34b := by
  intro E _ _ hE P hP φ hφ hφ4
  obtain ⟨ε₀⟩ := nonempty_equiv_of_stated E hE
  obtain ⟨A₀, hA₀S, hA₀9, hcent, -⟩ := l34KLSpec
  obtain ⟨ε, hεP, hεA⟩ := exists_equiv_map_eq ε₀ hP hA₀S hA₀9
  obtain ⟨r, hrR, hr, hpow⟩ := exists_aut_rep ε φ
  have hrc : ∀ a ∈ A₀, r * a = a * r := by
    intro a ha
    obtain ⟨b, hbP, rfl⟩ := hεA a ha
    have h1 := hr b
    rw [hφ b hbP] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm)
  exact (hpow 2).2 (hcent r hrR hrc ((hpow 4).1 hφ4))

theorem ff79KL34a_holds :
    FF79KL34a := by
  intro E _ _ hE β hβ3 P hP hβP ⟨K, hK, hKβ⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_of_stated E hE
  obtain ⟨A₀, hA₀S, hA₀9, -, hsq⟩ := l34KLSpec
  obtain ⟨ε, hεP, hεA⟩ := exists_equiv_map_eq ε₀ hP hA₀S hA₀9
  obtain ⟨r, hrR, hr, hpow⟩ := exists_aut_rep ε β
  have hr3 : r ^ 3 = 1 := (hpow 3).1 hβ3
  have hrn : ∀ a ∈ A₀, r * a * r⁻¹ ∈ A₀ := by
    intro a ha
    obtain ⟨b, hbP, rfl⟩ := hεA a ha
    rw [← hr b]
    exact hεP _ (hβP b hbP)
  have hK60 : Nat.card K = 60 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hK
  let K' : Subgroup (Equiv.Perm (Fin 42)) := (K.map ε.toMonoidHom).map S.subtype
  have hK'card : Nat.card K' = 60 := by
    rw [Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective ε.injective, hK60]
  have hK'le : K' ≤ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (ε k).2⟩
    have h1 := hr k
    rw [hKβ k hk] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
  have h60 : 60 ≤ Nat.card (Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S :
      Subgroup (Equiv.Perm (Fin 42))) := hK'card ▸ Subgroup.card_le_of_le hK'le
  obtain ⟨q, hqS, hqn, hq4, hq2, hqc⟩ := hsq r hrR hr3 hrn h60
  set q' : E := ε.symm ⟨q, hqS⟩ with hq'
  have hεq' : ((ε q' : S) : Equiv.Perm (Fin 42)) = q := by rw [hq']; simp
  have hεq2 : ((ε (q' ^ 2) : S) : Equiv.Perm (Fin 42)) = q ^ 2 := by
    rw [map_pow, Subgroup.coe_pow, hεq']
  refine ⟨q', ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨b, hbP, hb⟩ := hεA (q * (ε s : Equiv.Perm (Fin 42)) * q⁻¹)
      (hqn _ (hεP s hs))
    have : q' * s * q'⁻¹ = b := by
      apply ε.injective
      apply Subtype.ext
      rw [hb, map_mul, map_mul, map_inv]
      simp [hεq']
    rw [this]
    exact hbP
  · apply ε.injective
    apply Subtype.ext
    have h1 := hr (q' ^ 2)
    rw [hεq2] at h1
    rw [h1, hεq2, hqc]
    group
  · intro h
    apply hq2
    rw [← hεq2, h, map_one]
    rfl
  · have : q ^ 4 = 1 := hq4
    apply ε.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hεq', this, map_one]
    rfl

theorem ff79KL34_holds :
    FF79KL34 :=
  ⟨ff79KL34a_holds, ff79KL34b_holds⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
