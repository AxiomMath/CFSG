module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKL34Aut
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5KSpec
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.ComponentClassification.PSL3Four CFSG.RankThree.PartTwo.Sec21.FF79.KL34
  CFSG.RankThree.PartTwo.Sec21.FF79.KL35

theorem ff79KL35a_holds :
    FF79KL35a := by
  intro E _ _ hE β hβ3 P hP hβP ⟨K, hK, hKβ⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_of_stated E hE
  obtain ⟨A₀, hA₀S, hA₀9, hinv, -⟩ := l35KLSpec
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
  obtain ⟨τ, hτS, hτ2, hτ1, hτA, hτc⟩ := hinv r hrR hr3 hrn h60
  set σ : E := ε.symm ⟨τ, hτS⟩ with hσ
  have hεσ : ((ε σ : S) : Equiv.Perm (Fin 42)) = τ := by rw [hσ]; simp
  have hσ2 : σ ^ 2 = 1 := by
    apply ε.injective
    apply Subtype.ext
    rw [map_pow, Subgroup.coe_pow, hεσ, hτ2, map_one]
    rfl
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hτ1
    rw [← hεσ, h, map_one]
    rfl
  refine ⟨σ, orderOf_eq_prime hσ2 hσ1, ?_, ?_⟩
  · apply ε.injective
    apply Subtype.ext
    have h1 := hr σ
    rw [hεσ] at h1
    rw [h1, hεσ, hτc]
    group
  · intro s hs
    apply ε.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hεσ]
    exact hτA _ (hεP s hs)

theorem ff79KL35b_holds :
    FF79KL35b := by
  intro E _ _ hE β hβ3 hβn K hK hKβ g hg
  obtain ⟨ε⟩ := nonempty_equiv_of_stated E hE
  obtain ⟨-, -, -, -, hout⟩ := l35KLSpec
  obtain ⟨r, hrR, hr, hpow⟩ := exists_aut_rep ε β
  have hr3 : r ^ 3 = 1 := (hpow 3).1 hβ3
  have hrS : r ∉ S := by
    intro hrS
    apply hβn (ε.symm ⟨r, hrS⟩)
    ext x
    apply ε.injective
    apply Subtype.ext
    rw [hr x, MulAut.conj_apply, map_mul, map_mul, map_inv]
    simp
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
  have hc60 := hout r hrR hrS hr3 h60
  have hKeq : K' = Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S :=
    Subgroup.eq_of_le_of_card_ge hK'le (by rw [hc60, hK'card])
  have hgmem : ((ε g : S) : Equiv.Perm (Fin 42)) ∈
      Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (ε g).2⟩
    have h1 := hr g
    rw [hg] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
  rw [← hKeq] at hgmem
  obtain ⟨_, ⟨k, hk, rfl⟩, hke⟩ := hgmem
  have : ε k = ε g := Subtype.ext hke
  rw [← ε.injective this]
  exact hk

end CFSG.RankThree.PartTwo.Sec21.FF79
