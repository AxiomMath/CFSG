module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcLabel
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

namespace E6Nonsplit

section Cover

variable {C C' : Type} [Group C] [Group C']

theorem ggFix_conj_eq_centralizer (a : C) :
    ggFix (MulAut.conj a) = Subgroup.centralizer ({a} : Set C) := by
  ext x
  rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem isComponentOf_map_centralizer_of_central_cover (π : C →* C')
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center C) (a : C) {X : Subgroup C}
    (hX : IsComponentOf X (Subgroup.centralizer ({a} : Set C))) :
    IsComponentOf (X.map π) (Subgroup.centralizer ({π a} : Set C')) := by
  have h := LayerCC.isComponentOf_map_ggFix (f := π) (α := MulAut.conj a)
    (β := MulAut.conj (π a)) hπ hker (fun x => by simp [MulAut.conj_apply]) (K := X)
    (by rwa [ggFix_conj_eq_centralizer])
  rwa [ggFix_conj_eq_centralizer] at h

theorem ggNonsplitDvdAt_of_central_cover (π : C →* C') (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center C) {p : ℕ} (h : ExcNonsplit.GGNonsplitDvdAt C' p) :
    ExcNonsplit.GGNonsplitDvdAt C p := by
  intro a ha X hX
  have hX' := isComponentOf_map_centralizer_of_central_cover π hπ hker a hX
  have hdvd := h (π a) (by rw [← map_pow, ha, map_one]) (X.map π) hX'
  exact hdvd.trans (Subgroup.card_dvd_of_surjective (π.subgroupMap_surjective X))

end Cover

section E6


theorem ggNonsplitDvdAt_E6_sc_of_ad {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (h : ExcNonsplit.GGNonsplitDvdAt ↥(adjointGroup .E6 K) p) :
    ExcNonsplit.GGNonsplitDvdAt ↥(e6Data_valid.minGroup K) p :=
  ggNonsplitDvdAt_of_central_cover (e6Isogeny K) (e6Isogeny_surjective K)
    (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)).le h

theorem not_dvd_card_E6_sc_of_ad {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (h : ¬ p ∣ Nat.card ↥(adjointGroup .E6 K)) :
    ¬ p ∣ Nat.card ↥(e6Data_valid.minGroup K) := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  have hker := CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)
  have hcard : Nat.card ↥(e6Data_valid.minGroup K) =
      Nat.card ↥(adjointGroup .E6 K) * Nat.card ↥(e6Isogeny K).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (e6Isogeny K).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (e6Isogeny_surjective K)).toEquiv]
  rw [hcard] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · exact h h1
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p h1
    have hgc : (g : ↥(e6Data_valid.minGroup K)) ∈ Subgroup.center ↥(e6Data_valid.minGroup K) := by
      rw [← hker]
      exact g.2
    have h3 : g ^ 3 = 1 := Subtype.ext
      (CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 K hgc)
    have hdvd3 : p ∣ 3 := hg ▸ orderOf_dvd_of_pow_eq_one h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd3)

end E6

end E6Nonsplit

end CFSG.StandardType
