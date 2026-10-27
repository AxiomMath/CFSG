module

public import CFSG.Permutation.FiveTransitive.NormalizerSylowUniqueSquare
public import CFSG.Permutation.FiveTransitive.CentralizerSylowFusion
public import CFSG.Permutation.FiveTransitive.CardTwoNormalizer
public import CFSG.Permutation.FiveTransitive.FixedBaseInvolutionFusion

public section

namespace CFSG

namespace FiveTransitive.OyamaTwoSquareFixed

open MulAction FixedSetNormalizerHom

theorem square_fixed_lt_four
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (ha : orderOf a = 4) (hfa : orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4) :
    (fixedBy X (a ^ 2)).ncard < 4 := by
  classical
  by_contra hlt
  have hfix : 4 ≤ (fixedBy X (a ^ 2)).ncard := Nat.le_of_not_gt hlt
  have ha2 : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
  have ha2ne : a ^ 2 ≠ 1 := by intro h; simp only [h, orderOf_one] at ha2; contradiction
  let _ : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q, hq⟩ := exists_ne (1 : S)
  let qG : G := ((q : fixingSubgroup G s) : G)
  have hqQ : qG ∈ Q := by rw [← hQ]; exact Subgroup.mem_map_of_mem _ q.property
  have hqG : qG ≠ 1 := by
    intro h
    apply hq
    apply Subtype.ext
    exact Subtype.ext h
  let qQ : Q := ⟨qG, hqQ⟩
  have hqQne : qQ ≠ 1 := fun h => hqG (congrArg Subtype.val h)
  have hcard : Nat.card Q = 2 := by
    rw [← hQ, Subgroup.card_map_of_injective (fixingSubgroup G s).subtype_injective]
    exact hS
  have hNC : Subgroup.normalizer (Q : Set G) = Subgroup.centralizer ({qG} : Set G) :=
    CardTwoNormalizer.normalizer_eq_centralizer Q hcard qQ hqQne
  obtain ⟨c, hc⟩ := FixedBaseInvolutionFusion.exists_conjugate_eq 4 h4 s hs S hS q hq
    (a ^ 2) ha2 hfix
  change c * a ^ 2 * c⁻¹ = qG at hc
  have hconj : ∃ g : G, g * qG * g⁻¹ = a ^ 2 := by
    refine ⟨c⁻¹, ?_⟩
    rw [← hc]
    group
  obtain ⟨P, haP, _, hsq⟩ :=
    NormalizerSylowUniqueSquare.exists_sylow G X s S hS Q hQ hsix himage a haN ha hfa
  have heq : qG = a ^ 2 := by
    revert P
    rw [hNC]
    intro P haP _ hsq
    exact CentralizerSylowFusion.eq_square_of_unique_square qG a hconj P haP ha2ne hsq
  have ha2Q : a ^ 2 ∈ Q := heq ▸ hqQ
  have ha2N : a ^ 2 ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).pow_mem haN 2
  have hmap : fixedPermHom G X Q ⟨a ^ 2, ha2N⟩ = 1 := by
    apply (mem_ker_iff G X Q _).mpr
    intro x hx
    exact mem_fixedPoints.mp hx ⟨a ^ 2, ha2Q⟩
  have hpow : (fixedPermHom G X Q ⟨a, haN⟩) ^ 2 = 1 := by
    rw [← map_pow]
    exact hmap
  have hd := orderOf_dvd_of_pow_eq_one hpow
  rw [hfa] at hd
  norm_num at hd

end FiveTransitive.OyamaTwoSquareFixed

end CFSG
