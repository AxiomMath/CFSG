module

public import CFSG.Permutation.FiveTransitive.OyamaTwoOrderFourShape
public import CFSG.Permutation.FiveTransitive.OyamaCentralTwistFixed
public import CFSG.Permutation.FiveTransitive.NormalizerSylowCenter
public import CFSG.Permutation.FiveTransitive.NormalizerSylowOrderSixteen
public import CFSG.Permutation.FiveTransitive.NormalizerFourCenter
public import CFSG.Permutation.FiveTransitive.SylowCenterFusion
public import CFSG.Permutation.FiveTransitive.FourTransitiveTwoPart

public section

namespace CFSG

namespace FiveTransitive.OyamaTwoContradiction

open MulAction FixedSetNormalizerHom

theorem contradiction
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Nat.card X) (h4 : IsMultiplyPretransitive G X 4)
    (hglobal : ∀ T : Sylow 2 G, Nat.card T = 16)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup G s))
    (hS : Nat.card S = 2)
    (hsix : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X)) : False := by
  classical
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  let N := Subgroup.normalizer (Q : Set G)
  have hcard : Nat.card Q = 2 := by
    rw [show Q = (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype from rfl,
      Subgroup.card_map_of_injective (fixingSubgroup G s).subtype_injective]
    exact hS
  let _ : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q, hq⟩ := exists_ne (1 : S)
  let qG : G := ((q : fixingSubgroup G s) : G)
  let qQ : Q := ⟨qG, Subgroup.mem_map_of_mem _ q.property⟩
  have hqG : qG ≠ 1 := by
    intro h
    exact hq (Subtype.ext (Subtype.ext h))
  have hqQ : qQ ≠ 1 := fun h => hqG (congrArg Subtype.val h)
  have hqfix : (fixedBy X qG).ncard = 6 := by
    rw [OyamaCentralTwistFixed.fixedBy_eq_of_card_two Q hcard qQ hqQ]
    exact hsix
  obtain ⟨a₀, ha₀, _, _⟩ := OyamaTwoOrderFourShape.exists_order_four_shape
    G X h4 s hs S hS hsix himage
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  obtain ⟨a, haN, ha, hfa, _, _, _⟩ :=
    SixOrderFourNormalizerRepresentative.exists_conjugate G X h4 s hs S hsix heven a₀ ha₀
  have hshape := OyamaTwoOrderFourShape.fixed_zero_and_square_two G X h4 s hs S hS hsix himage a ha
  let z := a ^ 2
  have hzfix : (fixedBy X z).ncard = 2 := hshape.2
  have hzord : orderOf z = 2 := by dsimp [z]; rw [orderOf_pow, ha]; norm_num
  have hz2 : z ^ 2 = 1 := hzord ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by intro h; simp only [h, orderOf_one] at hzord; contradiction
  have hzN : z ∈ N := N.pow_mem haN 2
  have hzi : fixedPermHom G X Q ⟨z, hzN⟩ ≠ 1 := by
    intro h
    have hp : (fixedPermHom G X Q ⟨a, haN⟩) ^ 2 = 1 := by rw [← map_pow]; exact h
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hfa] at hd
    norm_num at hd
  have hqz : qG ≠ z := by intro h; rw [h] at hqfix; omega
  have htwist : (fixedBy X (qG * z)).ncard = 6 :=
    OyamaCentralTwistFixed.twist_fixed_six G X hX h4 s hs S Q rfl hcard hsix himage
      qQ hqQ z hzN hz2 hzi hzfix
  obtain ⟨P, haR, hQR, hsq, hnorm, hcenter⟩ :=
    NormalizerSylowCenter.exists_sylow_unique_square_center G X s S hS Q rfl hsix himage
      qQ hqQ a haN ha hfa
  let R : Subgroup G := (P : Subgroup N).map N.subtype
  have hPcard : Nat.card P = 16 :=
    NormalizerSylowOrderSixteen.card_eq_sixteen G X s S hS Q rfl hsix himage P
  let T₀ : Sylow 2 G := Classical.arbitrary _
  obtain ⟨T, hT⟩ := FourTransitiveTwoPart.exists_ambient_sylow_of_card_eq N P T₀
    (hPcard.trans (hglobal T₀).symm)
  have hRN : R ≤ N := by rintro x ⟨y, _, rfl⟩; exact y.property
  have hqR : qG ∈ R := hQR qQ.property
  have hqC : qG ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (NormalizerTwoElementInvolution.central_of_card_two Q hcard ⟨y, hRN hy⟩ qQ).symm
  have hzC : z ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hnorm y (R.le_normalizer hy)
  have hrC : qG * z ∈ Subgroup.centralizer (R : Set G) :=
    (Subgroup.centralizer (R : Set G)).mul_mem hqC hzC
  have horbit : ∀ n ∈ Subgroup.normalizer (R : Set G),
      n * qG * n⁻¹ = qG ∨ n * qG * n⁻¹ = qG * z :=
    NormalizerFourCenter.conjugate_eq_or_twist R qG z hqR hqC hqG hqz hnorm hcenter
  have hq2 : qG ^ 2 = 1 := by
    have h : qQ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one' (x := qQ)
    exact congrArg Subtype.val h
  have hcomm : Commute qG z :=
    NormalizerTwoElementInvolution.central_of_card_two Q hcard ⟨z, hzN⟩ qQ
  have hr2 : (qG * z) ^ 2 = 1 := by rw [hcomm.mul_pow, hq2, hz2, one_mul]
  have hr1 : qG * z ≠ 1 := by
    intro h
    have hqinv : qG⁻¹ = qG := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hq2)
    have he : z = qG⁻¹ := eq_inv_of_mul_eq_one_right h
    exact hqz (he.trans hqinv).symm
  have hrord : orderOf (qG * z) = 2 := orderOf_eq_prime hr2 hr1
  obtain ⟨c, hc⟩ := FixedBaseInvolutionFusion.exists_conjugate_eq 4 h4 s hs S hS q hq
    (qG * z) hrord (by omega)
  change c * (qG * z) * c⁻¹ = qG at hc
  have hconj : ∃ g : G, g * qG * g⁻¹ = qG * z := by
    refine ⟨c⁻¹, ?_⟩
    rw [inv_inv]
    calc
      c⁻¹ * qG * c = c⁻¹ * (c * (qG * z) * c⁻¹) * c :=
        congrArg (fun x : G => c⁻¹ * x * c) hc.symm
      _ = qG * z := by group
  have heq : qG = qG * z := by
    apply SylowCenterFusion.eq_of_conjugate_of_normalizer_conj_eq_or T qG (qG * z)
    · change qG ∈ Subgroup.centralizer ((T : Subgroup G) : Set G)
      rw [hT]; exact hqC
    · change qG * z ∈ Subgroup.centralizer ((T : Subgroup G) : Set G)
      rw [hT]; exact hrC
    · change ∀ n ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), _
      rw [hT]; exact horbit
    · exact hconj
  exact hz1 (mul_left_cancel ((mul_one qG).trans heq)).symm

end FiveTransitive.OyamaTwoContradiction

end CFSG
