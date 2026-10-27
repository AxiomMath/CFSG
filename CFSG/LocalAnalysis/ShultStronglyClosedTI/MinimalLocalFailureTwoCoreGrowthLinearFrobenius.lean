module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {G : Type u} [Group G] [Finite G]

theorem elementary_two_frobenius_complement_card
    (K R : Subgroup G) (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    [IsElementaryAbelian 2 R] : Nat.card R = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  have hinvolution : ∀ r : R, r ≠ 1 → orderOf r = 2 := by
    intro r hr
    exact orderOf_eq_prime_iff.mpr
      ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 R) r, hr⟩
  apply (Nat.card_eq_two_iff' (1 : R)).mpr
  refine ⟨t, ht, ?_⟩
  intro r hr
  exact CFSG.BenderSuzuki.External.frobenius_complement_involutions_eq
    K R hFrob r t (hinvolution r hr) (hinvolution t ht)

theorem frobenius_kernel_inverted_by_involution
    (K R : Subgroup G) (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    (t : R) (htorder : orderOf t = 2) :
    Odd (Nat.card K) ∧ IsMulCommutative K ∧
      ∀ x : K, (t : G) * (x : G) * (t : G)⁻¹ = (x⁻¹ : K) := by
  let : K.Normal := hFrob.normal
  let phi : MulAut K := MulAut.conjNormal (H := K) (t : G)
  have htne : t ≠ 1 := by
    intro ht
    subst t
    simp at htorder
  have htsq : (t : G) ^ 2 = 1 := by
    have ht : t ^ 2 = 1 := by
      rw [← htorder]
      exact pow_orderOf_eq_one t
    exact congrArg Subtype.val ht
  have hphisq : phi ^ 2 = 1 := by
    change (MulAut.conjNormal (H := K) (t : G)) ^ 2 = 1
    rw [← map_pow, htsq, map_one]
  have hphiinvolutive : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut K => psi x) hphisq
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hx
  have hphifree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hconj : (t : G) * (x : G) * (t : G)⁻¹ = (x : G) := by
      simpa only [phi, MulAut.conjNormal_apply] using congrArg Subtype.val hx
    have hcomm : (x : G) * (t : G) = (t : G) * (x : G) := by
      have heq := congrArg (fun y : G => y * (t : G)) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    have hcent := (CFSG.lemma_3_1 K R hFrob.kernel_ne_bot
      hFrob.complement_ne_bot hFrob.normal hFrob.isComplement').mp hFrob t htne
    have hxcent : (x : G) ∈ CFSG.elementCentralizerIn K (t : G) :=
      ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hcent] at hxcent
    exact Subtype.ext (Subgroup.mem_bot.mp hxcent)
  have hcommutative : IsMulCommutative K :=
    ⟨⟨fun x y => (hphifree.commute_all_of_involutive hphiinvolutive x y).eq⟩⟩
  refine ⟨hphifree.odd_card_of_involutive hphiinvolutive, hcommutative, ?_⟩
  intro x
  have hinverse := congrFun
    (hphifree.coe_eq_inv_of_involutive hphiinvolutive) x
  simpa only [phi, MulAut.conjNormal_apply] using congrArg Subtype.val hinverse

theorem elementary_two_TI_frobenius_decomposition
    (R : Subgroup G) (hRne : R ≠ ⊥) (hRproper : R ≠ ⊤)
    (hRelementary : IsElementaryAbelian 2 R)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g)) :
    ∃ K : Subgroup G, IsFrobeniusGroupWithKernelComplement K R ∧
      Nat.card R = 2 ∧ Odd (Nat.card K) ∧ IsMulCommutative K ∧
      ∀ t : R, orderOf t = 2 →
        ∀ x : K, (t : G) * (x : G) * (t : G)⁻¹ = (x⁻¹ : K) := by
  let : IsElementaryAbelian 2 R := hRelementary
  obtain ⟨K, hFrob⟩ :=
    CFSG.BenderSuzuki.External.Suzuki.VI.suzuki_ch6_theorem_2_3
      R hRne hRproper hTI
  have hRcard := elementary_two_frobenius_complement_card K R hFrob
  have htwo : 2 ∣ Nat.card R := by rw [hRcard]
  obtain ⟨t, htorder⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 htwo
  obtain ⟨hodd, hcomm, _⟩ := frobenius_kernel_inverted_by_involution K R hFrob t htorder
  refine ⟨K, hFrob, hRcard, hodd, hcomm, ?_⟩
  intro s hs
  exact (frobenius_kernel_inverted_by_involution K R hFrob s hs).2.2

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
