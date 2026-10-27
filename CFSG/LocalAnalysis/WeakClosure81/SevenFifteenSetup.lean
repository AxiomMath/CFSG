module

public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.SevenSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mem_of_mul_self_mem_of_odd_relIndex {A B : Subgroup G} [(A.subgroupOf B).Normal]
    (hodd : Odd (A.relIndex B)) {x : G} (hx : x ∈ B) (hx2 : x * x ∈ A) : x ∈ A := by
  let a : ↥B ⧸ A.subgroupOf B := QuotientGroup.mk ⟨x, hx⟩
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hx2
  have hdvd2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
  have hdvdN : orderOf a ∣ A.relIndex B := by
    rw [show A.relIndex B = Nat.card (↥B ⧸ A.subgroupOf B) from
      Subgroup.index_eq_card (A.subgroupOf B)]
    exact orderOf_dvd_natCard a
  have hcop : Nat.Coprime 2 (A.relIndex B) := Nat.coprime_two_left.mpr hodd
  have h1 : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdN
  have ha1 : a = 1 := orderOf_eq_one_iff.mp h1
  have hmem : (⟨x, hx⟩ : ↥B) ∈ A.subgroupOf B :=
    (QuotientGroup.eq_one_iff (N := A.subgroupOf B) (⟨x, hx⟩ : ↥B)).mp ha1
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem relIndex_eq_two_of_forall {A B : Subgroup G}
    (hex : ∃ x ∈ B, x ∉ A)
    (h : ∀ x ∈ B, ∀ y ∈ B, x ∉ A → y ∉ A → x⁻¹ * y ∈ A) :
    A.relIndex B = 2 := by
  obtain ⟨x₀, hx₀B, hx₀A⟩ := hex
  refine (Subgroup.index_eq_two_iff (H := A.subgroupOf B)).mpr ⟨⟨x₀, hx₀B⟩, fun b => ?_⟩
  rw [xor_def]
  by_cases hbA : (b : G) ∈ A
  · right
    refine ⟨Subgroup.mem_subgroupOf.mpr hbA, fun hba => ?_⟩
    have h1 : (b : G) * x₀ ∈ A := by
      have := Subgroup.mem_subgroupOf.mp hba
      simpa using this
    have h2 : (b : G)⁻¹ * ((b : G) * x₀) = x₀ := by group
    exact hx₀A (h2 ▸ A.mul_mem (A.inv_mem hbA) h1)
  · left
    refine ⟨Subgroup.mem_subgroupOf.mpr ?_, fun hb => hbA (Subgroup.mem_subgroupOf.mp hb)⟩
    have h3 : (b : G)⁻¹ ∉ A := fun hb => hbA (by simpa using A.inv_mem hb)
    have := h (b : G)⁻¹ (B.inv_mem b.2) x₀ hx₀B h3 hx₀A
    simpa using this

omit [Finite G] in
theorem inv_mul_mem_of_relIndex_eq_two {A B : Subgroup G} (hindex : A.relIndex B = 2)
    {x y : G} (hx : x ∈ B) (hy : y ∈ B) (hxA : x ∉ A) (hyA : y ∉ A) : x⁻¹ * y ∈ A := by
  have h2 : (A.subgroupOf B).index = 2 := hindex
  haveI hN : (A.subgroupOf B).Normal := Subgroup.normal_of_index_eq_two h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2
  have hxa : (⟨x, hx⟩ : ↥B) * a ∈ A.subgroupOf B := by
    rcases ha ⟨x, hx⟩ with h | h
    · exact h.1
    · exact absurd (Subgroup.mem_subgroupOf.mp h.1) hxA
  have hya : (⟨y, hy⟩ : ↥B) * a ∈ A.subgroupOf B := by
    rcases ha ⟨y, hy⟩ with h | h
    · exact h.1
    · exact absurd (Subgroup.mem_subgroupOf.mp h.1) hyA
  have hmem : (⟨y, hy⟩ : ↥B) * (⟨x, hx⟩ : ↥B)⁻¹ ∈ A.subgroupOf B := by
    have h0 : (⟨y, hy⟩ : ↥B) * a * ((⟨x, hx⟩ : ↥B) * a)⁻¹ ∈ A.subgroupOf B :=
      (A.subgroupOf B).mul_mem hya ((A.subgroupOf B).inv_mem hxa)
    have h1 : (⟨y, hy⟩ : ↥B) * a * ((⟨x, hx⟩ : ↥B) * a)⁻¹ =
        (⟨y, hy⟩ : ↥B) * (⟨x, hx⟩ : ↥B)⁻¹ := by group
    rwa [h1] at h0
  have h1 : y * x⁻¹ ∈ A := by
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa using this
  have hconj : (⟨x, hx⟩ : ↥B)⁻¹ * (⟨y * x⁻¹, B.mul_mem hy (B.inv_mem hx)⟩ : ↥B) *
      (⟨x, hx⟩ : ↥B)⁻¹⁻¹ ∈ A.subgroupOf B :=
    hN.conj_mem (⟨y * x⁻¹, B.mul_mem hy (B.inv_mem hx)⟩ : ↥B)
      (Subgroup.mem_subgroupOf.mpr h1) (⟨x, hx⟩ : ↥B)⁻¹
  have h3 : x⁻¹ * (y * x⁻¹) * x ∈ A := by
    have := Subgroup.mem_subgroupOf.mp hconj
    simpa using this
  have h4 : x⁻¹ * y = x⁻¹ * (y * x⁻¹) * x := by group
  rwa [h4]

theorem le_zpowers_sup_of_relIndex_eq_two {A V : Subgroup G} (hAV : A ≤ V)
    (hindex : A.relIndex V = 2) {v : G} (hv : v ∈ V) (hvA : v ∉ A) :
    V ≤ Subgroup.zpowers v ⊔ A := by
  intro w hw
  by_cases hwA : w ∈ A
  · exact Subgroup.mem_sup_right hwA
  · have h := inv_mul_mem_of_relIndex_eq_two hindex hv hw hvA hwA
    have hvw : v * (v⁻¹ * w) = w := by group
    rw [← hvw]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers v) h

theorem le_iSub_sup_commutator {V H E Q : Subgroup G}
    (hV : IsElemAbelian 2 V) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hQK : Q ≤ kSub V H E) (hIQ : iSub V H E ≤ Q)
    (hQnorm : (Q.subgroupOf (kSub V H E)).Normal) (hKQV : kSub V H E = Q ⊔ V)
    (hodd : Odd ((iSub V H E).relIndex Q)) :
    Q ≤ iSub V H E ⊔ ⁅Q, V⁆ := by
  let T : Subgroup G := iSub V H E ⊔ ⁅Q, V⁆
  change Q ≤ T
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hQH : Q ≤ H := hQK.trans hKH
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun U _ => inf_le_right
  have hIH : iSub V H E ≤ H := hIO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm)
  have hKHN : kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) := hKH.trans hHI
  have hKQ : kSub V H E ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mp hQnorm
  have hVK : V ≤ kSub V H E := hKQV ▸ le_sup_right
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) := hVK.trans hKQ
  have hcommQ : ⁅Q, V⁆ ≤ Q := (Subgroup.le_normalizer_iff_commutator_le_left).mp hVQ
  have hIT : iSub V H E ≤ T := le_sup_left
  have hTQ : T ≤ Q := sup_le hIQ hcommQ
  have hKcomm : kSub V H E ≤ Subgroup.normalizer (⁅Q, V⁆ : Subgroup G) := by
    rw [hKQV]
    exact sup_le (Subgroup.normalizer_commutator_ge_left (H₁ := Q) (H₂ := V))
      (Subgroup.normalizer_commutator_ge_right (H₁ := Q) (H₂ := V))
  have hKN : kSub V H E ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hKHN hKcomm).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hQTN : Q ≤ Subgroup.normalizer (T : Set G) := hQK.trans hKN
  have hVT : V ≤ Subgroup.normalizer (T : Set G) := hVK.trans hKN
  have hoddT : Odd (T.relIndex Q) :=
    hodd.of_dvd_nat ⟨(iSub V H E).relIndex T,
      by
        rw [mul_comm]
        exact (Subgroup.relIndex_mul_relIndex (H := iSub V H E) (K := T) (L := Q) hIT hTQ).symm⟩
  haveI hTN : (T.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTQ).mpr hQTN
  haveI hIN : ((iSub V H E).subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIQ).mpr (hQH.trans hHI)
  have hUle : ∀ U ∈ omegaSet V H E, U ≤ T ⊔ V := by
    intro U hU u hu
    have huK : u ∈ kSub V H E := le_kSub hU hu
    rw [hKQV] at huK
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Q V hVQ] at huK
    obtain ⟨q, hq, w, hw, rfl⟩ := huK
    have hqw2 : (q * w) * (q * w) = 1 :=
      elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet hV hU) hu
    have hw2 : w * w = 1 := elemAbelian_mul_self hV hw
    have hcommwq : ⁅w, q⁆ ∈ T :=
      Subgroup.mem_sup_right (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hw hq)
    have hqq : q * q ∈ T := by
      have h1 : q * ⁅w, q⁆ * q = 1 := by
        have h2 : q * (w * q * w⁻¹) * (w * w) = 1 := by
          rw [show q * (w * q * w⁻¹) * (w * w) = (q * w) * (q * w) by group, hqw2]
        rw [hw2, mul_one] at h2
        rw [show w * q * w⁻¹ = ⁅w, q⁆ * q by rw [commutatorElement_def]; group] at h2
        simpa [mul_assoc] using h2
      have h4 : q * ⁅w, q⁆ = q⁻¹ := by
        calc q * ⁅w, q⁆ = (q * ⁅w, q⁆ * q) * q⁻¹ := by group
          _ = 1 * q⁻¹ := by rw [h1]
          _ = q⁻¹ := one_mul _
      have h5 : ⁅w, q⁆ = (q * q)⁻¹ := by
        calc ⁅w, q⁆ = q⁻¹ * (q * ⁅w, q⁆) := by group
          _ = q⁻¹ * q⁻¹ := by rw [h4]
          _ = (q * q)⁻¹ := by rw [mul_inv_rev]
      have : (q * q)⁻¹ ∈ T := h5 ▸ hcommwq
      simpa using T.inv_mem this
    have hqT : q ∈ T := mem_of_mul_self_mem_of_odd_relIndex hoddT hq hqq
    exact Subgroup.mul_mem_sup hqT hw
  have hKle : kSub V H E ≤ T ⊔ V := iSup₂_le hUle
  intro q hq
  have hqK : q ∈ T ⊔ V := hKle (hQK hq)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left T V hVT] at hqK
  obtain ⟨t, ht, w, hw, rfl⟩ := hqK
  have hwQ : w ∈ Q := by
    have : w = t⁻¹ * (t * w) := by group
    rw [this]
    exact Q.mul_mem (Q.inv_mem (hTQ ht)) hq
  have hw2 : w * w = 1 := elemAbelian_mul_self hV hw
  have hwI : w ∈ iSub V H E :=
    mem_of_mul_self_mem_of_odd_relIndex hodd hwQ (by rw [hw2]; exact (iSub V H E).one_mem)
  exact T.mul_mem ht (Subgroup.mem_sup_left hwI)

theorem relIndex_inf_iSub_eq_two {V H E Q : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hQK : Q ≤ kSub V H E) (hIQ : iSub V H E ≤ Q)
    (hQnorm : (Q.subgroupOf (kSub V H E)).Normal) (hKQV : kSub V H E = Q ⊔ V)
    (hodd : Odd ((iSub V H E).relIndex Q)) (hQI : ¬ Q ≤ iSub V H E) :
    (V ⊓ iSub V H E).relIndex V = 2 := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hQH : Q ≤ H := hQK.trans hKH
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun U _ => inf_le_right
  have hVK : V ≤ kSub V H E := hKQV ▸ le_sup_right
  have hKQ : kSub V H E ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mp hQnorm
  have hVN : V ≤ Subgroup.normalizer (Q : Set G) := hVK.trans hKQ
  have hVnotO : ¬ V ≤ pCoreOf 2 H := (mem_omegaSet.mp hVΩ).choose_spec.2.2
  have hne0 : (V ⊓ iSub V H E).relIndex V ≠ 0 := by
    rw [show (V ⊓ iSub V H E).relIndex V = ((V ⊓ iSub V H E).subgroupOf V).index from rfl]
    exact Subgroup.index_ne_zero_of_finite
  have hne1 : (V ⊓ iSub V H E).relIndex V ≠ 1 := by
    intro h1
    exact hVnotO ((Subgroup.relIndex_eq_one.mp h1).trans (inf_le_right.trans hIO))
  have hle2 : (V ⊓ iSub V H E).relIndex V ≤ 2 := by
    by_contra h
    have hbig : 2 < (V ⊓ iSub V H E).relIndex V := lt_of_not_ge h
    have hbigI : 2 < (iSub V H E).relIndex V := by
      rwa [Subgroup.inf_relIndex_left] at hbig
    have hcomm : ⁅V, Q⁆ ≤ iSub V H E :=
      seven_three_five hV hTI hE hEH hEnorm hVΩ hOmH hIO
        (iSub_subgroupOf_normal hEH hEnorm) le_rfl hbigI hIQ hQH hVN hodd
    have hgen : Q ≤ iSub V H E ⊔ ⁅Q, V⁆ :=
      le_iSub_sup_commutator hV hEH hEnorm hOmH hQK hIQ hQnorm hKQV hodd
    have hcomm' : ⁅Q, V⁆ ≤ iSub V H E := by rw [Subgroup.commutator_comm]; exact hcomm
    exact hQI (hgen.trans (sup_le le_rfl hcomm'))
  omega

theorem relIndex_inf_iSub_eq_two_of_mem_omegaSet {V H E Q U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hQK : Q ≤ kSub V H E) (hIQ : iSub V H E ≤ Q)
    (hQnorm : (Q.subgroupOf (kSub V H E)).Normal) (hKQV : kSub V H E = Q ⊔ V)
    (hodd : Odd ((iSub V H E).relIndex Q))
    (hindex : (V ⊓ iSub V H E).relIndex V = 2) (hU : U ∈ omegaSet V H E) :
    (U ⊓ iSub V H E).relIndex U = 2 := by
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hQH : Q ≤ H := hQK.trans hKH
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun W _ => inf_le_right
  have hIH : iSub V H E ≤ H := hIO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHI : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIH (iSub_subgroupOf_normal hEH hEnorm)
  have hVK : V ≤ kSub V H E := hKQV ▸ le_sup_right
  have hKQ : kSub V H E ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mp hQnorm
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) := hVK.trans hKQ
  haveI hIN : ((iSub V H E).subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIQ).mpr (hQH.trans hHI)
  have hUQ : U ⊓ Q = U ⊓ iSub V H E := by
    refine le_antisymm ?_ (inf_le_inf le_rfl hIQ)
    intro u hu
    obtain ⟨huU, huQ⟩ := Subgroup.mem_inf.mp hu
    have hu2 : u * u = 1 := elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet hV hU) huU
    exact Subgroup.mem_inf.mpr ⟨huU,
      mem_of_mul_self_mem_of_odd_relIndex hodd huQ (by rw [hu2]; exact (iSub V H E).one_mem)⟩
  have hUnotO : ¬ U ≤ pCoreOf 2 H := (mem_omegaSet.mp hU).choose_spec.2.2
  have hUnotI : ¬ U ≤ iSub V H E := fun h => hUnotO (h.trans hIO)
  obtain ⟨u₀, hu₀U, hu₀I⟩ := Set.not_subset.mp hUnotI
  refine relIndex_eq_two_of_forall ⟨u₀, hu₀U, fun h => hu₀I (Subgroup.mem_inf.mp h).2⟩ ?_
  intro u₁ hu₁U u₂ hu₂U hu₁inf hu₂inf
  have hu₁I : u₁ ∉ iSub V H E := fun h => hu₁inf (Subgroup.mem_inf.mpr ⟨hu₁U, h⟩)
  have hu₂I : u₂ ∉ iSub V H E := fun h => hu₂inf (Subgroup.mem_inf.mpr ⟨hu₂U, h⟩)
  have hu₁Q : u₁ ∉ Q := fun h => hu₁inf (hUQ ▸ Subgroup.mem_inf.mpr ⟨hu₁U, h⟩)
  have hu₂Q : u₂ ∉ Q := fun h => hu₂inf (hUQ ▸ Subgroup.mem_inf.mpr ⟨hu₂U, h⟩)
  have hu₁K : u₁ ∈ kSub V H E := le_kSub hU hu₁U
  have hu₂K : u₂ ∈ kSub V H E := le_kSub hU hu₂U
  rw [hKQV, sup_comm] at hu₁K hu₂K
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V Q hVQ] at hu₁K hu₂K
  obtain ⟨w₁, hw₁V, q₁, hq₁Q, rfl⟩ := hu₁K
  obtain ⟨w₂, hw₂V, q₂, hq₂Q, rfl⟩ := hu₂K
  have hw₁I : w₁ ∉ iSub V H E := fun h => hu₁Q (Q.mul_mem (hIQ h) hq₁Q)
  have hw₂I : w₂ ∉ iSub V H E := fun h => hu₂Q (Q.mul_mem (hIQ h) hq₂Q)
  have hw : w₁⁻¹ * w₂ ∈ V ⊓ iSub V H E :=
    inv_mul_mem_of_relIndex_eq_two hindex hw₁V hw₂V
      (fun h => hw₁I h.2) (fun h => hw₂I h.2)
  have hprodU : (w₁ * q₁)⁻¹ * (w₂ * q₂) ∈ U := U.mul_mem (U.inv_mem hu₁U) hu₂U
  have hprodQ : (w₁ * q₁)⁻¹ * (w₂ * q₂) ∈ Q := by
    rw [show (w₁ * q₁)⁻¹ * (w₂ * q₂) = q₁⁻¹ * (w₁⁻¹ * w₂) * q₂ by group]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq₁Q) (hIQ hw.2)) hq₂Q
  exact hUQ ▸ Subgroup.mem_inf.mpr ⟨hprodU, hprodQ⟩

theorem iSub_le_commutator_kSub {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hU2 : ∀ U ∈ omegaSet V H E, (U ⊓ iSub V H E).relIndex U = 2) :
    iSub V H E ≤ ⁅iSub V H E, kSub V H E⁆ := by
  refine iSup₂_le fun U hU => ?_
  have hUea : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet hV hU
  have hUTI : IsTI U := isTI_of_mem_omegaSet hU hTI
  have hOmH_U : ∀ W ∈ omegaSet U H E, W ≤ H := by
    intro W hW
    exact hOmH W (by rwa [omegaSet_eq_of_mem hU] at hW)
  have hUΩ : U ∈ omegaSet U H E := by rwa [omegaSet_eq_of_mem hU]
  have hindex_U : (U ⊓ iSub U H E).relIndex U = 2 := by
    rw [iSub_eq_of_mem hU]
    exact hU2 U hU
  have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hUea hUTI hE hEH hEnorm hOmH_U hindex_U
  have hIO : iSub V H E ≤ pCoreOf 2 H := iSup₂_le fun W _ => inf_le_right
  have hUnotO : ¬ U ≤ pCoreOf 2 H := (mem_omegaSet.mp hU).choose_spec.2.2
  have hUnotI : ¬ U ≤ iSub U H E := by
    rw [iSub_eq_of_mem hU]
    exact fun h => hUnotO (h.trans hIO)
  obtain ⟨u, huU, huI⟩ := Set.not_subset.mp hUnotI
  have hcomm := commutator_iSub_eq_inf_iSub hUea hUTI hE hEH hEnorm hOmH_U hUΩ hN huU huI
  have hzK : Subgroup.zpowers u ≤ kSub V H E :=
    Subgroup.zpowers_le.mpr (le_kSub hU huU)
  have hle : U ⊓ iSub V H E ≤ ⁅iSub V H E, kSub V H E⁆ := by
    have hUinf : U ⊓ iSub V H E = U ⊓ iSub U H E := by rw [iSub_eq_of_mem hU]
    rw [hUinf, ← hcomm, iSub_eq_of_mem hU]
    exact Subgroup.commutator_mono le_rfl hzK
  rw [← inf_iSub_eq_inf_pCoreOf hU]
  exact hle

theorem commutator_mem_iSub_of_mem_centralizer {V H E : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hVΩ : V ∈ omegaSet V H E)
    (hindex : (V ⊓ iSub V H E).relIndex V = 2)
    {v : G} (hv : v ∈ V) (hvI : v ∉ iSub V H E)
    {y w : G} (hyI : y ∈ Subgroup.normalizer (iSub V H E : Set G))
    (hw : w ∈ ⁅iSub V H E, Subgroup.zpowers v⁆) (hw1 : w ≠ 1)
    (hyw : y ∈ Subgroup.centralizer ({w} : Set G)) :
    ⁅v, y⁆ ∈ iSub V H E := by
  have hN := nVSub_eq_inf_iSub_of_relIndex_eq_two hV hTI hE hEH hEnorm hOmH hindex
  have hcomm := commutator_iSub_eq_inf_iSub hV hTI hE hEH hEnorm hOmH hVΩ hN hv hvI
  have hwVI : w ∈ V ⊓ iSub V H E := by rw [← hcomm]; exact hw
  have hwV : w ∈ V := (Subgroup.mem_inf.mp hwVI).1
  have hyN : y ∈ Subgroup.normalizer (V : Set G) :=
    centralizer_le_normalizer_of_isTI hTI hwV hw1 hyw
  let b : G := y * v * y⁻¹
  have hbV : b ∈ V := (Subgroup.mem_normalizer_iff.mp hyN v).mp hv
  have hbI : b ∉ iSub V H E := by
    intro hb
    apply hvI
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (iSub V H E : Set G) :=
      (Subgroup.normalizer (iSub V H E : Set G)).inv_mem hyI
    have h1 : y⁻¹ * b * y ∈ iSub V H E := by
      simpa using (Subgroup.mem_normalizer_iff.mp hyinv b).mp hb
    have h2 : y⁻¹ * b * y = v := by simp only [b]; group
    rwa [h2] at h1
  have ha : v⁻¹ * b ∈ V ⊓ iSub V H E :=
    inv_mul_mem_of_relIndex_eq_two hindex hv hbV (fun h => hvI h.2) (fun h => hbI h.2)
  have hb_eq : b = v * (v⁻¹ * b) := by group
  have hcommvy : ⁅v, y⁆ = v * b⁻¹ := by simp only [commutatorElement_def, b]; group
  have h3 : v * b⁻¹ = v * (v⁻¹ * b)⁻¹ * v⁻¹ := by rw [hb_eq]; group
  have h4 : v * (v⁻¹ * b)⁻¹ * v⁻¹ = (v⁻¹ * b)⁻¹ := by
    have hc : v⁻¹ * (v⁻¹ * b)⁻¹ = (v⁻¹ * b)⁻¹ * v⁻¹ :=
      hV.comm (V.inv_mem hv) (V.inv_mem ha.1)
    calc v * (v⁻¹ * b)⁻¹ * v⁻¹ = v * ((v⁻¹ * b)⁻¹ * v⁻¹) := by group
      _ = v * (v⁻¹ * (v⁻¹ * b)⁻¹) := by rw [← hc]
      _ = (v⁻¹ * b)⁻¹ := by group
  rw [hcommvy, h3, h4]
  exact (iSub V H E).inv_mem ha.2

end CFSG.LocalAnalysis.WeakClosure81
