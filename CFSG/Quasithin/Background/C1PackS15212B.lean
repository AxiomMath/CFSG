module

public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.EmptyFaithful.S152Y22
public import CFSG.Quasithin.Background.C1PackS15348

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152N

namespace W3

noncomputable local instance instFintype' : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEq' : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0' : DecidablePred (· ∈ N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

theorem pow_three_of_mem_N0 : ∀ w : W3, w ∈ N0 → w ^ 3 = 1 := by
  decide +kernel

theorem mem_N0_of_pow_nine : ∀ w : W3, w ^ 9 = 1 → w ∈ N0 := by
  decide +kernel

theorem oTwoUpper_top : oTwoUpper (⊤ : Subgroup W3) = N0 := by
  apply le_antisymm
  · refine (Subgroup.closure_le N0).mpr fun w hw => ?_
    have hodd : Odd (orderOf w) := hw.2
    have hdvd : orderOf w ∣ 72 := card_eq ▸ orderOf_dvd_natCard w
    have hcop : Nat.Coprime (orderOf w) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
    have h9 : orderOf w ∣ 9 :=
      hcop.dvd_of_dvd_mul_left (by simpa using hdvd : orderOf w ∣ 2 ^ 3 * 9)
    exact mem_N0_of_pow_nine w (orderOf_dvd_iff_pow_eq_one.mp h9)
  · intro n hn
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top n) ?_
    exact Odd.of_dvd_nat (by decide : Odd 3)
      (orderOf_dvd_of_pow_eq_one (pow_three_of_mem_N0 n hn))

end W3

end S152N

section Xi

variable {G : Type} [Group G] [Finite G] {T Mc M H B : Subgroup G}

namespace C1Pack12

theorem map_imageOTwoQuot_oTwoUpper (φ : OTwoQuot H ≃* S152N.W3) :
    (imageOTwoQuot H (oTwoUpper H)).map (φ : OTwoQuot H →* S152N.W3) = S152N.W3.N0 := by
  have h1 : imageOTwoQuot H H = ⊤ := by
    unfold imageOTwoQuot
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [S152Y.imageOTwoQuot_oTwoUpper (le_refl H), h1, ← oTwoUpper_map,
    Subgroup.map_top_of_surjective _ φ.surjective]
  exact S152N.W3.oTwoUpper_top

theorem pow_three_mem_pCoreOf (φ : OTwoQuot H ≃* S152N.W3) {x : G} (hx : x ∈ oTwoUpper H) :
    x ^ 3 ∈ pCoreOf 2 H := by
  have hxH : x ∈ H := oTwoUpper_le H hx
  have hmem : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot H) ∈ imageOTwoQuot H (oTwoUpper H) :=
    mem_imageOTwoQuot_iff.mpr ⟨x, hxH, hx, rfl⟩
  have h1 : φ (QuotientGroup.mk ⟨x, hxH⟩) ∈ S152N.W3.N0 := by
    rw [← map_imageOTwoQuot_oTwoUpper φ]
    exact Subgroup.mem_map_of_mem _ hmem
  have h2 : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot H) ^ 3 = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    exact S152N.W3.pow_three_of_mem_N0 _ h1
  have h3 : (QuotientGroup.mk (⟨x, hxH⟩ ^ 3 : ↥H) : OTwoQuot H) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact h2
  exact (mk_eq_one_iff_mem_pCoreOf (⟨x, hxH⟩ ^ 3 : ↥H)).mp h3

omit [Finite G] in
theorem relIndex_inf_pCoreOf_eq_card {H X : Subgroup G} (hXH : X ≤ H) :
    (X ⊓ pCoreOf 2 H).relIndex X = Nat.card ↥(imageOTwoQuot H X) := by
  let f : ↥X →* OTwoQuot H :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)).comp (Subgroup.inclusion hXH)
  have hker : f.ker = (X ⊓ pCoreOf 2 H).subgroupOf X := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h' : (QuotientGroup.mk (⟨(x : G), hXH x.2⟩ : ↥H) : OTwoQuot H) = 1 := h
      exact ⟨x.2, (mk_eq_one_iff_mem_pCoreOf (⟨(x : G), hXH x.2⟩ : ↥H)).mp h'⟩
    · intro h
      have h' : (⟨(x : G), hXH x.2⟩ : ↥H).1 ∈ pCoreOf 2 H := h.2
      exact (mk_eq_one_iff_mem_pCoreOf (⟨(x : G), hXH x.2⟩ : ↥H)).mpr h'
  have hrange : f.range = imageOTwoQuot H X := by
    ext u
    simp only [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_imageOTwoQuot_iff.mpr ⟨x, hXH x.2, x.2, rfl⟩
    · intro hu
      obtain ⟨x, hxH, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
      exact ⟨⟨x, hxX⟩, rfl⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]

theorem relIndex_pCoreOf_oTwoUpper (φ : OTwoQuot H ≃* S152N.W3) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hcard : Nat.card ↥(imageOTwoQuot H (oTwoUpper H)) = 9 := by
    have h1 := congrArg (fun X : Subgroup S152N.W3 => Nat.card X)
      (map_imageOTwoQuot_oTwoUpper (H := H) φ)
    simp only [S152N.W3.card_N0] at h1
    rw [← h1]
    exact (Subgroup.card_map_of_injective φ.injective).symm
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H),
    relIndex_inf_pCoreOf_eq_card hKH, hcard]

omit [Finite G] in
theorem eq_one_of_pow_two_pow_of_pow_three' {A : Type*} [Group A] {z : A} {k : ℕ}
    (h2 : z ^ 2 ^ k = 1) (h3 : z ^ 3 = 1) : z = 1 := by
  have h : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hc : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  rw [hc] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

namespace St12

variable (s : St12 T Mc M H B)

include s

theorem inf_le_pCoreOf (φ : OTwoQuot H ≃* S152N.W3) {y : G} (hyK : y ∈ oTwoUpper H) (hyT : y ∈ T) :
    y ∈ pCoreOf 2 H := by
  have hyH : y ∈ H := oTwoUpper_le H hyK
  obtain ⟨k, hk⟩ := s.sylow.2.1 ⟨y, hyT⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : (QuotientGroup.mk ⟨y, hyH⟩ : OTwoQuot H) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨y, hyH⟩ ^ 2 ^ k : ↥H) = 1 := Subtype.ext (by simpa using hk')
    rw [this]
    exact QuotientGroup.mk_one _
  have h3 : (QuotientGroup.mk ⟨y, hyH⟩ : OTwoQuot H) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff_mem_pCoreOf (⟨y, hyH⟩ ^ 3 : ↥H)).mpr (pow_three_mem_pCoreOf φ hyK)
  exact (mk_eq_one_iff_mem_pCoreOf ⟨y, hyH⟩).mp (eq_one_of_pow_two_pow_of_pow_three' h2 h3)

theorem xi : IsXi T (oTwoUpper H) := by
  obtain ⟨φ⟩ := s.iso
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H)
  refine ⟨(C1Pack153.oTwoUpper_idem' H).symm, s.T_le_H.trans (le_normalizer_oTwoUpper H), ?_, 3,
    Nat.prime_three, by norm_num, ?_, Or.inl ?_, ?_⟩
  · rw [s.sup_eq]
    exact s.hH.1.2
  · intro x hx
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx 3, pow_three_mem_pCoreOf φ hx⟩
  · rw [relIndex_pCoreOf_oTwoUpper φ]; norm_num
  · intro Y hY1 hY2 hYT
    have hO2K : pCoreOf 2 (oTwoUpper H) ≤ Y := le_sup_right.trans hY1
    have hYH : Y ≤ H := hY2.trans hKH
    rcases S152N.eq_or_eq_of_le s.sylow φ (le_sup_right : T ≤ Y ⊔ T)
      (sup_le hYH s.T_le_H) with hN | hN
    ·
      left
      refine le_antisymm (fun y hy => ?_) hY1
      have hyT : y ∈ T := hN ▸ (le_sup_left : Y ≤ Y ⊔ T) hy
      have hyQ : y ∈ pCoreOf 2 H := s.inf_le_pCoreOf φ (hY2 hy) hyT
      exact Subgroup.mem_sup_right (hpK ▸ (⟨hY2 hy, hyQ⟩ : y ∈ oTwoUpper H ⊓ pCoreOf 2 H))
    ·
      right
      refine le_antisymm hY2 (fun k hk => ?_)
      have hkH : k ∈ ((Y ⊔ T : Subgroup G) : Set G) := by
        rw [hN]
        exact hKH hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Y T hYT] at hkH
      obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hkH
      have htK : t ∈ oTwoUpper H :=
        (oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem (hY2 hy)) hk |> fun h => by
          simpa using h
      have htQ : t ∈ pCoreOf 2 H := s.inf_le_pCoreOf φ htK ht
      have htO : t ∈ pCoreOf 2 (oTwoUpper H) := hpK ▸ (⟨htK, htQ⟩ : t ∈ oTwoUpper H ⊓ pCoreOf 2 H)
      exact Y.mul_mem hy (hO2K htO)

end St12

end C1Pack12

end Xi

end CFSG.Quasithin
