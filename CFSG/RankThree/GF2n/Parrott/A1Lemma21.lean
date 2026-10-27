module

public import CFSG.RankThree.GF2n.Parrott.Section3Remarks
public import CFSG.RankThree.GF2n.Parrott.A1CentralizerOrders
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem map_centralizer_eq_of_map_zpowers_eq {x y g : G}
    (h : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) := by
  have hy : Subgroup.zpowers y = Subgroup.zpowers (g * x * g⁻¹) := by
    rw [← h, MonoidHom.map_zpowers]
    rfl
  have hC : Subgroup.centralizer ({y} : Set G) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hy,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hC]
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hv ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * v * g⁻¹ * (g * x * g⁻¹) = g * (v * x) * g⁻¹ := by group
      _ = g * (x * v) * g⁻¹ := by rw [hv]
      _ = g * x * g⁻¹ * (g * v * g⁻¹) := by group
  · intro hw
    refine ⟨g⁻¹ * w * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    calc g⁻¹ * w * g * x = g⁻¹ * (w * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * w) * g := by rw [hw]
      _ = x * (g⁻¹ * w * g) := by group

section CaseOne


set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)

theorem exists_isSylowOf_centralizer_sigma1_mul_sigma2_inv (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)}
    (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    ∃ T₂ : Subgroup G,
      IsSylowOf 2 T₂ (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ∧
      T₂ ≤ H z ∧ Nat.card T₂ = 64 ∧
      (∃ E : Subgroup G, E ≤ T₂ ∧ IsElemAbelian 2 E ∧ Nat.card E = 8) ∧
      ∀ x ∈ T₂, orderOf x = 2 → 16 ≤ Nat.card (T₂ ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQP := hrange.ge
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  obtain ⟨Q₁, Q₂, hQ, hQi, hQc, hQ₁, hQ₂, -, -⟩ :=
    exists_quaternion_pair_CJ_sigma1_mul_sigma2_inv_of hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂
      hc hne hy hyσ hu
  obtain ⟨t₀, ht₀, hct₁, hct₂⟩ := exists_lift_t_commute_of hcard φ hker hQP hσ₁ hσ₂ h3₁ h3₂ hc
  set s : ↥(H z) := σ₁ * σ₂⁻¹ with hs
  set P := CJ z (s : G) with hPdef
  have hcts : Commute s t₀ := hct₁.symm.mul_left hct₂.symm.inv_left
  have hτN : (t₀ : G) ∈ Subgroup.normalizer (P : Set G) := mem_normalizer_CJ_of_commute hcts
  have hτmap : Q₁.map (MulAut.conj (t₀ : G)).toMonoidHom = Q₂ :=
    map_conj_t_quaternion_pair_of hJ hcard hcomm hCHJ φ hker hQP hσ₁ hσ₂ h3₂ hc hne hy hyσ hu ht₀
      hQ hQi hQc hQ₁ hQ₂
  have hτJ : (t₀ : G) ∉ J z := by
    intro h
    have hk : t₀ ∈ φ.ker := by rw [hker, Subgroup.mem_subgroupOf]; exact h
    rw [MonoidHom.mem_ker, ht₀] at hk
    exact t_ne_one (congrArg Subtype.val hk)
  have hτP : (t₀ : G) ∉ P := fun h => hτJ (mem_CJ.mp h).2
  have hτ2 : (t₀ : G) * t₀ ∈ P := by
    have hk : t₀ * t₀ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, ht₀]
      apply Subtype.ext
      simp [t_sq]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    refine mem_CJ.mpr ⟨?_, hk⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((hcts.mul_right hcts).eq.symm)
  have hz2 := orderOf_z hJ hcomm
  set T₂ := P ⊔ Subgroup.zpowers (t₀ : G) with hT₂
  have h64 : Nat.card T₂ = 64 :=
    card_eq_sixtyFour hQ₁ hQ₂ hQc hz2 hQi hQ hτN hτ2 hτP rfl
  have hZ : T₂ ⊓ Subgroup.centralizer (T₂ : Set G) = Subgroup.zpowers z :=
    centralizer_inter_eq hQ₁ hQ₂ hQc hz2 hQi hQ hτN hτmap hτ2 hτP rfl
  have h16 := card_centralizer_ge_sixteen hQ₁ hQ₂ hQc hz2 hQi hQ hτN hτmap hτ2 hτP rfl
  obtain ⟨E, hEP, hE, hE8⟩ := exists_elemAbelian_eight hQ₁ hQ₂ hQc hz2 hQi hQ
  have hPC : P ≤ Subgroup.centralizer ({(s : G)} : Set G) := inf_le_left
  have hτC : (t₀ : G) ∈ Subgroup.centralizer ({(s : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcts.eq.symm)
  have hT₂C : T₂ ≤ Subgroup.centralizer ({(s : G)} : Set G) :=
    sup_le hPC (Subgroup.zpowers_le_of_mem hτC)
  have hT₂H : T₂ ≤ H z := sup_le ((inf_le_right : P ≤ J z).trans J_le_H)
    (Subgroup.zpowers_le_of_mem t₀.2)
  have hT₂p : IsPGroup 2 T₂ := IsPGroup.of_card (n := 6) (by rw [h64]; norm_num)
  have hcardHs := card_H_inf_centralizer_sigma1_mul_sigma2_inv hJ hcard hcomm hCHJ φ hker hrange
    hσ₁ hσ₂ h3₂ hc hy hyσ
  have hSylH : IsSylowOf 2 T₂ (H z ⊓ Subgroup.centralizer ({(s : G)} : Set G)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (le_inf hT₂H hT₂C) ?_
    rw [h64, hcardHs]
    have hf : (2 ^ 6 * 27 : ℕ).factorization 2 = 6 := by
      rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [hf]
    norm_num
  have hN : Subgroup.normalizer (T₂ : Set G) ⊓ Subgroup.centralizer ({(s : G)} : Set G) ≤ H z := by
    intro n hn
    have hnT := (Subgroup.mem_inf.mp hn).1
    have hzZ : z ∈ T₂ ⊓ Subgroup.centralizer (T₂ : Set G) := hZ ▸ Subgroup.mem_zpowers z
    have hnz : n * z * n⁻¹ ∈ T₂ ⊓ Subgroup.centralizer (T₂ : Set G) := by
      obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hzZ
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hnT z).mp hzT, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hzC ⊢
      intro w hw
      have hw' : n⁻¹ * w * n ∈ T₂ := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnT) w).mp hw
        simpa using this
      have h1 := hzC _ hw'
      calc w * (n * z * n⁻¹) = n * ((n⁻¹ * w * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
        _ = n * z * n⁻¹ * w := by group
    rw [hZ] at hnz
    have hnz2 : orderOf (n * z * n⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz2]
    have hnzz : n * z * n⁻¹ = z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnz
      have hk2 : z ^ k = z ^ (k % 2) := by
        rw [← zpow_mod_orderOf z k, hz2]
        norm_num
      rw [← hk, hk2] at hnz2 ⊢
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [h, zpow_zero, orderOf_one] at hnz2
        norm_num at hnz2
      · rw [h, zpow_one]
    rw [show (H z : Subgroup G) = Subgroup.centralizer ({z} : Set G) from rfl,
      Subgroup.mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hnzz]
  have hSyl : IsSylowOf 2 T₂ (Subgroup.centralizer ({(s : G)} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hSylH hN
  exact ⟨T₂, hSyl, hT₂H, h64, ⟨E, hEP.trans le_sup_left, hE, hE8⟩, h16⟩

private theorem exists_conj_le_of_isSylowOf {T K X : Subgroup G} (hT : IsSylowOf 2 T K)
    (hXK : X ≤ K) (hX : IsPGroup 2 X) : ∃ k ∈ K, ∀ x ∈ X, k⁻¹ * x * k ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  have hS : IsSylowOf 2 ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  have hXS : X ≤ (Q : Subgroup K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXK]
    exact Subgroup.map_mono hQ
  obtain ⟨k, hkK, hk⟩ := hT.exists_mem_conj hS
  exact ⟨k, hkK, fun x hx => (hk x).mp (hXS hx)⟩

theorem lemma21_not_conj (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G))
    (hy : ∃ y : ↥(H z), orderOf y = 9 ∧ y ^ 3 = σ₁) (hu : ∃ u' : ↥(H z), u' * σ₁ * u'⁻¹ = σ₂) :
    (∀ g : G, (Subgroup.zpowers (σ₁ : G)).map (MulAut.conj g).toMonoidHom ≠
      Subgroup.zpowers ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)) ∧
    (∀ g : G, (Subgroup.zpowers ((σ₁ * σ₂⁻¹ : ↥(H z)) : G)).map (MulAut.conj g).toMonoidHom ≠
      Subgroup.zpowers ((σ₁ * σ₂ : ↥(H z)) : G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy9, hyσ⟩ := hy
  obtain ⟨u, hu⟩ := hu
  obtain ⟨T₂, hSyl, -, h64, ⟨E, hET, hE, hE8⟩, h16⟩ :=
    exists_isSylowOf_centralizer_sigma1_mul_sigma2_inv hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂
      h3₂ hc hne hy9 hyσ hu
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  ·
    have hCg := map_centralizer_eq_of_map_zpowers_eq hg
    obtain ⟨T₁, hT₁le, hT₁2, hT₁64, hT₁E⟩ :=
      exists_le_H_inf_centralizer_sigma1_card_eq_sixtyFour hJ hcard hcomm hCHJ φ hker hrange.ge
        hσ₁ hc hne hy9 hyσ hu
    have hT₁'C : T₁.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
      hCg ▸ Subgroup.map_mono (hT₁le.trans inf_le_right)
    have hT₁'64 : Nat.card (T₁.map (MulAut.conj g).toMonoidHom) = 64 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hT₁64]
    have hSyl₁ : IsSylowOf 2 (T₁.map (MulAut.conj g).toMonoidHom)
        (Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) :=
      CFSG.ABGLocalTools.isSylowOf_of_card hT₁'C (by rw [hT₁'64, ← h64, hSyl.card_eq])
    obtain ⟨k, -, hk⟩ := hSyl.exists_mem_conj hSyl₁
    have hE'T₁ : E.map (MulAut.conj (g⁻¹ * k)).toMonoidHom ≤ T₁ := by
      rintro _ ⟨e, he, rfl⟩
      have hke : k * e * k⁻¹ ∈ T₁.map (MulAut.conj g).toMonoidHom := by
        rw [hk]
        simpa [mul_assoc] using hET he
      obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hke
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwe ⊢
      have : w = g⁻¹ * k * e * (g⁻¹ * k)⁻¹ := by
        rw [show g⁻¹ * k * e * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * e * k⁻¹) * g by group, ← hwe]
        group
      rw [← this]
      exact hw
    have hle := hT₁E _ hE'T₁ (hE.map _)
    rw [Subgroup.card_map_of_injective (MulAut.conj (g⁻¹ * k)).injective, hE8] at hle
    norm_num at hle
  ·
    have hCg := map_centralizer_eq_of_map_zpowers_eq hg
    have hzC : z ∈ Subgroup.centralizer ({((σ₁ * σ₂ : ↥(H z)) : G)} : Set G) :=
      zpowers_le_centralizer (σ₁ * σ₂) (Subgroup.mem_zpowers z)
    have hx₀C : g⁻¹ * z * g ∈ Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
      rw [← hCg] at hzC
      obtain ⟨c, hc', hcz⟩ := Subgroup.mem_map.mp hzC
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcz
      have : c = g⁻¹ * z * g := by rw [← hcz]; group
      rw [← this]
      exact hc'
    have hz2 := orderOf_z hJ hcomm
    have hX2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * z * g)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, show g⁻¹ * z * g = MulAut.conj g⁻¹ z by simp,
        MulEquiv.orderOf_eq, hz2, pow_one]
    obtain ⟨k, hkC, hk⟩ := exists_conj_le_of_isSylowOf hSyl (Subgroup.zpowers_le_of_mem hx₀C) hX2
    set x := k⁻¹ * (g⁻¹ * z * g) * k with hx
    have hxT : x ∈ T₂ := hk _ (Subgroup.mem_zpowers _)
    have hx2 : orderOf x = 2 := by
      rw [hx, show k⁻¹ * (g⁻¹ * z * g) * k = MulAut.conj (g * k)⁻¹ z by
        simp, MulEquiv.orderOf_eq, hz2]
    have h16x := h16 x hxT hx2
    have hW : (T₂ ⊓ Subgroup.centralizer ({x} : Set G)).map
        (MulAut.conj (g * k)).toMonoidHom ≤
          H z ⊓ Subgroup.centralizer ({((σ₁ * σ₂ : ↥(H z)) : G)} : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨hwT, hwx⟩ := Subgroup.mem_inf.mp hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hwx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [show (H z : Subgroup G) = Subgroup.centralizer ({z} : Set G) from rfl,
          Subgroup.mem_centralizer_singleton_iff]
        have hzx : z = (g * k) * x * (g * k)⁻¹ := by rw [hx]; group
        rw [hzx]
        calc g * k * w * (g * k)⁻¹ * (g * k * x * (g * k)⁻¹)
            = g * k * (w * x) * (g * k)⁻¹ := by group
          _ = g * k * (x * w) * (g * k)⁻¹ := by rw [hwx]
          _ = g * k * x * (g * k)⁻¹ * (g * k * w * (g * k)⁻¹) := by group
      · have hkw : k * w * k⁻¹ ∈
            Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
          mul_mem (mul_mem hkC (hSyl.le hwT)) (inv_mem hkC)
        rw [← hCg]
        refine Subgroup.mem_map.mpr ⟨k * w * k⁻¹, hkw, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hW2 : IsPGroup 2 ((T₂ ⊓ Subgroup.centralizer ({x} : Set G)).map
        (MulAut.conj (g * k)).toMonoidHom) :=
      (hSyl.isPGroup.to_le inf_le_left).map _
    have hW8 := card_le_of_le_H_inf_centralizer_sigma1_mul_sigma2 hJ hcard hcomm hCHJ φ hker
      hrange hσ₁ hσ₂ hc hne hy9 hyσ hu hW hW2
    rw [Subgroup.card_map_of_injective (MulAut.conj (g * k)).injective] at hW8
    omega

end CaseOne

end CFSG.RankThree.GF2n.Parrott.Remarks
