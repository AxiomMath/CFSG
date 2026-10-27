module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section NormalizerGrowth

variable {G : Type*} [Group G] [Finite G]

private theorem exists_mem_normalizer_of_lt {H P : Subgroup G} (hP : IsPGroup 2 P) (hHP : H ≤ P)
    (hne : H ≠ P) : ∃ x ∈ P, x ∉ H ∧ x ∈ normalizer (H : Set G) := by
  set IP : Subgroup P := H.subgroupOf P with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hHP fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ IP := by rw [htop]; trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : IP < normalizer (IP : Set P) := Group.normalizerCondition_of_isNilpotent IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, fun hx => hxnot (mem_subgroupOf.mpr hx), ?_⟩
  have hxsub : x ∈ (normalizer (H : Set G)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hHP]
    exact hxN
  exact mem_subgroupOf.mp hxsub

private theorem eq_of_isPGroup_of_odd_index {T K Q : Subgroup G} {k : ℕ} (hk : Odd k)
    (hTK : Nat.card T * k = Nat.card K) (hTQ : T ≤ Q) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    Q = T := by
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : Nat.card Q ∣ Nat.card T * k := hTK ▸ card_dvd_of_le hQK
  have hcop : Nat.Coprime (Nat.card Q) k := by
    rw [hb]
    exact Nat.Coprime.pow_left b (Nat.coprime_two_left.2 hk)
  exact (eq_of_le_of_card_ge hTQ (Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd))).symm

end NormalizerGrowth

theorem exists_sylow_central_of_centralizer_sylow {X : Type*} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) (T : Subgroup X) (hTle : T ≤ centralizer ({t} : Set X)) (htT : t ∈ T)
    (hT2 : IsPGroup 2 T) {k : ℕ} (hk : Odd k)
    (hTK : Nat.card T * k = Nat.card ↥(centralizer ({t} : Set X)))
    (hZ : ∀ c ∈ T, orderOf c = 2 → (∀ s ∈ T, s * c = c * s) → c = t) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = T := by
  refine ⟨⟨T, hT2, fun {Q} hQ2 hTQ => ?_⟩, rfl⟩
  by_contra hne
  obtain ⟨n, hnQ, hnT, hnN⟩ := exists_mem_normalizer_of_lt hQ2 hTQ (Ne.symm hne)
  have hcT : n * t * n⁻¹ ∈ T := (mem_normalizer_iff.1 hnN t).1 htT
  have hc2 : orderOf (n * t * n⁻¹) = 2 := by
    rw [← ht]
    exact (MulAut.conj n).orderOf_eq t
  have hcentral : ∀ s ∈ T, s * (n * t * n⁻¹) = (n * t * n⁻¹) * s := by
    intro s hs
    have hs' : n⁻¹ * s * n ∈ T := (mem_normalizer_iff''.1 hnN s).1 hs
    have h1 : t * (n⁻¹ * s * n) = (n⁻¹ * s * n) * t :=
      mem_centralizer_singleton_iff.1 (hTle hs') |>.symm
    calc s * (n * t * n⁻¹) = n * ((n⁻¹ * s * n) * t) * n⁻¹ := by group
      _ = n * (t * (n⁻¹ * s * n)) * n⁻¹ := by rw [h1]
      _ = (n * t * n⁻¹) * s := by group
  have hnt : n * t = t * n := mul_inv_eq_iff_eq_mul.1 (hZ _ hcT hc2 hcentral)
  have hnK : n ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.2 hnt
  have hQT := eq_of_isPGroup_of_odd_index hk hTK (le_inf hTQ hTle) inf_le_right hQ2.to_inf_left
  exact hnT (hQT ▸ (⟨hnQ, hnK⟩ : n ∈ Q ⊓ centralizer ({t} : Set X)))

theorem exists_odd_card_mul_of_centralizer_sylow {G : Type*} [Group G] [Finite G] {y t : G}
    (ht : orderOf t = 2) (hty : t * y = y * t) (T : Subgroup G)
    (hTle : T ≤ centralizer ({y} : Set G) ⊓ centralizer ({t} : Set G)) (htT : t ∈ T)
    (hT2 : IsPGroup 2 T) {k : ℕ} (hk : Odd k)
    (hTK : Nat.card T * k = Nat.card ↥(centralizer ({y} : Set G) ⊓ centralizer ({t} : Set G)))
    (hZ : ∀ c ∈ T, orderOf c = 2 → (∀ s ∈ T, s * c = c * s) → c = t) :
    ∃ m : ℕ, Odd m ∧ Nat.card T * m = Nat.card ↥(centralizer ({y} : Set G)) := by
  set X : Subgroup G := centralizer ({y} : Set G)
  have htX : t ∈ X := mem_centralizer_singleton_iff.2 hty
  have hTX : T ≤ X := hTle.trans inf_le_left
  have hKX : X ⊓ centralizer ({t} : Set G) ≤ X := inf_le_left
  let t' : X := ⟨t, htX⟩
  have ht' : orderOf t' = 2 := by
    rw [← ht]
    exact (orderOf_injective X.subtype X.subtype_injective t').symm
  have hcent : centralizer ({t'} : Set X) = (X ⊓ centralizer ({t} : Set G)).subgroupOf X := by
    ext a
    exact ⟨fun h => ⟨a.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 h))⟩,
      fun h => mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 h.2))⟩
  have hcardT : Nat.card (T.subgroupOf X) = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv
  have hcardK : Nat.card ((X ⊓ centralizer ({t} : Set G)).subgroupOf X) =
      Nat.card ↥(X ⊓ centralizer ({t} : Set G)) :=
    Nat.card_congr (subgroupOfEquivOfLe hKX).toEquiv
  have hTle' : T.subgroupOf X ≤ centralizer ({t'} : Set X) := fun a ha =>
    mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 (hTle (mem_subgroupOf.1 ha)).2))
  have hTK' : Nat.card (T.subgroupOf X) * k = Nat.card ↥(centralizer ({t'} : Set X)) := by
    rw [hcent, hcardT, hcardK]
    exact hTK
  have hZ' : ∀ c ∈ T.subgroupOf X, orderOf c = 2 → (∀ s ∈ T.subgroupOf X, s * c = c * s) →
      c = t' := by
    intro c hc hc2 hcs
    have hcG : (c : G) ∈ T := mem_subgroupOf.1 hc
    have hc2' : orderOf (c : G) = 2 := by
      rw [← hc2]
      exact orderOf_injective X.subtype X.subtype_injective c
    exact Subtype.ext (hZ (c : G) hcG hc2' fun s hs =>
      congrArg Subtype.val (hcs ⟨s, hTX hs⟩ (mem_subgroupOf.2 hs)))
  obtain ⟨S, hS⟩ := exists_sylow_central_of_centralizer_sylow ht' (T.subgroupOf X) hTle'
    (mem_subgroupOf.2 htT) hT2.comap_subtype hk hTK' hZ'
  refine ⟨(T.subgroupOf X).index, ?_, ?_⟩
  · have h := S.not_dvd_index
    rw [hS] at h
    exact Nat.odd_iff.2 (by omega)
  · have h := Subgroup.card_mul_index (T.subgroupOf X)
    rwa [hcardT] at h

end CFSG.Sporadic.Recognition.LyonsSims
