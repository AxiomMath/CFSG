module

public import CFSG.Quasithin.Recognition.J2RecDefs
public import CFSG.Quasithin.Recognition.J2RecQ8D8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

theorem z_mem_centralizer (z : G) : z ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.mp hg]

theorem orderOf_eq (h : IsTypeH2 G z) : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h.sq h.ne_one

theorem z_mem_pCoreOf (h : IsTypeH2 G z) :
    z ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, h.orderOf_eq, pow_one]
  have hle : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.2 (z_mem_centralizer z)
  have hn : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro g hg
    have hgc : Commute g z := (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hcz : ∀ k : ℤ, g * z ^ k * g⁻¹ = z ^ k := fun k => by
      rw [(hgc.zpow_right k).eq, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [hcz k]
      exact hn
    · intro hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
      have : n = z ^ k := by
        calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
          _ = g⁻¹ * z ^ k * g := by rw [← hk]
          _ = g⁻¹ * (g * z ^ k * g⁻¹) * g := by rw [hcz k]
          _ = z ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  exact le_pCoreOf_of_le_normalizer 2 hle hn hz2 (Subgroup.mem_zpowers z)

theorem card_pCoreOf (h : IsTypeH2 G z) :
    Nat.card (pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) = 32 := h.q8d8.1

theorem card_centralizer (h : IsTypeH2 G z) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = 1920 := by
  set H := Subgroup.centralizer ({z} : Set G) with hH
  obtain ⟨e⟩ := h.quot
  have h60 : Nat.card (OTwoQuot H) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hQ : Nat.card (CFSG.Open.pCore 2 ↥H) = 32 := by
    have := h.card_pCoreOf
    unfold pCoreOf at this
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at this
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
  rw [h60, hQ] at this
  have h2 : Nat.card ↥H = Nat.card (Subgroup.centralizer ({z} : Set G)) := rfl
  omega

theorem eq_one_or_eq_of_mem_center (h : IsTypeH2 G z) {y : G}
    (hy : y ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
    (hc : ∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), y * q = q * y) :
    y = 1 ∨ y = z := by
  set Q := pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) with hQ
  have : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ, h.card_pCoreOf]; norm_num)
  obtain ⟨φ, -, -, -, hcenter⟩ := h.q8d8.exists_hom
  have hzQ : z ∈ Q := h.z_mem_pCoreOf
  have hzc : (⟨z, hzQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (pCoreOf_le 2 _ g.2)
  have hyc : (⟨y, hy⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g.1 g.2).symm
  rcases hcenter _ hyc with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · rcases hcenter _ hzc with h2 | h2
    · exact absurd (congrArg Subtype.val h2) h.ne_one
    · exact Or.inr (congrArg Subtype.val (h1.trans h2.symm))

variable [Finite G]

theorem pCoreOf_le_sylow {S : Subgroup G}
    (hS : IsSylowTwoOf S (Subgroup.centralizer ({z} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≤ S :=
  A4.le_of_normal_of_isSylowTwoOf hS (pCoreOf_le 2 _)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
      (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem eq_one_or_eq_of_mem_center_sylow (h : IsTypeH2 G z) {S : Subgroup G}
    (hS : IsSylowTwoOf S (Subgroup.centralizer ({z} : Set G))) {y : G} (hy : y ∈ S)
    (hc : ∀ s ∈ S, y * s = s * y) : y = 1 ∨ y = z := by
  have hQS := pCoreOf_le_sylow hS
  have hyH : y ∈ Subgroup.centralizer ({z} : Set G) := hS.1 hy
  have hyC : y ∈ Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun q hq => (hc q (hQS hq)).symm
  have hCT : Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := h.charTwo
  exact h.eq_one_or_eq_of_mem_center (hCT ⟨hyH, hyC⟩) fun q hq => hc q (hQS hq)

private theorem eq_of_inf_normalizer_le_aux {P S : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ≤ P)
    (hN : P ⊓ Subgroup.normalizer (S : Set G) ≤ S) : S = P := by
  by_contra hne
  have hIPlt : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm hSP fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt : S.subgroupOf P < Subgroup.normalizer ((S.subgroupOf P : Subgroup P) : Set P) :=
    hnc _ hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxnot (Subgroup.mem_subgroupOf.mpr (hN ⟨x.2, hxNorm⟩))

theorem isSylowTwoOf_top (h : IsTypeH2 G z) {S : Subgroup G}
    (hS : IsSylowTwoOf S (Subgroup.centralizer ({z} : Set G))) : IsSylowTwoOf S ⊤ := by
  have hS' := hS
  rw [A4.isSylowTwoOf_iff_maximal] at hS ⊢
  obtain ⟨hSH, hS2, hmax⟩ := hS
  refine ⟨le_top, hS2, fun P _ hP hSP => ?_⟩
  by_contra hPS
  have hne : ¬ P ⊓ Subgroup.normalizer (S : Set G) ≤ S := fun hle =>
    hPS (le_of_eq (eq_of_inf_normalizer_le_aux hP hSP hle).symm)
  obtain ⟨n, ⟨hnP, hnN⟩, hnS⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hzS : z ∈ S := pCoreOf_le_sylow hS' h.z_mem_pCoreOf
  have hnz : n * z * n⁻¹ = z := by
    have h1 : n * z * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hnN z).mp hzS
    have hc : ∀ s ∈ S, (n * z * n⁻¹) * s = s * (n * z * n⁻¹) := by
      intro s hs
      have ht : n⁻¹ * s * n ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) s).mp hs
        simpa using this
      have hzt : (n⁻¹ * s * n) * z = z * (n⁻¹ * s * n) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hS'.1 ht)
      calc n * z * n⁻¹ * s = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by rw [hzt]
        _ = s * (n * z * n⁻¹) := by group
    rcases h.eq_one_or_eq_of_mem_center_sylow hS' h1 fun s hs => hc s hs with h2 | h2
    · exfalso
      apply h.ne_one
      have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
      rw [this, h2]
      group
    · exact h2
  have hnH : n ∈ Subgroup.centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hnz]
  have hle : P ⊓ Subgroup.centralizer ({z} : Set G) ≤ S :=
    hmax (P ⊓ Subgroup.centralizer ({z} : Set G)) inf_le_right (hP.to_le inf_le_left)
      (le_inf hSP hSH)
  exact hnS (hle ⟨hnP, hnH⟩)

end IsTypeH2

end CFSG.Quasithin
