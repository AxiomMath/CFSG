module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup CFSG.RankThree.PartOne

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem relIndex_relPPrimeCore_eq {H V : Subgroup G} (hVH : V ≤ H) :
    (CFSG.Open.relPPrimeCore 3 H).relIndex V =
      (CFSG.pPrimeCore 3 ↥H).relIndex (V.subgroupOf H) := by
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    Nat.prime_three H]
  conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hVH]
  exact Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective

theorem isElemAbelian_subgroupOf {A H : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.subgroupOf H) :=
  ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (comm_of_isElemAbelian hA x.2 y.2))⟩⟩,
    fun x hx => Subtype.ext (by simpa using hA.2 (x : G) hx)⟩

theorem card_subgroupOf_of_le {A H : Subgroup G} (h : A ≤ H) :
    Nat.card (A.subgroupOf H) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem subgroupOf_inf_le_normalizer {H M A : Subgroup G} (h : M ≤ normalizer (A : Set G)) :
    (H ⊓ M).subgroupOf H ≤ normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  intro m hm
  have hmM : (m : G) ∈ M := (Subgroup.mem_inf.1 hm).2
  have hn := Subgroup.mem_normalizer_iff.1 (h hmM)
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  exact hn (x : G)

theorem pCore_le_subgroupOf {H M S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S H)
    (hSM : S ≤ M) : CFSG.pCore 2 ↥H ≤ (H ⊓ M).subgroupOf H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have h1 : CFSG.pCore 2 ↥H ≤ (Q : Subgroup ↥H) :=
    IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup) Q
  rw [hQ] at h1
  refine h1.trans ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2
    (Subgroup.mem_inf.2 ⟨x.2, hSM (Subgroup.mem_subgroupOf.1 hx)⟩)

theorem not_le_sup_subgroupOf {H V₀ V : Subgroup G} (hV₀ : V₀ ≤ H) (hV : V ≤ H)
    (h : ¬ V ≤ V₀ ⊔ CFSG.Open.relPPrimeCore 3 H) :
    ¬ V.subgroupOf H ≤ V₀.subgroupOf H ⊔ CFSG.pPrimeCore 3 ↥H := by
  intro hle
  apply h
  have h1 := Subgroup.map_mono (f := H.subtype) hle
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hV, Subgroup.map_subgroupOf_eq_of_le hV₀,
    ← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H] at h1
  exact h1

theorem not_sup_subgroupOf {H H₀ : Subgroup G} (hH₀ : H₀ ≤ H)
    (h : ¬ H ≤ H₀ ⊔ CFSG.Open.relPPrimeCore 3 H) :
    ¬ ⊤ ≤ H₀.subgroupOf H ⊔ CFSG.pPrimeCore 3 ↥H := by
  intro hle
  apply h
  have h1 := Subgroup.map_mono (f := H.subtype) hle
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hH₀, Subgroup.map_top,
    Subgroup.range_subtype,
    ← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H] at h1
  exact h1

theorem centralizer_ne_top {z : G} (hz2 : orderOf z = 2) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hzc : z ∈ Subgroup.center G := by
    have : ({z} : Set G) ⊆ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.1 htop
    exact this (Set.mem_singleton z)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz2
    omega
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem centralizer_singleton_eq_normalizer_zpowers {z : G} (hz2 : orderOf z = 2) :
    centralizer ({z} : Set G) = normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  apply le_antisymm
  · have h0 : centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
        centralizer ({z} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro n hn
    exact Subgroup.centralizer_le_normalizer _ (by rw [h0]; exact hn)
  · intro n hn
    have h1 : n * z * n⁻¹ ∈ Subgroup.zpowers z :=
      (Subgroup.mem_normalizer_iff.1 hn z).1 (Subgroup.mem_zpowers z)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hk2 : z ^ k = z ^ (k % 2) := by
      have := (zpow_mod_orderOf z k).symm
      rw [hz2] at this
      simpa using this
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exfalso
      rw [h, zpow_zero] at hk2
      rw [hk2] at hk
      apply hz1
      have : n * z * n⁻¹ = 1 := hk.symm
      simpa using this
    · rw [h, zpow_one] at hk2
      rw [hk2] at hk
      have h3 := hk.symm
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3

theorem centralizer_pCore_le (hC : CFSG.Open.IsCharTwoType G) {z : G} (hz2 : orderOf z = 2) :
    centralizer ((CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :
      Subgroup ↥(centralizer ({z} : Set G))) : Set ↥(centralizer ({z} : Set G))) ≤
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hloc : IsTwoLocal (centralizer ({z} : Set G)) := by
    refine ⟨Subgroup.zpowers z, ?_, ?_, centralizer_singleton_eq_normalizer_zpowers hz2⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      exact hz1
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hz2, pow_one]
  have h := hC _ hloc
  intro x hx
  have hx' : (x : G) ∈ centralizer ({z} : Set G) ⊓
      centralizer ((CFSG.Open.pCoreOf 2 (centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx y hy
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := h hx'
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem isKGroup_centralizer (hK : CFSG.Open.IsKProper G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz2 : orderOf z = 2) :
    CFSG.Open.IsKGroup ↥(centralizer ({z} : Set G)) :=
  hK.isKGroup _ (centralizer_ne_top hz2 hs hnab)

theorem loc67_of_amb (hK : CFSG.Open.IsKProper G) (hC : CFSG.Open.IsCharTwoType G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {V₀ V M S : Subgroup G} {z c : G} (hz2 : orderOf z = 2) (hV : IsElemAbelian 2 V)
    (hzV : z ∈ V) (hV₀V : V₀ ≤ V) (hcard : Nat.card V = 16 * Nat.card V₀)
    (hcard₀ : Nat.card V₀ ≤ 4) (hMV : normalizer (V : Set G) = M)
    (hMV₀ : M ≤ normalizer (V₀ : Set G))
    (hrank : CFSG.Open.pRank 3 (centralizer ({z} : Set G)) ≤ 1)
    (hse : IsStronglyPEmbedded 3
      ((centralizer ({z} : Set G) ⊓ M).subgroupOf (centralizer ({z} : Set G))))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))) (hSM : S ≤ M)
    (hnsup : ¬ centralizer ({z} : Set G) ≤
      centralizer ({z} : Set G) ⊓ M ⊔ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)))
    (hVK : ¬ V ≤ V₀ ⊔ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)))
    (hcH : c ∈ centralizer ({z} : Set G)) (hcM : c ∈ M) (hc3 : orderOf c = 3)
    (hcV : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀) :
    Loc67 ↥(centralizer ({z} : Set G)) (V₀.subgroupOf (centralizer ({z} : Set G)))
      (V.subgroupOf (centralizer ({z} : Set G)))
      ((centralizer ({z} : Set G) ⊓ M).subgroupOf (centralizer ({z} : Set G))) := by
  have hVH : V ≤ centralizer ({z} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_of_isElemAbelian hV hv hzV)
  have hV₀H : V₀ ≤ centralizer ({z} : Set G) := hV₀V.trans hVH
  exact
    { elemAbelian := isElemAbelian_subgroupOf hV
      le := fun x hx => hV₀V hx
      card_eq := by
        rw [card_subgroupOf_of_le hVH, card_subgroupOf_of_le hV₀H]
        exact hcard
      card₀_le := by
        rw [card_subgroupOf_of_le hV₀H]
        exact hcard₀
      le_normalizer := subgroupOf_inf_le_normalizer hMV.ge
      le_normalizer₀ := subgroupOf_inf_le_normalizer hMV₀
      pCore_le := pCore_le_subgroupOf hSyl hSM
      strong := hse
      rank := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) _).symm.trans_le hrank
      not_le_sup := not_le_sup_subgroupOf hV₀H hVH hVK
      not_sup := not_sup_subgroupOf inf_le_left hnsup
      charTwo := centralizer_pCore_le hC hz2
      kGroup := isKGroup_centralizer hK hs hnab hz2
      exists_c := ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hcH, hcM⟩),
        by rw [← Subgroup.orderOf_coe]; exact hc3, fun v hv => hcV (v : G) hv⟩ }

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
