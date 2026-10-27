module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreAct
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBSylow
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQStrong
public import CFSG.Holt.TwoGroupsFocal

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem burnside_sub {H P : Subgroup G} (hP : IsSylowOf 3 P H)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {x y g : G} (hx : x ∈ P) (hy : y ∈ P) (hg : g ∈ H)
    (hgxy : g * x * g⁻¹ = y) : ∃ n ∈ H, n ∈ Nor P ∧ n * x * n⁻¹ = y := by
  have hPH := hP.1
  have hP' : IsSylowOf 3 (P.subgroupOf H) (⊤ : Subgroup ↥H) := by
    refine ⟨le_top, hP.2.1.comap_of_injective H.subtype (Subgroup.subtype_injective H), ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hP.2.2
  have hPc' : ∀ x ∈ P.subgroupOf H, ∀ y ∈ P.subgroupOf H, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hPc x hx y hy)
  obtain ⟨n, hn, hnxy⟩ := fusion (P.subgroupOf H) hP' hPc' (x := ⟨x, hPH hx⟩) (y := ⟨y, hPH hy⟩)
    (hx : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H) (hy : (⟨y, hPH hy⟩ : ↥H) ∈ P.subgroupOf H)
    (g := ⟨g, hg⟩) (Subtype.ext hgxy)
  refine ⟨n, n.2, ?_, congrArg Subtype.val hnxy⟩
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro z
  constructor
  · intro hz
    exact (hn ⟨z, hPH hz⟩).1 hz
  · intro hz
    have hzD : z ∈ H := by
      have h1 : (n : G) * z * (n : G)⁻¹ ∈ H := hPH hz
      have : z = (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * n := by group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem n.2) h1) n.2
    exact (hn ⟨z, hzD⟩).2 hz

theorem b₁_sq (h : FF84Sec4 b L B K b₁ b₂) : b₁ ^ 2 = b₁⁻¹ := by
  have h3 := pow3_of_mem h (mem_b₁ h)
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]; exact h3

theorem bb₁sq_mem (h : FF84Sec4 b L B K b₁ b₂) : b * b₁ ^ 2 ∈ B :=
  mul_mem (mem_b h) (pow_mem (mem_b₁ h) 2)

theorem bb₁sq_ne_one (h : FF84Sec4 b L B K b₁ b₂) : b * b₁ ^ 2 ≠ 1 := by
  rw [b₁_sq h]; exact bb₁inv_ne_one h

theorem bb₁sq_cube (h : FF84Sec4 b L B K b₁ b₂) : (b * b₁ ^ 2) ^ 3 = 1 := by
  have hc : Commute b (b₁ ^ 2) := (comm_of_mem h (mem_b h) (mem_b₁ h)).pow_right 2
  rw [hc.mul_pow, ← pow_mul, mul_comm 2 3, pow_mul, pow3_of_mem h (mem_b₁ h), one_pow,
    pow3_of_mem h (mem_b h), one_mul]

theorem relIndex_U (h : FF84Sec4 b L B K b₁ b₂) :
    (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)).relIndex B = 3 := by
  set U := Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) with hU
  have hUB : U ≤ B := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact bb₁sq_mem h
    · rw [Set.mem_singleton_iff.1 hz]; exact mem_b₂ h)
  have hxU : b * b₁ ^ 2 ∈ U := Subgroup.subset_closure (by simp)
  have hyU : b₂ ∈ U := Subgroup.subset_closure (by simp)
  have hc27 : Nat.card B = 3 ^ 3 := card_B h
  have hd : Nat.card U ∣ 3 ^ 3 := hc27 ▸ Subgroup.card_dvd_of_le hUB
  obtain ⟨k, hk, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hk2 : k = 2 := by
    interval_cases k
    · exfalso
      have : U = ⊥ := Subgroup.card_eq_one.1 (by simpa using hkU)
      rw [this, Subgroup.mem_bot] at hxU
      exact bb₁sq_ne_one h hxU
    · exfalso
      have hord : orderOf (b * b₁ ^ 2) = 3 :=
        orderOf_eq_prime (bb₁sq_cube h) (bb₁sq_ne_one h)
      have hle : Subgroup.zpowers (b * b₁ ^ 2) ≤ U := Subgroup.zpowers_le.2 hxU
      have hcz : Nat.card (Subgroup.zpowers (b * b₁ ^ 2)) = 3 := by
        rw [Nat.card_zpowers, hord]
      have heq : Subgroup.zpowers (b * b₁ ^ 2) = U :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hkU]; norm_num)
      have hxE : b * b₁ ^ 2 ∈ Subgroup.closure ({b, b₁} : Set G) :=
        mul_mem (Subgroup.subset_closure (by simp)) (pow_mem (Subgroup.subset_closure (by simp)) 2)
      rw [← heq] at hyU
      exact b₂_notin_E h (Subgroup.zpowers_le.2 hxE hyU)
    · rfl
    · exfalso
      have heq : U = B := Subgroup.eq_of_le_of_card_ge hUB (by rw [hkU, hc27])
      exact not_B_le_pair h (bb₁sq_mem h) (mem_b₂ h) (by rw [← hU, heq])
  have h1 := Subgroup.card_mul_index (U.subgroupOf B)
  have h2 : Nat.card (U.subgroupOf B) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  rw [h2, hkU, hk2, hc27] at h1
  show (U.subgroupOf B).index = 3
  omega

theorem S41_D0 (h : FF84Sec4 b L B K b₁ b₂) :
    ∃ D₀ : Subgroup G, D₀ ≤ Cen (b * b₁) ∧ (D₀.subgroupOf (Cen (b * b₁))).Normal ∧
      D₀.relIndex (Cen (b * b₁)) = 3 ∧ ⁅Cen (b * b₁), Cen (b * b₁)⁆ ≤ D₀ ∧
      IsSylowOf 3 (Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G)) D₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Cen (b * b₁) with hDdef
  set U := Subgroup.closure ({b * b₁ ^ 2, b₂} : Set G) with hU
  have hS : IsSylowOf 3 B D := S41_B_sylow h
  have hfus : CFSG.Open.fusionIsSylowIn 3 B D :=
    ⟨hS.1, hS.2.1, fun P hPD hP hBP => le_antisymm (le_of_isSylowOf hS hPD hP hBP) hBP⟩
  have hUB : U ≤ B := (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact bb₁sq_mem h
    · rw [Set.mem_singleton_iff.1 hz]; exact mem_b₂ h)
  have hUc : U = Subgroup.closure ({b * b₁⁻¹, b₂} : Set G) := by rw [hU, b₁_sq h]
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => (comm_of_mem h hx hy).eq
  have hfoc : ∀ x ∈ B, ∀ g ∈ D, g * x * g⁻¹ ∈ B → x⁻¹ * (g * x * g⁻¹) ∈ U := by
    intro x hx g hg hgx
    obtain ⟨n, hnD, hnN, hn⟩ := burnside_sub hS hBc hx hgx hg rfl
    rw [← hn, hUc]
    exact focal_core h hnD hnN hx
  obtain ⟨N, hND, hNn, hp, hidx, hinf⟩ := Holt.exists_normal_inf_eq_of_focal' hfus hUB hfoc
  have h3 : N.relIndex D = 3 := by rw [hidx]; exact relIndex_U h
  refine ⟨N, hND, hNn, h3, ?_, ?_⟩
  ·
    have hcard : Nat.card (↥D ⧸ N.subgroupOf D) = 3 := h3
    haveI : Fact (Nat.card (↥D ⧸ N.subgroupOf D)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
    haveI : IsCyclic (↥D ⧸ N.subgroupOf D) := isCyclic_of_prime_card hcard
    have hcomm : ∀ q q' : ↥D ⧸ N.subgroupOf D, q * q' = q' * q := fun q q' =>
      (IsCyclic.commGroup (α := ↥D ⧸ N.subgroupOf D)).mul_comm q q'
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    have h1 : (QuotientGroup.mk' (N.subgroupOf D)) ⁅(⟨g, hg⟩ : ↥D), ⟨g', hg'⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
    have h2 : ⁅(⟨g, hg⟩ : ↥D), ⟨g', hg'⟩⁆ ∈ N.subgroupOf D := by
      exact (QuotientGroup.eq_one_iff _).1 h1
    exact h2
  · have hUN : U ≤ N := by
      rw [← hinf]; exact inf_le_left
    refine ⟨hUN, hS.2.1.of_injective (Subgroup.inclusion hUB) (Subgroup.inclusion_injective hUB), ?_⟩
    have e1 := Subgroup.relIndex_mul_relIndex U N D hUN hND
    have e2 := Subgroup.relIndex_mul_relIndex U B D hUB hS.1
    rw [h3] at e1
    rw [relIndex_U h] at e2
    have : U.relIndex N = B.relIndex D := by omega
    rw [this]
    exact hS.2.2

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
