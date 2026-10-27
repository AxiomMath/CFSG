module

public import CFSG.Quasithin.H13.NQCatLieCartanTools
public import CFSG.Quasithin.H13.NQCatLieMultG24
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan.G2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

variable {K : Type} [Field K]

theorem torusElt_conj_gX
    (i : Fin Tag.G2.rank) (u : Kˣ) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) (c : K) :
    torusElt Tag.G2 K i u * pinnedX Tag.G2 K γ c * (torusElt Tag.G2 K i u)⁻¹ =
      pinnedX Tag.G2 K γ (((u ^ (∑ j, Tag.G2.cartan i j * γ j) : Kˣ) : K) * c) := by
  rw [torusElt_eq_rootDiagUnit, rootDiagUnit_conj_pinnedX _ hγ]
  congr 3
  simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, ← zpow_mul]
  exact prod_zpow_eq_zpow_sum _ _ _

theorem normalizer_posUnipotent_inf_eq
    {τ : Tag} :
    Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) ⊓ adjointGroup τ K =
      borelGroup τ K := by
  obtain ⟨-, -, -, -, -, -, -, -, hnormal, -, -, hBC⟩ := triangular_borel_structure.{0, 0} τ K
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hnormal
  refine le_antisymm ?_ (le_inf hBN (hBC K).1)
  have hUA : posUnipotent τ K ≤
      Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) ⊓ adjointGroup τ K :=
    le_inf Subgroup.le_normalizer posUnipotent_le_adjointGroup
  have hle := (chevalley_positive_root_overgroup_parabolic_containment inf_le_right hUA).1
  have hJ : {k | weylElt τ K k 1 ∈
      Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) ⊓ adjointGroup τ K} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    have hy : yUnit τ K k (-1) ∈ posUnipotent τ K := by
      rw [yUnit_eq_weylElt_mul, neg_neg]
      exact (Subgroup.mem_normalizer_iff.mp hk.1 _).mp (xUnit_mem_posUnipotent k 1)
    have hn : weylElt τ K k 1 ∈ parabolicSubgroup τ K ∅ := by
      rw [parabolicSubgroup_empty, weylElt_one_eq]
      exact hUB (mul_mem (mul_mem (xUnit_mem_posUnipotent k 1) hy) (xUnit_mem_posUnipotent k 1))
    exact weylElt_mem_parabolicSubgroup_iff.mp hn
  rw [hJ, parabolicSubgroup_empty] at hle
  exact hle

theorem torusConcl_g2
    [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    TorusConcl ↥(adjointGroup Tag.G2 K) False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨hcomm, -, -, -, -, -, -, -, -, -, -, hBC⟩ := triangular_borel_structure.{0, 0} Tag.G2 K
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hHC : torusGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_left.trans (hBC K).1
  have hU : IsSylowTwoOf (posUnipotent Tag.G2 K) (adjointGroup Tag.G2 K) :=
    isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1
  refine torusConcl_of_le hUC hHC hU torusGroup_le_normalizer_posUnipotent ?_ ?_ hcomm ?_
  · rw [inf_comm, normalizer_posUnipotent_inf_eq, borelGroup, sup_comm]
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, hK]
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    exact (Nat.odd_iff.2 (by omega)).pow
  intro E hEU hE hE16 hEC
  have hFacts := G2.parabolicFacts_one hK hf
  have hUP := posUnipotent_le_parabolicSubgroup (τ := Tag.G2) (K := K) {i1}
  have hQU := parabolicRadical_le_posUnipotent (τ := Tag.G2) (K := K) {i1}
  have hc : ∀ x : E, ∃ t : K, (x : ModGL Tag.G2 K) = gX rC t := by
    intro x
    have hxC : (x : ModGL Tag.G2 K) ∈
        Subgroup.centralizer (parabolicRadical Tag.G2 K {i1} : Set (ModGL Tag.G2 K)) :=
      Subgroup.centralizer_le hQU (hEC x.2)
    exact LieMult.eq_gX_rC_of_mem_center_one ⟨hFacts.selfCentralizing ⟨hUP (hEU x.2), hxC⟩, hxC⟩
  choose β hβ using hc
  have hβinj : Function.Injective β := fun x y hxy => Subtype.ext (by rw [hβ x, hβ y, hxy])
  have h16 : 16 ≤ Nat.card K := by
    rw [← hE16]
    exact Nat.card_le_card_of_injective β hβinj
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE16]; norm_num)
    exact exists_ne 1
  have ht₀ : β x₀ ≠ 0 := by
    intro h0
    apply hx₀
    apply Subtype.ext
    rw [hβ x₀, h0, gX_zero, Subgroup.coe_one]
  have hrC : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1
  have hrR : IsRoot Tag.G2 rR := (isRoot_pos_iff.2 (by simp)).1
  have e0 : (∑ j, Tag.G2.cartan i0 j * rC j) = 1 := by decide
  have e1 : (∑ j, Tag.G2.cartan i1 j * rC j) = 0 := by decide
  have e2 : (∑ j, Tag.G2.cartan i1 j * rR j) = 2 := by decide
  refine ⟨lt_of_lt_of_le ?_ (card_le_relIndex_of_hom (torusEltHom Tag.G2 K i0)
    (fun u => torusElt_mem_torusGroup i0 u) fun u hu => ?_), fun h0 => ?_⟩
  · rw [Nat.card_units]
    omega
  ·
    have h1 := Subgroup.mem_centralizer_iff.1 hu (x₀ : ModGL Tag.G2 K) x₀.2
    rw [hβ x₀] at h1
    have h2 : torusElt Tag.G2 K i0 u * gX rC (β x₀) * (torusElt Tag.G2 K i0 u)⁻¹ =
        gX rC (β x₀) := by
      change gX rC (β x₀) * torusElt Tag.G2 K i0 u = torusElt Tag.G2 K i0 u * gX rC (β x₀) at h1
      rw [← h1]
      group
    rw [torusElt_conj_gX i0 u hrC, e0, zpow_one] at h2
    have h3 := pinnedX_injective Tag.G2 K rC h2
    exact Units.ext ((mul_left_eq_self₀.1 h3).resolve_right ht₀)
  ·
    obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Kˣ, u₀ ≠ 1 := by
      have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by rw [Nat.card_units]; omega)
      exact exists_ne 1
    have hg : torusElt Tag.G2 K i1 u₀ ∈ torusGroup Tag.G2 K ⊓
        Subgroup.centralizer (E : Set (ModGL Tag.G2 K)) := by
      refine ⟨torusElt_mem_torusGroup i1 u₀, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      rw [show w = gX rC (β ⟨w, hw⟩) from hβ ⟨w, hw⟩]
      have h1 := torusElt_conj_gX i1 u₀ hrC (β ⟨w, hw⟩)
      rw [e1, zpow_zero, Units.val_one, one_mul] at h1
      calc gX rC (β ⟨w, hw⟩) * torusElt Tag.G2 K i1 u₀ =
          (torusElt Tag.G2 K i1 u₀ * gX rC (β ⟨w, hw⟩) * (torusElt Tag.G2 K i1 u₀)⁻¹) *
            torusElt Tag.G2 K i1 u₀ := by rw [h1]
        _ = torusElt Tag.G2 K i1 u₀ * gX rC (β ⟨w, hw⟩) := by group
    rw [h0, Subgroup.mem_bot] at hg
    have h1 := torusElt_conj_gX i1 u₀ hrR (1 : K)
    rw [hg, e2, one_mul, inv_one, mul_one, mul_one] at h1
    have h2 := pinnedX_injective Tag.G2 K rR h1
    have h3 : ((u₀ : K) - 1) ^ 2 = 0 := by
      have h4 : ((u₀ ^ (2 : ℤ) : Kˣ) : K) = (u₀ : K) ^ 2 := by
        rw [zpow_two, Units.val_mul, sq]
      rw [h4] at h2
      have h5 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination -h2 + (1 - (u₀ : K)) * h5
    exact hu₀ (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)))

end CFSG.Quasithin.H13.NQCat.LieCartan.G2
