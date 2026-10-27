module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveG
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem exists_conj (h : Hyp65 n M V₀ V g) :
    ∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l := by
  haveI := h.K_normal
  obtain ⟨z, hz⟩ := h.quotPair.exists_conj_eq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((KOf M V g).subgroupOf (LOf V g)) z
  rw [imgK_conj M V g x V] at hz
  refine ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, ?_⟩
  exact eq_of_imgK_eq h (conjV_mem_pairConjOf V g)
    ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, Or.inl rfl⟩ hz

private theorem s65_SixFiveH_comm_of_mem_K (M V : Subgroup G) (g : G)
    [((KOf M V g).subgroupOf (LOf V g)).Normal] {a b : ↥(LOf V g)}
    (hab : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ KOf M V g) :
    QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) a *
        QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) b =
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) b *
        QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) a := by
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have h1 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))
      (a * b * a⁻¹ * b⁻¹) = 1 :=
    (mk_eq_one_iff_mem_K M V g (a * b * a⁻¹ * b⁻¹)).2 (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hab)
  simpa only [map_mul, map_inv, commutatorElement_def] using h1

section Certified


theorem C_le_K (h : Hyp65 n M V₀ V g) : COf M V₀ V g ≤ KOf M V g := by
  haveI := h.K_normal
  intro c hc
  have hcL : c ∈ LOf V g := (Subgroup.mem_inf.1 hc).1
  let c' : ↥(LOf V g) := ⟨c, hcL⟩
  have hmemV : imgK M V g V ≤ Subgroup.centralizer
      ({QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) c'} : Set _) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [imgK] at ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
    have hyV : (y : G) ∈ V := Subgroup.mem_subgroupOf.1 hy
    have hcomm : c * (y : G) * c⁻¹ * (y : G)⁻¹ ∈ KOf M V g := by
      have hmem : ⁅c, (y : G)⁆ ∈ ⁅COf M V₀ V g, V⁆ :=
        Subgroup.commutator_mem_commutator hc hyV
      have hU : ⁅c, (y : G)⁆ ∈ UOf M V g := commutator_C_V_le_U h hmem
      have hK : ⁅c, (y : G)⁆ ∈ KOf M V g := (le_sup_left : UOf M V g ≤ KOf M V g) hU
      simpa only [commutatorElement_def] using hK
    exact s65_SixFiveH_comm_of_mem_K M V g hcomm
  have hmemB : imgK M V g (conjSubgroup V g) ≤ Subgroup.centralizer
      ({QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) c'} : Set _) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [imgK] at ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
    have hyB : (y : G) ∈ conjSubgroup V g := Subgroup.mem_subgroupOf.1 hy
    have hcomm : c * (y : G) * c⁻¹ * (y : G)⁻¹ ∈ KOf M V g := by
      have hmem : ⁅c, (y : G)⁆ ∈ ⁅COf M V₀ V g, conjSubgroup V g⁆ :=
        Subgroup.commutator_mem_commutator hc hyB
      have hB : ⁅c, (y : G)⁆ ∈ BOf M V g := commutator_C_conjV_le_B h hmem
      have hK : ⁅c, (y : G)⁆ ∈ KOf M V g :=
        (le_sup_right : BOf M V g ≤ KOf M V g) hB
      simpa only [commutatorElement_def] using hK
    exact s65_SixFiveH_comm_of_mem_K M V g hcomm
  have hcenter : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) c' ∈
      Subgroup.center (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have htop : (⊤ : Subgroup (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))) ≤
        Subgroup.centralizer
          ({QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) c'} : Set _) := by
      rw [← imgK_sup M V g]
      exact sup_le hmemV hmemB
    have hx := htop (Subgroup.mem_top x)
    exact (Subgroup.mem_centralizer_iff.1 hx _ (Set.mem_singleton _)).symm
  have h1 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) c' = 1 := by
    have h2 := hcenter
    rw [h.quotPair.center_eq_bot, Subgroup.mem_bot] at h2
    exact h2
  exact (mk_eq_one_iff_mem_K M V g c').1 h1

theorem C_eq_K (h : Hyp65 n M V₀ V g) : COf M V₀ V g = KOf M V g := by
  exact le_antisymm (C_le_K h) (K_le_C h)

theorem quotShape (h : Hyp65 n M V₀ V g) [((KOf M V g).subgroupOf (LOf V g)).Normal] :
    QuotShape (LOf V g) (KOf M V g) (E3.mQuot V (conjSubgroup M g)) := by
  obtain ⟨hshape, hcard⟩ := h.quotPair.quotShape
  unfold QuotShape
  refine ⟨hshape, ?_⟩
  change twoRank (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) =
    padicValNat 2 ((conjSubgroup M g).relIndex V)
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have hrel : (conjSubgroup M g).relIndex V =
      2 ^ twoRank (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) := by
    rw [← card_imgK h, hcard]
  rw [hrel, padicValNat.prime_pow]

theorem genHyp (h : Hyp65 n M V₀ V g) : GenHyp M V g := by
  haveI := h.K_normal
  intro x hx hxK
  have hxL : x ∈ LOf V g := (le_sup_right : conjSubgroup V g ≤ LOf V g) hx
  let x' : ↥(LOf V g) := ⟨x, hxL⟩
  let W : Subgroup G := (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g)
  let W' : Subgroup ↥(LOf V g) := W.subgroupOf (LOf V g)
  have hx1 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) x' ≠ 1 := by
    intro h1
    exact hxK ((mk_eq_one_iff_mem_K M V g x').1 h1)
  have hxmem : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) x' ∈
      imgK M V g (conjSubgroup V g) := by
    rw [imgK]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
  have hsup := h.quotPair.sup_zpowers_eq_top hxmem hx1
  have hVW : V ≤ W := by
    change V ≤ (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g)
    exact (le_sup_left : V ≤ V ⊔ Subgroup.zpowers x).trans le_sup_left
  have hzW : Subgroup.zpowers x ≤ W := by
    change Subgroup.zpowers x ≤ (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g)
    exact (le_sup_right : Subgroup.zpowers x ≤ V ⊔ Subgroup.zpowers x).trans le_sup_left
  have hVW' : V.subgroupOf (LOf V g) ≤ W' :=
    Subgroup.subgroupOf_mono (LOf V g) hVW
  have hxW' : x' ∈ W' :=
    Subgroup.mem_subgroupOf.2 (hzW (Subgroup.mem_zpowers x))
  have hxmap : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) x' ∈
      W'.map (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) :=
    Subgroup.mem_map_of_mem _ hxW'
  have htop : (⊤ : Subgroup (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g))) ≤
      W'.map (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) := by
    rw [← hsup]
    refine sup_le ?_ ?_
    · rw [imgK]
      exact Subgroup.map_mono hVW'
    · exact Subgroup.zpowers_le.2 hxmap
  have hW'map : W'.map (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) = ⊤ :=
    le_antisymm le_top htop
  have hK'W' : (KOf M V g).subgroupOf (LOf V g) ≤ W' :=
    Subgroup.subgroupOf_mono (LOf V g) le_sup_right
  have h1 : W' ⊔ (KOf M V g).subgroupOf (LOf V g) = ⊤ := by
    have h2 := congrArg (Subgroup.comap
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)))) hW'map
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
    exact h2
  have hW' : W' = ⊤ := by
    have h3 := sup_eq_left.2 hK'W'
    rw [← h3]
    exact h1
  intro l hl
  have hl' : (⟨l, hl⟩ : ↥(LOf V g)) ∈ W' := by
    rw [hW']
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hl'

theorem swapHyp (h : Hyp65 n M V₀ V g) : SwapHyp V g := by
  haveI := h.K_normal
  obtain ⟨z, hz1, hz2⟩ := h.quotPair.exists_swap
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((KOf M V g).subgroupOf (LOf V g)) z
  rw [imgK_conj M V g x V] at hz1
  rw [imgK_conj M V g x (conjSubgroup V g)] at hz2
  refine ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, ?_, ?_⟩
  · exact eq_of_imgK_eq h ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, Or.inl rfl⟩
      (conjV_mem_pairConjOf V g) hz1
  · exact eq_of_imgK_eq h ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, Or.inr rfl⟩
      (V_mem_pairConjOf V g) hz2

theorem six_five_one (h : Hyp65 n M V₀ V g) :
    ∃ _ : ((KOf M V g).subgroupOf (LOf V g)).Normal,
      (KOf M V g : Set G) = (BOf M V g : Set G) * (UOf M V g : Set G) ∧
      QuotShape (LOf V g) (KOf M V g) (E3.mQuot V (conjSubgroup M g)) ∧
      (∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) ∧
      COf M V₀ V g = KOf M V g := by
  haveI := h.K_normal
  exact ⟨h.K_normal, K_coe_eq_mul h, quotShape h, exists_conj h, C_eq_K h⟩

end Certified

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
