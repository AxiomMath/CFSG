module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem exists_component (h69 : R6_9 Dat) :
    ∃ K : Subgroup m.Hbar, IsComponentOf K ⊤ := by
  by_contra h
  push Not at h
  exact m.layer_ne_bot h69 (sSup_eq_bot.2 fun K hK => absurd hK (h K))

variable (hKM : UCK.KMult) (hK3 : UCK.KMult3) (h69 : R6_9 Dat)
include hKM hK3 h69

theorem layer_eq {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    componentLayerOf (⊤ : Subgroup m.Hbar) = K :=
  le_antisymm (sSup_le fun _ hK' => (m.component_unique hKM hK3 h69 hK' hK).le) (le_sSup hK)

theorem component_normal {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    K.Normal := by
  rw [← m.layer_eq hKM hK3 h69 hK]
  exact ⟨fun n hn g => (CFSG.GorensteinWalter.componentLayerOf_isNormalIn ⊤).2 g (mem_top g) n hn⟩

theorem mem_bar_Z_of_centralizes {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) {a : m.Hbar} (ha : a ∈ m.bar m.A)
    (hac : ∀ k ∈ K, a * k = k * a) : a ∈ m.bar m.Z := by
  by_contra haZ
  have hKM' := m.pre_le_M_of_centralizer h69 ha haZ hac
  obtain ⟨y, hyR, hyK, hy1, hyr⟩ := m.exists_mem_component h69 hK
  obtain ⟨b, hbA, rfl⟩ := m.mem_bar_A_of_pow h69 hyR hyr
  exact m.hZ.not_le (m.H_le_M_of_le_M (m.pre_le_H K)
    (m.H_le_normalizer_pre (m.component_normal hKM hK3 h69 hK)) hKM' (t := (b : G))
    ((m.mem_pre).2 ⟨b.2, hyK⟩) hbA fun hbZ =>
      hy1 (m.bar_Z_inf_component hKM hK3 h69 hK (m.mem_bar_of_mem hbZ) hyK))

theorem pCore_inf_component {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) :
    CFSG.pCore m.r m.Hbar ⊓ K = ⊥ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI hKs := m.isSimpleGroup_component hKM hK3 h69 hK
  set N : Subgroup ↥K := (CFSG.pCore m.r m.Hbar).subgroupOf K with hN
  haveI : N.Normal := Subgroup.normal_subgroupOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥K) ∈ N := hx.1
    rw [h, mem_bot] at this
    exact (mem_bot).2 (congrArg Subtype.val this)
  · exfalso
    have hKp : IsPGroup m.r ↥K := by
      have hle : K ≤ CFSG.pCore m.r m.Hbar := fun x hx => by
        have : (⟨x, hx⟩ : ↥K) ∈ N := h ▸ mem_top _
        exact this
      exact CFSG.pCore_isPGroup.to_le hle
    haveI := hKp.isNilpotent
    have hperf := hK.2.2.2.1
    haveI : Nontrivial ↥K := hK.2.2.1
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K).ne hperf

theorem pCore_le_centralizer_component {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) :
    CFSG.pCore m.r m.Hbar ≤ centralizer (K : Set m.Hbar) := by
  haveI := m.component_normal hKM hK3 h69 hK
  have hc : ⁅CFSG.pCore m.r m.Hbar, K⁆ = ⊥ := by
    rw [eq_bot_iff, ← m.pCore_inf_component hKM hK3 h69 hK]
    exact Subgroup.commutator_le_inf _ _
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc

theorem pCore_le_bar_R : CFSG.pCore m.r m.Hbar ≤ m.bar m.R := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hS := m.bar_R_sylow h69
  have hP : IsPGroup m.r ↥(CFSG.pCore m.r m.Hbar ⊔ m.bar m.R) :=
    IsPGroup.to_sup_of_normal_left CFSG.pCore_isPGroup hS.isPGroup
  have h := hS.eq_of_le le_sup_right le_top hP
  rw [← h]
  exact le_sup_left

theorem bar_Z_le_pCore : m.bar m.Z ≤ CFSG.pCore m.r m.Hbar := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  refine le_sSup ⟨⟨fun n hn g => ?_⟩, IsPGroup.of_card (n := 1) (by rw [m.card_bar_Z, pow_one])⟩
  rw [← m.bar_Z_comm hn g, mul_inv_cancel_right]
  exact hn

theorem isCyclic_pCore {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    IsCyclic ↥(CFSG.pCore m.r m.Hbar) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hZP := m.bar_Z_le_pCore hKM hK3 h69
  refine N588.isCyclic_of_forall_pow_eq_one_mem m.d.odd CFSG.pCore_isPGroup
    (Z₀ := (m.bar m.Z).subgroupOf (CFSG.pCore m.r m.Hbar)) ?_ ?_
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv).trans m.card_bar_Z
  · intro x hx
    have hxA : (x : m.Hbar) ∈ m.bar m.A := m.mem_bar_A_of_pow h69
      (m.pCore_le_bar_R hKM hK3 h69 x.2) (by simpa using congrArg Subtype.val hx)
    exact m.mem_bar_Z_of_centralizes hKM hK3 h69 hK hxA fun k hk =>
      (mem_centralizer_iff.1 (m.pCore_le_centralizer_component hKM hK3 h69 hK x.2) k hk).symm

theorem mem_pCore_of_centralizes {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) {c : m.Hbar}
    (hcK : c ∈ centralizer (K : Set m.Hbar))
    (hcP : c ∈ centralizer (CFSG.pCore m.r m.Hbar : Set m.Hbar)) :
    c ∈ CFSG.pCore m.r m.Hbar := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set P := CFSG.pCore m.r m.Hbar with hP
  have hFP : CFSG.fittingSubgroupOf (⊤ : Subgroup m.Hbar) ≤ P :=
    le_sSup ⟨CFSG.fittingSubgroupOf_normal ⊤ inferInstance, m.isPGroup_fittingSubgroupOf⟩
  have hFstar : generalizedFittingSubgroupOf (⊤ : Subgroup m.Hbar) ≤ P ⊔ K := by
    rw [generalizedFittingSubgroupOf, m.layer_eq hKM hK3 h69 hK]
    exact sup_le_sup_right hFP _
  have hcF : c ∈ centralizer (generalizedFittingSubgroupOf (⊤ : Subgroup m.Hbar) :
      Set m.Hbar) := by
    have hle : generalizedFittingSubgroupOf (⊤ : Subgroup m.Hbar) ≤
        centralizer ({c} : Set m.Hbar) := by
      refine hFstar.trans (sup_le ?_ ?_)
      · intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact (mem_centralizer_iff.1 hcP x hx).symm
      · intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        exact (mem_centralizer_iff.1 hcK x hx).symm
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.1 (hle hx) c rfl).symm
  have hcmem := CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le hcF
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_of_normal_left (s := P) (t := K)).mp (hFstar hcmem)
  have hyK : y ∈ centralizer (K : Set m.Hbar) :=
    m.pCore_le_centralizer_component hKM hK3 h69 hK hy
  have hzC : z ∈ centralizer (K : Set m.Hbar) := by
    have : z = y⁻¹ * (y * z) := by group
    rw [this]
    exact (centralizer (K : Set m.Hbar)).mul_mem ((centralizer _).inv_mem hyK) hcK
  have hz1 : z = 1 := by
    have hc := m.center_component_eq_bot hKM hK3 h69 hK
    have : (⟨z, hz⟩ : ↥K) ∈ center ↥K := Subgroup.mem_center_iff.2 fun k =>
      Subtype.ext (mem_centralizer_iff.1 hzC k k.2)
    rw [hc, mem_bot] at this
    exact congrArg Subtype.val this
  rw [hz1, mul_one]
  exact hy

theorem isSolvable_centralizer_component {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) :
    Group.IsSolvable ↥(centralizer (K : Set m.Hbar)) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set P := CFSG.pCore m.r m.Hbar with hP
  set C := centralizer (K : Set m.Hbar) with hC
  haveI hcyc : IsCyclic ↥P := m.isCyclic_pCore hKM hK3 h69 hK
  have hCN : C ≤ normalizer (P : Set m.Hbar) := le_top.trans (normalizer_eq_top (H := P)).ge
  let φ : ↥C →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hCN)
  have hker : ∀ c ∈ φ.ker, ((c : ↥C) : m.Hbar) ∈ P := by
    intro c hc
    refine m.mem_pCore_of_centralizes hKM hK3 h69 hK c.2 ?_
    rw [mem_centralizer_iff]
    intro p hp
    have h1 := congrArg (fun f : MulAut ↥P => (f ⟨p, hp⟩ : m.Hbar)) (MonoidHom.mem_ker.1 hc)
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulAut.one_apply] at h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    simp only [Subgroup.coe_inclusion] at h1
    calc p * c = (c * p * (c : m.Hbar)⁻¹) * c := by rw [h1]
      _ = c * p := by group
  have hcommP : ∀ a b : ↥P, a * b = b * a := (IsCyclic.commGroup (α := ↥P)).mul_comm
  haveI : Group.IsSolvable ↥φ.ker := isSolvable_of_comm fun a b => by
    have h1 := hcommP ⟨_, hker a a.2⟩ ⟨_, hker b b.2⟩
    have h2 : ((a : ↥C) : m.Hbar) * ((b : ↥C) : m.Hbar) =
        ((b : ↥C) : m.Hbar) * ((a : ↥C) : m.Hbar) := congrArg Subtype.val h1
    exact Subtype.ext (Subtype.ext h2)
  haveI : Group.IsSolvable (↥C ⧸ φ.ker) := by
    let e := QuotientGroup.quotientKerEquivRange φ
    refine isSolvable_of_comm fun a b => e.injective ?_
    rw [map_mul, map_mul]
    exact Subtype.ext (N588.MulAut.mul_comm_of_isCyclic _ _)
  exact Group.isSolvable_of_subgroup_quotient φ.ker

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
