module

public import CFSG.GroupTheory.LocalCores.Components
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup

section Subnormal

variable {G : Type*} [Group G] [Finite G]

theorem map_pPrimeCore_le_of_isSubnormal_of_prime {s : ℕ} [Fact s.Prime] {X : Subgroup G}
    (hX : X.IsSubnormal) : (CFSG.pPrimeCore s X).map X.subtype ≤ CFSG.pPrimeCore s G := by
  have key : ∀ {X Z : Subgroup G}, X ≤ Z → Z ≤ Subgroup.normalizer (X : Set G) →
      (CFSG.pPrimeCore s X).map X.subtype ≤ (CFSG.pPrimeCore s Z).map Z.subtype := by
    intro X Z hXZ hZN
    have hLZ : (CFSG.pPrimeCore s X).map X.subtype ≤ Z := (Subgroup.map_subtype_le _).trans hXZ
    have hle : ((CFSG.pPrimeCore s X).map X.subtype).subgroupOf Z ≤ CFSG.pPrimeCore s Z := by
      apply le_sSup
      refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using CFSG.Walter.conj_mem_map_of_characteristic (hZN z.2) hl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc (CFSG.pPrimeCore s X).map X.subtype
        = (((CFSG.pPrimeCore s X).map X.subtype).subgroupOf Z).map Z.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLZ).symm
      _ ≤ (CFSG.pPrimeCore s Z).map Z.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => CFSG.Walter.conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact CFSG.pPrimeCore_coprime_card
  | step X Z hXZ hZ hN ih =>
    exact (key hXZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hXZ).mp hN)).trans ih

end Subnormal

section Quasisimple

variable {K : Type*} [Group K] [Finite K]

theorem eq_bot_of_sylow_le_center_of_isPerfect {s : ℕ} [Fact s.Prime] (hK : Group.IsPerfect K)
    (R : Sylow s K) (hR : (R : Subgroup K) ≤ Subgroup.center K) : (R : Subgroup K) = ⊥ := by
  have hP : Subgroup.normalizer ((R : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((R : Subgroup K) : Set K) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_center_iff.1 (hR hy) g).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' R hP
  set τ := MonoidHom.transferSylow R hP with hτ
  have hker : (⊤ : Subgroup K) ≤ τ.ker := by
    have hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
      have := Group.isPerfect_def.1 hK
      rwa [_root_.commutator_def] at this
    rw [← hperf, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext ?_)
    exact Subgroup.mem_center_iff.1 (hR (τ b).2) (τ a)
  have hdisj := hcomp.disjoint
  rw [top_le_iff.1 hker] at hdisj
  exact (disjoint_comm.1 hdisj |> disjoint_top.1)

theorem commutator_eq_self_of_not_central {G : Type*} [Group G] {L S : Subgroup G}
    (hL : CFSG.IsQuasisimple L) (hSL : S ≤ L)
    (hS : ¬ ∀ x ∈ S, ∀ y ∈ L, x * y = y * x) : ⁅L, S⁆ = L := by
  have hNL : ⁅L, S⁆ ≤ L := Subgroup.commutator_le_of_le le_rfl hSL
  have hnorm : (⁅L, S⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 (Subgroup.normalizer_commutator_ge_left L S)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hnorm with htop | hcen
  · exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 htop)
  · exfalso
    have h1 : ⁅⁅L, S⁆, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxL : x ∈ L := hNL hx
      have := hcen (show (⟨x, hxL⟩ : L) ∈ ⁅L, S⁆.subgroupOf L from hx)
      have h2 := Subgroup.mem_center_iff.1 this ⟨y, hy⟩
      exact congrArg Subtype.val h2
    have h2 := CFSG.LocalCores.perfect_double_commutator hL.1 h1
    apply hS
    intro x hx y hy
    have : y ∈ centralizer (S : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2 hy
    exact (Subgroup.mem_centralizer_iff.1 this) x hx

end Quasisimple

section Norm

variable {G : Type*} [Group G]

theorem exists_mem_centralizer_conj_eq {a : G} {n : ℕ} (hn : 0 < n) (han : a ^ n = 1) {L : Subgroup G}
    (hcomm : ∀ i : ℕ, 0 < i → i < n → ∀ x ∈ L, ∀ y ∈ L,
      a ^ i * x * (a ^ i)⁻¹ * y = y * (a ^ i * x * (a ^ i)⁻¹))
    {z : G} (hz : z ∈ L) :
    ∃ d : G, d * a = a * d ∧ ∀ y ∈ L, d * y * d⁻¹ = z * y * z⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  set c : ℕ → G := fun i => a ^ i * z * (a ^ i)⁻¹ with hc
  set R : G := ((List.range m).map (fun i => c (i + 1))).prod with hR
  have hRy : ∀ y ∈ L, R * y = y * R := by
    intro y hy
    refine Commute.eq ?_
    refine Commute.list_prod_left _ _ ?_
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    exact hcomm (i + 1) (Nat.succ_pos i) (Nat.succ_lt_succ (List.mem_range.1 hi)) z hz y hy
  have hc0 : c 0 = z := by simp [hc]
  have hD : ((List.range (m + 1)).map c).prod = z * R := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, hc0]
    rfl
  have hstep : ∀ i : ℕ, a * c i * a⁻¹ = c (i + 1) := fun i => by
    simp only [hc, pow_succ', mul_inv_rev]
    group
  have hconj : a * ((List.range (m + 1)).map c).prod * a⁻¹ = R * z := by
    have h1 : a * ((List.range (m + 1)).map c).prod * a⁻¹
        = ((List.range (m + 1)).map (fun i => c (i + 1))).prod := by
      have := map_list_prod (MulAut.conj a).toMonoidHom ((List.range (m + 1)).map c)
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
      rw [this, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      exact hstep i
    rw [h1, List.range_succ, List.map_append, List.prod_append]
    have hcm : c (m + 1) = z := by simp [hc, han]
    simp [hR, hcm]
  refine ⟨z * R, ?_, ?_⟩
  · have h2 : a * (z * R) * a⁻¹ = z * R := by
      rw [hD] at hconj
      rw [hconj]
      exact hRy z hz
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · intro y hy
    have hRy' : R * y * R⁻¹ = y := mul_inv_eq_iff_eq_mul.2 (hRy y hy)
    calc z * R * y * (z * R)⁻¹ = z * (R * y * R⁻¹) * z⁻¹ := by group
      _ = z * y * z⁻¹ := by rw [hRy']

end Norm

section Normalizer

variable {G : Type*} [Group G]

theorem mem_normalizer_of_map_conj_eq {L : Subgroup G} {g : G}
    (heq : L.map (MulAut.conj g).toMonoidHom = L) : g ∈ normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [heq] at this
  · intro hx
    rw [← heq] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    have h3 : (MulAut.conj g) x' = (MulAut.conj g) x := by simpa [MulAut.conj_apply] using hxx
    have h4 : x' = x := (MulAut.conj g).injective h3
    rw [← h4]
    exact hx'

end Normalizer

end CFSG.LocalAnalysis.UniquenessCase.UCK
