module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSignedPermUniversal
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCoxeterCollapse
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter
public import CFSG.YGroups.Y443.Basic

public noncomputable section

namespace CFSG.Sporadic.GLQ

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj MonsterY443Derived)
open CFSG.ComponentClassification.PresentationLocal
open Equiv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace MonsterTwoRank

local instance : DecidableRel MonsterY443Adj := fun a b => by
  rcases a with _ | ⟨i, j⟩ <;> rcases b with _ | ⟨i', j'⟩ <;> unfold MonsterY443Adj <;>
    infer_instance

@[expose] def forkGen : Fin 7 → MonsterY443Gen :=
  ![some ⟨2, ⟨0, by decide⟩⟩, some ⟨1, ⟨0, by decide⟩⟩, none, some ⟨0, ⟨0, by decide⟩⟩,
    some ⟨0, ⟨1, by decide⟩⟩, some ⟨0, ⟨2, by decide⟩⟩, some ⟨0, ⟨3, by decide⟩⟩]

theorem forkGen_injective : Function.Injective forkGen := by decide

theorem adj_forkGen_iff : ∀ i j : Fin 7,
    MonsterY443Adj (forkGen i) (forkGen j) ↔ (forkGraph 7).Adj i j := by
  decide

@[expose] def forkElt (i : Fin 7) : MonsterY443 := PresentedGroup.of (forkGen i)

theorem forkElt_sq (i : Fin 7) : forkElt i ^ 2 = 1 := by
  rw [sq]
  exact CFSG.YGroups.Y443.gen_mul_self _

theorem forkElt_pair (i j : Fin 7) (hij : i ≠ j) :
    (forkElt i * forkElt j) ^ coxeterEntry i j = 1 := by
  unfold coxeterEntry
  split_ifs with h
  · exact CFSG.YGroups.Y443.gen_pair_adj ((adj_forkGen_iff i j).mpr h)
  · exact CFSG.YGroups.Y443.gen_pair_nonadj (forkGen_injective.ne hij)
      fun h' => h ((adj_forkGen_iff i j).mp h')

theorem exists_forkHom : ∃ φ : W 7 →* MonsterY443, ∀ i, φ (s i) = forkElt i :=
  (even_signed_permutation_universal_homomorphism (by norm_num) forkElt forkElt_sq
    forkElt_pair).1.exists

@[expose] def kerSub {n : ℕ} {G : Type*} [Group G] (φ : W n →* G) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | ∃ hv : v ∈ evenSubspace n, φ (mk v hv 1) = 1}
  add_mem' {v w} hv hw := by
    obtain ⟨hv, hφv⟩ := hv
    obtain ⟨hw, hφw⟩ := hw
    refine ⟨Submodule.add_mem _ hv hw, ?_⟩
    have h : mk (v + w) (Submodule.add_mem _ hv hw) 1 = mk v hv 1 * mk w hw 1 :=
      ext_vec (by rw [vec_mul, vec_mk, vec_mk, vec_mk, right_mk, permVec_one]) (by simp)
    rw [h, map_mul, hφv, hφw, one_mul]
  zero_mem' := ⟨Submodule.zero_mem _, by rw [mk_zero]; exact map_one _⟩
  smul_mem' c v hv := by
    obtain ⟨hv, hφv⟩ := hv
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 c with rfl | rfl
    · refine ⟨by rw [zero_smul]; exact Submodule.zero_mem _, ?_⟩
      have h : mk ((0 : ZMod 2) • v) (by rw [zero_smul]; exact Submodule.zero_mem _) 1 = 1 :=
        ext_vec (by rw [vec_mk, zero_smul, vec_one]) (by simp)
      rw [h, map_one]
    · refine ⟨by rw [one_smul]; exact hv, ?_⟩
      have h : mk ((1 : ZMod 2) • v) (by rw [one_smul]; exact hv) 1 = mk v hv 1 :=
        ext_vec (by rw [vec_mk, vec_mk, one_smul]) rfl
      rw [h, hφv]

theorem permVec_mem_kerSub {n : ℕ} {G : Type*} [Group G] (φ : W n →* G) (σ : Perm (Fin n))
    {v : Fin n → ZMod 2} (hv : v ∈ kerSub φ) : permVec σ v ∈ kerSub φ := by
  obtain ⟨hv', hφ⟩ := hv
  refine ⟨permVec_mem σ hv', ?_⟩
  have h : mk (permVec σ v) (permVec_mem σ hv') 1 =
      (SemidirectProduct.inr σ : W n) * mk v hv' 1 * (SemidirectProduct.inr σ)⁻¹ := by
    refine ext_vec ?_ (by simp)
    rw [show mk v hv' 1 = SemidirectProduct.inl (Multiplicative.ofAdd ⟨v, hv'⟩) from rfl,
      vec_inr_mul_inl_mul_inv, vec_mk, vec_inl]
  rw [h, map_mul, map_mul, hφ, mul_one, map_inv, mul_inv_cancel]

theorem graph_cliqueFree_three : CFSG.YGroups.Y443.graph.CliqueFree 3 := by
  have key : ∀ a b c : MonsterY443Gen, MonsterY443Adj a b → MonsterY443Adj a c →
      MonsterY443Adj b c → False := by
    decide
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hS
  exact key a b c hab hac hbc

theorem derived_eq_bot_of_eq
    (h : (PresentedGroup.of (some ⟨2, ⟨0, by decide⟩⟩) : MonsterY443) =
      PresentedGroup.of (some ⟨1, ⟨0, by decide⟩⟩)) : MonsterY443Derived = ⊥ := by
  set x₂₁ : MonsterY443Gen := some ⟨1, ⟨0, by decide⟩⟩ with hx₂₁
  set x₂₂ : MonsterY443Gen := some ⟨1, ⟨1, by decide⟩⟩ with hx₂₂
  set x₃₁ : MonsterY443Gen := some ⟨2, ⟨0, by decide⟩⟩ with hx₃₁
  have hadj : MonsterY443Adj x₂₂ x₂₁ := by decide
  have hnadj : ¬ MonsterY443Adj x₂₂ x₃₁ := by decide
  have hne : x₂₂ ≠ x₃₁ := by decide
  have h3 := CFSG.YGroups.Y443.gen_pair_adj hadj
  have h2 := CFSG.YGroups.Y443.gen_pair_nonadj hne hnadj
  rw [h] at h2
  have h1 := eq_one_of_sq_of_cube h2 h3
  have heq : (PresentedGroup.of x₂₁ : MonsterY443) = PresentedGroup.of x₂₂ := by
    have hsq := CFSG.YGroups.Y443.gen_mul_self x₂₁
    calc (PresentedGroup.of x₂₁ : MonsterY443) =
        PresentedGroup.of x₂₂ * PresentedGroup.of x₂₁ * PresentedGroup.of x₂₁ := by
          rw [h1, one_mul]
      _ = PresentedGroup.of x₂₂ := by rw [mul_assoc, hsq, mul_one]
  obtain ⟨_, _, _, hcyc, _⟩ := triangle_free_coxeter_adjacent_generator_collapse
    CFSG.YGroups.Y443.graph CFSG.YGroups.Y443.graph_connected graph_cliqueFree_three
    (PresentedGroup.of : MonsterY443Gen → MonsterY443) (PresentedGroup.closure_range_of _)
    (fun v => by rw [sq]; exact CFSG.YGroups.Y443.gen_mul_self v)
    (fun u v huv => CFSG.YGroups.Y443.gen_pair_adj huv)
    (fun u v huv hn => CFSG.YGroups.Y443.gen_pair_nonadj huv hn)
    (CFSG.YGroups.Y443.graph_adj.mpr (CFSG.YGroups.Y443.adj_symm hadj)) heq
  have hcomm : IsMulCommutative MonsterY443 := IsCyclic.isMulCommutative
  rw [eq_bot_iff]
  change ⁅(⊤ : Subgroup MonsterY443), ⊤⁆ ≤ ⊥
  rw [Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm.is_comm.comm g₁ g₂

theorem kerSub_eq_bot (φ : W 7 →* MonsterY443) (hφ : ∀ i, φ (s i) = forkElt i)
    (hM : MonsterY443Derived ≠ ⊥) : kerSub φ = ⊥ := by
  rcases (odd_even_weight_permutation_module_irreducible (n := 7) (by norm_num) (by decide)).1
      (kerSub φ) (fun v hv => hv.1) (fun σ v hv => permVec_mem_kerSub φ σ hv) with h | h
  · exact h
  · exfalso
    apply hM
    have hb : basisVec (⟨0, by norm_num⟩ : Fin 7) + basisVec ⟨1, by norm_num⟩ ∈ kerSub φ := by
      rw [h]
      exact basisVec_add_basisVec_mem _ _
    obtain ⟨_, hφb⟩ := hb
    have h01 : forkElt ⟨0, by norm_num⟩ * forkElt ⟨1, by norm_num⟩ = 1 := by
      rw [← hφ, ← hφ, ← map_mul, s_zero_mul_s_one (by norm_num)]
      exact hφb
    apply derived_eq_bot_of_eq
    have hsq : forkElt ⟨1, by norm_num⟩ * forkElt ⟨1, by norm_num⟩ = 1 := by
      rw [← sq]
      exact forkElt_sq _
    calc (PresentedGroup.of (some ⟨2, ⟨0, by decide⟩⟩) : MonsterY443) =
        forkElt ⟨0, by norm_num⟩ * forkElt ⟨1, by norm_num⟩ * forkElt ⟨1, by norm_num⟩ := by
          rw [mul_assoc, hsq, mul_one]
          rfl
      _ = _ := by
          rw [h01, one_mul]
          rfl

end MonsterTwoRank

open MonsterTwoRank

theorem monster_nontrivial_two_rank_at_least_six :
    (MonsterY443Derived ≠ ⊥ →
      ∃ E : Subgroup MonsterY443Derived, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 64) ∧
    ∀ (K : Type*) [Group K] [Finite K] [Nontrivial K],
      Nonempty (K ≃* MonsterY443Derived) → 6 ≤ CFSG.pRank 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : MonsterY443Derived ≠ ⊥ →
      ∃ E : Subgroup MonsterY443Derived, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 64 := by
    intro hM
    obtain ⟨φ, hφ⟩ := exists_forkHom
    have hU := kerSub_eq_bot φ hφ hM
    let ψ : signSubgroup 7 →* MonsterY443 := φ.comp (signSubgroup 7).subtype
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨x, hx⟩ h1
      have hr : x.right = 1 := mem_signSubgroup_iff.mp hx
      have hxmk : x = mk (vec x) (vec_mem x) 1 := by
        conv_lhs => rw [eq_mk x]
        rw [hr]
      have hvU : vec x ∈ kerSub φ := ⟨vec_mem x, by rw [← hxmk]; exact h1⟩
      rw [hU, Submodule.mem_bot] at hvU
      exact Subtype.ext (ext_vec (by rw [hvU, OneMemClass.coe_one, vec_one])
        (by rw [hr, OneMemClass.coe_one, right_one]))
    have hle : (signSubgroup 7).map φ ≤ MonsterY443Derived := by
      refine (Subgroup.map_mono (signSubgroup_le_commutator (by norm_num))).trans ?_
      change Subgroup.map φ (commutator (W 7)) ≤ commutator MonsterY443
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have : CFSG.IsElementaryAbelian 2 (signSubgroup 7) := isElementaryAbelian_signSubgroup
    have : CFSG.IsElementaryAbelian 2 ((signSubgroup 7).map φ) := CFSG.IsElementaryAbelian.map φ
    have hcard : Nat.card ((signSubgroup 7).map φ) = 64 := by
      have h1 : ψ.range = (signSubgroup 7).map φ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv,
        card_signSubgroup (by norm_num)]
      norm_num
    refine ⟨((signSubgroup 7).map φ).subgroupOf MonsterY443Derived,
      CFSG.IsElementaryAbelian.subgroupOf hle, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  refine ⟨hE, fun K _ _ _ ⟨e⟩ => ?_⟩
  have hM : MonsterY443Derived ≠ ⊥ := by
    have : Nontrivial MonsterY443Derived := e.injective.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  obtain ⟨E, hEab, hEcard⟩ := hE hM
  have := hEab
  have hE' : CFSG.IsElementaryAbelian 2 (E.map e.symm.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  refine CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.le_pRank_of_subgroup hE'
    (r := 6) ?_
  rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]
  norm_num

end CFSG.Sporadic.GLQ
