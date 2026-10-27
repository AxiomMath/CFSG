module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.GroupTheory.OddOrderClosure
import CFSG.GroupTheory.PCoreOfSubnormal
import CFSG.GroupTheory.PElementSubgroup
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8LiftGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {X : Type} [Group X] [Finite X]

private lemma subgroupOf_oUpperTwo {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    (S17.oUpperTwo H).subgroupOf H = CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup H) := by
  rw [S17.oUpperTwo_eq_closure, CFSG.GroupTheory.oddOrderClosure_eq_closure]
  set S : Set G := {x : G | x ∈ H ∧ Odd (orderOf x)} with hS
  have hpre : H.subtype ⁻¹' S = {x : ↥H | x ∈ (⊤ : Subgroup H) ∧ Odd (orderOf x)} := by
    ext x
    simp [hS, Subgroup.orderOf_coe]
  rw [← hpre]
  have himg : H.subtype '' (H.subtype ⁻¹' S) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx, rfl⟩
  have hmap : (Subgroup.closure (H.subtype ⁻¹' S)).map H.subtype = Subgroup.closure S := by
    rw [MonoidHom.map_closure, himg]
  rw [← hmap]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

private lemma mem_of_odd_of_pow_mem {G : Type*} [Group G] {N : Subgroup G} {o : G}
    (hodd : Odd (orderOf o)) {k : ℕ} (h : o ^ 2 ^ k ∈ N) : o ∈ N := by
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((orderOf o : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
  obtain ⟨a, b, hab⟩ := hcop
  have e : o = (o ^ 2 ^ k) ^ a := by
    calc o = o ^ (1 : ℤ) := (zpow_one o).symm
      _ = o ^ (a * ((2 ^ k : ℕ) : ℤ) + b * ((orderOf o : ℕ) : ℤ)) := by rw [hab]
      _ = (o ^ 2 ^ k) ^ a * (o ^ orderOf o) ^ b := by
          rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (o ^ 2 ^ k) ^ a := by rw [pow_orderOf_eq_one, one_zpow, mul_one]
  rw [e]
  exact N.zpow_mem h a

theorem opp_eq_self_of_quot (Y : Subgroup X) {S : Type} [Group S] [Finite S] (φ : ↥Y →* S)
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hgen : Opp 2 (⊤ : Subgroup S) = ⊤) : Opp 2 Y = Y := by
  have hOpple : Opp 2 Y ≤ Y := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact (Subgroup.closure_le Y).mpr fun x hx => hx.1
  have hker_le : φ.ker ≤ (Opp 2 Y).subgroupOf Y := by
    intro k hk
    change (k : X) ∈ Opp 2 Y
    have hkp : IsPGroup 2 ((φ.ker).map Y.subtype) := hker.map Y.subtype
    have hle := CFSG.le_pElementSubgroup_of_isPGroup (p := 2) Nat.prime_two hkp
      (Subgroup.map_subtype_le (φ.ker))
    simpa only [Opp, Subgroup.coe_subtype] using
      hle (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
  have hmap_top : ((Opp 2 Y).subgroupOf Y).map φ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    change Subgroup.closure {s : S | s ∈ (⊤ : Subgroup S) ∧ ∃ k : ℕ, orderOf s = 2 ^ k} ≤
      ((Opp 2 Y).subgroupOf Y).map φ
    rw [Subgroup.closure_le]
    rintro s ⟨-, k, hk⟩
    have hs : s ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one s
    obtain ⟨x, hxφ, m, hxm⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.exists_lift_pElement φ hφ hs
    refine Subgroup.mem_map.mpr ⟨x, ?_, hxφ⟩
    change (x : X) ∈ Opp 2 Y
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxm)
    exact Subgroup.subset_closure ⟨x.2, j, by rw [Subgroup.orderOf_coe]; exact hj⟩
  have hsub_top : (Opp 2 Y).subgroupOf Y = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : φ z ∈ ((Opp 2 Y).subgroupOf Y).map φ := by
      rw [hmap_top]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
    have hmem : a⁻¹ * z ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haz, inv_mul_cancel]
    have hmemA : a⁻¹ * z ∈ (Opp 2 Y).subgroupOf Y := hker_le hmem
    rw [(mul_inv_cancel_left a z).symm]
    exact Subgroup.mul_mem _ ha hmemA
  exact le_antisymm hOpple (Subgroup.subgroupOf_eq_top.mp hsub_top)

theorem oUpperTwo_le_sup_pCoreOf_of_quot (Y₀ : Subgroup X) {S : Type} [Group S] [Finite S]
    (φ : ↥Y₀ →* S) (hφ : Function.Surjective φ) (hker : φ.ker ≤ CFSG.pCore 2 ↥Y₀)
    (hmin : ∀ N : Subgroup S, N.Normal → N ≠ ⊥ → S17.oUpperTwo (⊤ : Subgroup S) ≤ N)
    (Nn : Subgroup X) (hNnY : Nn ≤ Y₀) (hNn : (Nn.subgroupOf Y₀).Normal)
    (hNnQ : ¬ Nn ≤ pCoreOf 2 Y₀) : S17.oUpperTwo Y₀ ≤ Nn ⊔ pCoreOf 2 Y₀ := by
  rw [S17.oUpperTwo_eq_closure, Subgroup.closure_le]
  intro x hx
  obtain ⟨hxY, hxodd⟩ := hx
  let N : Subgroup S := (Nn.subgroupOf Y₀).map φ
  have hNnormal : N.Normal := hNn.map φ hφ
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hNnQ
    have hle : Nn.subgroupOf Y₀ ≤ CFSG.pCore 2 ↥Y₀ := by
      have h1 : (Nn.subgroupOf Y₀).map φ = ⊥ := hbot
      exact ((Subgroup.map_eq_bot_iff (Nn.subgroupOf Y₀)).mp h1).trans hker
    have h2 := Subgroup.map_mono (f := Y₀.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hNnY] at h2
    simpa only [CFSG.Open.pCoreOf] using h2
  have hxN : φ ⟨x, hxY⟩ ∈ N := by
    apply hmin N hNnormal hNne
    rw [S17.oUpperTwo_eq_closure]
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩
    have hdvd : orderOf (φ ⟨x, hxY⟩) ∣ orderOf x := by
      have hcoe : orderOf x = orderOf (⟨x, hxY⟩ : ↥Y₀) :=
        Subgroup.orderOf_coe (⟨x, hxY⟩ : ↥Y₀)
      rw [hcoe]
      exact orderOf_map_dvd φ ⟨x, hxY⟩
    exact hxodd.of_dvd_nat hdvd
  obtain ⟨n, hnN, hnφ⟩ := Subgroup.mem_map.mp hxN
  let k : ↥Y₀ := n⁻¹ * ⟨x, hxY⟩
  have hkk : k ∈ CFSG.pCore 2 ↥Y₀ := by
    apply hker
    rw [MonoidHom.mem_ker]
    dsimp only [k]
    rw [map_mul, map_inv, hnφ, inv_mul_cancel]
  have hnX : (n : X) ∈ Nn := Subgroup.mem_subgroupOf.mp hnN
  have hkX : (k : X) ∈ pCoreOf 2 Y₀ :=
    Subgroup.mem_map.mpr ⟨k, hkk, rfl⟩
  have hxprod : x = (n : X) * (k : X) := by
    have h : n * k = ⟨x, hxY⟩ := by
      dsimp only [k]
      group
    exact (congrArg Subtype.val h).symm
  rw [hxprod]
  exact Subgroup.mul_mem_sup hnX hkX

theorem card_bar2_oUpperTwo_of_quot (Y₀ : Subgroup X) {S : Type} [Group S] [Finite S]
    (φ : ↥Y₀ →* S) (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥Y₀) :
    Nat.card (Bar2 (S17.oUpperTwo Y₀)) = Nat.card (S17.oUpperTwo (⊤ : Subgroup S)) := by
  let J₀ : Subgroup X := S17.oUpperTwo Y₀
  have hJle : J₀ ≤ Y₀ := S17.oUpperTwo_le Y₀
  set ψ : ↥J₀ →* S := φ.comp (Subgroup.inclusion hJle) with hψdef
  have hJnormal : (J₀.subgroupOf Y₀).Normal :=
    CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf Y₀
  have hsub : CFSG.Open.IsSubnormal J₀ Y₀ :=
    CFSG.Assembly.isSubnormal_iff_open.1
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hJle).2 hJnormal.isSubnormal)
  have hcore : CFSG.Open.pCoreOf 2 J₀ = J₀ ⊓ CFSG.Open.pCoreOf 2 Y₀ :=
    CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsub
  have hψrange : ψ.range = (J₀.subgroupOf Y₀).map φ := by
    rw [MonoidHom.range_eq_map, hψdef]
    rw [← Subgroup.map_map (g := φ) (f := Subgroup.inclusion hJle)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      change (Subgroup.inclusion hJle x : X) ∈ J₀
      rw [Subgroup.coe_inclusion]
      exact x.2
    · intro hy
      exact ⟨⟨(y : X), hy⟩, Subgroup.mem_top _, Subtype.ext (Subgroup.coe_inclusion hJle _)⟩
  have hrange_le : ψ.range ≤ S17.oUpperTwo (⊤ : Subgroup S) := by
    rw [hψrange]
    have hJ : J₀.subgroupOf Y₀ = CFSG.GroupTheory.oddOrderClosure (⊤ : Subgroup ↥Y₀) :=
      subgroupOf_oUpperTwo Y₀
    rw [hJ]
    have hmap := CFSG.GroupTheory.map_oddOrderClosure_le φ (⊤ : Subgroup ↥Y₀)
    rw [Subgroup.map_top_of_surjective φ hφ] at hmap
    exact hmap.trans (le_of_eq (CFSG.GroupTheory.oddOrderClosure_eq_closure (⊤ : Subgroup S)))
  have hrange_ge : S17.oUpperTwo (⊤ : Subgroup S) ≤ ψ.range := by
    rw [S17.oUpperTwo_eq_closure, Subgroup.closure_le]
    rintro s ⟨-, hodd⟩
    obtain ⟨y, hφy⟩ := hφ s
    obtain ⟨k, hk⟩ :=
      CFSG.GroupTheory.pow_two_pow_mem_oddOrderClosure Y₀ (g := (y : X)) y.2
    have hwJ : ((y ^ 2 ^ k : ↥Y₀) : X) ∈ J₀ := by
      rw [Subgroup.coe_pow]
      change (y : X) ^ 2 ^ k ∈ CFSG.GroupTheory.oddOrderClosure Y₀
      exact hk
    have hpow : s ^ 2 ^ k ∈ ψ.range := by
      refine ⟨⟨((y ^ 2 ^ k : ↥Y₀) : X), hwJ⟩, ?_⟩
      rw [hψdef]
      change φ (Subgroup.inclusion hJle ⟨((y ^ 2 ^ k : ↥Y₀) : X), hwJ⟩) = s ^ 2 ^ k
      have hincl : (Subgroup.inclusion hJle
          ⟨((y ^ 2 ^ k : ↥Y₀) : X), hwJ⟩ : ↥Y₀) = y ^ 2 ^ k :=
        Subtype.ext rfl
      rw [hincl, map_pow, hφy]
    exact mem_of_odd_of_pow_mem hodd hpow
  have hrange_eq : ψ.range = S17.oUpperTwo (⊤ : Subgroup S) :=
    le_antisymm hrange_le hrange_ge
  have hkerψ : ψ.ker = CFSG.pCore 2 ↥J₀ := by
    have h1 : ψ.ker = (CFSG.pCore 2 ↥Y₀).comap (Subgroup.inclusion hJle) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap, ← hker]
      rfl
    have hPY : CFSG.pCore 2 ↥Y₀ = (CFSG.Open.pCoreOf 2 Y₀).subgroupOf Y₀ := by
      unfold CFSG.Open.pCoreOf
      exact (Subgroup.comap_map_eq_self_of_injective Y₀.subtype_injective _).symm
    have hcomap : (CFSG.pCore 2 ↥Y₀).comap (Subgroup.inclusion hJle) =
        CFSG.pCore 2 ↥J₀ := by
      rw [hPY, Subgroup.comap_inclusion_subgroupOf hJle (CFSG.Open.pCoreOf 2 Y₀)]
      rw [show (CFSG.Open.pCoreOf 2 Y₀).subgroupOf J₀ =
          (J₀ ⊓ CFSG.Open.pCoreOf 2 Y₀).subgroupOf J₀ from by
        rw [inf_comm]
        exact (Subgroup.inf_subgroupOf_right _ _).symm]
      rw [← hcore]
      unfold CFSG.Open.pCoreOf
      exact Subgroup.comap_map_eq_self_of_injective J₀.subtype_injective _
    exact h1.trans hcomap
  calc Nat.card (Bar2 J₀)
      = Nat.card (↥J₀ ⧸ ψ.ker) := by simp only [Bar2, hkerψ]
    _ = Nat.card ψ.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    _ = Nat.card (S17.oUpperTwo (⊤ : Subgroup S)) := by rw [hrange_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
