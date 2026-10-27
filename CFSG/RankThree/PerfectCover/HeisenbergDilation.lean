module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_pow_pow_of_mem_center {a b : G} (h : ⁅a, b⁆ ∈ center G) (m n : ℕ) :
    ⁅a ^ m, b ^ n⁆ = ⁅a, b⁆ ^ (m * n) := by
  have h1 : ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n :=
    (Commute.commutatorElement_pow_right (mem_center_iff.mp h b) n).symm
  have h2 : ⁅a, b ^ n⁆ ∈ center G := h1 ▸ pow_mem h n
  rw [← Commute.commutatorElement_pow_left (mem_center_iff.mp h2 a) m, h1, ← pow_mul,
    mul_comm]

theorem commutatorElement_mul_central_left {a b z : G} (hz : z ∈ center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  simpa using CFSG.SectionRank.commutatorElement_mul_mem_center a b hz (one_mem (center G))

theorem commutatorElement_mul_commute_right {a b d : G} (h : Commute a d) :
    ⁅a, b * d⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * (b * d) * a⁻¹ * (d⁻¹ * b⁻¹) = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [(h.inv_left).eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem mk_mem_center_of_mem_commutator {w : G} (hw : w ∈ commutator G) :
    (QuotientGroup.mk' ⁅commutator G, (⊤ : Subgroup G)⁆ w) ∈
      center (G ⧸ ⁅commutator G, (⊤ : Subgroup G)⁆) := by
  rw [mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have h : QuotientGroup.mk' ⁅commutator G, (⊤ : Subgroup G)⁆ ⁅w, y⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (commutator_mem_commutator hw (mem_top y))
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h.symm

theorem dilation_on_commutator {φ : G →* G} {k : ℕ}
    (hφ : ∀ x : G, (x ^ k)⁻¹ * φ x ∈ commutator G) :
    ∀ w ∈ commutator G, (w ^ (k ^ 2))⁻¹ * φ w ∈ ⁅commutator G, (⊤ : Subgroup G)⁆ := by
  set N := ⁅commutator G, (⊤ : Subgroup G)⁆ with hN
  let π := QuotientGroup.mk' N
  have hcen : ∀ w ∈ commutator G, π w ∈ center (G ⧸ N) := fun w hw =>
    mk_mem_center_of_mem_commutator hw
  have hφ' : ∀ x, π (φ x) = π x ^ k * π ((x ^ k)⁻¹ * φ x) := by
    intro x
    rw [map_mul, map_inv, map_pow]
    group
  have hS : commutator G = closure {g | ∃ g₁ ∈ (⊤ : Subgroup G), ∃ g₂ ∈ (⊤ : Subgroup G),
      ⁅g₁, g₂⁆ = g} := by
    rw [_root_.commutator_def, Subgroup.commutator_def]
  suffices key : ∀ w ∈ commutator G, π (φ w) = π w ^ (k ^ 2) by
    intro w hw
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    change π ((w ^ (k ^ 2))⁻¹ * φ w) = 1
    rw [map_mul, map_inv, map_pow, key w hw, inv_mul_cancel]
  intro w hw
  rw [hS] at hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, -, y, -, rfl⟩ := hw
    have hxy : π ⁅x, y⁆ ∈ center (G ⧸ N) :=
      hcen _ (commutator_mem_commutator (mem_top x) (mem_top y))
    rw [map_commutatorElement] at hxy
    rw [map_commutatorElement φ, map_commutatorElement π, map_commutatorElement π x y, hφ' x,
      hφ' y,
      CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hcen _ (hφ x)) (hcen _ (hφ y)),
      commutatorElement_pow_pow_of_mem_center hxy, sq]
  | one => simp
  | mul w w' hw hw' ih ih' =>
    have hc : Commute (π w) (π w') := mem_center_iff.mp (hcen w' (hS ▸ hw')) (π w)
    rw [map_mul, map_mul, ih, ih', map_mul, hc.mul_pow]
  | inv w hw ih => rw [map_inv, map_inv, map_inv, ih, inv_pow]

theorem dilation_on_third_term {φ : G →* G} {k : ℕ}
    (hφ : ∀ x : G, (x ^ k)⁻¹ * φ x ∈ commutator G)
    (hcent : ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ center G) :
    ∀ c ∈ ⁅commutator G, (⊤ : Subgroup G)⁆, φ c = c ^ (k ^ 3) := by
  have h2 := dilation_on_commutator hφ
  have hγ4 : ⁅⁅commutator G, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, coe_top, centralizer_univ]
    exact hcent
  have h22 : ⁅commutator G, commutator G⁆ = ⊥ := by
    have h := commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup G))
      (H₂ := (⊤ : Subgroup G)) (H₃ := commutator G)
      (by rw [commutator_comm (⊤ : Subgroup G) (commutator G)]; exact hγ4) hγ4
    rwa [← _root_.commutator_def] at h
  have hS : ⁅commutator G, (⊤ : Subgroup G)⁆ = closure {g | ∃ g₁ ∈ commutator G,
      ∃ g₂ ∈ (⊤ : Subgroup G), ⁅g₁, g₂⁆ = g} := Subgroup.commutator_def _ _
  intro c hc
  rw [hS] at hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨w, hw, x, -, rfl⟩ := hc
    have hz : (w ^ (k ^ 2))⁻¹ * φ w ∈ center G := hcent (h2 w hw)
    have hd : (x ^ k)⁻¹ * φ x ∈ commutator G := hφ x
    have hφw : φ w = w ^ (k ^ 2) * ((w ^ (k ^ 2))⁻¹ * φ w) := by group
    have hφx : φ x = x ^ k * ((x ^ k)⁻¹ * φ x) := by group
    have hwk : w ^ (k ^ 2) ∈ commutator G := pow_mem hw _
    have hcomm : Commute (w ^ (k ^ 2)) ((x ^ k)⁻¹ * φ x) := by
      have h0 : ⁅w ^ (k ^ 2), (x ^ k)⁻¹ * φ x⁆ = 1 := by
        have := commutator_mem_commutator hwk hd
        rwa [h22, mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp h0
    have hwx : ⁅w, x⁆ ∈ center G := hcent (commutator_mem_commutator hw (mem_top x))
    rw [map_commutatorElement, hφw, hφx, commutatorElement_mul_central_left hz,
      commutatorElement_mul_commute_right hcomm, commutatorElement_pow_pow_of_mem_center hwx,
      ← pow_succ]
  | one => simp
  | mul c c' hc hc' ih ih' =>
    have hc'z : c' ∈ center G := hcent (hS ▸ hc')
    rw [map_mul, ih, ih', (show Commute c c' from mem_center_iff.mp hc'z c).mul_pow]
  | inv c hc ih => rw [map_inv, ih, inv_pow]

theorem eq_one_of_pow_eq_self {p : ℕ} [Fact p.Prime] {c : G} (hc : ∃ j, c ^ p ^ j = 1)
    {m : ℕ} (hm : c ^ m = c) (hm1 : (m : ZMod p) ≠ 1) : c = 1 := by
  obtain ⟨j, hj⟩ := hc
  rcases m with _ | m
  · rw [pow_zero] at hm
    exact hm.symm
  · have h1 : c ^ m = 1 := by
      rw [pow_succ] at hm
      exact mul_right_cancel (hm.trans (one_mul c).symm)
    have hm' : ¬ p ∣ m := by
      intro hdvd
      apply hm1
      push_cast
      rw [(ZMod.natCast_eq_zero_iff m p).mpr hdvd, zero_add]
    have hcop : Nat.Coprime (p ^ j) m :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm')
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj)
      (orderOf_dvd_of_pow_eq_one h1))

end Commutators

variable {E : Type*} [Group E]

theorem perfect_central_prime_kernel_heisenberg_dilation_trivial' [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (_hp3 : 3 < p) (C : Subgroup E)
    (hCZ : C ≤ center E) (hCp : IsPGroup p C) (P : Sylow p E) {U : Type*} [Group U]
    (π : (P : Subgroup E) →* U) (hπ : Function.Surjective π)
    (hπker : π.ker = C.subgroupOf (P : Subgroup E))
    (hclass : (⊤ : Subgroup U).lowerCentralSeries 2 = ⊥)
    (_helem : IsElementaryAbelian p (U ⧸ commutator U))
    (a : E) (ha : a ∈ normalizer (P : Set E)) (t : (ZMod p)ˣ) (ht2 : t ^ 2 ≠ 1)
    (ht3 : t ^ 3 ≠ 1)
    (hact : ∀ x y : (P : Subgroup E), (y : E) = a * x * a⁻¹ →
      (QuotientGroup.mk (π y) : U ⧸ commutator U) =
        (QuotientGroup.mk (π x) : U ⧸ commutator U) ^ (t : ZMod p).val) :
    C = ⊥ := by
  set k := (t : ZMod p).val with hk
  have hCP : C ≤ (P : Subgroup E) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P C hCZ hCp
  let φ : (P : Subgroup E) →* (P : Subgroup E) :=
    { toFun := fun x => ⟨a * x * a⁻¹, (mem_normalizer_iff.mp ha x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hφ_apply : ∀ x : (P : Subgroup E), ((φ x : (P : Subgroup E)) : E) = a * x * a⁻¹ :=
    fun _ => rfl
  have hCcomm : C.subgroupOf (P : Subgroup E) ≤ commutator (P : Subgroup E) := by
    intro c hc
    obtain ⟨c', hc', hcc'⟩ := Subgroup.mem_map.mp
      (CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P C hCZ hCp hc)
    rwa [show c' = c from Subtype.ext hcc'] at hc'
  have hCcenter : C.subgroupOf (P : Subgroup E) ≤ center (P : Subgroup E) := by
    intro c hc
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (hCZ hc) g)
  have hφC : ∀ c ∈ C.subgroupOf (P : Subgroup E), φ c = c := by
    intro c hc
    apply Subtype.ext
    have hz : a * (c : E) = (c : E) * a := mem_center_iff.mp (hCZ hc) a
    rw [hφ_apply, hz, mul_assoc, mul_inv_cancel, mul_one]
  have hγ3 : ⁅commutator (P : Subgroup E), (⊤ : Subgroup (P : Subgroup E))⁆ ≤
      C.subgroupOf (P : Subgroup E) := by
    rw [← hπker]
    intro x hx
    have hmap := Subgroup.mem_map_of_mem π hx
    rw [map_commutator, _root_.commutator_def, map_commutator, map_top_of_surjective π hπ,
      ← _root_.commutator_def, ← Subgroup.top_lowerCentralSeries_one,
      ← Subgroup.lowerCentralSeries_succ, hclass] at hmap
    exact MonoidHom.mem_ker.mpr ((Subgroup.mem_bot).mp hmap)
  have hcommU : commutator U = (commutator (P : Subgroup E)).map π := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective π hπ]
  have hφ : ∀ x, (x ^ k)⁻¹ * φ x ∈ commutator (P : Subgroup E) := by
    intro x
    have h := hact x (φ x) rfl
    have hmem : π ((x ^ k)⁻¹ * φ x) ∈ commutator U := by
      rw [← QuotientGroup.eq_one_iff, map_mul, map_inv, map_pow, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_pow, h, inv_mul_cancel]
    have hle : (commutator U).comap π ≤ commutator (P : Subgroup E) := by
      rw [hcommU, comap_map_eq, hπker, sup_eq_left.mpr hCcomm]
    exact hle hmem
  have hpg : ∀ c : (P : Subgroup E), ∃ j, c ^ p ^ j = 1 := P.isPGroup'
  have hcast : ∀ n : ℕ, ((k ^ n : ℕ) : ZMod p) = ((t ^ n : (ZMod p)ˣ) : ZMod p) := by
    intro n
    rw [Nat.cast_pow, hk, ZMod.natCast_zmod_val, Units.val_pow_eq_pow_val]
  have hne : ∀ n : ℕ, t ^ n ≠ 1 → ((k ^ n : ℕ) : ZMod p) ≠ 1 := by
    intro n hn h1
    apply hn
    apply Units.ext
    rw [← hcast n, h1, Units.val_one]
  have hγ3bot : ⁅commutator (P : Subgroup E), (⊤ : Subgroup (P : Subgroup E))⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have h1 := dilation_on_third_term hφ (hγ3.trans hCcenter) c hc
    rw [hφC c (hγ3 hc)] at h1
    exact (Subgroup.mem_bot).mpr (eq_one_of_pow_eq_self (hpg c) h1.symm (hne 3 ht3))
  have hCbot : C.subgroupOf (P : Subgroup E) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have h1 := dilation_on_commutator hφ c (hCcomm hc)
    rw [hγ3bot, mem_bot, inv_mul_eq_one, hφC c hc] at h1
    exact (Subgroup.mem_bot).mpr (eq_one_of_pow_eq_self (hpg c) h1 (hne 2 ht2))
  rw [eq_bot_iff]
  intro c hc
  have h := hCbot ▸ (show (⟨c, hCP hc⟩ : (P : Subgroup E)) ∈ C.subgroupOf (P : Subgroup E)
    from hc)
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val ((Subgroup.mem_bot).mp h))

theorem perfect_central_prime_kernel_heisenberg_dilation_trivial [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (C : Subgroup E) [C.Normal]
    (hCZ : C ≤ center E) (hCp : IsPGroup p C) (P : Sylow p E)
    (hclass : (⊤ : Subgroup ((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E))).lowerCentralSeries
      2 = ⊥)
    (helem : IsElementaryAbelian p (((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E)) ⧸
      commutator ((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E))))
    (a : E) (ha : a ∈ normalizer (P : Set E)) (t : (ZMod p)ˣ) (ht2 : t ^ 2 ≠ 1)
    (ht3 : t ^ 3 ≠ 1)
    (hact : ∀ x y : (P : Subgroup E), (y : E) = a * x * a⁻¹ →
      ((y : (P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E)) :
          ((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E)) ⧸
            commutator ((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E))) =
        ((x : (P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E)) :
          ((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E)) ⧸
            commutator ((P : Subgroup E) ⧸ C.subgroupOf (P : Subgroup E))) ^
          (t : ZMod p).val) :
    C = ⊥ :=
  perfect_central_prime_kernel_heisenberg_dilation_trivial' hp3 C hCZ hCp P
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hclass helem
    a ha t ht2 ht3 hact

end CFSG.RankThree.PerfectCover
