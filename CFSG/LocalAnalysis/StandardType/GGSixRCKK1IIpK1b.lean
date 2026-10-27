module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpData
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAltCore
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType.RCKK1IIp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1

private def rP : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3

private def sP : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * Equiv.swap 1 3

private def tP : Fin 4 → Fin 8 := ![4, 5, 6, 7]

private def eT : Fin 4 → Equiv.Perm (Fin 8) :=
  ![1, Equiv.swap 4 5 * Equiv.swap 6 7, Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 4 7 * Equiv.swap 5 6]

private def v0 : Fin 4 → Equiv.Perm (Fin 8) := ![1, rP, sP, rP * sP]

private def cyc3 : Fin 4 → Equiv.Perm (Fin 8) :=
  ![Equiv.swap 4 5 * Equiv.swap 5 6, Equiv.swap 4 5 * Equiv.swap 5 7,
    Equiv.swap 4 6 * Equiv.swap 6 7, Equiv.swap 5 6 * Equiv.swap 6 7]

private abbrev inC (σ : Equiv.Perm (Fin 8)) : Prop := σ * rP * σ⁻¹ = rP

private abbrev inP (σ : Equiv.Perm (Fin 8)) : Prop :=
  inC σ ∧ ∃ j : Fin 4, ∀ i : Fin 4, σ (tP i) = eT j (tP i)

private lemma rckIIpK_v0_one : v0 1 = rP := rfl

private lemma rckIIpK_v0_two : v0 2 = sP := rfl

private lemma rckIIpK_v0_three : v0 3 = rP * sP := rfl

private abbrev presS (σ : Equiv.Perm (Fin 8)) : Prop := σ 0 < 4 ∧ σ 1 < 4 ∧ σ 2 < 4 ∧ σ 3 < 4

private lemma rckIIpK_rP_fix_T : ∀ y : Fin 8, 4 ≤ y → rP y = y := by decide +kernel

private lemma rckIIpK_rP_ne_S : ∀ x : Fin 8, x < 4 → rP x ≠ x := by decide +kernel

private lemma rckIIpK_presS_of_inC {σ : Equiv.Perm (Fin 8)} (h : inC σ) : presS σ := by
  have hcomm : σ * rP = rP * σ := by
    have := congrArg (fun τ => τ * σ) h
    simpa [mul_assoc] using this
  have hpt : ∀ x, σ (rP x) = rP (σ x) := fun x => congrFun (congrArg DFunLike.coe hcomm) x
  have key : ∀ x : Fin 8, x < 4 → σ x < 4 := by
    intro x hx4
    by_contra h4
    have h4' : 4 ≤ σ x := not_lt.mp h4
    have hfix : rP (σ x) = σ x := rckIIpK_rP_fix_T (σ x) h4'
    have := hpt x
    rw [hfix] at this
    exact rckIIpK_rP_ne_S x hx4 (σ.injective this)
  exact ⟨key 0 (by decide), key 1 (by decide), key 2 (by decide), key 3 (by decide)⟩

private def CList : List (Equiv.Perm (Fin 8)) :=
  ((permsOfList (List.finRange 8)).filter (fun σ => decide (presS σ))).filter
    (fun σ => decide (inC σ))

private lemma mem_CList {σ : Equiv.Perm (Fin 8)} (h : inC σ) : σ ∈ CList := by
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · refine List.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_permsOfList_iff.mpr (fun {x} _ => List.mem_finRange x)
    · rw [decide_eq_true_eq]; exact rckIIpK_presS_of_inC h
  · rw [decide_eq_true_eq]; exact h

private lemma rckIIpK_multiset_le_sum {s : Multiset ℕ} {a : ℕ} (h : a ∈ s) : a ≤ s.sum := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro h; simp at h
  · intro b s ih h
    rw [Multiset.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := ih h
      simp only [Multiset.sum_cons]
      omega

private lemma rckIIpK_pow_eight_of_pow_128 {σ : Equiv.Perm (Fin 8)} (h : σ ^ 128 = 1) :
    σ ^ 8 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one] at h ⊢
  rw [← Equiv.Perm.lcm_cycleType] at h ⊢
  rw [Multiset.lcm_dvd] at h ⊢
  intro n hn
  have hndvd : n ∣ 2 ^ 7 := h n hn
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hndvd
  have hle : 2 ^ j ≤ 8 := by
    have h1 : 2 ^ j ≤ σ.cycleType.sum := rckIIpK_multiset_le_sum hn
    rw [Equiv.Perm.sum_cycleType] at h1
    exact h1.trans (Finset.card_le_univ _)
  have hj3 : j ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ j := by omega
    have h16 : 16 ≤ 2 ^ j := by
      have := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) h4
      simpa using this
    omega
  exact pow_dvd_pow 2 hj3

private lemma rckIIpK_S8_witness (σ : Equiv.Perm (Fin 8)) (hC : inC σ) (hnot : ¬ inP σ)
    (h8 : σ ^ 8 = 1) :
    ∃ j : Fin 4, (cyc3 j * σ * (cyc3 j)⁻¹ * σ⁻¹) ^ 3 = 1 ∧
      cyc3 j * σ * (cyc3 j)⁻¹ * σ⁻¹ ≠ 1 := by
  have hcheck : CList.all (fun τ => decide (inC τ → ¬ inP τ → τ ^ 8 = 1 →
      ∃ j : Fin 4, (cyc3 j * τ * (cyc3 j)⁻¹ * τ⁻¹) ^ 3 = 1 ∧
        cyc3 j * τ * (cyc3 j)⁻¹ * τ⁻¹ ≠ 1)) = true := by
    decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) σ (mem_CList hC)) hC hnot h8

private lemma rckIIpK_S8_P_comm (σ : Equiv.Perm (Fin 8)) (hP : inP σ) (j : Fin 4) :
    σ * v0 j * σ⁻¹ * (v0 j)⁻¹ = 1 ∨ σ * v0 j * σ⁻¹ * (v0 j)⁻¹ = rP := by
  have hcheck : CList.all (fun τ => decide (inP τ → ∀ j : Fin 4,
      τ * v0 j * τ⁻¹ * (v0 j)⁻¹ = 1 ∨ τ * v0 j * τ⁻¹ * (v0 j)⁻¹ = rP)) = true := by
    decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) σ (mem_CList hP.1)) hP j

private lemma rckIIpK_rA8_coe : (rA8 : Equiv.Perm (Fin 8)) = rP := rfl

private lemma rckIIpK_sA8_coe : (sA8 : Equiv.Perm (Fin 8)) = sP := rfl

private lemma rckIIpK_mem_vA8 {v : alternatingGroup (Fin 8)} :
    v ∈ vA8 ↔ v = 1 ∨ v = rA8 ∨ v = sA8 ∨ v = rA8 * sA8 := by
  constructor
  · intro hv
    rw [vA8] at hv
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ x = rA8 ∨ x = sA8 ∨ x = rA8 * sA8)
      ?_ ?_ ?_ ?_ hv
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · rintro x y hx hy (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
        decide +kernel
    · rintro x hx (rfl | rfl | rfl | rfl) <;>
        decide +kernel
  · rintro (h | h | h | h)
    · rw [h, vA8]; exact Subgroup.one_mem _
    · rw [h, vA8]; exact Subgroup.subset_closure (by simp)
    · rw [h, vA8]; exact Subgroup.subset_closure (by simp)
    · rw [h, vA8]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private lemma rckIIpK_cyc3_mem (j : Fin 4) : cyc3 j ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases j <;> simp [cyc3, map_mul, Equiv.Perm.sign_swap]

private lemma rckIIpK_cyc3_comm (j : Fin 4) :
    (⟨cyc3 j, rckIIpK_cyc3_mem j⟩ : alternatingGroup (Fin 8)) * rA8 =
      rA8 * ⟨cyc3 j, rckIIpK_cyc3_mem j⟩ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [rckIIpK_rA8_coe]
  fin_cases j <;> decide +kernel

private lemma rckIIpK_no_order_three {Y : Subgroup (Equiv.Perm (Fin 8))} (hY : IsPGroup 2 Y)
    {a : Equiv.Perm (Fin 8)} (ha : a ∈ Y) (h3 : a ^ 3 = 1) (hne : a ≠ 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_orderOf_eq_pow (⟨a, ha⟩ : Y)
  have hkσ : orderOf a = 2 ^ k := by rw [← Subgroup.orderOf_mk a ha, hk]
  have hdvd3 : orderOf a ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr h3
  rw [hkσ] at hdvd3
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have : 2 ^ 2 ∣ 3 := (pow_dvd_pow 2 h2).trans hdvd3
    norm_num at this
  interval_cases k
  · rw [pow_zero] at hkσ
    exact hne (orderOf_eq_one_iff.mp hkσ)
  · rw [pow_one] at hdvd3
    norm_num at hdvd3

theorem rckIIp_S8_core (Y : Subgroup (Equiv.Perm (Fin 8))) (hY : IsPGroup 2 Y)
    (hfix : ∀ σ ∈ Y, σ * (rA8 : Equiv.Perm (Fin 8)) * σ⁻¹ = (rA8 : Equiv.Perm (Fin 8)))
    (hnorm : ∀ c : alternatingGroup (Fin 8), c * rA8 = rA8 * c →
      ∀ σ ∈ Y, (c : Equiv.Perm (Fin 8)) * σ * (c : Equiv.Perm (Fin 8))⁻¹ ∈ Y) :
    ∀ v ∈ vA8, ∀ σ ∈ Y, σ * (v : Equiv.Perm (Fin 8)) * σ⁻¹ * (v : Equiv.Perm (Fin 8))⁻¹ ∈
      Subgroup.zpowers (rA8 : Equiv.Perm (Fin 8)) := by
  intro v hv σ hσ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσinC : inC σ := by
    have h := hfix σ hσ
    rw [rckIIpK_rA8_coe] at h
    exact h
  have hσ128 : σ ^ 128 = 1 := by
    obtain ⟨k, hk⟩ := hY.exists_orderOf_eq_pow (⟨σ, hσ⟩ : Y)
    have hkσ : orderOf σ = 2 ^ k := by rw [← Subgroup.orderOf_mk σ hσ, hk]
    have hdvd : orderOf σ ∣ Nat.card (Equiv.Perm (Fin 8)) := orderOf_dvd_natCard σ
    have hcard : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num
    rw [hcard] at hdvd
    have hdvd' : 2 ^ k ∣ 40320 := hkσ ▸ hdvd
    have hk7 : k ≤ 7 := by
      by_contra h
      have hk8 : 8 ≤ k := by omega
      have : 2 ^ 8 ∣ 40320 := (pow_dvd_pow 2 hk8).trans hdvd'
      norm_num at this
    have hdvd128 : orderOf σ ∣ 128 := by
      rw [hkσ]; exact pow_dvd_pow 2 hk7
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd128
  have hσ8 : σ ^ 8 = 1 := rckIIpK_pow_eight_of_pow_128 hσ128
  have hσP : inP σ := by
    by_contra hnot
    obtain ⟨j, h3, hne⟩ := rckIIpK_S8_witness σ hσinC hnot hσ8
    have hmem : (cyc3 j : Equiv.Perm (Fin 8)) * σ * (cyc3 j : Equiv.Perm (Fin 8))⁻¹ ∈ Y := by
      have h := hnorm ⟨cyc3 j, rckIIpK_cyc3_mem j⟩ (rckIIpK_cyc3_comm j) σ hσ
      simpa using h
    exact rckIIpK_no_order_three hY (Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hσ)) h3 hne
  have hP := rckIIpK_S8_P_comm σ hσP
  have hP1 : σ * rP * σ⁻¹ * rP⁻¹ = 1 ∨ σ * rP * σ⁻¹ * rP⁻¹ = rP := by
    simpa only [rckIIpK_v0_one] using hP 1
  have hP2 : σ * sP * σ⁻¹ * sP⁻¹ = 1 ∨ σ * sP * σ⁻¹ * sP⁻¹ = rP := by
    simpa only [rckIIpK_v0_two] using hP 2
  have hP3 : σ * (rP * sP) * σ⁻¹ * (rP * sP)⁻¹ = 1 ∨
      σ * (rP * sP) * σ⁻¹ * (rP * sP)⁻¹ = rP := by
    simpa only [rckIIpK_v0_three] using hP 3
  rw [rckIIpK_rA8_coe]
  rcases rckIIpK_mem_vA8.mp hv with hv1 | hvr | hvs | hvrs
  · rw [hv1]; simp
  · have hv' : (v : Equiv.Perm (Fin 8)) = rP := by rw [hvr, rckIIpK_rA8_coe]
    rw [hv']
    rcases hP1 with h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · have hv' : (v : Equiv.Perm (Fin 8)) = sP := by rw [hvs, rckIIpK_sA8_coe]
    rw [hv']
    rcases hP2 with h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · have hv' : (v : Equiv.Perm (Fin 8)) = rP * sP := by
      rw [hvrs]
      push_cast
      rw [rckIIpK_rA8_coe, rckIIpK_sA8_coe]
    rw [hv']
    rcases hP3 with h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private lemma rckIIpK_congr_refl {G : Type*} [Group G] (α : MulAut G) :
    MulAut.congr (MulEquiv.refl G) α = α := by
  ext x
  rfl

private lemma rckIIpK_autPermN_conjNormal {S : Type} [Group S] {n : ℕ}
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : S ≃* alternatingGroup (Fin n)) (φ : MulAut S) :
    MulAut.conjNormal (H := alternatingGroup (Fin n))
        (CFSG.ComponentClassification.FooteLit.AltCore.autPermN hn hn6 e φ) =
      MulAut.congr e φ := by
  rw [CFSG.ComponentClassification.FooteLit.AltCore.autPermN, MulEquiv.trans_apply,
    ← MulEquiv.ofBijective_apply _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6),
    MulEquiv.apply_symm_apply]

private noncomputable def rckIIpK_autA8 : MulAut (alternatingGroup (Fin 8)) ≃* Equiv.Perm (Fin 8) :=
  CFSG.ComponentClassification.FooteLit.AltCore.autPermN (n := 8) (by norm_num) (by norm_num)
    (MulEquiv.refl (alternatingGroup (Fin 8)))

private lemma rckIIpK_autA8_conjNormal (φ : MulAut (alternatingGroup (Fin 8))) :
    MulAut.conjNormal (H := alternatingGroup (Fin 8)) (rckIIpK_autA8 φ) =
      MulAut.congr (MulEquiv.refl (alternatingGroup (Fin 8))) φ :=
  rckIIpK_autPermN_conjNormal (n := 8) (by norm_num) (by norm_num)
    (MulEquiv.refl (alternatingGroup (Fin 8))) φ

private lemma rckIIpK_autA8_conj (c : alternatingGroup (Fin 8)) :
    rckIIpK_autA8 (MulAut.conj c) = (c : Equiv.Perm (Fin 8)) := by
  have hc : MulAut.conj c = MulAut.conjNormal (H := alternatingGroup (Fin 8))
      (c : Equiv.Perm (Fin 8)) := by
    ext x : 1
    rfl
  rw [hc]
  have h := rckIIpK_autA8_conjNormal
    (MulAut.conjNormal (H := alternatingGroup (Fin 8)) (c : Equiv.Perm (Fin 8)))
  rw [rckIIpK_congr_refl] at h
  exact (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)).1 h

theorem rckIIp_A8_K1b : K1Lift.K1b rA8 vA8 := by
  intro Y hY hfix hnorm v hv φ hφ
  let Ys : Subgroup (Equiv.Perm (Fin 8)) := Y.map rckIIpK_autA8.toMonoidHom
  have hYmap : IsPGroup 2 Ys := hY.map rckIIpK_autA8.toMonoidHom
  have hfix' : ∀ σ ∈ Ys, σ * (rA8 : Equiv.Perm (Fin 8)) * σ⁻¹ =
      (rA8 : Equiv.Perm (Fin 8)) := by
    intro σ hσ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hσ
    have h := congrArg (fun α : MulAut (alternatingGroup (Fin 8)) => α rA8)
      (rckIIpK_autA8_conjNormal ψ)
    rw [rckIIpK_congr_refl, hfix ψ hψ] at h
    have h2 := congrArg (fun x : alternatingGroup (Fin 8) => (x : Equiv.Perm (Fin 8))) h
    simpa [MulAut.conjNormal_apply] using h2
  have hnorm' : ∀ c : alternatingGroup (Fin 8), c * rA8 = rA8 * c →
      ∀ σ ∈ Ys, (c : Equiv.Perm (Fin 8)) * σ * (c : Equiv.Perm (Fin 8))⁻¹ ∈ Ys := by
    intro c hc σ hσ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hσ
    have hmem : MulAut.conj c * ψ * (MulAut.conj c)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hnorm c hc) ψ).mp hψ
    have hΦc : rckIIpK_autA8 (MulAut.conj c) = (c : Equiv.Perm (Fin 8)) :=
      rckIIpK_autA8_conj c
    have hthis : rckIIpK_autA8 (MulAut.conj c * ψ * (MulAut.conj c)⁻¹) ∈ Ys :=
      Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    rwa [map_mul, map_mul, map_inv, hΦc] at hthis
  have hcore := rckIIp_S8_core Ys hYmap hfix' hnorm'
  have hσY : rckIIpK_autA8 φ ∈ Ys := Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  have hmem := hcore v hv (rckIIpK_autA8 φ) hσY
  have hφv : ((φ v : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
      rckIIpK_autA8 φ * (v : Equiv.Perm (Fin 8)) * (rckIIpK_autA8 φ)⁻¹ := by
    have h := congrArg (fun α : MulAut (alternatingGroup (Fin 8)) =>
      ((α v : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8))) (rckIIpK_autA8_conjNormal φ)
    rw [rckIIpK_congr_refl] at h
    simpa [MulAut.conjNormal_apply] using h.symm
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  apply Subtype.ext
  push_cast
  rw [hφv, hk]

end CFSG.StandardType.RCKK1IIp
