module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapBase
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapLemmaC
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveGrp
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFivePerm
public import CFSG.LocalAnalysis.WeakClosure81.CentralInSylowIndexReverse

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup CFSG.Timmesfeld.Bridge.Asc72

private theorem w85g_orderOf_mul_of_commuting_involutions {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x) (hne : x * y ≠ 1) :
    orderOf (x * y) = 2 := by
  have hcomm : Commute x y := hc
  have hpow : (x * y) ^ 2 = 1 := by
    rw [hcomm.mul_pow 2, pow_two, pow_two, hx, hy]
    simp
  exact orderOf_eq_prime hpow hne

private theorem w85g_mul_self_eq_one_of_oddTransp {G : Type*} [Group G] {D : Set G} {u e : G}
    (hD : IsOddTransp D) (hu : u ∈ D) (he : e ∈ D) (h2 : 2 ∣ orderOf (u * e)) :
    (u * e) * (u * e) = 1 := by
  rcases hD.2 u hu e he with hdvd | hodd
  · rwa [orderOf_dvd_iff_pow_eq_one, pow_two] at hdvd
  · exact absurd h2 hodd.not_two_dvd_nat

private theorem w85g_conj_mul_self {G : Type*} [Group G] {u v : G} (hv : v * v = 1) :
    (u * v * u⁻¹) * (u * v * u⁻¹) = 1 := by
  rw [show (u * v * u⁻¹) * (u * v * u⁻¹) = u * (v * v) * u⁻¹ by group, hv]
  simp

structure Gap5YHyp {n : ℕ} {Y : Type} [Group Y] (π : Y →* Perm (Fin n)) (t : Y)
    (b : MulAut Y) : Prop where
  surjective : Function.Surjective π
  odd_ker : Odd (Nat.card π.ker)
  max : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N ≤ π.ker
  mul_self : t * t = 1
  oddTranspClass : IsOddTranspClass {y : Y | IsConj t y}
  central : CentralInSylow Y (Subgroup.zpowers t)
  b_ne_one : b ≠ 1
  b_mul_self : b * b = 1
  b_apply : b t = t
  b_ker : ∀ o ∈ π.ker, b o = o

namespace Gap5YHyp

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {π : Y →* Perm (Fin n)} {t : Y} {b : MulAut Y}

theorem two_lt (h : Gap5YHyp π t b) : 2 < n := by
  by_contra hle
  rw [not_lt] at hle
  have ht2 : orderOf t = 2 := h.oddTranspClass.2.1.orderOf_eq_two (IsConj.refl t)
  interval_cases n
  · have hmem : t ∈ π.ker := MonoidHom.mem_ker.mpr (Subsingleton.elim (π t) 1)
    have h2 : 2 ∣ Nat.card π.ker := by
      have h1 := Subgroup.orderOf_dvd_natCard π.ker hmem
      rwa [ht2] at h1
    exact absurd h2 h.odd_ker.not_two_dvd_nat
  · have hmem : t ∈ π.ker := MonoidHom.mem_ker.mpr (Subsingleton.elim (π t) 1)
    have h2 : 2 ∣ Nat.card π.ker := by
      have h1 := Subgroup.orderOf_dvd_natCard π.ker hmem
      rwa [ht2] at h1
    exact absurd h2 h.odd_ker.not_two_dvd_nat
  · have hpt_ne : π t ≠ 1 := by
      intro hpt
      have hmem : t ∈ π.ker := MonoidHom.mem_ker.mpr hpt
      have h2 : 2 ∣ Nat.card π.ker := by
        have h1 := Subgroup.orderOf_dvd_natCard π.ker hmem
        rwa [ht2] at h1
      exact absurd h2 h.odd_ker.not_two_dvd_nat
    have hcases : ∀ σ : Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap 0 1 := by decide
    have hπt : π t = Equiv.swap 0 1 := by
      rcases hcases (π t) with hh | hh
      · exact absurd hh hpt_ne
      · exact hh
    refine h.b_ne_one (MulEquiv.ext fun y => ?_)
    show b y = y
    rcases hcases (π y) with hy | hy
    · exact h.b_ker y (MonoidHom.mem_ker.mpr hy)
    · have hty : π (t⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hπt, hy]
        simp
      have hker : t⁻¹ * y ∈ π.ker := MonoidHom.mem_ker.mpr hty
      have hb := h.b_ker (t⁻¹ * y) hker
      rw [map_mul, map_inv, h.b_apply] at hb
      exact mul_left_cancel hb

theorem ne_three (h : Gap5YHyp π t b) : n ≠ 3 := by
  rintro rfl
  have hNnormal : ((alternatingGroup (Fin 3)).comap π).Normal := inferInstance
  have hAindex : (alternatingGroup (Fin 3)).index = 2 :=
    alternatingGroup.index_eq_two
  have hNindex : ((alternatingGroup (Fin 3)).comap π).index = 2 := by
    rw [Subgroup.index_comap_of_surjective (alternatingGroup (Fin 3)) h.surjective, hAindex]
  have hAcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hYcard : Nat.card Y = Nat.card π.ker * 6 := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top.mpr h.surjective, Subgroup.card_top, Nat.card_perm,
      Nat.card_fin] at h1
    norm_num at h1
    exact h1.symm
  have hNcard : Nat.card ((alternatingGroup (Fin 3)).comap π) = 3 * Nat.card π.ker := by
    have h1 := Subgroup.card_mul_index ((alternatingGroup (Fin 3)).comap π)
    rw [hNindex, hYcard] at h1
    omega
  have hNodd : Odd (Nat.card ((alternatingGroup (Fin 3)).comap π)) := by
    rw [hNcard, Nat.mul_comm]
    exact h.odd_ker.mul (by decide : Odd 3)
  have hNle : (alternatingGroup (Fin 3)).comap π ≤ π.ker := h.max _ hNnormal hNodd
  have hAle : alternatingGroup (Fin 3) ≤ ⊥ := by
    have h1 : ((alternatingGroup (Fin 3)).comap π).map π ≤ π.ker.map π :=
      Subgroup.map_mono hNle
    rwa [Subgroup.map_comap_eq_self_of_surjective h.surjective (alternatingGroup (Fin 3)),
      (Subgroup.map_eq_bot_iff _).mpr le_rfl] at h1
  have h1 : Nat.card (alternatingGroup (Fin 3)) = 1 := by
    rw [le_bot_iff.mp hAle, Subgroup.card_bot]
  rw [hAcard] at h1
  norm_num at h1

theorem sign_eq (h : Gap5YHyp π t b) (hn : 2 ≤ n) : Perm.sign (π t) = -1 := by
  by_contra hne
  have h1 : Perm.sign (π t) = 1 := by
    rcases Int.units_eq_one_or (Perm.sign (π t)) with h1 | h1
    · exact h1
    · exact absurd h1 hne
  have hmem : π t ∈ alternatingGroup (Fin n) := mem_alternatingGroup.mpr h1
  have hDsub : {y : Y | IsConj t y} ⊆ (alternatingGroup (Fin n)).comap π := by
    intro y hy
    refine Subgroup.mem_comap.mpr ?_
    obtain ⟨u, rfl⟩ := isConj_iff.mp hy
    rw [mem_alternatingGroup]
    rw [show π (u * t * u⁻¹) = π u * π t * (π u)⁻¹ by rw [map_mul, map_mul, map_inv]]
    rw [map_mul, map_mul, map_inv, h1]
    simp
  have htop : (⊤ : Subgroup Y) ≤ (alternatingGroup (Fin n)).comap π := by
    rw [← h.oddTranspClass.2.2]
    exact (Subgroup.closure_le _).mpr hDsub
  have hall : alternatingGroup (Fin n) = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨y, rfl⟩ := h.surjective σ
    exact Subgroup.mem_comap.mp (htop (Subgroup.mem_top y))
  have hcard : 1 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (α := Fin n) hcard
  have hsa : Equiv.swap a c ∈ alternatingGroup (Fin n) := by
    rw [hall]
    exact Subgroup.mem_top _
  rw [mem_alternatingGroup, Equiv.Perm.sign_swap hac] at hsa
  exact absurd hsa (by decide)

theorem not_four_or_five (h : Gap5YHyp π t b) (hn : 2 ≤ n) : ¬ (n = 4 ∨ n = 5) := by
  have hpt2 : π t * π t = 1 := by rw [← map_mul, h.mul_self, map_one]
  have hmap := centralInSylow_map π h.surjective (Subgroup.zpowers t) h.central
  rw [MonoidHom.map_zpowers] at hmap
  have hodd := (centralInSylow_zpowers_iff_odd_index (π t) hpt2).mp hmap
  rintro (rfl | rfl)
  · exact gap5Perm_not_odd_index_four_five (Or.inl rfl) hpt2 (h.sign_eq (by omega)) hodd
  · exact gap5Perm_not_odd_index_four_five (Or.inr rfl) hpt2 (h.sign_eq (by omega)) hodd

theorem six_le (h : Gap5YHyp π t b) : 6 ≤ n := by
  have h2 := h.two_lt
  have h3 := h.ne_three
  have h45 := h.not_four_or_five (by omega)
  omega

theorem centralizer_not_le (h : Gap5YHyp π t b) :
    ¬ Subgroup.centralizer (π.ker : Set Y) ≤ π.ker := fun hC =>
  h.b_ne_one (gap5Grp_eq_one_of_fixes_normal_odd h.odd_ker hC h.b_mul_self h.b_ker)

theorem exists_lift (h : Gap5YHyp π t b) (hn : 6 ≤ n) :
    ∃ c ∈ Subgroup.centralizer (π.ker : Set Y), π (c * t * c⁻¹) ≠ π t ∧
      π t * π (c * t * c⁻¹) = π (c * t * c⁻¹) * π t := by
  have hMnormal : ((Subgroup.centralizer (π.ker : Set Y)).map π).Normal :=
    (inferInstance : (Subgroup.centralizer (π.ker : Set Y)).Normal).map π h.surjective
  haveI := hMnormal
  have hnt : Nontrivial ((Subgroup.centralizer (π.ker : Set Y)).map π) := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    by_contra hcon
    apply h.centralizer_not_le
    intro c hc
    rw [MonoidHom.mem_ker]
    by_contra hne
    exact hcon ⟨π c, Subgroup.mem_map.mpr ⟨c, hc, rfl⟩, hne⟩
  have hAle : alternatingGroup (Fin n) ≤ (Subgroup.centralizer (π.ker : Set Y)).map π :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin n) (by rw [Nat.card_fin]; omega) hnt
  have hpt2 : π t * π t = 1 := by rw [← map_mul, h.mul_self, map_one]
  obtain ⟨c₀, hc₀A, hne, hcomm⟩ :=
    gap5Perm_exists_commuting_conj (n := n) (by omega) hpt2 (h.sign_eq (by omega))
  obtain ⟨c, hcC, hπc⟩ := Subgroup.mem_map.mp (hAle hc₀A)
  refine ⟨c, hcC, ?_, ?_⟩
  · have h1 : π (c * t * c⁻¹) = c₀ * π t * c₀⁻¹ := by
      simp only [map_mul, map_inv, hπc]
    rw [h1]
    exact hne
  · have h1 : π (c * t * c⁻¹) = c₀ * π t * c₀⁻¹ := by
      simp only [map_mul, map_inv, hπc]
    rw [h1]
    exact hcomm

theorem mem_centralizer_ker (h : Gap5YHyp π t b) (hn : 6 ≤ n) :
    t ∈ Subgroup.centralizer (π.ker : Set Y) := by
  obtain ⟨c, hcC, hne, hcomm⟩ := h.exists_lift hn
  have htD : t ∈ {y : Y | IsConj t y} := IsConj.refl t
  have ht'D : c * t * c⁻¹ ∈ {y : Y | IsConj t y} := isConj_iff.mpr ⟨c, rfl⟩
  have hπt : π t * π t = 1 := by rw [← map_mul, h.mul_self, map_one]
  have ht'inv : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := w85g_conj_mul_self h.mul_self
  have hπt'inv : π (c * t * c⁻¹) * π (c * t * c⁻¹) = 1 := by
    rw [← map_mul, ht'inv, map_one]
  have hπne : π t * π (c * t * c⁻¹) ≠ 1 := by
    intro hh
    have h1 : π (c * t * c⁻¹) = (π t)⁻¹ := eq_inv_of_mul_eq_one_right hh
    have h2 : (π t)⁻¹ = π t := (eq_inv_of_mul_eq_one_right hπt).symm
    exact hne (h1.trans h2)
  have hπord : orderOf (π t * π (c * t * c⁻¹)) = 2 :=
    w85g_orderOf_mul_of_commuting_involutions hπt hπt'inv hcomm hπne
  have h2a : 2 ∣ orderOf (t * (c * t * c⁻¹)) := by
    have h1 := orderOf_map_dvd π (t * (c * t * c⁻¹))
    rw [map_mul, hπord] at h1
    exact h1
  have h0 : (t * (c * t * c⁻¹)) * (t * (c * t * c⁻¹)) = 1 :=
    w85g_mul_self_eq_one_of_oddTransp h.oddTranspClass.2.1 htD ht'D h2a
  have hq : ∀ q ∈ π.ker,
      (t * (q * (c * t * c⁻¹) * q⁻¹)) * (t * (q * (c * t * c⁻¹) * q⁻¹)) = 1 := by
    intro q hq
    have hqD : q * (c * t * c⁻¹) * q⁻¹ ∈ {y : Y | IsConj t y} := by
      refine isConj_iff.mpr ⟨q * c, ?_⟩
      group
    have hπq : π q = 1 := MonoidHom.mem_ker.mp hq
    have hπe : π (q * (c * t * c⁻¹) * q⁻¹) = π (c * t * c⁻¹) := by
      conv_lhs => rw [map_mul, map_mul, map_inv, hπq]
      simp
    have h2q : 2 ∣ orderOf (t * (q * (c * t * c⁻¹) * q⁻¹)) := by
      have h1 := orderOf_map_dvd π (t * (q * (c * t * c⁻¹) * q⁻¹))
      rw [map_mul, hπe, hπord] at h1
      exact h1
    exact w85g_mul_self_eq_one_of_oddTransp h.oddTranspClass.2.1 htD hqD h2q
  exact gap5Grp_mem_centralizer_of_involution h.odd_ker h.mul_self hcC h0 hq

theorem ker_eq_bot (h : Gap5YHyp π t b) (hn : 6 ≤ n) : π.ker = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have htC : t ∈ Subgroup.centralizer (π.ker : Set Y) := h.mem_centralizer_ker (by omega)
  have hCnormal : (Subgroup.centralizer (π.ker : Set Y)).Normal := inferInstance
  have hDsub : {y : Y | IsConj t y} ⊆ Subgroup.centralizer (π.ker : Set Y) := by
    intro y hy
    obtain ⟨u, rfl⟩ := isConj_iff.mp hy
    exact hCnormal.conj_mem t htC u
  have htop : (⊤ : Subgroup Y) ≤ Subgroup.centralizer (π.ker : Set Y) := by
    rw [← h.oddTranspClass.2.2]
    exact (Subgroup.closure_le _).mpr hDsub
  have hcenter : π.ker ≤ Subgroup.center Y := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top y)) z hz).symm
  have hinv : Subgroup.closure {y : Y | y * y = 1} = ⊤ := by
    rw [eq_top_iff, ← h.oddTranspClass.2.2]
    exact Subgroup.closure_mono fun y hy => h.oddTranspClass.2.1.mul_self_eq_one hy
  exact ker_eq_bot_of_closure_involutions π hcenter h.odd_ker h.surjective hinv

theorem isSwap (h : Gap5YHyp π t b) (hn : 7 ≤ n) : (π t).IsSwap := by
  by_contra hns
  have hns' : ∀ i j : Fin n, i ≠ j → π t ≠ Equiv.swap i j := by
    intro i j hij hh
    exact hns ⟨i, j, hij, hh⟩
  have hpt2 : π t * π t = 1 := by rw [← map_mul, h.mul_self, map_one]
  obtain ⟨σ, hσ⟩ :=
    gap5Perm_exists_conj_orderOf_eq_six (n := n) hn hpt2 (h.sign_eq (by omega)) hns'
  obtain ⟨y, hy⟩ := h.surjective σ
  have htD : t ∈ {z : Y | IsConj t z} := IsConj.refl t
  have hyD : y * t * y⁻¹ ∈ {z : Y | IsConj t z} := isConj_iff.mpr ⟨y, rfl⟩
  have hπy : π (y * t * y⁻¹) = σ * π t * σ⁻¹ := by
    rw [map_mul, map_mul, map_inv, hy]
  have hπw : π (t * (y * t * y⁻¹)) = π t * (σ * π t * σ⁻¹) := by
    rw [map_mul, hπy]
  have h6 : 6 ∣ orderOf (t * (y * t * y⁻¹)) := by
    have h1 := orderOf_map_dvd π (t * (y * t * y⁻¹))
    rw [hπw, hσ] at h1
    exact h1
  have h2 : 2 ∣ orderOf (t * (y * t * y⁻¹)) := dvd_trans (by decide : 2 ∣ 6) h6
  rcases h.oddTranspClass.2.1.2 t htD (y * t * y⁻¹) hyD with hdvd | hodd
  · have h1 : 6 ∣ 2 := dvd_trans h6 hdvd
    norm_num at h1
  · exact absurd h2 hodd.not_two_dvd_nat

end Gap5YHyp

theorem gap5_Y {n : ℕ} {Y : Type} [Group Y] [Finite Y] {π : Y →* Perm (Fin n)} {t : Y}
    {b : MulAut Y} (h : Gap5YHyp π t b) :
    π.ker = ⊥ ∧ 6 ≤ n ∧ (7 ≤ n → (π t).IsSwap) :=
  ⟨h.ker_eq_bot h.six_le, h.six_le, fun h7 => h.isSwap h7⟩

end CFSG.LocalAnalysis.WeakClosure81

end
