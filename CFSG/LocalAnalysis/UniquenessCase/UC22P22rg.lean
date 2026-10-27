module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22p22r_fo_mem_of_pow_mem {G : Type*} [Group G] {q : ℕ} (hq : q.Prime) {x : G} (hx : orderOf x = q)
    {N : Subgroup G} {m : ℕ} (hm : 0 < m) (hmq : m < q) (hxm : x ^ m ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime m (orderOf x) :=
    hx ▸ ((Nat.Prime.coprime_iff_not_dvd hq).2 (Nat.not_dvd_of_pos_of_lt hm hmq)).symm
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
  exact ha ▸ N.pow_mem hxm a

theorem uc22p22r_fo_norm_exists {Q : Type*} [Group Q] {q : ℕ} (hq : 0 < q) {x : Q} (hx : x ^ q = 1)
    {κ : Subgroup Q} {k : Q} (hk : k ∈ κ)
    (hcomm : ∀ m, 0 < m → m < q → ∀ y ∈ κ, Commute y (x ^ m * k * (x ^ m)⁻¹)) :
    ∃ d : Q, x * d * x⁻¹ = d ∧ ∀ s ∈ κ, d * s * d⁻¹ = k * s * k⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Q, c = fun i => x ^ i * k * (x ^ i)⁻¹ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Q, e = ((List.range n).map fun i => c (i + 1)).prod := ⟨_, rfl⟩
  have hc0 : c 0 = k := by simp [hc]
  have hcq : c (n + 1) = k := by simp [hc, hx]
  have hcomm' : ∀ y ∈ κ, Commute y e := fun y hy => by
    rw [he]
    refine Commute.list_prod_right _ _ fun z hz => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
    have hi' := List.mem_range.1 hi
    simpa [hc] using hcomm (i + 1) (Nat.succ_pos i) (Nat.succ_lt_succ hi') y hy
  have hprod : ((List.range (n + 1)).map c).prod = k * e := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, hc0, he]
    rfl
  have hstep : ∀ i, x * c i * x⁻¹ = c (i + 1) := fun i => by
    simp only [hc, pow_succ', mul_inv_rev, mul_assoc]
  have hconj : x * ((List.range (n + 1)).map c).prod * x⁻¹ = e * k := by
    have h1 := map_list_prod (MulAut.conj x) ((List.range (n + 1)).map c)
    simp only [MulAut.conj_apply, List.map_map, Function.comp_def, hstep] at h1
    rw [h1, List.range_succ, List.map_append, List.prod_append, he, List.map_singleton,
      List.prod_singleton, hcq]
  refine ⟨k * e, ?_, fun s hs => ?_⟩
  · rw [← hprod, hconj, hprod]
    exact (hcomm' k hk).eq.symm
  · have hes : e * s * e⁻¹ = s := by
      rw [← (hcomm' s hs).eq, mul_inv_cancel_right]
    calc k * e * s * (k * e)⁻¹ = k * (e * s * e⁻¹) * k⁻¹ := by simp only [mul_inv_rev, mul_assoc]
      _ = k * s * k⁻¹ := by rw [hes]

theorem uc22p22r_fo_commute_conj {Q : Type*} [Group Q] [Finite Q] {q : ℕ} (hq : q.Prime) {x : Q}
    (hx : orderOf x = q) {κ : Subgroup Q} (hκ : IsComponentOf κ ⊤) (hxκ : x ∉ normalizer (κ : Set Q))
    {m : ℕ} (hm : 0 < m) (hmq : m < q) {k : Q} (hk : k ∈ κ) {y : Q} (hy : y ∈ κ) :
    Commute y (x ^ m * k * (x ^ m)⁻¹) := by
  have hcomp := (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (x ^ m)) κ).2 hκ
  have hne : κ.map (MulAut.conj (x ^ m)).toMonoidHom ≠ κ := fun h =>
    hxκ (uc22p22r_fo_mem_of_pow_mem hq hx hm hmq (Subgroup.mem_normalizer_iff_map_conj_eq.2 h))
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hcomp hκ hne)
  exact Subgroup.mem_centralizer_iff.1
    (hcent (Subgroup.mem_map_of_mem (MulAut.conj (x ^ m)).toMonoidHom hk)) y hy

theorem uc22p22r_fo_sylow_inf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P K H : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hH : CFSG.Open.IsSubnormal H K) :
    CFSG.ABGLocalTools.IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | refl H => rwa [inf_eq_left.2 hP.le]
  | step hHM hN _ ih =>
    have h1 := (ih hP).inf_of_le_normalizer hHM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hN)
    rwa [inf_assoc, inf_eq_right.2 hHM] at h1

theorem uc22p22r_fo_le_of_conj_mem {Q : Type*} [Group Q] [Finite Q] {M S κ : Subgroup Q}
    (hκ : CFSG.Open.IsQuasisimple κ) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S κ)
    (h : ∀ k ∈ κ, ∀ s ∈ S, k * s * k⁻¹ ∈ M) : κ ≤ M := by
  by_contra hκM
  have hSN : S.subgroupOf κ ≤ (M.subgroupOf κ).normalCore := fun s hs b => h b b.2 s hs
  have hN : (M.subgroupOf κ).normalCore ≠ ⊤ := by
    intro htop
    refine hκM fun k hk => ?_
    have hmem : (⟨k, hk⟩ : κ) ∈ (M.subgroupOf κ).normalCore := htop ▸ Subgroup.mem_top _
    exact Subgroup.normalCore_le (M.subgroupOf κ) hmem
  have hSZ : S.subgroupOf κ ≤ Subgroup.center κ :=
    hSN.trans (CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hκ _ hN)
  have hodd : Odd (Nat.card (κ ⧸ Subgroup.center κ)) := by
    have h1 : ¬ 2 ∣ (S.subgroupOf κ).index := (CFSG.ABGLocalTools.isSylowOf_iff.1 hS).2.2
    have h2 : (Subgroup.center κ).index ∣ (S.subgroupOf κ).index := Subgroup.index_dvd_of_le hSZ
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h3 => h1 (h3.trans h2))
  haveI : Group.IsPerfect κ := ⟨hκ.1⟩
  haveI : Nontrivial (κ ⧸ Subgroup.center κ) := hκ.2.toNontrivial
  exact Group.IsPerfect.not_isSolvable (κ ⧸ Subgroup.center κ) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem uc22p22r_free_orbit {Q : Type} [Group Q] [Finite Q] {q : ℕ} (hq : q.Prime) (x : Q)
    (hx : orderOf x = q) {T M : Subgroup Q} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTM : T ≤ M)
    (hxM : x ∈ M) (hC : centralizer ({x} : Set Q) ≤ M) {κ : Subgroup Q} (hκ : IsComponentOf κ ⊤)
    (hκM : ¬ κ ≤ M) : x ∈ normalizer (κ : Set Q) := by
  have _ := hxM
  by_contra hxκ
  have hxq : x ^ q = 1 := hx ▸ pow_orderOf_eq_one x
  refine hκM (uc22p22r_fo_le_of_conj_mem hκ.2.2 (uc22p22r_fo_sylow_inf hT hκ.2.1) ?_)
  intro k hk s hs
  obtain ⟨d, hxd, hds⟩ := uc22p22r_fo_norm_exists hq.pos hxq hk fun m hm hmq y hy =>
    uc22p22r_fo_commute_conj hq hx hκ hxκ hm hmq hk hy
  have hdC : d ∈ centralizer ({x} : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact mul_inv_eq_iff_eq_mul.1 hxd
  have hdM : d ∈ M := hC hdC
  rw [← hds s hs.2]
  exact M.mul_mem (M.mul_mem hdM (hTM hs.1)) (M.inv_mem hdM)

end CFSG.LocalAnalysis.UniquenessCase.UC22
