module

public import CFSG.RankThree.PartOne.K133.Alpha
public import CFSG.RankThree.PartOne.K133.ParAFix
public import CFSG.RankThree.PartOne.S13K.KFLift
import CFSG.RankThree.PartOne.K133.Count
import CFSG.RankThree.PartOne.K133.Lift
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S12.Sec12FusMax
public import CFSG.RankThree.PartOne.K133.ParA

public section

namespace CFSG.RankThree.PartOne.K133One

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem mem_D_of_rel {p : ℕ} {E I J : Subgroup G} {b : G} (hbE : b ∈ E)
    (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hJb : J ≤ Subgroup.centralizer ({b} : Set G)) (hIJ : sectionTenRel p I J) :
    b ∈ thetaQuotientCentralizer p E I := by
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨hbE, hEI hbE, fun y hy => ?_⟩
  have hy' : y ∈ ((I ⊓ J : Subgroup G) : Set G) *
      (inSubgroup (aschbacherSolvableCore p) I : Set G) := by
    rw [← sectionTenRel_iff.1 hIJ]
    exact hy
  obtain ⟨j, hj, n, hn, rfl⟩ := hy'
  have hjb : j * b = b * j :=
    Subgroup.mem_centralizer_singleton_iff.1 (hJb (Subgroup.mem_inf.1 hj).2)
  have hbj : b * j * b⁻¹ = j := by rw [← hjb]; group
  have hbn : b * n * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I :=
    theta_conj_mem_of_normalizer p I (hEI hbE) hn
  have hkey : b * (j * n) * b⁻¹ * (j * n)⁻¹ = j * (b * n * b⁻¹ * n⁻¹) * j⁻¹ := by
    calc b * (j * n) * b⁻¹ * (j * n)⁻¹
        = (b * j * b⁻¹) * (b * n * b⁻¹) * n⁻¹ * j⁻¹ := by group
      _ = j * (b * n * b⁻¹) * n⁻¹ * j⁻¹ := by rw [hbj]
      _ = j * (b * n * b⁻¹ * n⁻¹) * j⁻¹ := by group
  rw [hkey]
  exact theta_conj_mem p I (Subgroup.mem_inf.1 hj).1
    ((inSubgroup (aschbacherSolvableCore p) I).mul_mem hbn
      ((inSubgroup (aschbacherSolvableCore p) I).inv_mem hn))

variable [Finite G]

theorem eq_sup_theta_of_normal {p : ℕ} (hp : p.Prime) {a : G} {I M K : Subgroup G}
    (hI : I ∈ thetaComponentsAt p a) (hIM : I = M ⊔ inSubgroup (aschbacherSolvableCore p) I)
    (hKM : K ≤ M) (hMI : M ≤ I) (hKn : M ≤ Subgroup.normalizer (K : Set G))
    (hKperf : Group.IsPerfect ↥K) (hKns : ¬ Group.IsSolvable ↥K) :
    I = K ⊔ inSubgroup (aschbacherSolvableCore p) I := by
  classical
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  let φ : ↥M →* (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    (thetaMk p I).comp (Subgroup.inclusion hMI)
  have hφ : Function.Surjective φ :=
    EmbeddingFixedResidual.surjective_inclusion_quotient hMI hIM
  have hKnorm : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hKn
  have hN : ((K.subgroupOf M).map φ).Normal := hKnorm.map φ hφ
  rcases LocalCores.quasisimple_normal_subgroups hq hN with htop | hcen
  ·
    refine le_antisymm ?_ (sup_le (hKM.trans hMI) (Subgroup.map_subtype_le _))
    intro x hx
    have hx' : thetaMk p I ⟨x, hx⟩ ∈ (K.subgroupOf M).map φ := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx'
    have hmI : (m : G) ∈ I := hMI m.2
    have h1 : thetaMk p I ⟨(m : G), hmI⟩ = thetaMk p I ⟨x, hx⟩ := hmx
    have hmx' : (m : G)⁻¹ * x ∈ I := I.mul_mem (I.inv_mem hmI) hx
    have h2 : thetaMk p I ⟨(m : G)⁻¹ * x, hmx'⟩ = 1 := by
      have e : (⟨(m : G)⁻¹ * x, hmx'⟩ : ↥I) = (⟨(m : G), hmI⟩ : ↥I)⁻¹ * ⟨x, hx⟩ := rfl
      rw [e, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (m : G)⁻¹ * x ∈ inSubgroup (aschbacherSolvableCore p) I :=
      (thetaMk_eq_one_iff p I hmx').1 h2
    have hmK : (m : G) ∈ K := Subgroup.mem_subgroupOf.1 hm
    have e2 : x = (m : G) * ((m : G)⁻¹ * x) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hmK h3
  ·
    exfalso
    apply hKns
    have hcomm : ⁅K, K⁆ ≤ inSubgroup (aschbacherSolvableCore p) I := by
      rw [Subgroup.commutator_le]
      intro k₁ hk₁ k₂ hk₂
      have hk₁M : k₁ ∈ M := hKM hk₁
      have hk₂M : k₂ ∈ M := hKM hk₂
      have hc₂ : thetaMk p I ⟨k₂, hMI hk₂M⟩ ∈
          Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I) :=
        hcen (Subgroup.mem_map.2 ⟨⟨k₂, hk₂M⟩, Subgroup.mem_subgroupOf.2 hk₂, rfl⟩)
      have hmk : (⁅k₁, k₂⁆ : G) ∈ I :=
        hMI (M.mul_mem (M.mul_mem (M.mul_mem hk₁M hk₂M) (M.inv_mem hk₁M)) (M.inv_mem hk₂M))
      refine (thetaMk_eq_one_iff p I hmk).1 ?_
      have e1 : (⟨⁅k₁, k₂⁆, hmk⟩ : ↥I) =
          ⁅(⟨k₁, hMI hk₁M⟩ : ↥I), (⟨k₂, hMI hk₂M⟩ : ↥I)⁆ := rfl
      rw [e1, commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [Subgroup.mem_center_iff.1 hc₂ (thetaMk p I ⟨k₁, hMI hk₁M⟩)]
      group
    have hKθ : K ≤ inSubgroup (aschbacherSolvableCore p) I := by
      have := Subgroup.isPerfect_iff.1 hKperf
      rw [this] at hcomm
      exact hcomm
    have := (theta_solvable_and_not_dvd hp I).1
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKθ)
      (Subgroup.inclusion_injective hKθ)

theorem D_le_fixed {p : ℕ} (hp : p.Prime) {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) {K : Subgroup G} (hK : IsKt p E t K)
    (hKk : K = kZero p E t) (hKq : CFSG.IsQuasisimple ↥K) (hKc : Subgroup.center ↥K = ⊥)
    (hmov : autMovedInG E t ≤ K) {I : Subgroup G} (hKI : K ≤ I) :
    thetaQuotientCentralizer p E I ≤ autFixedInG E t := by
  classical
  intro y hy
  obtain ⟨hyE, -, hyθ⟩ := mem_thetaQuotientCentralizer_iff.1 hy
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := by
    rw [hKk]
    exact E_le_normalizer_kZero h.E_elem t hyE
  let N₁ : Subgroup ↥K := (inSubgroup (aschbacherSolvableCore p) I).subgroupOf K
  have hN₁n : N₁.Normal := by
    refine ⟨fun n hn k => ?_⟩
    show ((k * n * k⁻¹ : ↥K) : G) ∈ inSubgroup (aschbacherSolvableCore p) I
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact theta_conj_mem p I (hKI k.2) hn
  have hN₁bot : N₁ = ⊥ := by
    rcases LocalCores.quasisimple_normal_subgroups hKq hN₁n with htop | hcen
    · exfalso
      have hKθ : K ≤ inSubgroup (aschbacherSolvableCore p) I := fun k hk => by
        have : (⟨k, hk⟩ : ↥K) ∈ N₁ := htop ▸ Subgroup.mem_top _
        exact this
      have := (theta_solvable_and_not_dvd hp I).1
      have : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKθ)
          (Subgroup.inclusion_injective _)
      have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hKq
      have : Group.IsPerfect ↥K := hKq.1
      exact Group.IsPerfect.not_isSolvable ↥K inferInstance
    · rw [hKc] at hcen
      exact le_bot_iff.1 hcen
  have hKy : ∀ k ∈ K, y * k = k * y := by
    intro k hk
    have h1 : y * k * y⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) I := hyθ k (hKI hk)
    have h2 : y * k * y⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.1 hyN k).1 hk) (K.inv_mem hk)
    have h3 : (⟨y * k * y⁻¹ * k⁻¹, h2⟩ : ↥K) ∈ N₁ := h1
    rw [hN₁bot, Subgroup.mem_bot] at h3
    have h4 : y * k * y⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h3
    have h5 : y * k * y⁻¹ = k := mul_inv_eq_one.1 h4
    calc y * k = (y * k * y⁻¹) * y := by group
      _ = k * y := by rw [h5]
  obtain ⟨hsup, -, -⟩ := hF13.reflection t ht
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hME : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hy' : y ∈ autFixedInG E t ⊔ autMovedInG E t := hsup ▸ hyE
  obtain ⟨s, hs, m, hm, hsm⟩ :=
    Sec12Fus.mem_sup_of_commute' (fun x hx z hz => hcommE x (hCE hx) z (hME hz)) hy'
  have hsK : s ∈ Subgroup.centralizer (K : Set G) := autFixedInG_le_centralizer_of_isKt hK hs
  have hmK : m ∈ K := hmov hm
  have hmc : ∀ k ∈ K, k * m = m * k := by
    intro k hk
    have hks : s * k = k * s := (Subgroup.mem_centralizer_iff.1 hsK k hk).symm
    have h5 : s * (k * m) = s * (m * k) := by
      calc s * (k * m) = (s * k) * m := by group
        _ = (k * s) * m := by rw [hks]
        _ = k * (s * m) := by group
        _ = k * y := by rw [hsm]
        _ = y * k := (hKy k hk).symm
        _ = (s * m) * k := by rw [hsm]
        _ = s * (m * k) := by group
    exact mul_left_cancel h5
  have hmz : (⟨m, hmK⟩ : ↥K) ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hmc g.1 g.2)
  rw [hKc, Subgroup.mem_bot] at hmz
  have hm1 : m = 1 := congrArg Subtype.val hmz
  rw [hm1, mul_one] at hsm
  rw [← hsm]
  exact hs

omit [Finite G] in
theorem card_autFixedInG_three {p : ℕ} {E : Subgroup G} {t : MulAut E} (hp : p.Prime)
    (hE : IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hrefl : E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
      Nat.card ↥(autMovedInG E t) = p) : Nat.card ↥(autFixedInG E t) = p ^ 2 := by
  obtain ⟨hsup, hdisj, hM⟩ := hrefl
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hME : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcomm : ∀ x ∈ autFixedInG E t, ∀ y ∈ autMovedInG E t, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hCE hx⟩ ⟨y, hME hy⟩)
  have h1 := card_sup_of_commute_disjoint hcomm hdisj
  rw [← hsup, hcard, hM] at h1
  have hp0 : 0 < p := hp.pos
  have : p ^ 2 * p = Nat.card ↥(autFixedInG E t) * p := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hp0 this).symm

theorem autFixedInG_eq_sup {p : ℕ} (hp : p.Prime) {E : Subgroup G} {t : MulAut E} {c e : G}
    (hE : IsElementaryAbelian p E) (hcard : Nat.card ↥(autFixedInG E t) = p ^ 2)
    (hc : c ∈ autFixedInG E t) (he : e ∈ autFixedInG E t) (hc1 : c ≠ 1)
    (hec : e ∉ Subgroup.zpowers c) :
    autFixedInG E t = Subgroup.zpowers c ⊔ Subgroup.zpowers e := by
  have : Fact p.Prime := ⟨hp⟩
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcE : c ∈ E := hCE hc
  have heE : e ∈ E := hCE he
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ Subgroup.one_mem _)
  have hcord : orderOf c = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) c hcE) hc1
  have heord : orderOf e = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e heE) he1
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤ autFixedInG E t :=
    sup_le (Subgroup.zpowers_le.2 hc) (Subgroup.zpowers_le.2 he)
  have hcard' : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers e) = p ^ 2 := by
    have h1 := card_sup_zpowers hp heord (Y := Subgroup.zpowers c) (fun y hy =>
      hcommE y ((Subgroup.zpowers_le.2 hcE) hy) e heE) hec
    rw [h1, Nat.card_zpowers, hcord]
    ring
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard'])).symm

theorem zpowers_eq_of_mem {p : ℕ} [Fact p.Prime] {c e : G} (hcord : orderOf c = p)
    (he : e ∈ Subgroup.zpowers c) (he1 : e ≠ 1) : Subgroup.zpowers e = Subgroup.zpowers c :=
  le_antisymm (Subgroup.zpowers_le.2 he)
    (Subgroup.zpowers_le.2 (HNB.mem_zpowers_of_mem_zpowers_prime hcord he he1))

theorem kf133One_clause_one_of_split (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L)
    {K : Subgroup G} (hK : IsKt p E t K) (hKk : K = kZero p E t) (hKq : CFSG.IsQuasisimple ↥K)
    (hKc : Subgroup.center ↥K = ⊥) (hsplit : SplitType p K) (hmov : autMovedInG E t ≤ K)
    {e : G} (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) :
    I = K ⊔ inSubgroup (aschbacherSolvableCore p) I ∨ I ∈ thetaCompZeroStarE p E := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p ↥E := h.E_elem
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have heE : e ∈ E := (Subgroup.map_subtype_le _) he
  have hEI : E ≤ Subgroup.normalizer (I : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI
  have hKL : K ≤ L := hF13.kt_le L hF13.inZeroStar t ht htL K hK
  have hKperf : Group.IsPerfect ↥K := hKq.1
  have hKns : ¬ Group.IsSolvable ↥K := by
    intro hsol
    have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hKq
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  have hK0 : K ≠ ⊥ := by
    intro hbot
    have : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hKq
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥K)
    exact ha (Subtype.ext (by simpa [hbot] using a.2))
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hrefl := hF13.reflection t ht
  have hCcard : Nat.card ↥(autFixedInG E t) = p ^ 2 :=
    card_autFixedInG_three hp h.E_elem hEcard hrefl
  have hcC : c ∈ autFixedInG E t :=
    Subgroup.mem_map.2 ⟨⟨c, hcE⟩, Sec13Base.fixes_c_of_mem_torusImage h hcE htL, rfl⟩
  have hcord : orderOf c = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) c hcE) h.c_ne_one
  have heord : orderOf e = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e heE) he1
  by_cases hcD : c ∈ thetaQuotientCentralizer p E I
  ·
    have hc := commutator_zpowers_le_theta hcD
    have hIL : sectionTenRel p I L :=
      sectionTenRel_of_trivial_action_fix hS h hKperf hK0 hKL he1 heE hI hKI
        (P := autFixedInG E t) (Subgroup.map_subtype_le _) (isKt_le_centralizer_fixed hK)
        (isKt_centralizes_fixed_theta hp hK he) hc
    by_cases hec : e ∈ Subgroup.zpowers c
    ·
      right
      have hIc : I ∈ thetaComponentsAt p c := by
        rw [← thetaComponentsAt_eq_of_zpowers_eq p (zpowers_eq_of_mem hcord hec he1)]
        exact hI
      have hLc : L ∈ thetaComponentsAt p c := h.L_mem.2
      rw [Sec12Fus.eq_of_sectionTenRel_of_mem_thetaComponentsAt hp hIc hLc hIL]
      exact hF13.inZeroStar
    ·
      left
      have hCeq : autFixedInG E t = Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
        autFixedInG_eq_sup hp h.E_elem hCcard hcC he h.c_ne_one hec
      have hIM : I = (I ⊓ L) ⊔ inSubgroup (aschbacherSolvableCore p) I := hIL
      have hKM : K ≤ I ⊓ L := le_inf hKI hKL
      have hMcent : I ⊓ L ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
        intro x hx
        obtain ⟨hxI, hxL⟩ := Subgroup.mem_inf.1 hx
        have hxe : x * e = e * x :=
          Subgroup.mem_centralizer_singleton_iff.1 ((mem_thetaComponentsAt_iff.1 hI).1 hxI)
        have hxc : c * x = x * c := Sec12Three.comm_c_L h x hxL
        have hCx : autFixedInG E t ≤ Subgroup.centralizer ({x} : Set G) := by
          rw [hCeq]
          refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.2 hxc
          · exact Subgroup.mem_centralizer_singleton_iff.2 hxe.symm
        refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        exact Subgroup.mem_centralizer_singleton_iff.1 (hCx hy)
      have hMn : I ⊓ L ≤ Subgroup.normalizer (K : Set G) := fun x hx => by
        rw [hKk]
        exact kZero_mem_normalizer (hMcent hx)
      exact eq_sup_theta_of_normal hp hI hIM hKM inf_le_left hMn hKperf hKns
  ·
    right
    have hDle := D_le_fixed hp h hF13 ht hK hKk hKq hKc hmov hKI
    have heD : e ∈ thetaQuotientCentralizer p E I := by
      rw [mem_thetaQuotientCentralizer_iff]
      refine ⟨heE, hEI heE, fun k hk => ?_⟩
      have hke : k * e = e * k :=
        Subgroup.mem_centralizer_singleton_iff.1 ((mem_thetaComponentsAt_iff.1 hI).1 hk)
      have : e * k * e⁻¹ * k⁻¹ = 1 := by rw [← hke]; group
      rw [this]
      exact Subgroup.one_mem _
    have hec : e ∉ Subgroup.zpowers c := by
      intro hec
      apply hcD
      exact (Subgroup.zpowers_le.2 heD) (HNB.mem_zpowers_of_mem_zpowers_prime hcord hec he1)
    have hCeq : autFixedInG E t = Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
      autFixedInG_eq_sup hp h.E_elem hCcard hcC he h.c_ne_one hec
    have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
      congrArg Subtype.val (h.E_elem.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
    have hDsub : ∀ d ∈ thetaQuotientCentralizer p E I, d ∈ Subgroup.zpowers e := by
      intro d hd
      have hdC : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers e := hCeq ▸ hDle hd
      obtain ⟨s, hs, u, hu, hsu⟩ := Sec12Fus.mem_sup_of_commute'
        (fun x hx z hz => hcommE x ((Subgroup.zpowers_le.2 hcE) hx) z
          ((Subgroup.zpowers_le.2 heE) hz)) hdC
      have huD : u ∈ thetaQuotientCentralizer p E I := (Subgroup.zpowers_le.2 heD) hu
      have hsD : s ∈ thetaQuotientCentralizer p E I := by
        have : s = d * u⁻¹ := by rw [← hsu]; group
        rw [this]
        exact Subgroup.mul_mem _ hd (Subgroup.inv_mem _ huD)
      by_cases hs1 : s = 1
      · rw [hs1, one_mul] at hsu
        rw [← hsu]
        exact hu
      · exfalso
        apply hcD
        exact (Subgroup.zpowers_le.2 hsD) (HNB.mem_zpowers_of_mem_zpowers_prime hcord hs hs1)
    obtain ⟨S, hSK, hS1, hS2, hSN, hSE⟩ := exists_two_subgroup_of_split h ht hK hsplit hmov
    have hEadm : E ∈ admissibleTriples p E := ⟨le_rfl, h.E_elem, hEcard, S, hS1, hS2, hSN⟩
    have hIfam : I ∈ thetaComponentFamily p E :=
      mem_thetaComponentFamily_iff.2 ⟨e, heE, he1, hI⟩
    refine ⟨⟨E, hEadm, mem_sectionTenZero_of_split h ht hK hsplit hmov he he1 hI hKI⟩,
      ⟨E, hEadm, hIfam⟩, ?_⟩
    intro J hJ hIJ
    obtain ⟨B, hBadm, hJB⟩ := hJ
    obtain ⟨b, hbB, hb1, hJb⟩ := mem_thetaComponentFamily_iff.1 hJB
    have hbE : b ∈ E := hBadm.1 hbB
    have hbD : b ∈ thetaQuotientCentralizer p E I :=
      mem_D_of_rel hbE hEI (mem_thetaComponentsAt_iff.1 hJb).1 hIJ
    have hbe : b ∈ Subgroup.zpowers e := hDsub b hbD
    have hJe : J ∈ thetaComponentsAt p e := by
      rw [← thetaComponentsAt_eq_of_zpowers_eq p (zpowers_eq_of_mem heord hbe hb1)]
      exact hJb
    rw [← Sec12Fus.eq_of_sectionTenRel_of_mem_thetaComponentsAt hp hI hJe hIJ]
    exact sectionTenRel_refl p I

theorem kf133One_clause_one_of_liftAt (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L)
    (hlift : KFLiftAt p E t) (hsplit : SplitType p (kZero p E t)) {e : G}
    (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e)
    (hKI : kZero p E t ≤ I) :
    I = kZero p E t ⊔ inSubgroup (aschbacherSolvableCore p) I ∨ I ∈ thetaCompZeroStarE p E :=
  kf133One_clause_one_of_split hS h hF13 hEA ht htL hlift.isKt rfl hlift.1 hlift.2.1 hsplit
    hlift.2.2.2.1 he he1 hI hKI

end CFSG.RankThree.PartOne.K133One
