module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenSix
public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type*} [Group G]

structure Hyp716 (V H E : Subgroup G) : Prop extends Hyp73 V H E (iSub V H E) where
  oddCore : fusionOddCoreOf (kSub V H E) = ⊥
  transitive : ∀ U ∈ omegaSet V H E, ∃ k ∈ kSub V H E, U = conjSubgroup V k

end CFSG.LocalAnalysis.WeakClosure81.SevenK

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

theorem commutator_eq_one_of_mem_center_of_odd {Q : Type*} [Group Q] {x v : Q} {m : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) (hv : v * v = 1) (hc : ⁅x, v⁆ ∈ Subgroup.center Q) :
    ⁅x, v⁆ = 1 := by
  generalize hzdef : ⁅x, v⁆ = z at hc ⊢
  have hz : ∀ g : Q, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hc g
  have ha : x * v = z * v * x := by rw [← hzdef, commutatorElement_def]; group
  have hb : ∀ j : ℕ, x ^ j * v = z ^ j * v * x ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hxz : x * z ^ j = z ^ j * x := Commute.pow_right (hz x) j
      calc x ^ (j + 1) * v = x * (x ^ j * v) := by rw [pow_succ', mul_assoc]
        _ = x * (z ^ j * v * x ^ j) := by rw [ih]
        _ = (x * z ^ j) * v * x ^ j := by simp only [mul_assoc]
        _ = (z ^ j * x) * v * x ^ j := by rw [hxz]
        _ = z ^ j * (x * v) * x ^ j := by simp only [mul_assoc]
        _ = z ^ j * (z * v * x) * x ^ j := by rw [ha]
        _ = z ^ (j + 1) * v * x ^ (j + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]
  have hzm1 : z ^ m = 1 := by
    have h1 := hb m
    rw [hx, one_mul, mul_one] at h1
    exact mul_right_cancel (a := z ^ m) (b := v) (c := 1) (by rw [one_mul]; exact h1.symm)
  have hzv : z * v = x * v * x⁻¹ := by rw [← hzdef, commutatorElement_def]; group
  have hsq : (z * v) * (z * v) = 1 := by
    rw [hzv]
    have h1 : x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
    rw [h1, hv]
    group
  have hzz : z * z = 1 := by
    have h1 : (z * v) * (z * v) = z * z * (v * v) := by
      calc (z * v) * (z * v) = z * (v * z) * v := by simp only [mul_assoc]
        _ = z * (z * v) * v := by rw [hz v]
        _ = z * z * (v * v) := by simp only [mul_assoc]
    rw [h1, hv, mul_one] at hsq
    exact hsq
  obtain ⟨k, hk⟩ := hm
  have hzm : z ^ m = z := by rw [hk, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
  rw [← hzm]
  exact hzm1

theorem mem_sup_of_le_centralizer {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hBA : B ≤ Subgroup.centralizer (A : Set Q)) {y : Q} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hAB : A ≤ Subgroup.normalizer (B : Set Q) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hc : a * h = h * a := Subgroup.mem_centralizer_iff.mp (hBA hh) a ha
      have e : a * h * a⁻¹ = h := by rw [hc, mul_inv_cancel_right]
      rw [e]
      exact hh
    · intro hh
      have hc : a⁻¹ * (a * h * a⁻¹) = (a * h * a⁻¹) * a⁻¹ :=
        Subgroup.mem_centralizer_iff.mp (hBA hh) a⁻¹ (Subgroup.inv_mem _ ha)
      have e : h = a⁻¹ * (a * h * a⁻¹) * a := by group
      have e' : a⁻¹ * (a * h * a⁻¹) * a = a * h * a⁻¹ := by rw [hc, inv_mul_cancel_right]
      rw [e, e']
      exact hh
  have hy' : y ∈ ((A ⊔ B : Subgroup Q) : Set Q) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem mem_normalizer_inf_centralizer {G : Type*} [Group G] {I : Subgroup G}
    (hI : IsMulCommutative I) {g x : G} (hg : g ∈ Subgroup.normalizer (I : Set G))
    (hc : ⁅x, g⁆ ∈ I) :
    g ∈ Subgroup.normalizer ((I ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  haveI := hI
  have key : ∀ g' : G, g' ∈ Subgroup.normalizer (I : Set G) → ⁅x, g'⁆ ∈ I →
      ∀ h ∈ I ⊓ Subgroup.centralizer ({x} : Set G),
        g' * h * g'⁻¹ ∈ I ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro g' hg' hc' h hh
    have hhI : h ∈ I := (Subgroup.mem_inf.mp hh).1
    have hhC : h * x = x * h :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hh).2
    have h1 : g' * h * g'⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp hg' h).mp hhI
    refine Subgroup.mem_inf.mpr ⟨h1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    generalize hc'def : ⁅x, g'⁆ = c' at hc'
    have e1 : x * g' = c' * g' * x := by rw [← hc'def, commutatorElement_def]; group
    have e2 : x * g'⁻¹ = g'⁻¹ * c'⁻¹ * x := by rw [← hc'def, commutatorElement_def]; group
    have hcw : c' * (g' * h * g'⁻¹) = (g' * h * g'⁻¹) * c' := setLike_mul_comm hc' h1
    have hxw : x * (g' * h * g'⁻¹) = (c' * (g' * h * g'⁻¹) * c'⁻¹) * x := by
      calc x * (g' * h * g'⁻¹) = (x * g') * h * g'⁻¹ := by simp only [mul_assoc]
        _ = (c' * g' * x) * h * g'⁻¹ := by rw [e1]
        _ = c' * g' * (x * h) * g'⁻¹ := by simp only [mul_assoc]
        _ = c' * g' * (h * x) * g'⁻¹ := by rw [hhC.symm]
        _ = c' * (g' * h) * (x * g'⁻¹) := by simp only [mul_assoc]
        _ = c' * (g' * h) * (g'⁻¹ * c'⁻¹ * x) := by rw [e2]
        _ = (c' * (g' * h * g'⁻¹) * c'⁻¹) * x := by simp only [mul_assoc]
    have hw : c' * (g' * h * g'⁻¹) * c'⁻¹ = g' * h * g'⁻¹ := by
      rw [hcw, mul_inv_cancel_right]
    rw [hw] at hxw
    exact hxw.symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg hc h hh, fun hh => ?_⟩
  have hc' : ⁅x, g⁻¹⁆ ∈ I := by
    have h1 : g⁻¹ * ⁅x, g⁆⁻¹ * g⁻¹⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp (Subgroup.inv_mem _ hc)
    have e : ⁅x, g⁻¹⁆ = g⁻¹ * ⁅x, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h1
  have h2 := key g⁻¹ (Subgroup.inv_mem _ hg) hc' _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h2

theorem conjSubgroup_inf_eq {G : Type*} [Group G] (g : G) (U V : Subgroup G) :
    CFSG.Quasithin.conjSubgroup (U ⊓ V) g =
      CFSG.Quasithin.conjSubgroup U g ⊓ CFSG.Quasithin.conjSubgroup V g :=
  Subgroup.map_inf_eq U V (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem conjSubgroup_inf_of_mem_normalizer {G : Type*} [Group G] {I : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (I : Set G)) (V : Subgroup G) :
    CFSG.Quasithin.conjSubgroup (V ⊓ I) a = CFSG.Quasithin.conjSubgroup V a ⊓ I := by
  rw [conjSubgroup_inf_eq, CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr ha]

theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {a : G}
    (hA : a ∈ Subgroup.normalizer (A : Set G)) (hB : a ∈ Subgroup.normalizer (B : Set G)) :
    a ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer] at hA hB ⊢
  unfold CFSG.Quasithin.conjSubgroup at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem iSub_le_kSub (V H E : Subgroup G) : iSub V H E ≤ kSub V H E :=
  iSup₂_le fun U hU => inf_le_left.trans (le_kSub hU)

theorem kSub_le_normalizer_iSub (h : Hyp716 V H E) :
    kSub V H E ≤ Subgroup.normalizer (iSub V H E : Set G) := by
  have hIleH : iSub V H E ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hHN : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH h.jnormal
  exact (kSub_le_of_forall_le h.omega_le).trans hHN

theorem conjSubgroup_mem_omegaSet_of_mem_kSub (h : Hyp716 V H E) {a : G}
    (ha : a ∈ kSub V H E) : conjSubgroup V a ∈ omegaSet V H E :=
  conjSubgroup_mem_omegaSet h.le h.normal h.mem (kSub_le_of_forall_le h.omega_le ha)

theorem inf_iSub_ne_bot (h : Hyp716 V H E) : V ⊓ iSub V H E ≠ ⊥ := by
  rw [inf_iSub_eq_inf_pCoreOf h.mem]
  exact inf_pCoreOf_ne_bot_of_mem_omegaSet h.elemAbelian h.abelian h.le h.normal h.mem

theorem iSub_le_of_normalized (h : Hyp716 V H E) {W : Subgroup G}
    (hW : kSub V H E ≤ Subgroup.normalizer (W : Set G)) (hVW : V ⊓ iSub V H E ≤ W) :
    iSub V H E ≤ W := by
  refine iSup₂_le fun U hU => ?_
  obtain ⟨k, hk, rfl⟩ := h.transitive U hU
  intro x hx
  have hx1 : x ∈ CFSG.Quasithin.conjSubgroup V k ⊓ iSub V H E := by
    rw [inf_iSub_eq_inf_pCoreOf hU]
    exact hx
  rw [← conjSubgroup_inf_of_mem_normalizer (kSub_le_normalizer_iSub h hk) V] at hx1
  have hx2 : k * x * k⁻¹ ∈ V ⊓ iSub V H E := CFSG.Quasithin.mem_conjSubgroup_iff.mp hx1
  exact (Subgroup.mem_normalizer_iff.mp (hW hk) x).mpr (hVW hx2)

theorem card_conjSubgroup_inf_iSub (h : Hyp716 V H E) {a : G} (ha : a ∈ kSub V H E) :
    Nat.card ↥(conjSubgroup V a ⊓ iSub V H E) = Nat.card ↥(V ⊓ iSub V H E) := by
  rw [← conjSubgroup_inf_of_mem_normalizer (kSub_le_normalizer_iSub h ha) V]
  exact card_conjSubgroup' a _


theorem isElemAbelian_iSub (h : Hyp716 V H E) : IsElemAbelian 2 (iSub V H E) :=
  seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le

theorem iSub_le_normalizer_of_mem_omegaSet (h : Hyp716 V H E) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : iSub V H E ≤ Subgroup.normalizer (U : Set G) := by
  have hUab := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
  have hUTI := isTI_of_mem_omegaSet hU h.ti
  have hΩ := omegaSet_eq_of_mem hU
  have hI := iSub_eq_of_mem hU
  have claim : ∀ {a u : G}, a ∈ iSub V H E → u ∈ U → a * u * a⁻¹ ∈ U := by
    intro a u ha hu
    have hc := commutator_mem_inf_iSub (V := U) (H := H) (E := E) hUab hUTI h.abelian h.le
      h.normal (by rw [hΩ]; exact h.omega_le) (by rw [hΩ]; exact hU) (a := a) (v := u)
      (by rw [hI]; exact ha) hu
    have e : a * u * a⁻¹ = ⁅a, u⁆ * u := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem (Subgroup.mem_inf.mp hc).1 hu
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨claim ha, fun hy => ?_⟩
  have h1 := claim (inv_mem ha) hy
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem kSub_inf_centralizer_iSub_le_pCoreOf_of_oddCore (h : Hyp716 V H E) :
    kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤ pCoreOf 2 (kSub V H E) := by
  have h4 := seven_four h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
  have hodd : CFSG.QuasithinUnique.oddCoreIn (kSub V H E) = ⊥ := h.oddCore
  rwa [hodd, sup_bot_eq] at h4

end CFSG.LocalAnalysis.WeakClosure81
