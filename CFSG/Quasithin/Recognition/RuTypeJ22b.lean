module

public import CFSG.Quasithin.Recognition.RuTypeJ22

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] noncomputable def zval (w : G) : F4 := by
  classical
  exact if w = 1 then 0 else 1

theorem zval_val (w : G) : zval w = 0 ∨ zval w = 1 := by
  unfold zval
  split_ifs <;> simp

theorem zval_eq_zero_iff (w : G) : zval w = 0 ↔ w = 1 := by
  unfold zval
  split_ifs with h
  · simp [h]
  · simp only [one_ne_zero, false_iff]
    exact h

namespace RuDataN

variable (N : RuDataN G)

abbrev HC : Subgroup G := ruH N.T ⊓ Subgroup.centralizer (ruU N.L N.T : Set G)


@[expose] noncomputable def uOf (x : Fin 2 → F4) : ruU N.L N.T :=
  Function.surjInv N.ψU_surj (Multiplicative.ofAdd x)

theorem ψU_uOf (x : Fin 2 → F4) : Multiplicative.toAdd (N.ψU (N.uOf x)) = x := by
  rw [uOf, Function.surjInv_eq N.ψU_surj, toAdd_ofAdd]

@[expose] noncomputable def pairF (q : G) (x : Fin 2 → F4) : F4 :=
  zval (q * N.uOf x * q⁻¹ * (N.uOf x : G)⁻¹)

variable [Finite G]

theorem zval_mul_aux {a b : G} (ha : a ∈ ruZ N.T) (hb : b ∈ ruZ N.T) :
    zval (a * b) = zval a + zval b := by
  have hz2 : N.z * N.z = 1 := by rw [← sq, N.z_sq]
  have hz1 := N.z_ne_one
  have h11 : (1 : F4) + 1 = 0 := by decide
  rcases N.mem_Z_iff.mp ha with rfl | rfl <;> rcases N.mem_Z_iff.mp hb with rfl | rfl <;>
    simp [zval, hz2, hz1, h11]

omit [Finite G] in
theorem comm_mem_Z {q u : G} (hq : q ∈ ruQ N.T) (hu : u ∈ ruU N.L N.T) :
    q * u * q⁻¹ * u⁻¹ ∈ ruZ N.T :=
  N.two.UZ_central q hq u hu

omit [Finite G] in
theorem comm_congr {h : G} (hh : h ∈ ruH N.T) {u u' : ruU N.L N.T} (e : N.ψU u = N.ψU u') :
    h * u * h⁻¹ * (u : G)⁻¹ = h * u' * h⁻¹ * (u' : G)⁻¹ := by
  have hw : N.ψU (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
  have hwZ := (N.ψU_eq_one_iff _).mp hw
  set w : G := ((u⁻¹ * u' : ruU N.L N.T) : G) with hwdef
  have hu' : (u' : G) = u * w := by simp [w]
  have hc : Commute h w := (N.Z_comm_H hwZ hh).symm
  have hc' : w * h⁻¹ = h⁻¹ * w := (hc.inv_left).eq.symm
  rw [hu']
  symm
  calc h * (u * w) * h⁻¹ * (u * w)⁻¹ = h * u * (w * h⁻¹) * w⁻¹ * (u : G)⁻¹ := by group
    _ = h * u * (h⁻¹ * w) * w⁻¹ * (u : G)⁻¹ := by rw [hc']
    _ = h * u * h⁻¹ * (u : G)⁻¹ := by group

omit [Finite G] in
theorem comm_mul_right {q u u' : G} (hq : q ∈ ruQ N.T) (hu : u ∈ ruU N.L N.T)
    (hu' : u' ∈ ruU N.L N.T) :
    q * (u * u') * q⁻¹ * (u * u')⁻¹ = (q * u * q⁻¹ * u⁻¹) * (q * u' * q⁻¹ * u'⁻¹) := by
  have hc : Commute (q * u' * q⁻¹ * u'⁻¹) u := N.Z_comm_H (N.comm_mem_Z hq hu') (N.U_le_H hu)
  have hc' : (q * u' * q⁻¹ * u'⁻¹) * u⁻¹ = u⁻¹ * (q * u' * q⁻¹ * u'⁻¹) := hc.inv_right.eq
  calc q * (u * u') * q⁻¹ * (u * u')⁻¹
      = (q * u * q⁻¹) * ((q * u' * q⁻¹ * u'⁻¹) * u⁻¹) := by group
    _ = (q * u * q⁻¹) * (u⁻¹ * (q * u' * q⁻¹ * u'⁻¹)) := by rw [hc']
    _ = (q * u * q⁻¹ * u⁻¹) * (q * u' * q⁻¹ * u'⁻¹) := by group

theorem comm_mul_left {q q' u : G} (hq : q ∈ ruQ N.T) (hq' : q' ∈ ruQ N.T)
    (hu : u ∈ ruU N.L N.T) :
    q * q' * u * (q * q')⁻¹ * u⁻¹ = (q * u * q⁻¹ * u⁻¹) * (q' * u * q'⁻¹ * u⁻¹) := by
  have h1 := N.comm_mem_Z hq' hu
  have h2 := N.comm_mem_Z hq hu
  have hc : Commute q (q' * u * q'⁻¹ * u⁻¹) := (N.Z_comm_H h1 (pCoreOf_le 2 _ hq)).symm
  have hconj : q * (q' * u * q'⁻¹ * u⁻¹) * q⁻¹ = q' * u * q'⁻¹ * u⁻¹ := by
    rw [hc.eq, mul_inv_cancel_right]
  have hZ : Commute (q' * u * q'⁻¹ * u⁻¹) (q * u * q⁻¹ * u⁻¹) := by
    rcases N.mem_Z_iff.mp h1 with e | e
    · rw [e]
      exact Commute.one_left _
    · rcases N.mem_Z_iff.mp h2 with e' | e'
      · rw [e']
        exact Commute.one_right _
      · rw [e, e']
  calc q * q' * u * (q * q')⁻¹ * u⁻¹
      = q * (q' * u * q'⁻¹ * u⁻¹) * q⁻¹ * (q * u * q⁻¹ * u⁻¹) := by group
    _ = (q' * u * q'⁻¹ * u⁻¹) * (q * u * q⁻¹ * u⁻¹) := by rw [hconj]
    _ = (q * u * q⁻¹ * u⁻¹) * (q' * u * q'⁻¹ * u⁻¹) := hZ.eq

theorem pairF_add {q : G} (hq : q ∈ ruQ N.T) (x y : Fin 2 → F4) :
    N.pairF q (x + y) = N.pairF q x + N.pairF q y := by
  unfold pairF
  have e : N.ψU (N.uOf (x + y)) = N.ψU (N.uOf x * N.uOf y) := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, N.ψU_uOf, N.ψU_uOf, N.ψU_uOf]
  rw [N.comm_congr (pCoreOf_le 2 _ hq) e]
  simp only [Subgroup.coe_mul]
  rw [N.comm_mul_right hq (N.uOf x).2 (N.uOf y).2,
    N.zval_mul_aux (N.comm_mem_Z hq (N.uOf x).2) (N.comm_mem_Z hq (N.uOf y).2)]

theorem pairF_mul {q q' : G} (hq : q ∈ ruQ N.T) (hq' : q' ∈ ruQ N.T) (x : Fin 2 → F4) :
    N.pairF (q * q') x = N.pairF q x + N.pairF q' x := by
  unfold pairF
  rw [N.comm_mul_left hq hq' (N.uOf x).2,
    N.zval_mul_aux (N.comm_mem_Z hq (N.uOf x).2) (N.comm_mem_Z hq' (N.uOf x).2)]

omit [Finite G] in
theorem pairF_val (q : G) (x : Fin 2 → F4) : N.pairF q x = 0 ∨ N.pairF q x = 1 :=
  zval_val _

theorem exists_ψQ {q : G} (hq : q ∈ ruQ N.T) : ∃ w, ∀ x, Sigma.formB w x = N.pairF q x :=
  Sigma.exists_formB_eq _ (N.pairF_add hq) (N.pairF_val q)

@[expose] noncomputable def ψQfun (q : ruQ N.T) : Fin 2 → F4 := (N.exists_ψQ q.2).choose

theorem formB_ψQfun (q : ruQ N.T) (x : Fin 2 → F4) :
    Sigma.formB (N.ψQfun q) x = N.pairF q x := (N.exists_ψQ q.2).choose_spec x

@[expose] noncomputable def ψQ : ruQ N.T →* Multiplicative (Fin 2 → F4) where
  toFun q := Multiplicative.ofAdd (N.ψQfun q)
  map_one' := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_one]
    refine Sigma.formB_inj fun x => ?_
    rw [N.formB_ψQfun]
    have h0 : Sigma.formB 0 x = 0 := by
      have := Sigma.formB_add_left 0 0 x
      rw [add_zero] at this
      exact add_eq_left.mp this.symm
    rw [h0]
    unfold pairF
    simp [zval]
  map_mul' q q' := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
    refine Sigma.formB_inj fun x => ?_
    rw [N.formB_ψQfun, Sigma.formB_add_left, N.formB_ψQfun, N.formB_ψQfun]
    exact N.pairF_mul q.2 q'.2 x

theorem formB_ψQ (q : ruQ N.T) (x : Fin 2 → F4) :
    Sigma.formB (Multiplicative.toAdd (N.ψQ q)) x = N.pairF q x := N.formB_ψQfun q x

theorem comm_eq_one_iff (q : ruQ N.T) (u : ruU N.L N.T) :
    (q : G) * u * (q : G)⁻¹ * (u : G)⁻¹ = 1 ↔
      Sigma.formB (Multiplicative.toAdd (N.ψQ q)) (Multiplicative.toAdd (N.ψU u)) = 0 := by
  rw [N.formB_ψQ, pairF, ← N.comm_congr (pCoreOf_le 2 _ q.2)
    (show N.ψU u = N.ψU (N.uOf (Multiplicative.toAdd (N.ψU u))) from
      Multiplicative.toAdd.injective (by rw [N.ψU_uOf])), zval_eq_zero_iff]

theorem ψQ_eq_one_iff (q : ruQ N.T) :
    N.ψQ q = 1 ↔ ∀ u ∈ ruU N.L N.T, (q : G) * u = u * q := by
  constructor
  · intro h u hu
    have e := (N.comm_eq_one_iff q ⟨u, hu⟩).mpr (by
      rw [h, toAdd_one]
      have := Sigma.formB_add_left 0 0 (Multiplicative.toAdd (N.ψU ⟨u, hu⟩))
      rw [add_zero] at this
      exact add_eq_left.mp this.symm)
    calc (q : G) * u = q * u * (q : G)⁻¹ * u⁻¹ * u * q := by group
      _ = u * q := by rw [show (q : G) * u * (q : G)⁻¹ * u⁻¹ = 1 from e, one_mul]
  · intro h
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    apply Sigma.formB_nondeg
    intro x
    have := (N.comm_eq_one_iff q (N.uOf x)).mp (by
      rw [h _ (N.uOf x).2]
      group)
    rwa [N.ψU_uOf] at this

omit [Finite G] in
theorem conj_mem_Q {h q : G} (hh : h ∈ ruH N.T) (hq : q ∈ ruQ N.T) : h * q * h⁻¹ ∈ ruQ N.T :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh) q).mp hq

omit [Finite G] in
theorem pairF_conj {h q : G} (hh : h ∈ ruH N.T) (hq : q ∈ ruQ N.T) (x : Fin 2 → F4) :
    N.pairF (h * q * h⁻¹) (sigmaAct (N.φ ⟨h, hh⟩) x) = N.pairF q x := by
  unfold pairF
  have hqH : h * q * h⁻¹ ∈ ruH N.T := pCoreOf_le 2 _ (N.conj_mem_Q hh hq)
  have e : N.ψU (N.uOf (sigmaAct (N.φ ⟨h, hh⟩) x)) =
      N.ψU ⟨h * N.uOf x * h⁻¹, N.conj_mem_U hh (N.uOf x).2⟩ := by
    apply Multiplicative.toAdd.injective
    rw [N.ψU_uOf, N.ψU_conj ⟨h, hh⟩ (N.uOf x), N.ψU_uOf]
  rw [N.comm_congr hqH e]
  congr 1
  have hcZ := N.comm_mem_Z hq (N.uOf x).2
  have hc : h * (q * N.uOf x * q⁻¹ * (N.uOf x : G)⁻¹) * h⁻¹ =
      q * N.uOf x * q⁻¹ * (N.uOf x : G)⁻¹ := by
    rw [(N.Z_comm_H hcZ hh).symm, mul_inv_cancel_right]
  rw [← hc]
  group

theorem ψQ_conj (h : ruH N.T) (q : ruQ N.T) :
    Multiplicative.toAdd (N.ψQ ⟨h * q * (h : G)⁻¹, N.conj_mem_Q h.2 q.2⟩) =
      sigmaAct (N.φ h) (Multiplicative.toAdd (N.ψQ q)) := by
  refine Sigma.formB_inj fun y => ?_
  have hy : y = sigmaAct (N.φ h) (sigmaAct (N.φ h)⁻¹ y) := by
    rw [← Sigma.sigmaAct_mul, mul_inv_cancel, Sigma.sigmaAct_one]
  rw [hy, N.formB_ψQ, Sigma.formB_sigmaAct, N.formB_ψQ]
  exact N.pairF_conj h.2 q.2 _

theorem exists_Q_not_comm : ∃ q ∈ ruQ N.T, (q : G) * N.v1V ≠ N.v1V * q := by
  obtain ⟨g, hg, hmove⟩ := SL3.exists_R0_move
  rw [← N.θQ_eq] at hg
  obtain ⟨⟨q, hqL⟩, hq, rfl⟩ := hg
  refine ⟨q, Subgroup.mem_subgroupOf.mp hq, fun e => hmove ?_⟩
  have h := (N.toRuData.conj_eq_iff ⟨q, hqL⟩ N.v1V).mp (by
    simp only
    rw [e, mul_inv_cancel_right])
  have e1 : Multiplicative.toAdd (N.ψV N.v1V) = ![0, 1, 0] := by simp [v1V]
  rwa [e1] at h

theorem ψQ_surjective : Function.Surjective N.ψQ := by
  obtain ⟨q₀, hq₀, hne⟩ := N.exists_Q_not_comm
  have hw₀ : Multiplicative.toAdd (N.ψQ ⟨q₀, hq₀⟩) ≠ 0 := by
    intro h0
    apply hne
    have : N.ψQ ⟨q₀, hq₀⟩ = 1 := Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    exact (N.ψQ_eq_one_iff _).mp this _ (N.V_le_U N.v1V.2)
  intro y
  by_cases hy : Multiplicative.toAdd y = 0
  · refine ⟨1, ?_⟩
    rw [map_one]
    exact Multiplicative.toAdd.injective (by rw [toAdd_one, hy])
  obtain ⟨x, hx⟩ := Sigma.exists_sigmaAct_eq hw₀ hy
  obtain ⟨h, rfl⟩ := N.φ_surj x
  refine ⟨⟨_, N.conj_mem_Q h.2 hq₀⟩, Multiplicative.toAdd.injective ?_⟩
  rw [N.ψQ_conj h ⟨q₀, hq₀⟩, hx]

theorem exists_comm_eq (w : Fin 2 → F4) : ∃ q ∈ ruQ N.T, ∀ u : ruU N.L N.T,
    zval ((q : G) * u * q⁻¹ * (u : G)⁻¹) = Sigma.formB w (Multiplicative.toAdd (N.ψU u)) := by
  obtain ⟨q, hq⟩ := N.ψQ_surjective (Multiplicative.ofAdd w)
  refine ⟨q, q.2, fun u => ?_⟩
  have e := N.formB_ψQ q (Multiplicative.toAdd (N.ψU u))
  rw [hq, toAdd_ofAdd] at e
  rw [e, pairF, N.comm_congr (pCoreOf_le 2 _ q.2)
    (show N.ψU u = N.ψU (N.uOf (Multiplicative.toAdd (N.ψU u))) from
      Multiplicative.toAdd.injective (by rw [N.ψU_uOf]))]

theorem mem_Z_of_comm_Q {u : G} (hu : u ∈ ruU N.L N.T)
    (hc : ∀ q ∈ ruQ N.T, q * u = u * q) : u ∈ ruZ N.T := by
  rw [← N.ψU_eq_one_iff ⟨u, hu⟩]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  apply Sigma.formB_nondeg
  intro w
  rw [Sigma.formB_comm]
  obtain ⟨q, hq⟩ := N.ψQ_surjective (Multiplicative.ofAdd w)
  have := (N.comm_eq_one_iff q ⟨u, hu⟩).mp (by
    simp only
    rw [hc q q.2]
    group)
  rwa [hq, toAdd_ofAdd] at this

omit [Finite G] in
theorem HC_le_Q : N.HC ≤ ruQ N.T := by
  intro h hh
  obtain ⟨hhH, hhc⟩ := Subgroup.mem_inf.mp hh
  have h1 : N.φ ⟨h, hhH⟩ = 1 := by
    apply Sigma.eq_one_of_sigmaAct_eq
    intro x
    have e := N.ψU_conj ⟨h, hhH⟩ (N.uOf x)
    have hcomm : h * (N.uOf x : G) * h⁻¹ = N.uOf x := by
      rw [← Subgroup.mem_centralizer_iff.mp hhc _ (N.uOf x).2, mul_inv_cancel_right]
    simp only [hcomm, N.ψU_uOf] at e
    exact e.symm
  have : (⟨h, hhH⟩ : ruH N.T) ∈ N.φ.ker := h1
  rw [N.φ_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem ψQ_ker : N.ψQ.ker = N.HC.subgroupOf (ruQ N.T) := by
  ext q
  rw [MonoidHom.mem_ker, N.ψQ_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨pCoreOf_le 2 _ q.2, fun u hu => (h u hu).symm⟩
  · rintro ⟨-, h⟩ u hu
    exact (h u hu).symm

theorem card_HC : Nat.card N.HC = 2 ^ 7 := by
  have h := Subgroup.card_ker_mul_card_of_surjective N.ψQ_surjective
  rw [N.ψQ_ker, card_subgroupOf_of_le N.HC_le_Q, N.toRuData.card_Q, RuData.card_F4sq] at h
  omega

theorem U_le_HC : ruU N.L N.T ≤ N.HC := fun u hu =>
  Subgroup.mem_inf.mpr ⟨N.U_le_H hu, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subtype.ext_iff.mp (N.U_elem.1.1.1 ⟨v, hv⟩ ⟨u, hu⟩)⟩

end RuDataN

end CFSG.Quasithin.RuType
