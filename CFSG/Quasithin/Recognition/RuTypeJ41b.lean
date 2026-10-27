module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.RuTypeJ27c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem eq_one_of_fixed_of_dRange {A : Type*} [CommGroup A] (hA : ∀ a : A, a * a = 1)
    (σ : A →* A) (h5 : ∀ a, σ^[5] a = a) {c : A} (hv : σ (σ c * c⁻¹) = σ c * c⁻¹) :
    σ c * c⁻¹ = 1 := by
  set v := σ c * c⁻¹ with hvdef
  have hfix : ∀ i, σ^[i] v = v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, hv]
  have h1 : ∏ i ∈ Finset.range 5, σ^[i] v = v := by
    simp only [hfix, Finset.prod_const, Finset.card_range]
    have h2 : v ^ 2 = 1 := by rw [pow_two]; exact hA v
    calc v ^ 5 = (v ^ 2) ^ 2 * v := by rw [← pow_mul, ← pow_succ]
      _ = v := by rw [h2, one_pow, one_mul]
  have h2 : ∏ i ∈ Finset.range 5, σ^[i] v = 1 := by
    have e : ∀ i, σ^[i] v = σ^[i + 1] c / σ^[i] c := by
      intro i
      rw [hvdef, iterate_map_mul, iterate_map_inv, ← Function.iterate_succ_apply, div_eq_mul_inv]
    simp only [e]
    rw [Finset.prod_range_div (fun i => σ^[i] c) 5, h5, Function.iterate_zero_apply, div_self']
  rw [← h1, h2]

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G)

@[expose, instance_reducible] noncomputable def qbarComm : CommGroup M.Qbar :=
  { (inferInstance : Group M.Qbar) with mul_comm := M.Qbar_comm }

theorem qbar_rearr (x y z w : M.Qbar) : x * y * (z * w) = x * z * (y * w) := by
  rw [mul_assoc x y, ← mul_assoc y z w, M.Qbar_comm y z, mul_assoc z y w, ← mul_assoc x z]

theorem actQ_mul_apply (h h' : ruH M.T) (a : M.Qbar) :
    M.actQ (h * h') a = M.actQ h (M.actQ h' a) := by
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [M.actQ_mk, M.actQ_mk, M.actQ_mk]
  congr 1
  apply Subtype.ext
  show (h : G) * (h' : G) * q * ((h : G) * h')⁻¹ = h * (h' * q * (h' : G)⁻¹) * (h : G)⁻¹
  group

theorem actQ_one_apply (a : M.Qbar) : M.actQ 1 a = a := by
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [M.actQ_mk]
  congr 1
  apply Subtype.ext
  show (1 : G) * q * (1 : G)⁻¹ = q
  group

theorem actQ_iterate (h : ruH M.T) (n : ℕ) (a : M.Qbar) : (M.actQ h)^[n] a = M.actQ (h ^ n) a := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, M.actQ_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', M.actQ_mul_apply]

@[expose] noncomputable def dQ (h : ruH M.T) : M.Qbar →* M.Qbar where
  toFun a := M.actQ h a * a⁻¹
  map_one' := by rw [map_one, inv_one, mul_one]
  map_mul' a a' := by
    rw [map_mul, mul_inv_rev, M.Qbar_comm a'⁻¹ a⁻¹, M.qbar_rearr]

theorem dQ_apply (h : ruH M.T) (a : M.Qbar) : M.dQ h a = M.actQ h a * a⁻¹ := rfl

noncomputable abbrev Q5bar (h : ruH M.T) : Subgroup M.Qbar := (M.dQ h).range

noncomputable abbrev HCbar : Subgroup M.Qbar :=
  (M.HC.subgroupOf (ruQ M.T)).map (QuotientGroup.mk' M.UQ)

variable [Finite G]

theorem mem_HCbar_mk (q : ruQ M.T) : (q : M.Qbar) ∈ M.HCbar ↔ (q : G) ∈ M.HC := by
  constructor
  · rintro ⟨q', hq', he⟩
    have hq'' : (q' : G) ∈ M.HC := hq'
    have e : (q' : M.Qbar) = (q : M.Qbar) := he
    rw [M.mk_eq_mk_iff] at e
    have hq : (q : G) = q' * ((q' : G)⁻¹ * q) := by group
    rw [hq]
    exact mul_mem hq'' (M.U_le_HC e)
  · intro hq
    exact ⟨q, Subgroup.mem_subgroupOf.mpr hq, rfl⟩

theorem card_HCbar : Nat.card M.HCbar = 4 := by
  have hpre : (QuotientGroup.mk : ruQ M.T → M.Qbar) ⁻¹' (M.HCbar : Set M.Qbar) =
      ((M.HC.subgroupOf (ruQ M.T)) : Set (ruQ M.T)) := by
    ext q
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact M.mem_HCbar_mk q
  have h := QuotientGroup.card_preimage_mk M.UQ (M.HCbar : Set M.Qbar)
  rw [hpre] at h
  have h1 : Nat.card ((M.HC.subgroupOf (ruQ M.T)) : Set (ruQ M.T)) = 2 ^ 7 := by
    show Nat.card (M.HC.subgroupOf (ruQ M.T)) = 2 ^ 7
    rw [card_subgroupOf_of_le M.HC_le_Q, M.card_HC]
  rw [h1, card_subgroupOf_of_le M.U_le_Q, M.toRuData.card_U] at h
  have h2 : Nat.card (M.HCbar : Set M.Qbar) = Nat.card M.HCbar := rfl
  rw [h2] at h
  omega

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem ker_dQ : (M.dQ ⟨b, hbH⟩).ker = M.HCbar := by
  ext a
  induction a using QuotientGroup.induction_on with
  | H q =>
  rw [MonoidHom.mem_ker, M.dQ_apply, mul_inv_eq_one, M.mem_HCbar_mk, M.actQ_mk]
  constructor
  · intro h
    have hψ := congrArg (fun a => Multiplicative.toAdd (M.ψQbar a)) h
    have e := M.ψQbar_actQ ⟨b, hbH⟩ (q : M.Qbar)
    rw [M.actQ_mk] at e
    rw [e] at hψ
    have h0 := Sigma.fix_order_five _ (φ_b_props hbH hb5) _ hψ
    have h1 : M.ψQ q = 1 := by
      rw [← M.ψQbar_mk]
      exact Multiplicative.toAdd.injective h0
    have h2 : q ∈ M.ψQ.ker := h1
    rw [M.ψQ_ker, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro hq
    have hb := M.comm_HC_of_pow_five hbH (pow_five_of_orderOf hb5) _ hq
    rw [M.mk_eq_mk_iff]
    show (b * q * b⁻¹)⁻¹ * q ∈ ruU M.L M.T
    have e : (b * (q : G) * b⁻¹)⁻¹ * q = (q : G)⁻¹ * (b * q * b⁻¹ * (q : G)⁻¹)⁻¹ * q := by group
    rw [e]
    have hqH : (q : G)⁻¹ ∈ ruH M.T := inv_mem (pCoreOf_le 2 _ q.2)
    have := M.conj_mem_U hqH (inv_mem hb)
    simpa using this

omit [Finite G] in
theorem actQ_b_iterate_five (a : M.Qbar) : (M.actQ ⟨b, hbH⟩)^[5] a = a := by
  rw [M.actQ_iterate]
  have : (⟨b, hbH⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext (by simp [pow_five_of_orderOf hb5])
  rw [this, M.actQ_one_apply]

theorem Q5bar_inf_HCbar : M.Q5bar ⟨b, hbH⟩ ⊓ M.HCbar = ⊥ := by
  let _ : CommGroup M.Qbar := M.qbarComm
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨c, rfl⟩ := hx1
  rw [Subgroup.mem_bot]
  have hk : M.dQ ⟨b, hbH⟩ c ∈ (M.dQ ⟨b, hbH⟩).ker := by rw [ker_dQ hbH hb5]; exact hx2
  rw [MonoidHom.mem_ker, M.dQ_apply, mul_inv_eq_one] at hk
  exact eq_one_of_fixed_of_dRange M.Qbar_sq (M.actQ ⟨b, hbH⟩) (actQ_b_iterate_five hbH hb5) hk

theorem card_Q5bar : Nat.card (M.Q5bar ⟨b, hbH⟩) = 16 := by
  show Nat.card (M.dQ ⟨b, hbH⟩).range = 16
  have h := Subgroup.card_ker_mul_card_range (M.dQ ⟨b, hbH⟩)
  rw [ker_dQ hbH hb5, M.card_HCbar, M.card_Qbar] at h
  omega

end Five

end RuDataM

end CFSG.Quasithin.RuType
