module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.CGT.Timmesfeld75.L2Defs
public import CFSG.LieType.BorelTits.Basic

import CFSG.CGT.PushingUpLit.Glue.NaturalIrred

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

section NatSecVec

variable {G : Type*} [Group G] {E : Subgroup G} {F : Type*} [Field F]

noncomputable def natSecVec (β : ↥E →* Multiplicative (Fin 2 → F)) (x : G) : Fin 2 → F :=
  haveI := Classical.propDecidable (x ∈ E)
  if h : x ∈ E then Multiplicative.toAdd (β ⟨x, h⟩) else 0

theorem natSecVec_of_mem (β : ↥E →* Multiplicative (Fin 2 → F)) {x : G} (hx : x ∈ E) :
    natSecVec β x = Multiplicative.toAdd (β ⟨x, hx⟩) := by
  unfold natSecVec
  rw [dif_pos hx]

theorem natSecVec_mul (β : ↥E →* Multiplicative (Fin 2 → F)) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : natSecVec β (x * y) = natSecVec β x + natSecVec β y := by
  rw [natSecVec_of_mem β (E.mul_mem hx hy), natSecVec_of_mem β hx, natSecVec_of_mem β hy]
  change Multiplicative.toAdd (β (⟨x, hx⟩ * ⟨y, hy⟩)) = _
  rw [map_mul, toAdd_mul]

theorem natSecVec_inv (β : ↥E →* Multiplicative (Fin 2 → F)) {x : G} (hx : x ∈ E) :
    natSecVec β x⁻¹ = -natSecVec β x := by
  rw [natSecVec_of_mem β (E.inv_mem hx), natSecVec_of_mem β hx]
  change Multiplicative.toAdd (β (⟨x, hx⟩⁻¹)) = _
  rw [map_inv, toAdd_inv]

theorem natSecVec_eq_zero_iff {β : ↥E →* Multiplicative (Fin 2 → F)} {N : Subgroup G}
    (hker : β.ker = N.subgroupOf E) {x : G} (hx : x ∈ E) : natSecVec β x = 0 ↔ x ∈ N := by
  rw [natSecVec_of_mem β hx, toAdd_eq_zero, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]

theorem natSecVec_eq_iff {β : ↥E →* Multiplicative (Fin 2 → F)} {N : Subgroup G}
    (hker : β.ker = N.subgroupOf E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    natSecVec β x = natSecVec β y ↔ x⁻¹ * y ∈ N := by
  rw [← natSecVec_eq_zero_iff hker (E.mul_mem (E.inv_mem hx) hy),
    natSecVec_mul β (E.inv_mem hx) hy, natSecVec_inv β hx, neg_add_eq_zero]

theorem exists_natSecVec_eq {β : ↥E →* Multiplicative (Fin 2 → F)} (hβ : Function.Surjective β)
    (v : Fin 2 → F) : ∃ x ∈ E, natSecVec β x = v := by
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd v)
  refine ⟨u, u.2, ?_⟩
  rw [natSecVec_of_mem β u.2, Subtype.coe_eta, hu, toAdd_ofAdd]

variable {L : Subgroup G} {α : ↥L →* SL(2, F)} {β : ↥E →* Multiplicative (Fin 2 → F)}

theorem natSecVec_conj
    (hβ : ∀ ℓ : ↥L, ∀ u v : ↥E, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (ℓ : ↥L) {x : G} (hx : x ∈ E) (hc : (ℓ : G) * x * (ℓ : G)⁻¹ ∈ E) :
    natSecVec β ((ℓ : G) * x * (ℓ : G)⁻¹) =
      (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ natSecVec β x := by
  rw [natSecVec_of_mem β hc, natSecVec_of_mem β hx]
  exact hβ ℓ ⟨x, hx⟩ ⟨_, hc⟩ rfl

theorem natSecVec_commutator
    (hβ : ∀ ℓ : ↥L, ∀ u v : ↥E, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (ℓ : ↥L) {x : G} (hx : x ∈ E) (hc : (ℓ : G) * x * (ℓ : G)⁻¹ ∈ E) :
    natSecVec β ⁅(ℓ : G), x⁆ =
      (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ natSecVec β x - natSecVec β x := by
  rw [commutatorElement_def, natSecVec_mul β hc (E.inv_mem hx), natSecVec_conj hβ ℓ hx hc,
    natSecVec_inv β hx, sub_eq_add_neg]

theorem natSec_mem_of_conj_mem (hα : Function.Surjective α) (hβinj : Function.Injective β)
    (hβ : ∀ ℓ : ↥L, ∀ u v : ↥E, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hLE : L ≤ Subgroup.normalizer (E : Set G)) {X : Set G}
    (hX : ∀ ℓ ∈ L, ∀ x ∈ X, ℓ * x * ℓ⁻¹ ∈ X) {y : G} (hyE : y ∈ E) (hyX : y ∈ X)
    (hy : y ≠ 1) {z : G} (hzE : z ∈ E) (hz : z ≠ 1) : z ∈ X := by
  have hne : ∀ {x : G} (hx : x ∈ E), x ≠ 1 → natSecVec β x ≠ 0 := by
    intro x hx hx1 h0
    apply hx1
    rw [natSecVec_of_mem β hx, toAdd_eq_zero, ← map_one β] at h0
    exact congrArg Subtype.val (hβinj h0)
  obtain ⟨g, hg⟩ :=
    CFSG.CGT.PushingUpLit.Glue.exists_sl2_mulVec_eq_of_ne_zero (hne hyE hy) (hne hzE hz)
  obtain ⟨ℓ, rfl⟩ := hα g
  have hc : (ℓ : G) * y * (ℓ : G)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hLE ℓ.2) y).mp hyE
  have h1 : natSecVec β ((ℓ : G) * y * (ℓ : G)⁻¹) = natSecVec β z := by
    rw [natSecVec_conj hβ ℓ hyE hc]
    exact hg
  rw [natSecVec_of_mem β hc, natSecVec_of_mem β hzE] at h1
  have h2 : (⟨(ℓ : G) * y * (ℓ : G)⁻¹, hc⟩ : ↥E) = ⟨z, hzE⟩ :=
    hβinj (Multiplicative.toAdd.injective h1)
  have h3 : (ℓ : G) * y * (ℓ : G)⁻¹ = z := congrArg Subtype.val h2
  rw [← h3]
  exact hX ℓ ℓ.2 y hyX

end NatSecVec

section SL2Vec

variable {F : Type} [Field F]

theorem utriElt_mulVec_apply_zero (s : F) (v : Fin 2 → F) :
    (((utriElt s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 0 = v 0 + s * v 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [utriElt_apply_00, utriElt_apply_01, one_mul]

theorem utriElt_mulVec_apply_one (s : F) (v : Fin 2 → F) :
    (((utriElt s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 1 = v 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [utriElt_apply_10, utriElt_apply_11, zero_mul, one_mul, zero_add]

theorem ltriElt_mulVec_apply_one (t : F) (v : Fin 2 → F) :
    (((ltriElt t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) 1 = t * v 0 + v 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ltriElt_apply_10, ltriElt_apply_11, one_mul]

theorem eq_zero_of_forall_sl2_mulVec_eq {v : Fin 2 → F}
    (h : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : v = 0 := by
  have h1 : v 1 = 0 := by
    have k := congrFun (h (utriElt 1)) 0
    rw [utriElt_mulVec_apply_zero, one_mul] at k
    linear_combination k
  have h0 : v 0 = 0 := by
    have k := congrFun (h (ltriElt 1)) 1
    rw [ltriElt_mulVec_apply_one, one_mul] at k
    linear_combination k
  ext i
  fin_cases i <;> simp [h0, h1]

theorem conj_utriElt_eq_of_mem_borel {g : SL(2, F)} (hg : g ∈ borel F) (r : F) :
    g * utriElt r * g⁻¹ = utriElt (g 0 0 ^ 2 * r) :=
  (eq_utriElt_of_mem_utri (conj_mem_utri_of_mem_borel hg (utriElt_mem_utri r))).trans
    (by rw [conj_utriElt_apply_01])

end SL2Vec

section Commutator

variable {G : Type*} [Group G] {L E : Subgroup G} {F : Type} [Field F]

theorem exists_commutator_natSecVec_eq {α : ↥L →* SL(2, F)} (hα : Function.Surjective α)
    {β : ↥E →* Multiplicative (Fin 2 → F)} (hβs : Function.Surjective β)
    (hβ : ∀ ℓ : ↥L, ∀ u v : ↥E, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hLE : L ≤ Subgroup.normalizer (E : Set G)) (x : G) :
    ∃ y ∈ ⁅L, E⁆, y ∈ E ∧ natSecVec β y = natSecVec β x := by
  obtain ⟨u₁, hu₁, hv₁⟩ := exists_natSecVec_eq hβs ![0, natSecVec β x 0]
  obtain ⟨u₂, hu₂, hv₂⟩ := exists_natSecVec_eq hβs ![natSecVec β x 1, 0]
  obtain ⟨l₁, hl₁⟩ := hα (utriElt 1)
  obtain ⟨l₂, hl₂⟩ := hα (ltriElt 1)
  have hc₁ : (l₁ : G) * u₁ * (l₁ : G)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hLE l₁.2) u₁).mp hu₁
  have hc₂ : (l₂ : G) * u₂ * (l₂ : G)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hLE l₂.2) u₂).mp hu₂
  have hm₁ : ⁅(l₁ : G), u₁⁆ ∈ E := mul_mem hc₁ (inv_mem hu₁)
  have hm₂ : ⁅(l₂ : G), u₂⁆ ∈ E := mul_mem hc₂ (inv_mem hu₂)
  refine ⟨⁅(l₁ : G), u₁⁆ * ⁅(l₂ : G), u₂⁆,
    mul_mem (Subgroup.commutator_mem_commutator l₁.2 hu₁)
      (Subgroup.commutator_mem_commutator l₂.2 hu₂), mul_mem hm₁ hm₂, ?_⟩
  rw [natSecVec_mul β hm₁ hm₂, natSecVec_commutator hβ l₁ hu₁ hc₁,
    natSecVec_commutator hβ l₂ hu₂ hc₂, hl₁, hl₂, hv₁, hv₂]
  ext i
  fin_cases i <;>
    simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10, utriElt_apply_11,
      ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

end Commutator

section Groups

variable {G : Type*} [Group G]

theorem mul_comm_of_mem_centerOf {Q : Subgroup G} {z y : G} (hz : z ∈ centerOf Q)
    (hy : y ∈ Q) : y * z = z * y :=
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y hy

theorem mem_centerOf_of_forall_comm {Q : Subgroup G} {z : G} (hz : z ∈ Q)
    (h : ∀ y ∈ Q, y * z = z * y) : z ∈ centerOf Q :=
  Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_iff.mpr h⟩

theorem mem_centerOf_conj_of_mem_normalizer {Q : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hz : z ∈ centerOf Q) :
    g * z * g⁻¹ ∈ centerOf Q := by
  refine mem_centerOf_of_forall_comm
    ((Subgroup.mem_normalizer_iff.mp hg z).mp (Subgroup.mem_inf.mp hz).1) fun y hy => ?_
  have hy' : g⁻¹ * y * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hg y).mp hy
  have key := mul_comm_of_mem_centerOf hz hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [key]
    _ = g * z * g⁻¹ * y := by group

theorem le_normalizer_centerOf_of_le_normalizer {X Q : Subgroup G}
    (h : X ≤ Subgroup.normalizer (Q : Set G)) :
    X ≤ Subgroup.normalizer (centerOf Q : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => mem_centerOf_conj_of_mem_normalizer (h hg) hz, fun hz => ?_⟩
  have := mem_centerOf_conj_of_mem_normalizer (inv_mem (h hg)) hz
  simpa [mul_assoc] using this

theorem le_normalizer_of_forall_conj_mem_of_mem {L K : Subgroup G}
    (h : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) : L ≤ Subgroup.normalizer (K : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h l hl k, fun hk => ?_⟩
  have := h l⁻¹ (inv_mem hl) _ hk
  simpa [mul_assoc] using this

theorem commutator_mul_left_eq_of_mem_centerOf {Q : Subgroup G} {z w b : G}
    (hz : z ∈ centerOf Q) (hw : w ∈ Q) (hb : b ∈ Q) : ⁅z * w, b⁆ = ⁅w, b⁆ := by
  have h1 : z * w = w * z := (mul_comm_of_mem_centerOf hz hw).symm
  have h2 : z * b * z⁻¹ = b := by rw [← mul_comm_of_mem_centerOf hz hb, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def, h1]
  calc w * z * b * (w * z)⁻¹ * b⁻¹ = w * (z * b * z⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = w * b * w⁻¹ * b⁻¹ := by rw [h2]

theorem commutator_mul_right_eq_of_mem_centerOf {Q : Subgroup G} {z w b : G}
    (hz : z ∈ centerOf Q) (hw : w ∈ Q) (hb : b ∈ Q) : ⁅w, z * b⁆ = ⁅w, b⁆ := by
  have h1 : w * z = z * w := mul_comm_of_mem_centerOf hz hw
  have hC : ⁅w, b⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hw hb) (Q.inv_mem hw)) (Q.inv_mem hb)
  have h2 : z * ⁅w, b⁆ * z⁻¹ = ⁅w, b⁆ := by
    rw [← mul_comm_of_mem_centerOf hz hC, mul_inv_cancel_right]
  calc ⁅w, z * b⁆ = w * z * b * w⁻¹ * b⁻¹ * z⁻¹ := by rw [commutatorElement_def]; group
    _ = z * w * b * w⁻¹ * b⁻¹ * z⁻¹ := by rw [h1]
    _ = z * ⁅w, b⁆ * z⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅w, b⁆ := h2

theorem conj_mem_pCoreOf_of_mem {L : Subgroup G} {l x : G} (hl : l ∈ L)
    (hx : x ∈ pCoreOf 2 L) : l * x * l⁻¹ ∈ pCoreOf 2 L :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hl) x).mp hx

theorem commutator_mem_pCoreOf_of_mem {L : Subgroup G} {l x : G} (hl : l ∈ L)
    (hx : x ∈ pCoreOf 2 L) : ⁅l, x⁆ ∈ pCoreOf 2 L := by
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_pCoreOf_of_mem hl hx) (inv_mem hx)

theorem commutator_pCoreOf_le_pCoreOf (L : Subgroup G) : ⁅pCoreOf 2 L, L⁆ ≤ pCoreOf 2 L := by
  rw [Subgroup.commutator_le]
  intro x hx l hl
  rw [commutatorElement_def, show x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) by group]
  exact mul_mem hx (conj_mem_pCoreOf_of_mem hl (inv_mem hx))

theorem exists_pow_two_pow_eq_one_of_mem_pCoreOf [Finite G] {L : Subgroup G} {y : G}
    (hy : y ∈ pCoreOf 2 L) : ∃ m : ℕ, y ^ (2 ^ m) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 L ⟨y, hy⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem mem_of_conj_eq_mul_of_odd {K : Subgroup G} {h x y : G} {n m : ℕ} (hn : Odd n)
    (hhn : h ^ n = 1) (hhK : ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hym : y ^ (2 ^ m) = 1) (hhy : h * y * h⁻¹ * y⁻¹ ∈ K) (hx : h * x * h⁻¹ = y * x) :
    y ∈ K := by
  have hyk : ∀ j : ℕ, ∀ k ∈ K, y ^ j * k * (y ^ j)⁻¹ ∈ K := by
    intro j
    induction j with
    | zero => intro k hk; simpa using hk
    | succ j ih =>
      intro k hk
      rw [pow_succ', show y * y ^ j * k * (y * y ^ j)⁻¹ = y * (y ^ j * k * (y ^ j)⁻¹) * y⁻¹ by
        group]
      exact hyK _ (ih k hk)
  have hpow : ∀ j : ℕ, h * y ^ j * h⁻¹ * (y ^ j)⁻¹ ∈ K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show h * y ^ (j + 1) * h⁻¹ * (y ^ (j + 1))⁻¹ =
          (h * y ^ j * h⁻¹ * (y ^ j)⁻¹) * (y ^ j * (h * y * h⁻¹ * y⁻¹) * (y ^ j)⁻¹) by
        rw [pow_succ]; group]
      exact K.mul_mem ih (hyk j _ hhy)
  have hiter : ∀ j : ℕ, h ^ j * x * (h ^ j)⁻¹ * x⁻¹ * (y ^ j)⁻¹ ∈ K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : h ^ (j + 1) * x * (h ^ (j + 1))⁻¹ * x⁻¹ * (y ^ (j + 1))⁻¹ =
          (h * (h ^ j * x * (h ^ j)⁻¹ * x⁻¹ * (y ^ j)⁻¹) * h⁻¹) *
            (h * y ^ j * h⁻¹ * (y ^ j)⁻¹) * (y ^ j * (h * x * h⁻¹ * x⁻¹ * y⁻¹) * (y ^ j)⁻¹) := by
        rw [pow_succ', pow_succ]
        group
      have h3 : y ^ j * (h * x * h⁻¹ * x⁻¹ * y⁻¹) * (y ^ j)⁻¹ = 1 := by
        rw [hx]
        group
      rw [e, h3, mul_one]
      exact K.mul_mem (hhK _ ih) (hpow j)
  have hyn : y ^ n ∈ K := by simpa [hhn] using hiter n
  have hcop : Nat.Coprime n (orderOf y) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hym)
      (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hn))
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk]
  exact K.pow_mem hyn k

theorem conj_eq_of_odd_of_fixed {h x : G} {n m : ℕ} (hn : Odd n) (hhn : h ^ n = 1)
    (hm : (h * x * h⁻¹ * x⁻¹) ^ (2 ^ m) = 1)
    (hfix : h * (h * x * h⁻¹ * x⁻¹) * h⁻¹ = h * x * h⁻¹ * x⁻¹) : h * x * h⁻¹ = x := by
  have hy := mem_of_conj_eq_mul_of_odd (K := ⊥) (x := x) hn hhn
    (fun k hk => by rw [Subgroup.mem_bot.mp hk]; simp)
    (fun k hk => by rw [Subgroup.mem_bot.mp hk]; simp) hm
    (by rw [hfix, mul_inv_cancel]; exact one_mem _) (by group)
  rwa [Subgroup.mem_bot, mul_inv_eq_one] at hy

end Groups

end CFSG.Quasithin.F112R.St84

end
