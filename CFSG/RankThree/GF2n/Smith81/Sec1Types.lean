module

public import CFSG.RankThree.GF2n.Smith81.Sec1Model
public import CFSG.RankThree.GF2n.Smith81.Sec1
public import CFSG.RankThree.GF2n.Stroth80.Ctx

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjOrbit (S : Subgroup G) (x : G) : Set G := {y | ∃ s ∈ S, y = s * x * s⁻¹}

@[expose] def cosetSet (x : G) (Z : Subgroup G) : Set G := (fun z => x * z) '' (Z : Set G)

@[expose] def HasDim (Q Z : Subgroup G) (k : ℕ) (x : G) : Prop :=
  Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (k + 1)

@[expose] def Lin (Q Z : Subgroup G) (x : G) : Prop :=
  x ∈ Subgroup.normalizer (Q : Set G) ∧ x ∉ Q ∧ ∀ z ∈ Z, x * z * x⁻¹ = z

@[expose] def IsTypeA (Q Z : Subgroup G) (k : ℕ) (x : G) : Prop :=
  Lin Q Z x ∧ HasDim Q Z k x ∧ ∀ q ∈ Q, ⁅q, x * q * x⁻¹⁆ = 1

section Group

variable {Q : Subgroup G} {x : G}

theorem mem_zpowers_of_mul_self_eq_one (hx : x * x = 1) {y : G} (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨n, rfl⟩ := hy
  show x ^ n = 1 ∨ x ^ n = x
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem commutator_zpowers_eq_closure (hx : x * x = 1) :
    ⁅Q, Subgroup.zpowers x⁆ = Subgroup.closure {g | ∃ q ∈ Q, ⁅q, x⁆ = g} := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q hq t ht
    rcases mem_zpowers_of_mul_self_eq_one hx ht with rfl | rfl
    · simp only [commutatorElement_one_right]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨q, hq, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)

end Group

section StrothSec

variable [Finite G] {M Q Z : Subgroup G}

theorem conj_mem_Q (H : StrothHyp M Q Z) {x : G} (hxM : x ∈ M) {q : G} (hq : q ∈ Q) :
    x * q * x⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hxM) q).mp hq

theorem comm_mem_Q (H : StrothHyp M Q Z) {x : G} (hxM : x ∈ M) {q : G} (hq : q ∈ Q) :
    ⁅q, x⁆ ∈ Q := by
  have h := Q.mul_mem hq (Q.inv_mem (conj_mem_Q H hxM hq))
  have e : ⁅q, x⁆ = q * (x * q * x⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rwa [e]

theorem sq_mem_Z (H : StrothHyp M Q Z) {q : G} (hq : q ∈ Q) : q ^ 2 ∈ Z :=
  H.toHyp79.sq_mem_V hq

theorem comm_mem_Z (H : StrothHyp M Q Z) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) : ⁅a, b⁆ ∈ Z :=
  H.toHyp79.comm_mem_V ha hb

theorem Z_central (H : StrothHyp M Q Z) {z q : G} (hz : z ∈ Z) (hq : q ∈ Q) :
    z * q = q * z :=
  H.toHyp79.V_central hz hq

theorem Z_sq (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) : z ^ 2 = 1 :=
  H.toHyp79.sq_eq_one z hz

end StrothSec

section XAction

variable [Finite G] {M Q Z : Subgroup G} {K : Type} [Field K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

structure XAct (M₀ : Tim79.QuadModel Q Z K γ) (x : G) where
  T : M₀.E ≃ₗ[K] M₀.E
  hπ : ∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)
  hQ : ∀ e, M₀.Qf (T e) = M₀.Qf e
  hB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f

theorem exists_xact (hD : GlobalModelData M Q Z γ M₀) {x : G} (hxM : x ∈ M)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) : Nonempty (XAct M₀ x) := by
  obtain ⟨T, h1, h2, h3⟩ := hD.linear_of_centralizes hxM hxZ
  exact ⟨⟨T, h1, h2, h3⟩⟩

variable {x : G}

theorem XAct.T_T (A : XAct M₀ x) (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1)
    (e : M₀.E) : A.T (A.T e) = e := by
  obtain ⟨y, hy, rfl⟩ := M₀.π_surj e
  rw [← A.hπ y hy, ← A.hπ _ (conj_mem_Q H hxM hy)]
  congr 1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [hxinv]
  calc x * (x * y * x) * x = (x * x) * y * (x * x) := by group
    _ = y := by rw [hx2]; simp

theorem XAct.pi_comm (A : XAct M₀ x) (H : StrothHyp M Q Z) (hxM : x ∈ M) {q : G} (hq : q ∈ Q) :
    M₀.π ⁅q, x⁆ = M₀.π q - A.T (M₀.π q) := by
  have hu := conj_mem_Q H hxM hq
  have e : ⁅q, x⁆ = q * (x * q * x⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, M₀.π_mul q hq _ (Q.inv_mem hu), Tim79.QuadModel.pi_inv M₀ hu, A.hπ q hq]
  exact (sub_eq_add_neg _ _).symm

theorem XAct.B_comm_gen (A : XAct M₀ x) (hK2 : (2 : K) = 0) (H : StrothHyp M Q Z) (hxM : x ∈ M)
    (hx2 : x * x = 1) {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    M₀.B (M₀.π ⁅q, x⁆) (M₀.π ⁅q', x⁆) = 0 := by
  rw [A.pi_comm H hxM hq, A.pi_comm H hxM hq']
  set e := M₀.π q
  set e' := M₀.π q'
  have h1 : M₀.B (A.T e) e' = M₀.B e (A.T e') := by
    have := A.hB (A.T e) e'
    rw [A.T_T H hxM hx2] at this
    exact this.symm
  simp only [map_sub, LinearMap.sub_apply]
  rw [A.hB e e', h1]
  linear_combination (M₀.B e e' - M₀.B e (A.T e')) * hK2

end XAction

section DStructure

variable [Finite G] {M Q Z : Subgroup G} {K : Type} [Field K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {x : G}

def commGens (Q : Subgroup G) (x : G) : Set G := {g | ∃ q ∈ Q, ⁅q, x⁆ = g}

theorem gen_comm (hD : GlobalModelData M Q Z γ M₀) (A : XAct M₀ x) (hK2 : (2 : K) = 0)
    (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1) {q q' : G} (hq : q ∈ Q)
    (hq' : q' ∈ Q) : ⁅q, x⁆ * ⁅q', x⁆ = ⁅q', x⁆ * ⁅q, x⁆ :=
  commutatorElement_eq_one_iff_mul_comm.mp
    ((GM.comm_eq_one_iff hD (comm_mem_Q H hxM hq) (comm_mem_Q H hxM hq')).mpr
      (A.B_comm_gen hK2 H hxM hx2 hq hq'))

theorem D_comm (hD : GlobalModelData M Q Z γ M₀) (A : XAct M₀ x) (hK2 : (2 : K) = 0)
    (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1) :
    ∀ a ∈ Subgroup.closure (commGens Q x), ∀ b ∈ Subgroup.closure (commGens Q x),
      a * b = b * a := by
  have hc : IsMulCommutative (Subgroup.closure (commGens Q x)) := by
    refine Subgroup.isMulCommutative_closure ?_
    rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ _
    exact gen_comm hD A hK2 H hxM hx2 hq hq'
  intro a ha b hb
  exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem D_inv (hD : GlobalModelData M Q Z γ M₀) (A : XAct M₀ x) (hK2 : (2 : K) = 0)
    (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1) :
    ∀ y ∈ Subgroup.closure (commGens Q x), x * y * x⁻¹ = y⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨q, hq, rfl⟩ := hy
    simp only [commutatorElement_def]
    have e1 : (q * x * q⁻¹ * x⁻¹)⁻¹ = x * q * x⁻¹ * q⁻¹ := by group
    rw [e1]
    rw [hxinv]
    calc x * (q * x * q⁻¹ * x) * x = x * q * x * q⁻¹ * (x * x) := by group
      _ = x * q * x * q⁻¹ := by rw [hx2, mul_one]
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, iha, ihb, mul_inv_rev]
    exact D_comm hD A hK2 H hxM hx2 a⁻¹ (Subgroup.inv_mem _ ha) b⁻¹ (Subgroup.inv_mem _ hb)
  | inv a ha iha =>
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group, iha]

theorem D_comm_x (hD : GlobalModelData M Q Z γ M₀) (A : XAct M₀ x) (hK2 : (2 : K) = 0)
    (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1) {y : G}
    (hy : y ∈ Subgroup.closure (commGens Q x)) : ⁅y, x⁆ = y ^ 2 := by
  have h := D_inv hD A hK2 H hxM hx2 y hy
  calc ⁅y, x⁆ = y * (x * y * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    _ = y * y := by rw [h, inv_inv]
    _ = y ^ 2 := (sq y).symm

theorem D_le_Q (H : StrothHyp M Q Z) (hxM : x ∈ M) :
    Subgroup.closure (commGens Q x) ≤ Q :=
  (Subgroup.closure_le Q).mpr (by rintro _ ⟨q, hq, rfl⟩; exact comm_mem_Q H hxM hq)

end DStructure

section Equivs

variable [Finite G] {M Q Z : Subgroup G} {K : Type} [Field K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {x : G}

theorem gen_sq_iff (hD : GlobalModelData M Q Z γ M₀) (A : XAct M₀ x) (hK2 : (2 : K) = 0)
    (H : StrothHyp M Q Z) (hxM : x ∈ M) {q : G} (hq : q ∈ Q) :
    ⁅q, x⁆ ^ 2 = 1 ↔ ⁅q, x * q * x⁻¹⁆ = 1 := by
  have hc := comm_mem_Q H hxM hq
  have hu := conj_mem_Q H hxM hq
  rw [GM.sq_eq_one_iff hD hc, GM.comm_eq_one_iff hD hq hu, A.pi_comm H hxM hq, A.hπ q hq]
  set e := M₀.π q
  have h1 : M₀.Qf (e - A.T e) = - M₀.B e (A.T e) := by
    have h := M₀.Qf_add e (-(A.T e))
    have h' := M₀.Qf_smul (-1) (A.T e)
    rw [neg_one_smul] at h'
    rw [sub_eq_add_neg, h, h', map_neg, A.hQ e]
    linear_combination (M₀.Qf e) * hK2
  rw [h1, neg_eq_zero]

theorem D_sq_iff_gen (hD : GlobalModelData M Q Z γ M₀) (A : XAct M₀ x) (hK2 : (2 : K) = 0)
    (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1) :
    (∀ y ∈ Subgroup.closure (commGens Q x), y ^ 2 = 1) ↔ ∀ q ∈ Q, ⁅q, x⁆ ^ 2 = 1 := by
  constructor
  · intro h q hq
    exact h _ (Subgroup.subset_closure ⟨q, hq, rfl⟩)
  · intro h y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      exact h q hq
    | one => simp
    | mul a b ha hb iha ihb =>
      have hcomm : Commute a b := D_comm hD A hK2 H hxM hx2 a ha b hb
      rw [hcomm.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]

def preimageSub (M₀ : Tim79.QuadModel Q Z K γ) (R : Submodule K M₀.E) : Subgroup G where
  carrier := {y | y ∈ Q ∧ M₀.π y ∈ R}
  mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
    rw [M₀.π_mul a ha.1 b hb.1]; exact R.add_mem ha.2 hb.2⟩
  one_mem' := ⟨Q.one_mem, by rw [Tim79.QuadModel.pi_one M₀]; exact R.zero_mem⟩
  inv_mem' := fun {a} ha =>
    ⟨Q.inv_mem ha.1, by rw [Tim79.QuadModel.pi_inv M₀ ha.1]; exact R.neg_mem ha.2⟩

theorem mem_preimageSub {M₀ : Tim79.QuadModel Q Z K γ} {R : Submodule K M₀.E} {y : G} :
    y ∈ preimageSub M₀ R ↔ y ∈ Q ∧ M₀.π y ∈ R := Iff.rfl

def commSpace (A : XAct M₀ x) : Submodule K M₀.E :=
  LinearMap.range ((A.T : M₀.E →ₗ[K] M₀.E) - LinearMap.id)

theorem mem_commSup_iff (A : XAct M₀ x) (H : StrothHyp M Q Z) (hxM : x ∈ M) (hx2 : x * x = 1)
    (hZQ : Z ≤ Q) {y : G} :
    y ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) ↔ y ∈ Q ∧ M₀.π y ∈ commSpace A := by
  have hW : (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) = preimageSub M₀ (commSpace A) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [commutator_zpowers_eq_closure hx2, Subgroup.closure_le]
        rintro _ ⟨q, hq, rfl⟩
        refine ⟨comm_mem_Q H hxM hq, ?_⟩
        rw [A.pi_comm H hxM hq]
        exact ⟨-(M₀.π q), by simp [sub_eq_add_neg, add_comm]⟩
      · intro z hz
        exact ⟨hZQ hz, by rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact Submodule.zero_mem _⟩
    · rintro y ⟨hyQ, e, he⟩
      obtain ⟨q, hq, hπq⟩ := M₀.π_surj (-e)
      have h1 : M₀.π ⁅q, x⁆ = M₀.π y := by
        rw [A.pi_comm H hxM hq, hπq, ← he]
        simp [sub_eq_add_neg, add_comm]
      have h2 : y⁻¹ * ⁅q, x⁆ ∈ Z := by
        refine (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hyQ) (comm_mem_Q H hxM hq))).mp ?_
        rw [M₀.π_mul _ (Q.inv_mem hyQ) _ (comm_mem_Q H hxM hq), Tim79.QuadModel.pi_inv M₀ hyQ, h1]
        exact neg_add_cancel _
      have h3 : y = ⁅q, x⁆ * (y⁻¹ * ⁅q, x⁆)⁻¹ := by group
      rw [h3]
      exact Subgroup.mul_mem_sup
        (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)) (Z.inv_mem h2)
  rw [hW]
  exact Iff.rfl

theorem exists_comm_rep (A : XAct M₀ x) (H : StrothHyp M Q Z) (hxM : x ∈ M) {y : G} (hyQ : y ∈ Q)
    (hy : M₀.π y ∈ commSpace A) : ∃ q ∈ Q, ∃ z₀ ∈ Z, y = ⁅q, x⁆ * z₀ := by
  obtain ⟨e, he⟩ := hy
  obtain ⟨q, hq, hπq⟩ := M₀.π_surj (-e)
  have h1 : M₀.π ⁅q, x⁆ = M₀.π y := by
    rw [A.pi_comm H hxM hq, hπq, ← he]
    simp [sub_eq_add_neg, add_comm]
  have h2 : y⁻¹ * ⁅q, x⁆ ∈ Z := by
    refine (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hyQ) (comm_mem_Q H hxM hq))).mp ?_
    rw [M₀.π_mul _ (Q.inv_mem hyQ) _ (comm_mem_Q H hxM hq), Tim79.QuadModel.pi_inv M₀ hyQ, h1]
    exact neg_add_cancel _
  exact ⟨q, hq, (y⁻¹ * ⁅q, x⁆)⁻¹, Z.inv_mem h2, by group⟩

end Equivs

section Count

variable [Finite G] {M Q Z : Subgroup G} {K : Type} [Field K]
  [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {x : G}

theorem card_preimageSub (hZQ : Z ≤ Q) (R : Submodule K M₀.E) :
    Nat.card (preimageSub M₀ R) = Nat.card R * Nat.card Z := by
  classical
  choose lift hlift_mem hlift using M₀.π_surj
  have hlift_mem' : ∀ r : R, lift r.1 ∈ preimageSub M₀ R := fun r =>
    ⟨hlift_mem r.1, by rw [hlift r.1]; exact r.2⟩
  let f : R × Z → preimageSub M₀ R := fun p =>
    ⟨lift p.1.1 * p.2.1, Subgroup.mul_mem _ (hlift_mem' p.1)
      (show (p.2.1 : G) ∈ preimageSub M₀ R from
        ⟨hZQ p.2.2, by rw [(M₀.π_ker _ (hZQ p.2.2)).mpr p.2.2]; exact R.zero_mem⟩)⟩
  have hπf : ∀ p : R × Z, M₀.π (lift p.1.1 * p.2.1) = p.1.1 := fun p => by
    rw [M₀.π_mul _ (hlift_mem _) _ (hZQ p.2.2), hlift,
      (M₀.π_ker _ (hZQ p.2.2)).mpr p.2.2, add_zero]
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨r, hr⟩, ⟨z, hz⟩⟩ ⟨⟨r', hr'⟩, ⟨z', hz'⟩⟩ h
      have h1 := congrArg Subtype.val h
      have hr_eq : r = r' := by
        have := congrArg M₀.π h1
        simpa [f, hπf (⟨⟨r, hr⟩, ⟨z, hz⟩⟩ : R × Z), hπf (⟨⟨r', hr'⟩, ⟨z', hz'⟩⟩ : R × Z)] using this
      subst hr_eq
      have hzz : z = z' := mul_left_cancel (a := lift r) h1
      subst hzz
      rfl
    · rintro ⟨y, hyQ, hyR⟩
      let r : R := ⟨M₀.π y, hyR⟩
      have h1 : (lift r.1)⁻¹ * y ∈ Z := by
        refine (M₀.π_ker _ (Q.mul_mem (Q.inv_mem (hlift_mem _)) hyQ)).mp ?_
        rw [M₀.π_mul _ (Q.inv_mem (hlift_mem _)) _ hyQ,
          Tim79.QuadModel.pi_inv M₀ (hlift_mem _), hlift]
        exact neg_add_cancel _
      refine ⟨(r, ⟨_, h1⟩), Subtype.ext ?_⟩
      show lift r.1 * ((lift r.1)⁻¹ * y) = y
      group
  rw [Nat.card_congr (Equiv.ofBijective f hbij).symm, Nat.card_prod]

theorem card_comm_sup (hcard : Nat.card K = Nat.card Z) (A : XAct M₀ x) (H : StrothHyp M Q Z)
    (hxM : x ∈ M) (hx2 : x * x = 1) :
    Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) =
      Nat.card Z ^ (Module.finrank K (commSpace A) + 1) := by
  have hZQ := H.Z_normal.1
  have h1 : (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) = preimageSub M₀ (commSpace A) := by
    ext y
    exact mem_commSup_iff A H hxM hx2 hZQ
  rw [h1, card_preimageSub hZQ, Module.natCard_eq_pow_finrank (K := K), hcard, pow_succ]

end Count

section Main110

variable [Finite G] {M Q Z : Subgroup G} {x : G}

theorem commutator_zpowers_eq_closure' (hx : x * x = 1) :
    ⁅Q, Subgroup.zpowers x⁆ = Subgroup.closure (commGens Q x) :=
  commutator_zpowers_eq_closure hx

theorem exists_model (H : StrothHyp M Q Z) {x : G} (hxM : x ∈ M)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
      GlobalModelData M Q Z γ M₀ ∧ Nat.card K = Nat.card Z ∧ (2 : K) = 0 ∧
        Nonempty (XAct M₀ x) := by
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨A⟩ := exists_xact hD hxM hxZ
  exact ⟨K, hK, hfin, γ, M₀, hD, hD.card, CharP.cast_eq_zero K 2, ⟨A⟩⟩

theorem D_conj_mem (hx2 : x * x = 1) {q : G} (hq : q ∈ Q) {y : G}
    (hy : y ∈ ⁅Q, Subgroup.zpowers x⁆) : q * y * q⁻¹ ∈ ⁅Q, Subgroup.zpowers x⁆ := by
  rw [commutator_zpowers_eq_closure' hx2] at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨q', hq', rfl⟩ := hy
    have h1 : q * ⁅q', x⁆ * q⁻¹ = ⁅q * q', x⁆ * ⁅q, x⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨q * q', Q.mul_mem hq hq', rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨q, hq, rfl⟩))
  | one => simpa using Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) by group]
    exact Subgroup.mul_mem _ iha ihb
  | inv a ha iha =>
    rw [show q * a⁻¹ * q⁻¹ = (q * a * q⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ iha

theorem Z_le_comm (H : StrothHyp M Q Z) (hxM : x ∈ M) (hxQ : x ∉ Q) (hx2 : x * x = 1)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) : Z ≤ ⁅Q, Subgroup.zpowers x⁆ := by
  obtain ⟨K, _, _, γ, M₀, hD, hcard, hK2, ⟨A⟩⟩ := exists_model H hxM hxZ
  obtain ⟨y, hyQ, hyZ⟩ : ∃ y ∈ Q, ⁅x, y⁆ ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact hxQ (H.centralizer_Qt x hxM hcon)
  have hcQ : ⁅y, x⁆ ∈ Q := comm_mem_Q H hxM hyQ
  have hcZ : ⁅y, x⁆ ∉ Z := by
    intro h
    apply hyZ
    have := Z.inv_mem h
    rwa [commutatorElement_inv] at this
  have hcD : ⁅y, x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ :=
    Subgroup.commutator_mem_commutator hyQ (Subgroup.mem_zpowers x)
  intro z hz
  obtain ⟨q, hq, hqz⟩ := GM.exists_comm hD hcQ hcZ hz
  rw [← hqz]
  have h1 : ⁅⁅y, x⁆, q⁆ = ⁅y, x⁆ * (q * ⁅y, x⁆ * q⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  exact Subgroup.mul_mem _ hcD (Subgroup.inv_mem _ (D_conj_mem hx2 hq hcD))

end Main110

section Smith110

variable [Finite G] {M Q Z : Subgroup G} {x : G}

theorem smith_1_10 (H : StrothHyp M Q Z) (hxM : x ∈ M) (hxQ : x ∉ Q)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hx2 : x * x = 1) :
    List.TFAE
      [ ∃ k, IsTypeA Q Z k x,
        IsElemAbelian 2 ⁅Q, Subgroup.zpowers x⁆,
        ⁅Q, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer ({x} : Set G),
        conjOrbit ⁅Q, Subgroup.zpowers x⁆ x ∩ cosetSet x Z = {x} ] := by
  obtain ⟨K, _, _, γ, M₀, hD, hcard, hK2, ⟨A⟩⟩ := exists_model H hxM hxZ
  have hLin : Lin Q Z x := ⟨H.Q_normal.2 hxM, hxQ, hxZ⟩
  have hDeq := commutator_zpowers_eq_closure' (Q := Q) hx2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hDQ : ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ∈ Q := fun y hy => by
    rw [hDeq] at hy; exact D_le_Q H hxM hy
  have hDcomm : ∀ a ∈ ⁅Q, Subgroup.zpowers x⁆, ∀ b ∈ ⁅Q, Subgroup.zpowers x⁆, a * b = b * a := by
    rw [hDeq]; exact D_comm hD A hK2 H hxM hx2
  have hcx : ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, ⁅y, x⁆ = y ^ 2 := fun y hy => by
    rw [hDeq] at hy; exact D_comm_x hD A hK2 H hxM hx2 hy
  have hsq : (∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ^ 2 = 1) ↔ ∀ q ∈ Q, ⁅q, x⁆ ^ 2 = 1 := by
    rw [hDeq]; exact D_sq_iff_gen hD A hK2 H hxM hx2
  have hgen : ∀ q ∈ Q, ⁅q, x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ := fun q hq =>
    Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
  have hb : IsElemAbelian 2 ⁅Q, Subgroup.zpowers x⁆ ↔ ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ^ 2 = 1 := by
    constructor
    · exact fun h y hy => h.2 y hy
    · exact fun h => ⟨⟨⟨fun a b => Subtype.ext (hDcomm a a.2 b b.2)⟩⟩, fun y hy => h y hy⟩
  have hc : ⁅Q, Subgroup.zpowers x⁆ ≤ Subgroup.centralizer ({x} : Set G) ↔
      ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ^ 2 = 1 := by
    constructor
    · intro h y hy
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hy)
      rw [← hcx y hy]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h1
    · intro h y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hcx y hy
      rw [h y hy] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hxs : ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y * x * y⁻¹ = x * y ^ 2 := by
    intro y hy
    have h1 : y * x * y⁻¹ = ⁅y, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [h1, hcx y hy]
    have hz : y ^ 2 ∈ Z := sq_mem_Z H (hDQ y hy)
    exact (mul_inv_eq_iff_eq_mul.mp (hxZ _ hz)).symm
  have hd : conjOrbit ⁅Q, Subgroup.zpowers x⁆ x ∩ cosetSet x Z = {x} ↔
      ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ^ 2 = 1 := by
    constructor
    · intro h y hy
      have hmem : y * x * y⁻¹ ∈ conjOrbit ⁅Q, Subgroup.zpowers x⁆ x ∩ cosetSet x Z :=
        ⟨⟨y, hy, rfl⟩, ⟨y ^ 2, sq_mem_Z H (hDQ y hy), (hxs y hy).symm⟩⟩
      rw [h] at hmem
      have h2 : x * y ^ 2 = x * 1 := by rw [← hxs y hy, mul_one]; exact hmem
      exact mul_left_cancel h2
    · intro h
      ext y
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, -⟩
        rw [hxs s hs, h s hs, mul_one]
        rfl
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨⟨1, Subgroup.one_mem _, by simp⟩, ⟨1, Z.one_mem, by simp⟩⟩
  have ha : (∃ k, IsTypeA Q Z k x) ↔ ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ^ 2 = 1 := by
    rw [hsq]
    constructor
    · rintro ⟨k, -, -, hA⟩ q hq
      exact (gen_sq_iff hD A hK2 H hxM hq).mpr (hA q hq)
    · intro h
      exact ⟨Module.finrank K (commSpace A), hLin, card_comm_sup hcard A H hxM hx2,
        fun q hq => (gen_sq_iff hD A hK2 H hxM hq).mp (h q hq)⟩
  tfae_have 1 ↔ 2 := by rw [ha, hb]
  tfae_have 2 ↔ 3 := by rw [hb, hc]
  tfae_have 3 ↔ 4 := by rw [hc, hd]
  tfae_finish

end Smith110

section Smith111

variable [Finite G] {M Q Z : Subgroup G} {x : G}

def fuseSet (Q Z : Subgroup G) (x : G) : Set G := {w | w ∈ Z ∧ ∃ q ∈ Q, ⁅q, x⁆ = w}

theorem fuse_iff (H : StrothHyp M Q Z) (hxM : x ∈ M) (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) {z : G}
    (hz : z ∈ Z) : x * z ∈ conjOrbit Q x ↔ z ∈ fuseSet Q Z x := by
  constructor
  · rintro ⟨q, hq, hqz⟩
    refine ⟨hz, q, hq, ?_⟩
    have h1 : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hxZ z hz)
    have : ⁅q, x⁆ = (q * x * q⁻¹) * x⁻¹ := by simp only [commutatorElement_def, mul_assoc]
    rw [this, ← hqz, h1]; group
  · rintro ⟨-, q, hq, hqz⟩
    refine ⟨q, hq, ?_⟩
    have h1 : x * z = z * x := mul_inv_eq_iff_eq_mul.mp (hxZ z hz)
    rw [h1, ← hqz]
    simp only [commutatorElement_def]; group

theorem cent_eq_CQt_iff (H : StrothHyp M Q Z) (hx2 : x * x = 1) :
    ((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
        CQt Q Z (Subgroup.zpowers x) ↔
      ∀ q ∈ Q, ⁅q, x⁆ ∈ Z → ⁅q, x⁆ = 1 := by
  constructor
  · intro h q hq hqZ
    have hmem : q ∈ CQt Q Z (Subgroup.zpowers x) := by
      refine ⟨hq, fun t ht => ?_⟩
      rcases mem_zpowers_of_mul_self_eq_one hx2 ht with rfl | rfl
      · simpa using Z.one_mem
      · rw [← commutatorElement_inv]; exact Z.inv_mem hqZ
    rw [← h] at hmem
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2
    exact commutatorElement_eq_one_iff_mul_comm.mpr this
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      refine ⟨hyQ, fun t ht => ?_⟩
      rcases mem_zpowers_of_mul_self_eq_one hx2 ht with rfl | rfl
      · simpa using Z.one_mem
      · have := Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [commutatorElement_eq_one_iff_mul_comm.mpr this.symm]
        exact Z.one_mem
    · rintro ⟨hyQ, hy⟩
      refine Subgroup.mem_inf.mpr ⟨hyQ, ?_⟩
      have h1 : ⁅y, x⁆ ∈ Z := by
        rw [← commutatorElement_inv]; exact Z.inv_mem (hy x (Subgroup.mem_zpowers x))
      have := commutatorElement_eq_one_iff_mul_comm.mp (h y hyQ h1)
      exact Subgroup.mem_centralizer_singleton_iff.mpr this

theorem smith_1_11_first (H : StrothHyp M Q Z) (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z)
    (hx2 : x * x = 1) :
    conjOrbit Q x ∩ cosetSet x Z = {x} ↔
      ((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
        CQt Q Z (Subgroup.zpowers x) := by
  rw [cent_eq_CQt_iff H hx2, ← smith_1_11_iff hxZ]
  constructor
  · intro h q hq hmem
    have : q * x * q⁻¹ ∈ conjOrbit Q x ∩ cosetSet x Z := ⟨⟨q, hq, rfl⟩, hmem⟩
    rw [h] at this
    exact this
  · intro h
    ext y
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hmem⟩
      exact h s hs hmem
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨1, Q.one_mem, by simp⟩, ⟨1, Z.one_mem, by simp⟩⟩

theorem fuse_eq_coset_of_all (H : StrothHyp M Q Z) (hxM : x ∈ M)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hall : ∀ z ∈ Z, z ∈ fuseSet Q Z x) :
    conjOrbit Q x ∩ cosetSet x Z = cosetSet x Z := by
  apply Set.inter_eq_right.mpr
  rintro _ ⟨z, hz, rfl⟩
  exact (fuse_iff H hxM hxZ hz).mpr (hall z hz)

theorem smith_1_11_not_typeA (H : StrothHyp M Q Z) (hxM : x ∈ M) (hxQ : x ∉ Q)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hx2 : x * x = 1) (hna : ¬ ∃ k, IsTypeA Q Z k x) :
    conjOrbit Q x ∩ cosetSet x Z = cosetSet x Z := by
  obtain ⟨K, _, _, γ, M₀, hD, hcard, hK2, ⟨A⟩⟩ := exists_model H hxM hxZ
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hK2
  have hLin : Lin Q Z x := ⟨H.Q_normal.2 hxM, hxQ, hxZ⟩
  have hDeq := commutator_zpowers_eq_closure' (Q := Q) hx2
  have hZQ := H.Z_normal.1
  have hZD := Z_le_comm H hxM hxQ hx2 hxZ
  have hcx : ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, ⁅y, x⁆ = y ^ 2 := fun y hy => by
    rw [hDeq] at hy; exact D_comm_x hD A hK2 H hxM hx2 hy
  have hDQ : ∀ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ∈ Q := fun y hy => by
    rw [hDeq] at hy; exact D_le_Q H hxM hy
  obtain ⟨y₀, hy₀D, hy₀⟩ : ∃ y ∈ ⁅Q, Subgroup.zpowers x⁆, y ^ 2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hna
    have hsq : ∀ q ∈ Q, ⁅q, x⁆ ^ 2 = 1 := fun q hq =>
      hcon _ (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x))
    exact ⟨Module.finrank K (commSpace A), hLin, card_comm_sup hcard A H hxM hx2,
      fun q hq => (gen_sq_iff hD A hK2 H hxM hq).mp (hsq q hq)⟩
  have hz₀ : γ (y₀ ^ 2) ≠ 0 := fun h => hy₀ (hD.reg.inj _ (sq_mem_Z H (hDQ y₀ hy₀D)) h)
  refine fuse_eq_coset_of_all H hxM hxZ fun z hz => ?_
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (γ z / γ (y₀ ^ 2))
  have hπy₀ : M₀.π y₀ ∈ commSpace A :=
    ((mem_commSup_iff A H hxM hx2 hZQ).mp (Subgroup.mem_sup_left hy₀D)).2
  obtain ⟨c, hcQ, hπc⟩ := M₀.π_surj (r • M₀.π y₀)
  have hcD : c ∈ ⁅Q, Subgroup.zpowers x⁆ := by
    have : c ∈ (⁅Q, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G) :=
      (mem_commSup_iff A H hxM hx2 hZQ).mpr ⟨hcQ, by rw [hπc]; exact Submodule.smul_mem _ _ hπy₀⟩
    rwa [sup_eq_left.mpr hZD] at this
  have hc2 : c ^ 2 = z := by
    refine GM.eq_of_γ_eq hD (sq_mem_Z H hcQ) hz ?_
    rw [M₀.sq_eq c hcQ, hπc, M₀.Qf_smul, ← M₀.sq_eq y₀ (hDQ y₀ hy₀D)]
    rw [div_eq_iff hz₀] at hr
    rw [hr, sq]
  exact ⟨hz, c, hcQ, by rw [hcx c hcD, hc2]⟩

end Smith111

end CFSG.RankThree.GF2n.Smith81
