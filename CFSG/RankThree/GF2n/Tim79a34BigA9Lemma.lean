module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RepresentationTheory.Basic

public section

open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Tim79a.BigA9Data

@[expose] def F2 (E : Type) [Group E] (_hc : ∀ a b : E, a * b = b * a)
    (_hs : ∀ a : E, a * a = 1) : Type :=
  Additive E

namespace F2

variable {E E' : Type} [Group E] [Group E'] {hc : ∀ a b : E, a * b = b * a}
  {hs : ∀ a : E, a * a = 1} {hc' : ∀ a b : E', a * b = b * a} {hs' : ∀ a : E', a * a = 1}

@[expose] def ofMul : E ≃ F2 E hc hs := Additive.ofMul

@[expose] def toMul (x : F2 E hc hs) : E := Additive.toMul x

instance : AddCommGroup (F2 E hc hs) :=
  { (inferInstance : AddGroup (Additive E)) with
    add_comm := fun a b => congrArg Additive.ofMul (hc (Additive.toMul a) (Additive.toMul b)) }

theorem add_self (x : F2 E hc hs) : x + x = 0 :=
  congrArg Additive.ofMul (hs (Additive.toMul x))

instance : Module (ZMod 2) (F2 E hc hs) :=
  AddCommGroup.zmodModule fun x => by rw [two_nsmul]; exact add_self x

instance [Finite E] : Finite (F2 E hc hs) :=
  Finite.of_equiv E ofMul

theorem natCard_eq : Nat.card (F2 E hc hs) = Nat.card E :=
  (Nat.card_congr (ofMul : E ≃ F2 E hc hs)).symm

@[simp] theorem ofMul_mul (a b : E) :
    (ofMul (a * b) : F2 E hc hs) = ofMul a + ofMul b := rfl

@[simp] theorem ofMul_one : (ofMul 1 : F2 E hc hs) = 0 := rfl

@[expose] def map (f : E →* E') : F2 E hc hs →ₗ[ZMod 2] F2 E' hc' hs' :=
  AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive f)

@[expose] def bil (B : E → E → E') (h1 : ∀ a a' b, B (a * a') b = B a b * B a' b)
    (h2 : ∀ a b b', B a (b * b') = B a b * B a b') :
    F2 E hc hs →ₗ[ZMod 2] F2 E hc hs →ₗ[ZMod 2] F2 E' hc' hs' :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun x : F2 E hc hs => AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk' (fun y : F2 E hc hs => (ofMul (B (toMul x) (toMul y)) : F2 E' hc' hs'))
          (fun y y' => by exact congrArg ofMul (h2 _ _ _))))
      (fun x x' => LinearMap.ext fun y => congrArg ofMul (h1 _ _ _)))

end F2

section Config

variable {Mg : Type} [Group Mg]

structure Setup (P V A : Subgroup Mg) : Prop where
  A_le_V : A ≤ V
  V_le_P : V ≤ P
  V_sq : ∀ v ∈ V, v * v = 1
  V_cent : ∀ v ∈ V, ∀ x ∈ P, v * x = x * v
  P_sq : ∀ x ∈ P, x * x ∈ V
  P_comm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ A

variable {P V A : Subgroup Mg}

abbrev Quo (P V : Subgroup Mg) [V.Normal] : Type := ↥P ⧸ V.subgroupOf P

namespace Setup

variable [V.Normal] (S : Setup P V A)

include S in
theorem quo_comm (a b : Quo P V) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  induction b using QuotientGroup.induction_on with | _ y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have h := S.A_le_V (S.P_comm (↑y)⁻¹ (P.inv_mem y.2) (↑x)⁻¹ (P.inv_mem x.2))
  simpa [commutatorElement_def, mul_assoc] using h

include S in
theorem quo_sq (a : Quo P V) : a * a = 1 := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact S.P_sq x x.2

include S in
theorem A_comm (a b : ↥A) : a * b = b * a :=
  Subtype.ext (S.V_cent a (S.A_le_V a.2) b (S.V_le_P (S.A_le_V b.2)))

include S in
theorem A_sq (a : ↥A) : a * a = 1 :=
  Subtype.ext (S.V_sq a (S.A_le_V a.2))

end Setup

section Action

variable [P.Normal] [V.Normal] [A.Normal]

@[expose] def cE (m : Mg) : Quo P V →* Quo P V :=
  QuotientGroup.map (V.subgroupOf P) (V.subgroupOf P)
    (MulAut.conjNormal m : MulAut ↥P).toMonoidHom (fun v hv => by
      rw [Subgroup.mem_subgroupOf] at hv
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      have h := Subgroup.Normal.conj_mem ‹V.Normal› _ hv m
      simpa [MulAut.conjNormal_apply] using h)

theorem cE_mk (m : Mg) (x : ↥P) :
    cE (V := V) m (x : Quo P V) = ((MulAut.conjNormal m x : ↥P) : Quo P V) := rfl

theorem cE_one (a : Quo P V) : cE (V := V) (1 : Mg) a = a := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  rw [cE_mk, map_one]
  rfl

theorem cE_mul (m m' : Mg) (a : Quo P V) :
    cE (V := V) (m * m') a = cE (V := V) m (cE (V := V) m' a) := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  rw [cE_mk, cE_mk, cE_mk, map_mul]
  rfl

end Action

namespace Setup

section Spaces

variable [P.Normal] [V.Normal] [A.Normal] (S : Setup P V A)

abbrev U : Type := F2 (Quo P V) S.quo_comm S.quo_sq

abbrev Aspace : Type := F2 ↥A S.A_comm S.A_sq

@[expose] def actU : Mg →* Module.End (ZMod 2) S.U where
  toFun m := F2.map (cE m)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
    exact congrArg F2.ofMul (cE_one a)
  map_mul' m m' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
    exact congrArg F2.ofMul (cE_mul m m' a)

@[expose] def actA : Mg →* Module.End (ZMod 2) S.Aspace where
  toFun m := F2.map (MulAut.conjNormal m : MulAut ↥A).toMonoidHom
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
    exact congrArg F2.ofMul (show (MulAut.conjNormal (1 : Mg) : MulAut ↥A) a = a by
      rw [map_one]; rfl)
  map_mul' m m' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
    exact congrArg F2.ofMul (show (MulAut.conjNormal (m * m') : MulAut ↥A) a =
      (MulAut.conjNormal m : MulAut ↥A) ((MulAut.conjNormal m' : MulAut ↥A) a) by
      rw [map_mul]; rfl)

include S in
theorem commutator_mul_central {x y v w : Mg} (hx : x ∈ P) (hy : y ∈ P) (hv : v ∈ V)
    (hw : w ∈ V) : ⁅x * v, y * w⁆ = ⁅x, y⁆ := by
  have hvc : Commute v (y * w) := S.V_cent v hv (y * w) (P.mul_mem hy (S.V_le_P hw))
  have hwc : Commute x w := (S.V_cent w hw x hx).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hvc.commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, hwc.commutator_eq]
  simp

@[expose] def kE : Quo P V → Quo P V → ↥A :=
  Quotient.lift₂ (s₁ := QuotientGroup.leftRel (V.subgroupOf P))
    (s₂ := QuotientGroup.leftRel (V.subgroupOf P))
    (fun x y : ↥P => (⟨⁅(x : Mg), (y : Mg)⁆, S.P_comm x x.2 y y.2⟩ : ↥A))
    (fun x y x' y' hx hy => by
      have hx' : (x : Mg)⁻¹ * x' ∈ V :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hx)
      have hy' : (y : Mg)⁻¹ * y' ∈ V :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hy)
      apply Subtype.ext
      have ex : (x' : Mg) = x * ((x : Mg)⁻¹ * x') := by group
      have ey : (y' : Mg) = y * ((y : Mg)⁻¹ * y') := by group
      show ⁅(x : Mg), (y : Mg)⁆ = ⁅(x' : Mg), (y' : Mg)⁆
      rw [ex, ey]
      exact (S.commutator_mul_central x.2 y.2 hx' hy').symm)

theorem kE_mk (x y : ↥P) : kE S (x : Quo P V) (y : Quo P V) =
    ⟨⁅(x : Mg), (y : Mg)⁆, S.P_comm x x.2 y y.2⟩ := rfl

include S in
theorem conj_central {c : Mg} (hc : c ∈ V) {x : Mg} (hx : x ∈ P) : x * c * x⁻¹ = c := by
  rw [← S.V_cent c hc x hx, mul_inv_cancel_right]

include S in
theorem kE_mul_left (a a' b : Quo P V) : kE S (a * a') b = kE S a b * kE S a' b := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  induction a' using QuotientGroup.induction_on with | _ x' => ?_
  induction b using QuotientGroup.induction_on with | _ y => ?_
  rw [← QuotientGroup.mk_mul, kE_mk, kE_mk, kE_mk]
  apply Subtype.ext
  show ⁅((x * x' : ↥P) : Mg), (y : Mg)⁆ = ⁅(x : Mg), (y : Mg)⁆ * ⁅(x' : Mg), (y : Mg)⁆
  have h1 := S.A_le_V (S.P_comm x' x'.2 y y.2)
  have h2 := S.V_le_P (S.A_le_V (S.P_comm x x.2 y y.2))
  rw [Subgroup.coe_mul, commutatorElement_mul_left_eq_conj_mul, S.conj_central h1 x.2]
  exact S.V_cent _ h1 _ h2

include S in
theorem kE_mul_right (a b b' : Quo P V) : kE S a (b * b') = kE S a b * kE S a b' := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  induction b using QuotientGroup.induction_on with | _ y => ?_
  induction b' using QuotientGroup.induction_on with | _ y' => ?_
  rw [← QuotientGroup.mk_mul, kE_mk, kE_mk, kE_mk]
  apply Subtype.ext
  show ⁅(x : Mg), ((y * y' : ↥P) : Mg)⁆ = ⁅(x : Mg), (y : Mg)⁆ * ⁅(x : Mg), (y' : Mg)⁆
  have h1 := S.A_le_V (S.P_comm x x.2 y' y'.2)
  have h3 : ⁅(x : Mg), (y : Mg)⁆ * (y : Mg) * ⁅(x : Mg), (y' : Mg)⁆ * (y : Mg)⁻¹ =
      ⁅(x : Mg), (y : Mg)⁆ * ((y : Mg) * ⁅(x : Mg), (y' : Mg)⁆ * (y : Mg)⁻¹) := by group
  rw [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj, h3, S.conj_central h1 y.2]

theorem kE_equivariant (m : Mg) (a b : Quo P V) :
    kE S (cE m a) (cE m b) = (MulAut.conjNormal m : MulAut ↥A) (kE S a b) := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  induction b using QuotientGroup.induction_on with | _ y => ?_
  rw [cE_mk, cE_mk, kE_mk, kE_mk]
  apply Subtype.ext
  show ⁅m * (x : Mg) * m⁻¹, m * (y : Mg) * m⁻¹⁆ = m * ⁅(x : Mg), (y : Mg)⁆ * m⁻¹
  exact (conjugate_commutatorElement _ _ _).symm

@[expose] def kappa : S.U →ₗ[ZMod 2] S.U →ₗ[ZMod 2] S.Aspace :=
  F2.bil (kE S) S.kE_mul_left S.kE_mul_right

theorem kappa_equivariant (m : Mg) (x y : S.U) :
    S.kappa (S.actU m x) (S.actU m y) = S.actA m (S.kappa x y) := by
  obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
  obtain ⟨b, rfl⟩ := F2.ofMul.surjective y
  exact congrArg F2.ofMul (S.kE_equivariant m a b)

theorem actU_trivial {Q : Subgroup Mg} (hQ : ∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V) (q : Mg)
    (hq : q ∈ Q) : S.actU q = 1 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
  induction a using QuotientGroup.induction_on with | _ p => ?_
  refine congrArg F2.ofMul ?_
  show cE q (p : Quo P V) = (p : Quo P V)
  rw [cE_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simpa [MulAut.conjNormal_apply, commutatorElement_def, div_eq_mul_inv] using hQ q hq p p.2

theorem actA_trivial {Q : Subgroup Mg} (hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q) (q : Mg)
    (hq : q ∈ Q) : S.actA q = 1 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := F2.ofMul.surjective x
  refine congrArg F2.ofMul (Subtype.ext ?_)
  show q * (a : Mg) * q⁻¹ = (a : Mg)
  rw [hQA q hq a a.2, mul_inv_cancel_right]

end Spaces

end Setup

section Descent

variable {Q : Subgroup Mg} [Q.Normal]

@[expose] def descend (Lb : Subgroup (Mg ⧸ Q)) {M : Type*} [Monoid M] (ρ0 : Mg →* M)
    (h : ∀ q ∈ Q, ρ0 q = 1) : ↥Lb →* M :=
  (QuotientGroup.lift Q ρ0 fun q hq => (MonoidHom.mem_ker).2 (h q hq)).comp Lb.subtype

theorem descend_mk (Lb : Subgroup (Mg ⧸ Q)) {M : Type*} [Monoid M] (ρ0 : Mg →* M)
    (h : ∀ q ∈ Q, ρ0 q = 1) (m : Mg) (hm : (m : Mg ⧸ Q) ∈ Lb) :
    descend Lb ρ0 h ⟨m, hm⟩ = ρ0 m :=
  QuotientGroup.lift_mk Q (fun q hq => (MonoidHom.mem_ker).2 (h q hq)) m

theorem exists_mk (Lb : Subgroup (Mg ⧸ Q)) (g : ↥Lb) :
    ∃ (m : Mg) (hm : (m : Mg ⧸ Q) ∈ Lb), g = ⟨m, hm⟩ := by
  obtain ⟨g, hg⟩ := g
  induction g using QuotientGroup.induction_on with | _ m => exact ⟨m, hg, rfl⟩

end Descent

theorem natCard_quo [Finite Mg] [V.Normal] (hVP : V ≤ P)
    (hcard : Nat.card ↥P = 2 ^ 8 * Nat.card ↥V) : Nat.card (Quo P V) = 2 ^ 8 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf P)
  have h2 : Nat.card ↥(V.subgroupOf P) = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv
  have hpos : 0 < Nat.card ↥V := Nat.card_pos
  rw [h2, hcard] at h1
  exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

theorem finrank_of_natCard {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] {d : ℕ}
    (h : Nat.card M = 2 ^ d) : Module.finrank (ZMod 2) M = d := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  rw [Nat.card_zmod, h] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

namespace Setup

section Final

variable [P.Normal] [V.Normal] [A.Normal] (S : Setup P V A) {Q : Subgroup Mg} [Q.Normal]

theorem rho_injective (Lb : Subgroup (Mg ⧸ Q)) [IsSimpleGroup ↥Lb]
    (hQ : ∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V)
    (hnt : ∃ m : Mg, (m : Mg ⧸ Q) ∈ Lb ∧ ∃ x ∈ P, ⁅m, x⁆ ∉ V) :
    Function.Injective (descend Lb S.actU (S.actU_trivial hQ)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (MonoidHom.ker (descend Lb S.actU (S.actU_trivial hQ))) with h | h
  · have hmem : g ∈ MonoidHom.ker (descend Lb S.actU (S.actU_trivial hQ)) := hg
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    obtain ⟨m, hm, x, hx, hmx⟩ := hnt
    have hker : (⟨m, hm⟩ : ↥Lb) ∈ MonoidHom.ker (descend Lb S.actU (S.actU_trivial hQ)) := by
      rw [h]
      exact Subgroup.mem_top _
    have h1 : S.actU m = 1 := by
      have h0 := MonoidHom.mem_ker.mp hker
      rwa [descend_mk] at h0
    have h2 := LinearMap.congr_fun h1 (F2.ofMul ((⟨x, hx⟩ : ↥P) : Quo P V))
    have h3 : cE m ((⟨x, hx⟩ : ↥P) : Quo P V) = ((⟨x, hx⟩ : ↥P) : Quo P V) :=
      F2.ofMul.injective h2
    rw [cE_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at h3
    exact hmx (by simpa [MulAut.conjNormal_apply, commutatorElement_def, div_eq_mul_inv] using h3)

theorem kappa_span (hspan : A ≤ ⁅P, P⁆) (l : Module.Dual (ZMod 2) S.Aspace)
    (hl : ∀ x y, l (S.kappa x y) = 0) : l = 0 := by
  let lφ : ↥A →* Multiplicative (ZMod 2) :=
    { toFun := fun a => Multiplicative.ofAdd (l (F2.ofMul a))
      map_one' := by simp
      map_mul' := fun a b => by simp }
  have hle : ⁅P, P⁆ ≤ (MonoidHom.ker lφ).map A.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⟨⁅x, y⁆, S.P_comm x hx y hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have h := hl (F2.ofMul ((⟨x, hx⟩ : ↥P) : Quo P V)) (F2.ofMul ((⟨y, hy⟩ : ↥P) : Quo P V))
    exact congrArg Multiplicative.ofAdd h
  refine LinearMap.ext fun v => ?_
  obtain ⟨a, rfl⟩ := F2.ofMul.surjective v
  obtain ⟨b, hb, hba⟩ := hle (hspan a.2)
  have hb' : b = a := Subtype.ext hba
  subst hb'
  have h0 := MonoidHom.mem_ker.mp hb
  simpa [lφ] using h0

end Final

end Setup

end Config

end CFSG.RankThree.GF2n.Tim79a.BigA9Data

namespace CFSG.RankThree.GF2n.Tim79a

theorem a9_data_of_pq {Mg : Type} [Group Mg] [Finite Mg] (Q P V A : Subgroup Mg)
    [Q.Normal] [P.Normal] [V.Normal] [A.Normal] (Lb : Subgroup (Mg ⧸ Q))
    (e : ↥Lb ≃* alternatingGroup (Fin 9))
    (hAV : A ≤ V) (hVP : V ≤ P) (hPQ : P ≤ Q)
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hVsq : ∀ v ∈ V, v * v = 1)
    (hVcent : ∀ v ∈ V, ∀ x ∈ P, v * x = x * v)
    (hsq : ∀ x ∈ P, x * x ∈ V) (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ A)
    (hQ : ∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V) (hQA : ∀ q ∈ Q, ∀ a ∈ A, q * a = a * q)
    (hcard : Nat.card P = 2 ^ 8 * Nat.card V) (hA4 : Nat.card A = 4)
    (hspan : A ≤ ⁅P, P⁆)
    (hnt : ∃ m : Mg, (m : Mg ⧸ Q) ∈ Lb ∧ ∃ x ∈ P, ⁅m, x⁆ ∉ V) :
    ∃ (L U A' : Type) (_ : Group L) (_ : AddCommGroup U) (_ : Module (ZMod 2) U)
      (_ : FiniteDimensional (ZMod 2) U) (_ : AddCommGroup A') (_ : Module (ZMod 2) A')
      (_ : FiniteDimensional (ZMod 2) A') (_ : L ≃* alternatingGroup (Fin 9))
      (ρ : Representation (ZMod 2) L U) (ρA : Representation (ZMod 2) L A')
      (κ : U →ₗ[ZMod 2] U →ₗ[ZMod 2] A'), Function.Injective ρ ∧
      Module.finrank (ZMod 2) U = 8 ∧ Module.finrank (ZMod 2) A' = 2 ∧
      (∀ (g : L) (x y : U), κ (ρ g x) (ρ g y) = ρA g (κ x y)) ∧
      (∀ l : Module.Dual (ZMod 2) A', (∀ x y, l (κ x y) = 0) → l = 0) := by
  have S : BigA9Data.Setup P V A := ⟨hAV, hVP, hVsq, hVcent, hsq, hcomm⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥Lb := e.isSimpleGroup
  have hU : Nat.card S.U = 2 ^ 8 :=
    (BigA9Data.F2.natCard_eq).trans (BigA9Data.natCard_quo hVP hcard)
  have hA : Nat.card S.Aspace = 2 ^ 2 :=
    (BigA9Data.F2.natCard_eq).trans (by rw [hA4]; norm_num)
  refine ⟨↥Lb, S.U, S.Aspace, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, e,
    BigA9Data.descend Lb S.actU (S.actU_trivial hQ),
    BigA9Data.descend Lb S.actA (S.actA_trivial hQA), S.kappa,
    S.rho_injective Lb hQ hnt, BigA9Data.finrank_of_natCard hU,
    BigA9Data.finrank_of_natCard hA, ?_, fun l hl => S.kappa_span hspan l hl⟩
  intro g x y
  obtain ⟨m, hm, rfl⟩ := BigA9Data.exists_mk Lb g
  rw [BigA9Data.descend_mk, BigA9Data.descend_mk]
  exact S.kappa_equivariant m x y

end CFSG.RankThree.GF2n.Tim79a
