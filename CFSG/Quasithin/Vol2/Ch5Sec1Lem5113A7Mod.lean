module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113A7Std
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourA7
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Aut
public import CFSG.Quasithin.Background.A7Q528Class
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.A7ZK

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.X3E (Vec lin wmap wapp toVec toVec_wapp exists_toVec toVec_injOn
  toVec_zero wmap_cons)
open CFSG.Quasithin.B45Alt7 (gen7 eval7 indBlk)
open scoped IsMulCommutative commutatorElement

@[expose] def e0 : Subgroup (G6.PermMod 7) where
  carrier := {v | Multiplicative.toAdd v 5 = 0 ∧ Multiplicative.toAdd v 6 = 0 ∧
    ∑ i, Multiplicative.toAdd v i = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, toAdd_mul, Pi.add_apply, Finset.sum_add_distrib] at hx hy ⊢
    exact ⟨by rw [hx.1, hy.1, add_zero], by rw [hx.2.1, hy.2.1, add_zero],
      by rw [hx.2.2, hy.2.2, add_zero]⟩
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact ⟨by simp [hx.1], by simp [hx.2.1], by simp [hx.2.2]⟩

theorem mem_e0 {v : G6.PermMod 7} : v ∈ e0 ↔ Multiplicative.toAdd v 5 = 0 ∧
    Multiplicative.toAdd v 6 = 0 ∧ ∑ i, Multiplicative.toAdd v i = 0 := Iff.rfl

theorem inv_eq_self_permMod (x : G6.PermMod 7) : x⁻¹ = x := by
  apply inv_eq_of_mul_eq_one_right
  apply Multiplicative.toAdd.injective
  funext i
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  exact key _

theorem mul_inv_permAct_mem_e0 (w : G6.PermMod 7) {r : alternatingGroup (Fin 7)}
    (hr : r ∈ A7Std.r0) : w * (G6.permAct 7 (r : Perm (Fin 7)) w)⁻¹ ∈ e0 := by
  obtain ⟨h5, h6⟩ := (A7Std.mem_r0 r).mp hr
  have h5' : (r : Perm (Fin 7))⁻¹ 5 = 5 := by rw [Perm.inv_eq_iff_eq, h5]
  have h6' : (r : Perm (Fin 7))⁻¹ 6 = 6 := by rw [Perm.inv_eq_iff_eq, h6]
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [inv_eq_self_permMod]
  refine mem_e0.mpr ⟨?_, ?_, ?_⟩
  · simp only [toAdd_mul, Pi.add_apply, G6.permAct_apply, h5']
    exact key _
  · simp only [toAdd_mul, Pi.add_apply, G6.permAct_apply, h6']
    exact key _
  · simp only [toAdd_mul, Pi.add_apply, G6.permAct_apply]
    rw [Finset.sum_add_distrib,
      Equiv.sum_comp ((r : Perm (Fin 7))⁻¹) (fun i => Multiplicative.toAdd w i)]
    exact key _

@[expose] def c5p : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def c5 : alternatingGroup (Fin 7) :=
  ⟨c5p, by rw [Perm.mem_alternatingGroup, c5p]; decide +kernel⟩

theorem c5_mem : c5 ∈ A7Std.r0 :=
  (A7Std.mem_r0 c5).mpr ⟨show c5p 5 = 5 by decide, show c5p 6 = 6 by decide⟩

theorem eq_one_of_mem_e0 {v : G6.PermMod 7} (hv : v ∈ e0) (hfix : G6.permAct 7 c5p v = v) :
    v = 1 := by
  obtain ⟨h5, h6, hs⟩ := mem_e0.mp hv
  have hc : ∀ i, Multiplicative.toAdd v (c5p⁻¹ i) = Multiplicative.toAdd v i := fun i => by
    rw [← G6.permAct_apply, hfix]
  have e1 : c5p⁻¹ 1 = 0 := by decide
  have e2 : c5p⁻¹ 2 = 1 := by decide
  have e3 : c5p⁻¹ 3 = 2 := by decide
  have e4 : c5p⁻¹ 4 = 3 := by decide
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [Fin.sum_univ_seven, h5, h6, ← h4, ← h3, ← h2, ← h1] at hs
  have key : ∀ a : ZMod 2, a + a + a + a + a + 0 + 0 = 0 → a = 0 := by decide
  have h0 := key _ hs
  have hv1 : Multiplicative.toAdd v 1 = 0 := by rw [← h1]; exact h0
  have hv2 : Multiplicative.toAdd v 2 = 0 := by rw [← h2]; exact hv1
  have hv3 : Multiplicative.toAdd v 3 = 0 := by rw [← h3]; exact hv2
  have hv4 : Multiplicative.toAdd v 4 = 0 := by rw [← h4]; exact hv3
  have hv : ∀ i, Multiplicative.toAdd v i = 0 := by
    intro i
    fin_cases i
    exacts [h0, hv1, hv2, hv3, hv4, h5, h6]
  apply Multiplicative.toAdd.injective
  funext i
  rw [hv i]
  rfl

section Comm

variable {G : Type} [Group G]

theorem commutator_le_left_of_le_normalizer {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hBA hb) _).mp (A.inv_mem ha)
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ A := A.mul_mem ha h1
  simpa [mul_assoc] using h2

theorem conj_mem_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G))
    {x : G} (hx : x ∈ ⁅A, B⁆) : g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have h1 : (MulAut.conj g).toMonoidHom ⁅a, b⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
      ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
  have h2 := hle hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2

theorem le_normalizer_commutator {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_commutator (hA hg) (hB hg), fun hx => ?_⟩
  have h1 := conj_mem_commutator (hA (X.inv_mem hg)) (hB (X.inv_mem hg)) hx
  simpa [mul_assoc] using h1

theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hAB : A ≤ B) (hB : IsElemAbelian p B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

@[expose] def conjAut {Y U : Subgroup G} (hYU : Y ≤ Subgroup.normalizer (U : Set G)) :
    ↥Y →* MulAut ↥U where
  toFun y :=
    { toFun := fun u => ⟨(y : G) * u * (y : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hYU y.2) u).mp u.2⟩
      invFun := fun u => ⟨(y : G)⁻¹ * u * y, by
        have h := (Subgroup.mem_normalizer_iff.mp (hYU (Y.inv_mem y.2)) u).mp u.2
        simpa using h⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext u
    simp
  map_mul' a b := by
    ext u
    simp [mul_assoc]

theorem coe_conjAut {Y U : Subgroup G} (hYU : Y ≤ Subgroup.normalizer (U : Set G)) (y : ↥Y)
    (u : ↥U) : ((conjAut hYU y u : ↥U) : G) = (y : G) * u * (y : G)⁻¹ := rfl

end Comm

section Group

variable {G : Type} [Group G] [Finite G]

theorem rep_cases {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ U → Y ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = U)
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) (hcard : Nat.card U ≤ 2 ^ 12) :
    (∃ β : ↥U ≃* ↥(G6.coreMod 7), ∀ (y : ↥Y) (u : ↥U),
      (β (conjAut hYU y u) : G6.PermMod 7) =
        G6.permAct 7 ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7))
          (β u)) ∨
    ∃ j < 2, ∃ Ψ : Vec 4 ≃ ↥U, Ψ 0 = 1 ∧ (∀ (w : List Bool) (y : ↥Y),
      e (QuotientGroup.mk y) = eval7 w → ∀ s : Vec 4,
        Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = conjAut hYU y (Ψ s)) ∧
      ∀ s t : Vec 4, Ψ (s + t) = Ψ s * Ψ t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 ↥U :=
    { toIsMulCommutative := hU.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun q =>
        Subtype.ext (by simpa using hU.2 q q.2) }
  have : Finite (Additive ↥U) := inferInstanceAs (Finite ↥U)
  let _ : MulDistribMulAction ↥Y ↥U := MulDistribMulAction.compHom ↥U (conjAut hYU)
  set ρY : Representation (ZMod 2) ↥Y (Additive ↥U) :=
    CFSG.Theory.Representation.ofElementaryAbelianAction (A := ↥Y) (G := ↥U) (p := 2) with hρY
  have hρYapp : ∀ (y : ↥Y) (u : ↥U),
      ρY y (Additive.ofMul u) = Additive.ofMul (conjAut hYU y u) := fun y u => by
    rw [hρY, CFSG.Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    rfl
  have hker : CFSG.pCore 2 ↥Y ≤ ρY.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro w
    induction w using Additive.rec with
    | ofMul q =>
      rw [hρYapp, Module.End.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_conjAut]
      have hyO : (y : G) ∈ pCoreOf 2 Y := by
        rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
        exact ⟨y, hy, rfl⟩
      have h1 : (q : G) * y = y * q := Subgroup.mem_centralizer_iff.mp (hO hyO) q q.2
      rw [← h1, mul_inv_cancel_right]
  set ρ : Representation (ZMod 2) B45Alt7.A7 (Additive ↥U) :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥Y) ρY hker).comp e.symm.toMonoidHom with hρ
  have hρα : ∀ y : ↥Y, ρ (e (QuotientGroup.mk y)) = ρY y := fun y => by
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hirr' : ∀ J : Submodule (ZMod 2) (Additive ↥U), (∀ g, ∀ s ∈ J, ρ g s ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    let J' : Subgroup G :=
      { carrier := {x | ∃ h : x ∈ U, Additive.ofMul (⟨x, h⟩ : ↥U) ∈ J}
        one_mem' := ⟨U.one_mem, J.zero_mem⟩
        mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, J.add_mem ha.2 hb.2⟩
        inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, J.neg_mem ha.2⟩ }
    have hJ'U : J' ≤ U := fun x hx => hx.1
    have hconj : ∀ y : ↥Y, ∀ x ∈ J', (y : G) * x * (y : G)⁻¹ ∈ J' := by
      rintro y x ⟨hx, hx'⟩
      have h1 := hJ (e (QuotientGroup.mk y)) _ hx'
      rw [hρα, hρYapp] at h1
      exact ⟨_, h1⟩
    have hYJ : Y ≤ Subgroup.normalizer (J' : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hconj ⟨y, hy⟩ x, fun hx => ?_⟩
      have h1 := hconj ⟨y, hy⟩⁻¹ _ hx
      simpa [mul_assoc] using h1
    rcases hirr J' hJ'U hYJ with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      induction w using Additive.rec with
      | ofMul q =>
        have h1 : (q : G) ∈ J' := ⟨q.2, hw⟩
        rw [h, Subgroup.mem_bot] at h1
        have h2 : q = 1 := Subtype.ext h1
        rw [h2, Submodule.mem_bot]
        rfl
    · right
      rw [eq_top_iff]
      intro w _
      induction w using Additive.rec with
      | ofMul q =>
        have h1 : (q : G) ∈ J' := by
          rw [h]
          exact q.2
        obtain ⟨_, h2⟩ := h1
        exact h2
  have hnt' : ∃ g s, ρ g s ≠ s := by
    by_contra hall
    push Not at hall
    apply hnt
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 := hall (e (QuotientGroup.mk ⟨y, hy⟩)) (Additive.ofMul ⟨q, hq⟩)
    rw [hρα, hρYapp] at h1
    have h2 : y * q * y⁻¹ = q :=
      congrArg (fun w : Additive ↥U => ((Additive.toMul w : ↥U) : G)) h1
    calc q * y = y * q * y⁻¹ * y := by rw [h2]
      _ = y * q := inv_mul_cancel_right _ _
  have hcard' : Nat.card (Additive ↥U) ≤ 2 ^ 12 := hcard
  rcases A7Q528.section_cases ρ hirr' hnt' hcard' with ⟨β, hβ⟩ | ⟨j, hj, Ψ, hΨ⟩
  · left
    refine ⟨(MulEquiv.multiplicativeAdditive ↥U).symm.trans β, fun y u => ?_⟩
    have h1 := hβ (e (QuotientGroup.mk y)) (Additive.ofMul u)
    rw [hρα, hρYapp] at h1
    exact h1
  · right
    have hw : ∀ (w : List Bool) (s : Vec 4),
        Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = ρ (eval7 w) (Ψ s) := by
      intro w
      induction w with
      | nil =>
        intro s
        show Ψ (LinearMap.id s) = ρ 1 (Ψ s)
        rw [LinearMap.id_apply, map_one, Module.End.one_apply]
      | cons b w ih =>
        intro s
        rw [wmap_cons, hΨ, ih]
        show ρ (gen7 b) (ρ (eval7 w) (Ψ s)) = ρ (gen7 b * eval7 w) (Ψ s)
        rw [map_mul, Module.End.mul_apply]
    refine ⟨j, hj, Ψ.toEquiv.trans Additive.toMul, ?_, fun w y hy s => ?_, fun s t => ?_⟩
    · show Additive.toMul (Ψ 0) = 1
      rw [map_zero]
      rfl
    · have h1 := hw w s
      rw [← hy, hρα] at h1
      have h2 := hρYapp y (Additive.toMul (Ψ s))
      rw [ofMul_toMul] at h2
      show Additive.toMul (Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s)) =
        conjAut hYU y (Additive.toMul (Ψ s))
      rw [h1, h2]
      rfl
    · show Additive.toMul (Ψ (s + t)) = Additive.toMul (Ψ s) * Additive.toMul (Ψ t)
      rw [map_add]
      rfl

theorem exists_coreMod_equiv {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ U → Y ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = U)
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) (hcard : Nat.card U = 2 ^ 6) :
    ∃ β : ↥U ≃* ↥(G6.coreMod 7), ∀ (y : ↥Y) (u : ↥U),
      (β (conjAut hYU y u) : G6.PermMod 7) =
        G6.permAct 7 ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7))
          (β u) := by
  rcases rep_cases e hYU hU hO hirr hnt (by rw [hcard]; norm_num) with h | ⟨j, -, Ψ, -, -⟩
  · exact h
  · exfalso
    have h1 := Nat.card_congr Ψ
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
      hcard] at h1
    norm_num at h1

theorem exists_four_addEquiv {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ U → Y ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = U)
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) (hcard : Nat.card U = 2 ^ 4) :
    ∃ j < 2, ∃ Ψ : Vec 4 ≃ ↥U, Ψ 0 = 1 ∧ (∀ (w : List Bool) (y : ↥Y),
      e (QuotientGroup.mk y) = eval7 w → ∀ s : Vec 4,
        Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = conjAut hYU y (Ψ s)) ∧
      ∀ s t : Vec 4, Ψ (s + t) = Ψ s * Ψ t := by
  rcases rep_cases e hYU hU hO hirr hnt (by rw [hcard]; norm_num) with ⟨β, -⟩ | h
  · exfalso
    have h1 := Nat.card_congr β.toEquiv
    rw [hcard, Explicit.card_coreMod (by norm_num)] at h1
    norm_num at h1
  · exact h

theorem exists_four_equiv {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U)
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ U → Y ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = U)
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) (hcard : Nat.card U = 2 ^ 4) :
    ∃ j < 2, ∃ Ψ : Vec 4 ≃ ↥U, Ψ 0 = 1 ∧ ∀ (w : List Bool) (y : ↥Y),
      e (QuotientGroup.mk y) = eval7 w → ∀ s : Vec 4,
        Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = conjAut hYU y (Ψ s) := by
  obtain ⟨j, hj, Ψ, h0, hw, -⟩ := exists_four_addEquiv e hYU hU hO hirr hnt hcard
  exact ⟨j, hj, Ψ, h0, hw⟩

@[expose] def p0aWord : List Bool := [true, false, true, true, false, true, false, true, true, true]

@[expose] def p0bWord : List Bool :=
  [true, false, true, true, true, true, false, true, false, true, false]

theorem eval7_p0aWord :
    ∀ i : Fin 7, ((eval7 p0aWord : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = A7Std.p0a i := by
  decide +kernel

theorem eval7_p0bWord :
    ∀ i : Fin 7, ((eval7 p0bWord : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = A7Std.p0b i := by
  decide +kernel

theorem eval7_p0aWord_mem : eval7 p0aWord ∈ A7Std.p0 := by
  rw [A7Std.mem_p0, Equiv.ext eval7_p0aWord]
  simp [A7Std.p0L]

theorem eval7_p0bWord_mem : eval7 p0bWord ∈ A7Std.p0 := by
  rw [A7Std.mem_p0, Equiv.ext eval7_p0bWord]
  simp [A7Std.p0L]

theorem p0_fix_check : ∀ j < 2, ∀ x < 16,
    wapp 4 (indBlk true j) p0aWord x < 16 ∧ wapp 4 (indBlk true j) p0bWord x < 16 ∧
      (wapp 4 (indBlk true j) p0aWord x = x → wapp 4 (indBlk true j) p0bWord x = x →
        x = 0 ∨ x = [8, 4].getD j 0) := by
  decide +kernel

theorem exists_fixed_packed {j : ℕ} {s : Vec 4}
    (ha : wmap (fun b => lin 4 (indBlk true j b)) p0aWord s = s)
    (hb : wmap (fun b => lin 4 (indBlk true j b)) p0bWord s = s) (hj : j < 2) :
    ∃ x < 16, toVec 4 x = s ∧ wapp 4 (indBlk true j) p0aWord x = x ∧
      wapp 4 (indBlk true j) p0bWord x = x := by
  obtain ⟨x, hx, rfl⟩ := exists_toVec s
  have hx' : x < 16 := by simpa using hx
  obtain ⟨hla, hlb, -⟩ := p0_fix_check j hj x hx'
  refine ⟨x, hx', rfl, ?_, ?_⟩
  · rw [← toVec_wapp] at ha
    exact toVec_injOn (by simpa using hla) hx ha
  · rw [← toVec_wapp] at hb
    exact toVec_injOn (by simpa using hlb) hx hb

omit [Finite G] in
theorem eq_of_fixed_p0 {Y U : Subgroup G} {hYU : Y ≤ Subgroup.normalizer (U : Set G)} {j : ℕ}
    (hj : j < 2) {Ψ : Vec 4 ≃ ↥U} (hΨ0 : Ψ 0 = 1) {e : O2Q Y ≃* alternatingGroup (Fin 7)}
    (hΨ : ∀ (w : List Bool) (y : ↥Y), e (QuotientGroup.mk y) = eval7 w → ∀ s : Vec 4,
      Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = conjAut hYU y (Ψ s))
    {ya yb : ↥Y} (ha : e (QuotientGroup.mk ya) = eval7 p0aWord)
    (hb : e (QuotientGroup.mk yb) = eval7 p0bWord) {u₁ u₂ : ↥U}
    (h1a : conjAut hYU ya u₁ = u₁) (h1b : conjAut hYU yb u₁ = u₁)
    (h2a : conjAut hYU ya u₂ = u₂) (h2b : conjAut hYU yb u₂ = u₂) (hu₁ : u₁ ≠ 1)
    (hu₂ : u₂ ≠ 1) : u₁ = u₂ := by
  have key : ∀ u : ↥U, conjAut hYU ya u = u → conjAut hYU yb u = u →
      wmap (fun b => lin 4 (indBlk true j b)) p0aWord (Ψ.symm u) = Ψ.symm u ∧
        wmap (fun b => lin 4 (indBlk true j b)) p0bWord (Ψ.symm u) = Ψ.symm u := by
    intro u hua hub
    refine ⟨Ψ.injective ?_, Ψ.injective ?_⟩
    · rw [hΨ _ _ ha, Equiv.apply_symm_apply, hua]
    · rw [hΨ _ _ hb, Equiv.apply_symm_apply, hub]
  obtain ⟨k1a, k1b⟩ := key u₁ h1a h1b
  obtain ⟨k2a, k2b⟩ := key u₂ h2a h2b
  obtain ⟨x₁, hx₁, hs₁, hx₁a, hx₁b⟩ := exists_fixed_packed k1a k1b hj
  obtain ⟨x₂, hx₂, hs₂, hx₂a, hx₂b⟩ := exists_fixed_packed k2a k2b hj
  have hne : ∀ {u : ↥U} {x : ℕ}, toVec 4 x = Ψ.symm u → u ≠ 1 → x ≠ 0 := by
    intro u x hs hu hx
    apply hu
    rw [← Equiv.apply_symm_apply Ψ u, ← hs, hx, toVec_zero, hΨ0]
  have h1 := ((p0_fix_check j hj x₁ hx₁).2.2 hx₁a hx₁b).resolve_left (hne hs₁ hu₁)
  have h2 := ((p0_fix_check j hj x₂ hx₂).2.2 hx₂a hx₂b).resolve_left (hne hs₂ hu₂)
  rw [← Equiv.apply_symm_apply Ψ u₁, ← Equiv.apply_symm_apply Ψ u₂, ← hs₁, ← hs₂, h1, h2]

omit [Finite G] in
theorem commutator_inf_centralizer_eq_bot {Y U K : Subgroup G}
    (e : O2Q Y ≃* alternatingGroup (Fin 7)) (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hKY : K ≤ Y) (β : ↥U ≃* ↥(G6.coreMod 7))
    (hβ : ∀ (y : ↥Y) (u : ↥U), (β (conjAut hYU y u) : G6.PermMod 7) =
      G6.permAct 7 ((e (QuotientGroup.mk y) : alternatingGroup (Fin 7)) : Perm (Fin 7)) (β u))
    (hR : (modO2Image Y K).map e.toMonoidHom = A7Std.r0) :
    ⁅U, K⁆ ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have hmemR : ∀ y : ↥Y, (y : G) ∈ K → e (QuotientGroup.mk y) ∈ A7Std.r0 := fun y hy => by
    rw [← hR]
    exact ⟨QuotientGroup.mk y, ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, rfl⟩
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y : ↥Y, (y : G) ∈ K ∧ e (QuotientGroup.mk y) = c5 := by
    have h1 : c5 ∈ (modO2Image Y K).map e.toMonoidHom := hR ▸ c5_mem
    obtain ⟨q, ⟨y, hy, rfl⟩, hq⟩ := h1
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, hq⟩
  have hUK : ⁅U, K⁆ ≤ (e0.comap ((G6.coreMod 7).subtype.comp β.toMonoidHom)).map U.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    refine ⟨⟨a, ha⟩ * (conjAut hYU ⟨k, hKY hk⟩ ⟨a, ha⟩)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hβ]
      exact mul_inv_permAct_mem_e0 _ (hmemR _ hk)
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut,
        commutatorElement_def]
      group
  rw [eq_bot_iff]
  rintro x ⟨hx, hxc⟩
  obtain ⟨u, hu, rfl⟩ := hUK hx
  have h1 : (y₀ : G) * u = u * y₀ := Subgroup.mem_centralizer_iff.mp hxc _ hy₀K
  have hcu : conjAut hYU y₀ u = u :=
    Subtype.ext (by rw [coe_conjAut, h1, mul_inv_cancel_right])
  have hfix : G6.permAct 7 c5p (β u : G6.PermMod 7) = β u := by
    have h2 := hβ y₀ u
    rw [hcu, hy₀] at h2
    exact h2.symm
  have h3 : (β u : G6.PermMod 7) = 1 := eq_one_of_mem_e0 (Subgroup.mem_comap.mp hu) hfix
  have h4 : u = 1 := β.injective ((Subtype.ext h3).trans (map_one β).symm)
  rw [h4, map_one]
  exact Subgroup.one_mem _

theorem inf_centralizer_le_pCoreOf {Y U : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hs : IsSimpleGroup (O2Q Y)) (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) :
    Y ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 Y := by
  refine le_pCoreOf_of_normal_of_ne hY hs inf_le_left (fun y hy => ?_) (fun he => hnt ?_)
  · exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYU hy⟩
  · rw [← he]
    exact inf_le_right

theorem exists_pow_five_not_mem_centralizer {Y U K : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hs : IsSimpleGroup (O2Q Y)) (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) (hKY : K ≤ Y) (h5 : 5 ∣ Nat.card K) :
    ∃ x ∈ K, x ^ 5 = 1 ∧ x ∉ Subgroup.centralizer (U : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hx5 : x ^ 5 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  refine ⟨x, x.2, by rw [← Subgroup.coe_pow, hx5, Subgroup.coe_one], fun hxc => ?_⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    ⟨x, inf_centralizer_le_pCoreOf hY hs hYU hnt ⟨hKY x.2, hxc⟩⟩
  have h1 : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  rw [Subgroup.orderOf_coe, hx] at h2
  have h3 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h2
  norm_num at h3

theorem inf_centralizer_eq_bot_of_card_sixteen {Y U K : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hs : IsSimpleGroup (O2Q Y)) (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hnt : ¬ Y ≤ Subgroup.centralizer (U : Set G)) (hKY : K ≤ Y) (h5 : 5 ∣ Nat.card K)
    (hU : Nat.card U = 16) : U ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxK, hx5, hxU⟩ := exists_pow_five_not_mem_centralizer hY hs hYU hnt hKY h5
  have hmod := card_modEq_card_inf_centralizer (hYU (hKY hxK)) hx5
  rw [hU] at hmod
  have hdvd : Nat.card ↥(U ⊓ Subgroup.centralizer ({x} : Set G)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hU]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hbot : U ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    rw [hi'] at hmod
    interval_cases i
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hi']; rfl)
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · exfalso
      apply hxU
      have heq : U ⊓ Subgroup.centralizer ({x} : Set G) = U :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hi', hU]; norm_num)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' := (heq.ge hu).2
      exact (Subgroup.mem_centralizer_iff.mp hu' x (Set.mem_singleton x)).symm
  refine eq_bot_iff.mpr ((inf_le_inf_left U (Subgroup.centralizer_le ?_)).trans hbot.le)
  exact Set.singleton_subset_iff.mpr hxK

end Group

end CFSG.Quasithin.A7ZK
