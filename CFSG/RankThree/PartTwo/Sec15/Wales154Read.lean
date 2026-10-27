module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
public import CFSG.RankThree.PartTwo.Sec15.Wales154Reduce

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mul_inv_mem_of_eq_sup {Y D : Subgroup G} {e : G}
    (hdec : Y = pPrimeCoreOf 3 Y ⊔ D)
    (heO : e ∈ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G))
    (heD : D ≤ Subgroup.centralizer ({e} : Set G)) :
    ∀ y ∈ Y, e * y * e⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y := by
  set O := pPrimeCoreOf 3 Y with hO
  have hOY : O ≤ Y := pPrimeCoreOf_le 3 Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  let S : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ e * y * e⁻¹ * y⁻¹ ∈ O}
      one_mem' := ⟨Y.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
        refine ⟨Y.mul_mem haY hbY, ?_⟩
        have e1 : e * (a * b) * e⁻¹ * (a * b)⁻¹ =
            (e * a * e⁻¹ * a⁻¹) * (a * (e * b * e⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e1]
        exact O.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hYO haY) _).mp hb)
      inv_mem' := by
        rintro a ⟨haY, ha⟩
        refine ⟨Y.inv_mem haY, ?_⟩
        have e1 : e * a⁻¹ * e⁻¹ * a⁻¹⁻¹ = a⁻¹ * (e * a * e⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (hYO (Y.inv_mem haY)) _).mp (O.inv_mem ha) }
  have hOS : O ≤ S := fun k hk => by
    refine ⟨hOY hk, ?_⟩
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp heO k).mp hk) (O.inv_mem hk)
  have hDS : D ≤ S := fun d hd => by
    have hdY : d ∈ Y := by
      rw [hdec]
      exact Subgroup.mem_sup_right hd
    refine ⟨hdY, ?_⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (heD hd)
    rw [show e * d * e⁻¹ * d⁻¹ = 1 by rw [← hc]; group]
    exact O.one_mem
  intro y hy
  rw [hdec] at hy
  exact ((sup_le hOS hDS) hy).2

theorem trivial_of_dec {A Y : Subgroup G} {LB : Subgroup G → Subgroup G} {e : G} (heA : e ∈ A)
    (he3 : orderOf e = 3) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hdec : Y = pPrimeCoreOf 3 Y ⊔
      deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers e : Set G))) :
    ∀ y ∈ Y, e * y * e⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y := by
  refine conj_mul_inv_mem_of_eq_sup hdec
    ((normalizer_le_normalizer_pPrimeCoreOf 3 Y) (hAY heA)) ?_
  refine sSup_le fun Q hQ => ?_
  refine le_centralizer_of_mem_invariantPiSubgroups heA he3
    ⟨hQ.2.trans inf_le_right, hQ.1.1.1.2.1, hQ.1.1.1.2.2⟩

theorem false_of_trivial_of_lB_eq_bot' {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A))
    {B : Subgroup G} (hB : IsHyperplane A B) (hLB : lB A B = ⊥)
    (hBtriv : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27
  set O := pPrimeCoreOf 3 Y with hO
  set OB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hOB
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hpi : ∀ X : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 X) := fun X =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
  have hK : IsPiSubgroup (piCompl 3) (OA ⊔ OB) :=
    isPiSubgroup_piCompl_sup (hpi _) (hpi _)
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1))
  set V := Y ⊓ (OA ⊔ OB) with hV
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hYW : Y ≤ V ⊔ O := by
    refine hY.2.2.1.le.trans (sSup_le fun Q hQ => ?_)
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hB.1.trans hQ.1.1.2.2
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three B Q (hA.isPGroup.to_le hB.1) hQ3 hBQ]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro q hq b hb
      have h1 := O.inv_mem (hBtriv b hb q (hQ.2 hq))
      have e : ⁅q, b⁆ = (b * q * b⁻¹ * q⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mem_sup_right h1
    · have h1 := hQ.1.2 B hB
      rw [qBound, hLB, sup_bot_eq, sup_comm] at h1
      exact le_sup_of_le_left (le_inf (inf_le_left.trans hQ.2) h1)
  have hW3 : IsPiSubgroup (piCompl 3) (V ⊔ O) :=
    isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_of_le hK inf_le_right) (hpi Y)
      (inf_le_left.trans hYO)
  have hY3 : ¬ 3 ∣ Nat.card Y := fun h3 =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hW3 (h3.trans (Subgroup.card_dvd_of_le hYW))
  have hY1 : Y = ⊥ := by
    rw [hY.2.1, oPrimeResidualOf_eq_closure, eq_bot_iff, Subgroup.closure_le]
    rintro x ⟨hxY, k, hxk⟩
    have hcop : Nat.Coprime (3 ^ k) (Nat.card Y) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)
    have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
    have h2 : orderOf x ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hxY
    have h3 : orderOf x ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  exact ne_bot_of_mem_scriptY4 hY hY1

theorem trivial_of_le {X Y : Subgroup G} (hXY : X ≤ Y) {e : G}
    (heX : e ∈ Subgroup.normalizer (X : Set G))
    (htriv : ∀ y ∈ Y, e * y * e⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y) :
    ∀ x ∈ X, e * x * e⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : pPrimeCoreOf 3 Y ⊓ X ≤ pPrimeCoreOf 3 X := by
    refine le_pPrimeCoreOf inf_le_right ?_ ?_
    · exact Late.le_normalizer_inf (hXY.trans (le_normalizer_pPrimeCoreOf 3 Y))
        Subgroup.le_normalizer
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 Y)
  intro x hx
  refine hle ⟨htriv x (hXY hx), ?_⟩
  exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp heX x).mp hx) (X.inv_mem hx)

@[expose] noncomputable def trivSub (X : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 X}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨mul_mem haN hbN, fun x hx => ?_⟩
    have hbx : b * x * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hbN x).mp hx
    have e1 : a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e1]
    have haO : a ∈ Subgroup.normalizer (pPrimeCoreOf 3 X : Set G) :=
      (normalizer_le_normalizer_pPrimeCoreOf 3 X) haN
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp haO _).mp (hb x hx)) (ha x hx)
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨inv_mem haN, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) x).mp hx
    have h1 := ha _ hx'
    have e1 : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ =
        (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e1]
    exact inv_mem h1

theorem mem_zpowers_of_trivial {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hLB : ∀ B, IsHyperplane A B → lB A B = ⊥) {X : Subgroup G}
    (hX : X ∈ scriptY4 A (lB A)) {e₁ e₂ : G} (he₁A : e₁ ∈ A) (he₁ : e₁ ≠ 1) (he₂A : e₂ ∈ A)
    (h₁ : ∀ x ∈ X, e₁ * x * e₁⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 X)
    (h₂ : ∀ x ∈ X, e₂ * x * e₂⁻¹ * x⁻¹ ∈ pPrimeCoreOf 3 X) :
    e₂ ∈ Subgroup.zpowers e₁ := by
  by_contra hne
  have hA : Late.IsE27 A := h.isE27
  set B := Subgroup.closure ({e₁, e₂} : Set G) with hBdef
  have hB9 : Nat.card B = 9 :=
    Sec4.Item424Proof.card_closure_pair_eq_nine h.toSec13Data.isElemAbelian hA.2 he₁A he₂A he₁ hne
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact he₁A
    · rw [Set.mem_singleton_iff.mp hx]; exact he₂A
  have hB : IsHyperplane A B := ⟨hBA, by rw [hA.2, hB9]⟩
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  have hBT : B ≤ trivSub X := by
    rw [hBdef, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact ⟨hAX he₁A, h₁⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨hAX he₂A, h₂⟩
  exact false_of_trivial_of_lB_eq_bot' h hX hB (hLB B hB) fun b hb y hy => (hBT hb).2 y hy

@[expose] noncomputable def imgX (X Y : Subgroup G) : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  (X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))

omit [Finite G] in
theorem conj_mem_normalizer_barR {X Y R : Subgroup G} (hXY : X ≤ Y)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) :
    ∀ k ∈ imgX X Y, MulAut.conj k ∈ Subgroup.normalizer (barR Y R : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  rw [← Sec17.Proof17Res6.actQ_of_mem]
  exact actQ_mem_normalizer_barR (Y.le_normalizer x.2) (hXR hxX)

omit [Finite G] in
theorem isPGroup_barR {Y R : Subgroup G} (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hR2 : IsPGroup 2 R) : IsPGroup 2 (barR Y R) :=
  (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm).map _

theorem commutator_le_of_forall {X Y R : Subgroup G} (hXY : X ≤ Y)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hR2 : IsPGroup 2 R)
    (hK : ∀ P : Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)), IsPGroup 2 P →
      (∀ k ∈ imgX X Y, MulAut.conj k ∈ Subgroup.normalizer (P : Set _)) → P = ⊥) :
    ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y :=
  commutator_le_pCoreOf_of_barR_eq_bot hRY
    (hK _ (isPGroup_barR hRY hR2) (conj_mem_normalizer_barR hXY hXR))

omit [Finite G] in
theorem isPerfect_imgX {X Y : Subgroup G} (hXY : X ≤ Y) (hXp : Group.IsPerfect ↥X) :
    Group.IsPerfect (imgX X Y) := by
  have hXp' : Group.IsPerfect (X.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXY).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.IsPerfect.ofSurjective
    (f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).subgroupMap (X.subgroupOf Y))
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).subgroupMap_surjective _)

theorem imgX_ne_bot {X Y : Subgroup G} (hXY : X ≤ Y) (hXp : Group.IsPerfect ↥X)
    (hX1 : X ≠ ⊥) : imgX X Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hK
  apply hX1
  have hX2 : IsPGroup 2 ↥X := by
    intro x
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY x.2⟩ = 1 := by
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY x.2⟩ ∈ imgX X Y :=
        ⟨⟨x, hXY x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
      rw [hK, Subgroup.mem_bot] at this
      exact this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y)) ⟨_, h1⟩
    have hn1 := congrArg Subtype.val hn
    have hn2 := congrArg Subtype.val hn1
    exact ⟨n, Subtype.ext (by simpa using hn2)⟩
  by_contra hne
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
  have : Group.IsNilpotent ↥X := hX2.isNilpotent
  exact Group.IsPerfect.not_isSolvable ↥X inferInstance

end CFSG.RankThree.PartTwo.Sec15.Wales154
