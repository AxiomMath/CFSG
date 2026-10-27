module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofPair
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
public import CFSG.RankThree.PartTwo.Sec14.LBNatural

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Res9Fix

open Res9Pair

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def sig (X : Subgroup G) (g : G) :
    MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
  classical
  exact if hg : g ∈ Subgroup.normalizer (X : Set G) then
    Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨g, hg⟩) else 1

theorem sig_eq {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    sig X g = Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨g, hg⟩) := by
  unfold sig
  simp [hg]

theorem sig_mk {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) {y : G}
    (hy : y ∈ X) :
    sig X g (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
        ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp hy⟩ := by
  rw [sig_eq hg, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  rfl

theorem sig_mul {X : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hh : h ∈ Subgroup.normalizer (X : Set G)) : sig X (g * h) = sig X g * sig X h := by
  rw [sig_eq hg, sig_eq hh, sig_eq (mul_mem hg hh), ← map_mul, ← map_mul]
  rfl

theorem sig_pow_three {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hg3 : g ^ 3 = 1) : sig X g ^ 3 = 1 := by
  have h1 : (⟨g, hg⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hg3)
  rw [sig_eq hg, ← map_pow, ← map_pow, h1, map_one, map_one]

@[expose] noncomputable def XW (X : Subgroup G) (W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    Subgroup G :=
  (W.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))).map X.subtype

omit [Finite G] in
theorem XW_le (X : Subgroup G) (W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    XW X W ≤ X :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_XW {X : Subgroup G} {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} {y : G}
    (hy : y ∈ X) (hyW : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ∈ W) :
    y ∈ XW X W :=
  ⟨⟨y, hy⟩, hyW, rfl⟩

omit [Finite G] in
theorem mk_mem_of_mem_XW {X : Subgroup G} {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}
    {y : G} (hyW : y ∈ XW X W) (hy : y ∈ X) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ∈ W := by
  obtain ⟨y', hy', rfl⟩ := hyW
  exact hy'

omit [Finite G] in
theorem mk_eq_mk_iff {X : Subgroup G} {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨x, hx⟩ : ↥X) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ↔
      x * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
  constructor
  · intro h1
    exact ⟨_, h1, by simp [div_eq_mul_inv]⟩
  · rintro ⟨z, hz, hzeq⟩
    have : z = (⟨x, hx⟩ : ↥X) / ⟨y, hy⟩ := Subtype.ext (by
      simp only [Subgroup.coe_subtype] at hzeq
      rw [hzeq, Subgroup.coe_div, div_eq_mul_inv])
    rwa [← this]

omit [Finite G] in
theorem mk_eq_one_iff {X : Subgroup G} {y : G} (hy : y ∈ X) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨y, hy⟩ : ↥X) = 1 ↔
      y ∈ inSubgroup (aschbacherSolvableCore 3) X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, hzeq⟩
    have : z = ⟨y, hy⟩ := Subtype.ext hzeq
    rwa [← this]

omit [Finite G] in
theorem le_normalizer_XW (X : Subgroup G) {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}
    (hW : W.Normal) : X ≤ Subgroup.normalizer (XW X W : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, ?_, by simp⟩
    show QuotientGroup.mk' _ (⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact hW.conj_mem _ hy' _
  · rintro ⟨y', hy', hy'eq⟩
    have hyX : y ∈ X := by
      have h1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [h1]
      exact mul_mem (mul_mem (inv_mem hx) (hy'eq ▸ y'.2)) hx
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨y, hyX⟩ ∈ W
    have h1 : (⟨y, hyX⟩ : ↥X) = ⟨x, hx⟩⁻¹ * y' * ⟨x, hx⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (y' : G) = x * y * x⁻¹ from hy'eq]
      group)
    rw [h1, map_mul, map_mul, map_inv]
    have := hW.conj_mem _ hy' (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩)⁻¹
    simpa using this

structure Base (A : Subgroup G) (a : G) (X : Subgroup G) : Prop where
  isE27 : Late.IsE27 A
  mem : a ∈ A
  le_centralizer : A ≤ Subgroup.centralizer ({a} : Set G)
  le_centralizer_X : X ≤ Subgroup.centralizer ({a} : Set G)
  theta_le : inSubgroup (aschbacherSolvableCore 3) X ≤
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))
  inf_le_theta : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ X ≤
    inSubgroup (aschbacherSolvableCore 3) X
  le_normalizer : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)
  isPerfect : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X)

structure Ctx (A : Subgroup G) (a : G) (X : Subgroup G)
    (U V : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)) : Prop extends Base A a X where
  isPair : IsPair U V

section Ctx

variable {A X : Subgroup G} {a : G} {U V : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}

omit [Finite G] in
theorem Base.cent_le_normalizer_O (_hC : Base A a X) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
  le_normalizer_pPrimeCoreOf 3 _

omit [Finite G] in
theorem Base.X_le_normalizer_O (hC : Base A a X) :
    X ≤ Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
  hC.le_centralizer_X.trans hC.cent_le_normalizer_O

omit [Finite G] in
theorem Base.A_le_normalizer (hC : Base A a X) : A ≤ Subgroup.normalizer (X : Set G) :=
  hC.le_centralizer.trans hC.le_normalizer

omit [Finite G] in
theorem Base.pow_three (hC : Base A a X) {x : G} (hx : x ∈ A) : x ^ 3 = 1 :=
  hC.isE27.1.2 x hx

theorem Base.sig_fixed (hC : Base A a X) {g : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    {o y : G} (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X)
    (hcomm : g * (o * y) = o * y * g) :
    sig X g (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ := by
  rw [sig_mk (hC.le_normalizer hg) hy, mk_eq_mk_iff]
  refine hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have h1 : g * y * g⁻¹ * y⁻¹ = (g * o * g⁻¹)⁻¹ * o := by
      have h2 : g * y * g⁻¹ = (g * o * g⁻¹)⁻¹ * (o * y) := by
        calc g * y * g⁻¹ = (g * o * g⁻¹)⁻¹ * (g * (o * y) * g⁻¹) := by group
          _ = (g * o * g⁻¹)⁻¹ * (o * y) := by rw [hcomm]; group
      rw [h2]
      group
    rw [h1]
    exact mul_mem (inv_mem ((Subgroup.mem_normalizer_iff.mp (hC.cent_le_normalizer_O hg) o).mp ho))
      ho
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hC.le_normalizer hg) y).mp hy) (inv_mem hy)

omit [Finite G] in
theorem Base.mk_pow_eq_one (hC : Base A a X) {o y : G}
    (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X) {k : ℕ}
    (hk : (o * y) ^ k = 1) : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) ^ k = 1 := by
  obtain ⟨n', hn', hpow⟩ := Item148PtRes.exists_pow_eq_mul hC.X_le_normalizer_O ho hy k
  have h1 : y ^ k = n'⁻¹ := by
    have h2 : n' * y ^ k = 1 := by rw [← hpow, hk]
    exact eq_inv_of_mul_eq_one_right h2
  rw [← map_pow]
  have h3 : (⟨y, hy⟩ : ↥X) ^ k = ⟨y ^ k, pow_mem hy k⟩ := Subtype.ext (by simp)
  rw [h3, mk_eq_one_iff]
  exact hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨h1 ▸ inv_mem hn', pow_mem hy k⟩)

omit [Finite G] in
theorem Base.le_normalizer_sup_XW (hC : Base A a X)
    {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} (hW : W.Normal) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      Subgroup.normalizer ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W :
        Subgroup G) : Set G) := by
  have hXWN := (XW_le X W).trans hC.X_le_normalizer_O
  exact sup_le (Item148PtRes.le_normalizer_sup_left hXWN)
    (le_normalizer_sup (A := X) hC.X_le_normalizer_O (le_normalizer_XW X hW))

omit [Finite G] in
theorem Base.mul_mem_sup_XW {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} {o y : G}
    (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X)
    (hyW : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ∈ W) :
    o * y ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W :=
  mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right (mem_XW hy hyW))

omit [Finite G] in
theorem Base.mk_mem_of_mem_sup_XW (hC : Base A a X)
    {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} {m : G}
    (hm : m ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W) {o y : G}
    (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X)
    (hmeq : m = o * y) : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ∈ W := by
  obtain ⟨o', ho', y', hy', rfl⟩ :=
    Item148PtRes.exists_mul_of_mem_sup ((XW_le X W).trans hC.X_le_normalizer_O) hm
  have hy'X : y' ∈ X := XW_le X W hy'
  have h1 : y * y'⁻¹ = o⁻¹ * o' := by
    calc y * y'⁻¹ = o⁻¹ * (o * y) * y'⁻¹ := by group
      _ = o⁻¹ * (o' * y') * y'⁻¹ := by rw [hmeq]
      _ = o⁻¹ * o' := by group
  have h2 : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y', hy'X⟩ := by
    rw [mk_eq_mk_iff]
    exact hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨h1 ▸ mul_mem (inv_mem ho) ho',
      mul_mem hy (inv_mem hy'X)⟩)
  rw [h2]
  exact mk_mem_of_mem_XW hy' hy'X

theorem Ctx.le_sup_XW_of_isPerfect (hC : Ctx A a X U V) {H : Subgroup G}
    (hHp : Group.IsPerfect H) (hHN : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    {g : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (hg3 : g ^ 3 = 1)
    (hgH : H ≤ Subgroup.centralizer ({g} : Set G)) (hσ : ¬ TrivOn (sig X g) U) :
    H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V := by
  have := hC.isPerfect
  have hVn := hC.isPair.normal_right
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Res9Pair.le_of_isPerfect_of_forall_pow_mem (p := 3) hHp
    (hHN.trans (hC.le_normalizer_sup_XW hVn)) fun h hh => ?_
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hHN hh)
  have hfix := hC.sig_fixed hg ho hy
    ((Subgroup.mem_centralizer_singleton_iff.mp (hgH hh)).symm)
  obtain ⟨e, he⟩ := hC.isPair.exists_pow_mem_right_of_fixed
    (sig_pow_three (hC.le_normalizer hg) hg3) hσ hfix
  obtain ⟨o', ho', hpow⟩ := Item148PtRes.exists_pow_eq_mul hC.X_le_normalizer_O ho hy (3 ^ e)
  refine ⟨e, ?_⟩
  rw [hpow]
  refine Base.mul_mem_sup_XW ho' (pow_mem hy _) ?_
  have h3 : (⟨y ^ 3 ^ e, pow_mem hy _⟩ : ↥X) = (⟨y, hy⟩ : ↥X) ^ 3 ^ e := Subtype.ext (by simp)
  rw [h3, map_pow]
  exact he

theorem Ctx.le_sup_XW_of_coprime (hC : Ctx A a X U V) {H : Subgroup G}
    (hH3 : ¬ 3 ∣ Nat.card H) (hHN : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    {g : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (hg3 : g ^ 3 = 1)
    (hgH : H ≤ Subgroup.centralizer ({g} : Set G)) (hσ : ¬ TrivOn (sig X g) U) :
    H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V := by
  have := hC.isPerfect
  intro h hh
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hHN hh)
  have hfix := hC.sig_fixed hg ho hy
    ((Subgroup.mem_centralizer_singleton_iff.mp (hgH hh)).symm)
  have hk : Nat.Coprime (orderOf (o * y)) 3 := by
    have h1 : orderOf (o * y) ∣ Nat.card H := by
      rw [← Subgroup.orderOf_mk (o * y) hh]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      fun h3' => hH3 (h3'.trans h1))
  refine Base.mul_mem_sup_XW ho hy ?_
  exact hC.isPair.mem_right_of_fixed (sig_pow_three (hC.le_normalizer hg) hg3) hσ hfix
    (hC.mk_pow_eq_one ho hy (pow_orderOf_eq_one (o * y))) hk

@[expose] noncomputable def img (a : G) (X H : Subgroup G) :
    Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
  (((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ H) ⊓ X).subgroupOf X).map
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))

omit [Finite G] in
theorem mk_mem_img {H : Subgroup G} {y : G} (hy : y ∈ X)
    (hyH : y ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ H) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ∈ img a X H :=
  ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hyH, hy⟩), rfl⟩

omit [Finite G] in
theorem Base.mem_sup_of_mk_mem_img (hC : Base A a X) {H : Subgroup G} {y : G} (hy : y ∈ X)
    (h : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ ∈ img a X H) :
    y ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ H := by
  obtain ⟨w, hw, hweq⟩ := h
  have hw' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
  have h1 : y * (w : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X :=
    (mk_eq_mk_iff hy w.2).mp hweq.symm
  have e : y = y * (w : G)⁻¹ * w := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (hC.theta_le h1)) hw'.1

omit [Finite G] in
theorem Base.img_le_of_le_sup_XW (hC : Base A a X) {H : Subgroup G}
    {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}
    (hH : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W) : img a X H ≤ W := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
  have hwM : (w : G) ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W :=
    (sup_le le_sup_left hH) hw'.1
  exact hC.mk_mem_of_mem_sup_XW hwM (one_mem _) w.2 (one_mul _).symm

theorem Base.sig_mem_img (hC : Base A a X) {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    ∀ l ∈ img a X H, sig X g l ∈ img a X H := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
  have hgN : g ∈ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ H : Subgroup G) : Set G) :=
    le_normalizer_sup (A := Subgroup.zpowers g)
      (Subgroup.zpowers_le.mpr (hC.cent_le_normalizer_O hg)) (Subgroup.zpowers_le.mpr hgH)
      (Subgroup.mem_zpowers g)
  have h1 : sig X g (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) w) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
        ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hC.le_normalizer hg) _).mp w.2⟩ :=
    sig_mk (hC.le_normalizer hg) w.2
  rw [h1]
  exact mk_mem_img _ ((Subgroup.mem_normalizer_iff.mp hgN _).mp hw'.1)

omit [Finite G] in
theorem Base.exists_mul_of_le_sup (hC : Base A a X) {H : Subgroup G}
    {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} (hVn : W.Normal)
    (hHN : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hXle : X ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W) ⊔ H)
    (γ : ↥X ⧸ aschbacherSolvableCore 3 ↥X) : ∃ v ∈ W, ∃ l ∈ img a X H, γ = v * l := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) γ
  have hHM := hHN.trans (hC.le_normalizer_sup_XW hVn)
  obtain ⟨s, hs, l, hl, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hHM (hXle hy)
  obtain ⟨o, ho, yv, hyv, rfl⟩ :=
    Item148PtRes.exists_mul_of_mem_sup ((XW_le X W).trans hC.X_le_normalizer_O) hs
  obtain ⟨o'', ho'', y'', hy'', hl'⟩ :=
    Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hHN hl)
  have hyvX : yv ∈ X := XW_le X W hyv
  refine ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨yv, hyvX⟩, mk_mem_of_mem_XW hyv hyvX,
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y'', hy''⟩, ?_, ?_⟩
  · refine mk_mem_img hy'' ?_
    have e : y'' = o''⁻¹ * l := by rw [hl']; group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem ho'')) (Subgroup.mem_sup_right hl)
  · rw [← map_mul]
    have hmul : (⟨yv, hyvX⟩ : ↥X) * ⟨y'', hy''⟩ = ⟨yv * y'', mul_mem hyvX hy''⟩ := rfl
    rw [hmul, mk_eq_mk_iff]
    refine hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have e : o * yv * l * (yv * y'')⁻¹ = o * (yv * o'' * yv⁻¹) := by rw [hl']; group
      rw [e]
      exact mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hC.X_le_normalizer_O hyvX) o'').mp ho'')
    · exact mul_mem hy (inv_mem (mul_mem hyvX hy''))

end Ctx

omit [Finite G] in
theorem isPerfect_iSup {ι : Sort*} (K : ι → Subgroup G) (h : ∀ i, Group.IsPerfect (K i)) :
    Group.IsPerfect (⨆ i, K i : Subgroup G) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) (iSup_le fun i => ?_)
  calc K i = ⁅K i, K i⁆ := (Subgroup.isPerfect_iff.mp (h i)).symm
    _ ≤ ⁅⨆ i, K i, ⨆ i, K i⁆ := Subgroup.commutator_mono (le_iSup K i) (le_iSup K i)

theorem isPerfect_lB (A B : Subgroup G) : Group.IsPerfect (lB A B) := by
  unfold lB
  refine isPerfect_iSup _ fun b => isPerfect_iSup _ fun d => isPerfect_iSup _ fun L =>
    isPerfect_iSup _ fun _ => ?_
  exact Sec6.isPerfect_inSubgroup_perfectResidual _

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_lB {A B : Subgroup G} (hB : IsHyperplane A B) {w : G}
    (hw : w ∈ Subgroup.centralizer (A : Set G)) :
    w ∈ Subgroup.normalizer (lB A B : Set G) := by
  have hwN : w ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
    · have h1 : w * x = x * w := (Subgroup.mem_centralizer_iff.mp hw x hx).symm
      rw [h1, mul_inv_cancel_right]
      exact hx
    · have h1 : w⁻¹ * x = x * w⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp (inv_mem hw) x hx).symm
      rw [h1, inv_mul_cancel_right]
      exact hx
  have hBw : B.map (MulAut.conj w).toMonoidHom = B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : w * y = y * w := Subgroup.mem_centralizer_iff.mp hw y (hB.1 hy) |>.symm
      show w * y * w⁻¹ ∈ B
      rw [h1, mul_inv_cancel_right]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      have h1 : w * x = x * w := Subgroup.mem_centralizer_iff.mp hw x (hB.1 hx) |>.symm
      show w * x * w⁻¹ = x
      rw [h1, mul_inv_cancel_right]
  have h := isNaturalFamily_lB A w hwN B hB
  rw [hBw] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem mem_normalizer_iSup_lB {A : Subgroup G} {a w : G}
    (hw : w ∈ Subgroup.centralizer (A : Set G)) :
    w ∈ Subgroup.normalizer
      ((⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.centralizer (A : Set G), ∀ x ∈
      (⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D : Subgroup G),
      g * x * g⁻¹ ∈ (⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D : Subgroup G) := by
    intro g hg x hx
    set M := (⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D : Subgroup G) with hM
    have hle : M ≤ M.comap (MulAut.conj g).toMonoidHom := by
      refine iSup₂_le fun D hD y hy => ?_
      show g * y * g⁻¹ ∈ M
      have h1 := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_lB hD.1 hg) y).mp hy
      exact (le_iSup₂_of_le D hD le_rfl : lB A D ≤ M) h1
    exact hle hx
  refine mem_normalizer_of_conj_mem (key w hw) fun x hx => ?_
  have := key w⁻¹ (inv_mem hw) x hx
  rwa [inv_inv] at this

theorem delta_le_sup_iSup (hbal : Step143Balance) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
          ⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D := by
  have hA := h.isE27'
  have hAmax := h.maximal_isElemAbelian
  refine sSup_le fun P hP => ?_
  obtain ⟨hPq, hPa⟩ := hP
  have hP3 : ¬ 3 ∣ Nat.card P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hPq.1.2.1
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
    (by rw [hA.2]; norm_num) hPq.1.2.2
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3) fun H hHA hH9 => ?_
  have hH : IsHyperplane A H := ⟨hHA, by rw [hA.2, hH9]; norm_num⟩
  by_cases haH : a ∈ H
  · have hK := pPrimeCoreOf_centralizer_le_sup hA hAmax hH.1
      (commutator_pPrimeCoreOf_le hbal h ha ha1 hΩ hH haH)
    refine (hPq.2 H hH).trans ?_
    rw [qBound]
    have hLH : lB A H ≤ ⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D :=
      le_iSup₂_of_le (f := fun (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D) => lB A D) H
        ⟨hH, haH⟩ le_rfl
    exact sup_le (sup_le (hK.trans le_sup_left) (le_sup_right.trans le_sup_left))
      (hLH.trans le_sup_right)
  · have hAle := le_sup_zpowers_of_not_mem hA hH ha haH
    have hCA : P ⊓ Subgroup.centralizer (H : Set G) ≤
        P ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, mem_centralizer_of_le_sup hAle
        (Subgroup.mem_inf.mp hx).2 (hPa (Subgroup.mem_inf.mp hx).1)⟩
    exact hCA.trans ((inf_centralizer_le_xA hAmax hP3).trans (le_sup_right.trans le_sup_left))

omit [Finite G] in
theorem le_of_le_sup_normalizer {S O' N T Y : Subgroup G} (hY : Y ≤ S ⊔ O')
    (hO'S : O' ≤ Subgroup.normalizer (S : Set G)) (hSN : S ≤ N) (hYN : Y ≤ N) (hST : S ≤ T)
    (hO'T : O' ⊓ N ≤ T) : Y ≤ T := by
  intro y hy
  obtain ⟨s, hs, o', ho', rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hO'S (hY hy)
  have ho'N : o' ∈ N := by
    have e : o' = s⁻¹ * (s * o') := by group
    rw [e]
    exact mul_mem (inv_mem (hSN hs)) (hYN hy)
  exact mul_mem (hST hs) (hO'T (Subgroup.mem_inf.mpr ⟨ho', ho'N⟩))

omit [Finite G] in
theorem coprime_orderOf_of_mem {H : Subgroup G} (hH3 : ¬ 3 ∣ Nat.card H) {h : G} (hh : h ∈ H) :
    Nat.Coprime (orderOf h) 3 := by
  have h1 : orderOf h ∣ Nat.card H := by
    rw [← Subgroup.orderOf_mk h hh]
    exact orderOf_dvd_natCard _
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    fun h3' => hH3 (h3'.trans h1))

section Generic

variable {A X : Subgroup G} {a : G} {U V : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}

omit [Finite G] in
theorem Ctx.symm (hC : Ctx A a X U V) : Ctx A a X V U :=
  { hC with isPair := hC.isPair.symm }

theorem Base.commutator_mem (hC : Base A a X) {x : G}
    (hx : x ∈ Subgroup.centralizer ({a} : Set G)) {o y : G}
    (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X)
    {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}
    (hW : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ *
      (sig X x (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩))⁻¹ ∈ W) :
    ⁅o * y, x⁆ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W := by
  have hxN := hC.le_normalizer hx
  have hxy : x * y * x⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  have hm : y * (x * y * x⁻¹)⁻¹ ∈ XW X W := by
    refine mem_XW (mul_mem hy (inv_mem hxy)) ?_
    have e : (⟨y * (x * y * x⁻¹)⁻¹, mul_mem hy (inv_mem hxy)⟩ : ↥X) =
        ⟨y, hy⟩ * (⟨x * y * x⁻¹, hxy⟩ : ↥X)⁻¹ := rfl
    rw [e, map_mul, map_inv, ← sig_mk hxN hy]
    exact hW
  have e : ⁅o * y, x⁆ = o * (y * (x * y * x⁻¹)⁻¹) * (x * o⁻¹ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hm))
    (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hC.cent_le_normalizer_O hx) _).mp
      (inv_mem ho)))

theorem Ctx.le_sup_XW_of_trivOn (hC : Ctx A a X U V) (hAU : ∀ x ∈ A, TrivOn (sig X x) U)
    {R : Subgroup G} (hRN : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hRR : R = ⁅R, A⁆) :
    R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V := by
  have := hC.isPerfect
  rw [hRR, Subgroup.commutator_le]
  intro r hr x hx
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hRN hr)
  exact hC.commutator_mem (hC.le_centralizer hx) ho hy
    (hC.isPair.symm.mul_inv_mem_left_of_trivOn_right
      (sig_pow_three (hC.A_le_normalizer hx) (hC.pow_three hx)) (hAU x hx) _)

omit [Finite G] in
theorem Ctx.le_of_le_both (hC : Ctx A a X U V) {H : Subgroup G} (hH3 : ¬ 3 ∣ Nat.card H)
    (hHN : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hHU : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X U)
    (hHV : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V) :
    H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  intro h hh
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hHN hh)
  have hU := hC.mk_mem_of_mem_sup_XW (hHU hh) ho hy rfl
  have hV := hC.mk_mem_of_mem_sup_XW (hHV hh) ho hy rfl
  have h1 := hC.isPair.eq_one_of_mem_inf (Subgroup.mem_inf.mpr ⟨hU, hV⟩)
    (hC.mk_pow_eq_one ho hy (pow_orderOf_eq_one (o * y))) (coprime_orderOf_of_mem hH3 hh)
  exact mul_mem ho (hC.theta_le ((mk_eq_one_iff hy).mp h1))

omit [Finite G] in
theorem Ctx.le_sup_of_comm (hC : Ctx A a X U V) {H Lm : Subgroup G} (hH3 : ¬ 3 ∣ Nat.card H)
    (hHN : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hHU : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X U)
    (hcomm : ⁅U, U⁆ ≤ img a X Lm) :
    H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ Lm := by
  have := hC.isPerfect
  intro h hh
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hHN hh)
  have hU := hC.mk_mem_of_mem_sup_XW (hHU hh) ho hy rfl
  have h1 := hcomm (hC.isPair.mem_commutator_left hU
    (hC.mk_pow_eq_one ho hy (pow_orderOf_eq_one (o * y))) (coprime_orderOf_of_mem hH3 hh))
  exact mul_mem (Subgroup.mem_sup_left ho) (hC.mem_sup_of_mk_mem_img hy h1)

omit [Finite G] in
theorem Base.XW_bot_le (hC : Base A a X) :
    XW X ⊥ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y ∈
      (⊥ : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := hy
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
  exact hC.theta_le ⟨y, hy', rfl⟩

theorem Base.commutator_mem_O (hC : Base A a X) {x : G}
    (hx : x ∈ Subgroup.centralizer ({a} : Set G)) {o y : G}
    (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X)
    (hfix : sig X x (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) :
    ⁅o * y, x⁆ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have h1 := hC.commutator_mem hx ho hy (W := ⊥) (by rw [hfix, mul_inv_cancel]; exact one_mem _)
  exact (sup_le le_rfl hC.XW_bot_le) h1

theorem Ctx.le_O_of_trivOn_left (hC : Ctx A a X U V) (hAU : ∀ x ∈ A, TrivOn (sig X x) U)
    {R : Subgroup G} (hR3 : ¬ 3 ∣ Nat.card R)
    (hRN : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hRU : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X U)
    (hRR : R = ⁅R, A⁆) : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have := hC.isPerfect
  rw [hRR, Subgroup.commutator_le]
  intro r hr x hx
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hRN hr)
  have hU := hC.mk_mem_of_mem_sup_XW (hRU hr) ho hy rfl
  have hc := hC.isPair.mem_commutator_left hU
    (hC.mk_pow_eq_one ho hy (pow_orderOf_eq_one (o * y))) (coprime_orderOf_of_mem hR3 hr)
  exact hC.commutator_mem_O (hC.le_centralizer hx) ho hy
    (Item148PtRes.fixed_of_mem_commutator hC.isPair.centerIn_le_center (hAU x hx) hc)

theorem Ctx.commutator_le_O_of_trivOn (hC : Ctx A a X U V) (hAU : ∀ x ∈ A, TrivOn (sig X x) U)
    (hAV : ∀ x ∈ A, TrivOn (sig X x) V) {B' : Subgroup G} (hB'A : B' ≤ A) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have := hC.isPerfect
  rw [Subgroup.commutator_le]
  intro m hm x hx
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O hm
  exact hC.commutator_mem_O (hC.le_centralizer (hB'A hx)) ho hy
    (hC.isPair.eq_of_trivOn (hAU x (hB'A hx)) (hAV x (hB'A hx)) _)

theorem Base.exists_not_trivOn (hC : Base A a X) {D D' : Subgroup G} (hD : IsHyperplane A D)
    (hD' : IsHyperplane A D') (hne : D' ≠ D)
    {W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} (hDW : ∀ d ∈ D, TrivOn (sig X d) W)
    {x : G} (hxA : x ∈ A) (hxW : ¬ TrivOn (sig X x) W) :
    ∃ d' ∈ D', ¬ TrivOn (sig X d') W := by
  by_contra hall
  push Not at hall
  apply hxW
  have hD'D : ¬ D' ≤ D := by
    intro hle
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := hD.2
    have h2 := hD'.2
    omega
  obtain ⟨d', hd'D', hd'D⟩ := Set.not_subset.mp hD'D
  have hAle : A ≤ D ⊔ D' :=
    (le_sup_zpowers_of_not_mem hC.isE27 hD (hD'.1 hd'D') hd'D).trans
      (sup_le_sup_left (Subgroup.zpowers_le.mpr hd'D') D)
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hC.isE27.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hD'N : D' ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · rw [hcomm g (hD'.1 hg) y (hD.1 hy), mul_inv_cancel_right]
      exact hy
    · rw [hcomm g⁻¹ (inv_mem (hD'.1 hg)) y (hD.1 hy), inv_mul_cancel_right]
      exact hy
  obtain ⟨d, hd, e, he, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hD'N (hAle hxA)
  rw [sig_mul (hC.A_le_normalizer (hD.1 hd)) (hC.A_le_normalizer (hD'.1 he))]
  exact (hDW d hd).mul (hall e he)

theorem exists_hyperplane_ne {A D : Subgroup G} (hA : Late.IsE27 A) (hD : IsHyperplane A D)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) (haD : a ∈ D) :
    ∃ B' : Subgroup G, IsHyperplane A B' ∧ a ∈ B' ∧ B' ≠ D := by
  have hAD : ¬ A ≤ D := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    have h2 := hD.2
    rw [hA.2] at h1 h2
    omega
  obtain ⟨x, hxA, hxD⟩ := Set.not_subset.mp hAD
  have hxa : x ∉ Subgroup.zpowers a := fun hx => hxD ((Subgroup.zpowers_le.mpr haD) hx)
  refine ⟨Subgroup.closure {a, x}, Main148.isHyperplane_closure_pair148 hA ha hxA ha1 hxa,
    Subgroup.subset_closure (Set.mem_insert a _), fun heq => hxD ?_⟩
  rw [← heq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)

theorem Ctx.le_O_of_isPerfect_both (hC : Ctx A a X U V) {H : Subgroup G}
    (hHp : Group.IsPerfect H)
    (hHN : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hHU : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X U)
    (hHV : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V) :
    H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNO : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    sup_le Subgroup.le_normalizer hC.X_le_normalizer_O
  refine Res9Pair.le_of_isPerfect_of_forall_pow_mem (p := 3) hHp (hHN.trans hNO)
    fun h hh => ⟨1, ?_⟩
  obtain ⟨o, ho, y, hy, rfl⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O (hHN hh)
  have hU := hC.mk_mem_of_mem_sup_XW (hHU hh) ho hy rfl
  have hV := hC.mk_mem_of_mem_sup_XW (hHV hh) ho hy rfl
  have h1 := Subgroup.orderOf_dvd_natCard (U ⊓ V) (Subgroup.mem_inf.mpr ⟨hU, hV⟩)
  rw [hC.isPair.card_inf] at h1
  have h2 : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp h1
  rw [← map_pow] at h2
  have h3 : (⟨y, hy⟩ : ↥X) ^ 3 = ⟨y ^ 3, pow_mem hy 3⟩ := Subtype.ext (by simp)
  rw [h3, mk_eq_one_iff] at h2
  obtain ⟨o', ho', hpow⟩ := Item148PtRes.exists_pow_eq_mul hC.X_le_normalizer_O ho hy 3
  rw [pow_one, hpow]
  exact mul_mem ho' (hC.theta_le h2)

theorem Base.le_of_gen (hC : Base A a X)
    (hLD : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
      lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hgen : X ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
        ⨆ (D' : Subgroup G) (_ : IsHyperplane A D' ∧ a ∈ D'), lB A D')
    {T : Subgroup G} (hOT : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ≤ T)
    (hLT : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' → lB A D' ≤ T)
    (hO'T : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓
      (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ≤ T) : X ≤ T := by
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  set M := (⨆ (D' : Subgroup G) (_ : IsHyperplane A D' ∧ a ∈ D'), lB A D' : Subgroup G) with hM
  have hY : X ≤ (O ⊔ M) ⊔ O' :=
    hgen.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left))
  have hCAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hC.mem)
  have hO'S : O' ≤ Subgroup.normalizer ((O ⊔ M : Subgroup G) : Set G) := fun w hw =>
    le_normalizer_sup (A := Subgroup.zpowers w)
      (Subgroup.zpowers_le.mpr (hC.cent_le_normalizer_O (hCAa (pPrimeCoreOf_le 3 _ hw))))
      (Subgroup.zpowers_le.mpr (mem_normalizer_iSup_lB (pPrimeCoreOf_le 3 _ hw)))
      (Subgroup.mem_zpowers w)
  have hSN : O ⊔ M ≤ O ⊔ X := sup_le le_sup_left (iSup₂_le fun D' hD' => hLD D' hD'.1 hD'.2)
  have hST : O ⊔ M ≤ T := sup_le hOT (iSup₂_le fun D' hD' => hLT D' hD'.1 hD'.2)
  exact le_of_le_sup_normalizer hY hO'S hSN le_sup_right hST hO'T

theorem Ctx.lB_le_sup_XW (hC : Ctx A a X U V)
    (hLD : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
      lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    {D D' : Subgroup G} (hD : IsHyperplane A D) (hD' : IsHyperplane A D') (haD' : a ∈ D')
    (hne : D' ≠ D) (hDU : ∀ d ∈ D, TrivOn (sig X d) U) {x : G} (hxA : x ∈ A)
    (hxU : ¬ TrivOn (sig X x) U) :
    lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V := by
  obtain ⟨d', hd', hd'U⟩ := hC.exists_not_trivOn hD hD' hne hDU hxA hxU
  exact hC.le_sup_XW_of_isPerfect (isPerfect_lB A D') (hLD D' hD' haD')
    (hC.le_centralizer (hD'.1 hd')) (hC.pow_three (hD'.1 hd'))
    ((lB_le_centralizer A D').trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd')))
    hd'U

theorem not_three_dvd_inf (A N : Subgroup G) :
    ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ N : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _))

theorem Ctx.inf_le_sup_XW (hC : Ctx A a X U V) {x : G} (hxA : x ∈ A)
    (hxU : ¬ TrivOn (sig X x) U) :
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓
        (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V :=
  hC.le_sup_XW_of_coprime (not_three_dvd_inf A _) inf_le_right (hC.le_centralizer hxA)
    (hC.pow_three hxA) (inf_le_left.trans ((pPrimeCoreOf_le 3 _).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxA)))) hxU

theorem Ctx.le_sup_lB_core (hC : Ctx A a X U V) {D : Subgroup G} (hD : IsHyperplane A D)
    (haD : a ∈ D)
    (hLD : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
      lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hgen : X ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
        ⨆ (D' : Subgroup G) (_ : IsHyperplane A D' ∧ a ∈ D'), lB A D')
    (hDU : ∀ d ∈ D, TrivOn (sig X d) U) {x : G} (hxA : x ∈ A) (hxU : ¬ TrivOn (sig X x) U)
    (hΛ : img a X (lB A D) ≤ U ∨ ∀ y ∈ A, TrivOn (sig X y) V)
    {R : Subgroup G} (hR3 : ¬ 3 ∣ Nat.card R)
    (hRN : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hRU : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X U) :
    R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ lB A D := by
  have := hC.isPerfect
  have hXle : X ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X V) ⊔ lB A D := by
    refine hC.le_of_gen hLD hgen (le_sup_left.trans le_sup_left) (fun D' hD' haD' => ?_)
      ((hC.inf_le_sup_XW hxA hxU).trans le_sup_left)
    by_cases hne : D' = D
    · rw [hne]
      exact le_sup_right
    · exact (hC.lB_le_sup_XW hLD hD hD' haD' hne hDU hxA hxU).trans le_sup_left
  have hdec := hC.exists_mul_of_le_sup hC.isPair.normal_right (hLD D hD haD) hXle
  have hcomm : ⁅U, U⁆ ≤ img a X (lB A D) := by
    rcases hΛ with hΛU | hAV
    · exact hC.isPair.commutator_le_of_le_left hΛU hdec
    · have hxC : x ∈ Subgroup.centralizer (A : Set G) :=
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.isE27.1.1) hxA
      exact hC.isPair.commutator_le_of_trivOn_right hdec
        (sig_pow_three (hC.A_le_normalizer hxA) (hC.pow_three hxA))
        (hC.sig_mem_img (hC.le_centralizer hxA) (mem_normalizer_lB hD hxC)) (hAV x hxA) hxU
  exact hC.le_sup_of_comm hR3 hRN hRU hcomm

theorem Ctx.sup_le_of_nontriv (hC : Ctx A a X U V) {D : Subgroup G} (hD : IsHyperplane A D)
    (hLD : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
      lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hgen : X ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
        ⨆ (D' : Subgroup G) (_ : IsHyperplane A D' ∧ a ∈ D'), lB A D')
    (hDU : ∀ d ∈ D, TrivOn (sig X d) U) (hDV : ∀ d ∈ D, TrivOn (sig X d) V) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (h₁ : ¬ TrivOn (sig X x₁) U) (h₂ : ¬ TrivOn (sig X x₂) V) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have hXle : X ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ lB A D := by
    refine hC.le_of_gen hLD hgen le_sup_left (fun D' hD' haD' => ?_)
      ((hC.le_of_le_both (not_three_dvd_inf A _) inf_le_right (hC.symm.inf_le_sup_XW hx₂ h₂)
        (hC.inf_le_sup_XW hx₁ h₁)).trans le_sup_left)
    by_cases hne : D' = D
    · rw [hne]
      exact le_sup_right
    · exact (hC.le_O_of_isPerfect_both (isPerfect_lB A D') (hLD D' hD' haD')
        (hC.symm.lB_le_sup_XW hLD hD hD' haD' hne hDV hx₂ h₂)
        (hC.lB_le_sup_XW hLD hD hD' haD' hne hDU hx₁ h₁)).trans le_sup_left
  rw [sup_comm (lB A D)]
  exact sup_le le_sup_left hXle

theorem Ctx.le_qBound (hbal : Step143Balance) {L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hC : Ctx A a X U V) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hXΔ : X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)))
    (hLD : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
      lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    {D : Subgroup G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hα : ∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
      ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hβ : ¬ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    {R : Subgroup G}
    (hRN : R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
      Subgroup.centralizer (D : Set G))
    (hR3 : ¬ 3 ∣ Nat.card R) (hRR : R = ⁅R, A⁆) : R ≤ qBound A (lB A) D := by
  have hgen := hXΔ.trans (delta_le_sup_iSup hbal h hC.mem ha1 hΩ)
  have hRX : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X :=
    hRN.trans inf_le_left
  have hRD : R ≤ Subgroup.centralizer (D : Set G) := hRN.trans inf_le_right
  have hfin1 : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) →
      R ≤ qBound A (lB A) D := fun hRO =>
    (le_inf hRO hRD).trans ((Res7MemFix.inf_centralizer_le_pPrimeCoreOf haD).trans
      (by rw [qBound]; exact le_sup_left.trans le_sup_left))
  have hfin2 : R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ lB A D →
      R ≤ qBound A (lB A) D := fun hRL =>
    (le_inf hRL hRD).trans ((Res7MemFix.inf_centralizer_le_of_le_sup haD
      (le_of_eq (sup_comm _ _))).trans
      (by rw [qBound]; exact sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hRd : ∀ d ∈ D, R ≤ Subgroup.centralizer ({d} : Set G) := fun d hd =>
    hRD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd))
  have hfix : ∀ {W W' : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)}, Ctx A a X W W' →
      ∀ d ∈ D, ¬ TrivOn (sig X d) W →
        R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ XW X W' :=
    fun hC' d hd hdW => hC'.le_sup_XW_of_coprime hR3 hRX (hC.le_centralizer (hD.1 hd))
      (hC.pow_three (hD.1 hd)) (hRd d hd) hdW
  by_cases hDU : ∀ d ∈ D, TrivOn (sig X d) U
  · by_cases hDV : ∀ d ∈ D, TrivOn (sig X d) V
    · by_cases hAU : ∀ x ∈ A, TrivOn (sig X x) U
      · by_cases hAV : ∀ x ∈ A, TrivOn (sig X x) V
        ·
          exfalso
          obtain ⟨B', hB', haB', hB'D⟩ := exists_hyperplane_ne hC.isE27 hD hC.mem ha1 haD
          exact hα B' hB' haB' hB'D (hC.commutator_le_O_of_trivOn hAU hAV hB'.1)
        ·
          push Not at hAV
          obtain ⟨x, hxA, hxV⟩ := hAV
          exact hfin2 (hC.symm.le_sup_lB_core hD haD hLD hgen hDV hxA hxV (Or.inr hAU) hR3 hRX
            (hC.le_sup_XW_of_trivOn hAU hRX hRR))
      · push Not at hAU
        obtain ⟨x, hxA, hxU⟩ := hAU
        by_cases hAV : ∀ y ∈ A, TrivOn (sig X y) V
        ·
          exact hfin2 (hC.le_sup_lB_core hD haD hLD hgen hDU hxA hxU (Or.inr hAV) hR3 hRX
            (hC.symm.le_sup_XW_of_trivOn hAV hRX hRR))
        ·
          push Not at hAV
          obtain ⟨x', hx'A, hx'V⟩ := hAV
          exact absurd (hC.sup_le_of_nontriv hD hLD hgen hDU hDV hxA hx'A hxU hx'V) hβ
    ·
      push Not at hDV
      obtain ⟨d₂, hd₂, hd₂V⟩ := hDV
      have hRU := hfix hC.symm d₂ hd₂ hd₂V
      by_cases hAU : ∀ x ∈ A, TrivOn (sig X x) U
      · exact hfin1 (hC.le_O_of_trivOn_left hAU hR3 hRX hRU hRR)
      · push Not at hAU
        obtain ⟨x, hxA, hxU⟩ := hAU
        have hLU := hC.symm.le_sup_XW_of_isPerfect (isPerfect_lB A D) (hLD D hD haD)
          (hC.le_centralizer (hD.1 hd₂)) (hC.pow_three (hD.1 hd₂))
          ((lB_le_centralizer A D).trans
            (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd₂))) hd₂V
        exact hfin2 (hC.le_sup_lB_core hD haD hLD hgen hDU hxA hxU
          (Or.inl (hC.img_le_of_le_sup_XW hLU)) hR3 hRX hRU)
  · push Not at hDU
    obtain ⟨d₁, hd₁, hd₁U⟩ := hDU
    have hRV := hfix hC d₁ hd₁ hd₁U
    by_cases hDV : ∀ d ∈ D, TrivOn (sig X d) V
    ·
      by_cases hAV : ∀ x ∈ A, TrivOn (sig X x) V
      · exact hfin1 (hC.symm.le_O_of_trivOn_left hAV hR3 hRX hRV hRR)
      · push Not at hAV
        obtain ⟨x, hxA, hxV⟩ := hAV
        have hLV := hC.le_sup_XW_of_isPerfect (isPerfect_lB A D) (hLD D hD haD)
          (hC.le_centralizer (hD.1 hd₁)) (hC.pow_three (hD.1 hd₁))
          ((lB_le_centralizer A D).trans
            (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd₁))) hd₁U
        exact hfin2 (hC.symm.le_sup_lB_core hD haD hLD hgen hDV hxA hxV
          (Or.inl (hC.symm.img_le_of_le_sup_XW hLV)) hR3 hRX hRV)
    ·
      push Not at hDV
      obtain ⟨d₂, hd₂, hd₂V⟩ := hDV
      exact hfin1 (hC.le_of_le_both hR3 hRX (hfix hC.symm d₂ hd₂ hd₂V) hRV)

end Generic

theorem base_of {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L) (ha : a ∈ A)
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 a) {X : Subgroup G} (hX : X = sSup 𝒳)
    (hN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hP0 : ∀ P : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X), P.Normal →
      ¬ 3 ∣ Nat.card P → P = ⊥) : Base A a X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXa : X ≤ Subgroup.centralizer ({a} : Set G) :=
    hX ▸ sSup_le fun L hL => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hL)
  have hXN : X ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    hXa.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hNX : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊓ X ≤
      inSubgroup (aschbacherSolvableCore 3) X :=
    Item148PtRes.inf_le_theta_of_forall_normal hXN (coprime_card_pPrimeCoreOf 3 _) hP0
  have hXp : Group.IsPerfect ↥X := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le_self X) ?_
    rw [hX]
    refine sSup_le fun L hL => ?_
    have hLp : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hL)
    rw [← (Subgroup.isPerfect_iff).mp hLp]
    exact Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)
  exact
    { isE27 := h.isE27'
      mem := ha
      le_centralizer := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx ha)
      le_centralizer_X := hXa
      theta_le := Item148PtRes.theta_le_pPrimeCoreOf_of_eq_sSup h𝒳 hX
      inf_le_theta := hNX
      le_normalizer := fun g hg => Item148PtRes.mem_normalizer_of_eq_sSup h𝒳 hX hNX hg (hN hg)
      isPerfect := inferInstance }

theorem ctx_of {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L) (ha : a ∈ A)
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 a) {X : Subgroup G} (hX : X = sSup 𝒳)
    (hN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G))
    {U V : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X)} (hP : IsPair U V) : Ctx A a X U V := by
  have hU := hP.normal_left
  have hV := hP.normal_right
  exact { base_of h ha h𝒳 hX hN fun P hPn hP3 => Item148PtRes.eq_bot_of_normal_of_coprime
      hP.sup_eq hP.comm_eq hP.card_inf hP.cover_left hP.cover_right hPn hP3 with isPair := hP }

theorem le_qBound_of_centralProduct (hbal : Step143Balance) {A L : Subgroup G} {c a : G}
    (h : Sec14Std G A c L) (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    {X : Subgroup G} (hXΔ : X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)))
    (hLD : ∀ D' : Subgroup G, IsHyperplane A D' → a ∈ D' →
      lB A D' ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
    (hN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G))
    (h𝒳 : ∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ X = sSup 𝒳)
    (hT : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    {D : Subgroup G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hα : ∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
      ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hβ : ¬ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    {R : Subgroup G}
    (hRN : R ≤ (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ⊓
      Subgroup.centralizer (D : Set G))
    (hR3 : ¬ 3 ∣ Nat.card R) (hRR : R = ⁅R, A⁆) : R ≤ qBound A (lB A) D := by
  obtain ⟨𝒳, h𝒳a, -, hX𝒳⟩ := h𝒳
  obtain ⟨U, V, hP⟩ := exists_isPair hT
  exact (ctx_of h ha h𝒳a hX𝒳 hN hP).le_qBound hbal h ha1 hΩ hXΔ hLD hD haD hα hβ hRN hR3 hRR

end Res9Fix

end CFSG.RankThree.PartTwo.Sec14
