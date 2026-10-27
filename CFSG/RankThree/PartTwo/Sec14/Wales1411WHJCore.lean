module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJConf
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WYFrame
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Wales1411WTori
import CFSG.RankThree.PartTwo.Sec14.Item14Res4ProofL34
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec15.F153L3C2PCore
import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

structure HJCoreSetting {M : Type} [Group M] (Ybar Abar Xbar Rbar : Subgroup M) (abar : M) :
    Prop where
  le_normalizer_Y : Abar ≤ Subgroup.normalizer (Ybar : Set M)
  sup_eq_top : Ybar ⊔ Abar = ⊤
  le_normalizer_X : Ybar ⊔ Abar ≤ Subgroup.normalizer (Xbar : Set M)
  le_Y : Xbar ≤ Ybar
  eq_sup : Ybar = Xbar ⊔ Rbar
  le_centralizer_R : Rbar ≤ Subgroup.centralizer (Abar : Set M)
  not_three_dvd_R : ¬ 3 ∣ Nat.card Rbar
  isElemAbelian : CFSG.Assembly.IsElemAbelian 3 Abar
  card_A : Nat.card Abar = 27
  mem_A : abar ∈ Abar
  ne_one : abar ≠ 1
  le_centralizer_a : Ybar ≤ Subgroup.centralizer ({abar} : Set M)
  mem_zpowers : ∀ e ∈ Abar, Ybar ≤ Subgroup.centralizer ({e} : Set M) → e ∈ Subgroup.zpowers abar
  mem_A_of_three : ∀ x ∈ Ybar, x ∈ Subgroup.centralizer (Abar : Set M) → orderOf x = 3 →
    x ∈ Abar
  eq_bot_of_three : ∀ U : Subgroup M, U ≤ Ybar → Ybar ≤ Subgroup.normalizer (U : Set M) →
    ¬ 3 ∣ Nat.card U → U = ⊥
  perfect : Group.IsPerfect ↥Xbar

@[expose] def HJCoreType {M : Type} [Group M] (Xbar : Subgroup M) : Prop :=
  Sec4.IsTripleCover ↥Xbar CFSG.Blueprint.NativeSporadic.ON ∨ IsCentralProductA6Covers ↥Xbar ∨
    IsA6CoverTimesA5 ↥Xbar ∨
    Nonempty (↥Xbar ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
    Nonempty (↥Xbar ≃* alternatingGroup (Fin 7)) ∨
    (∃ _ : Fact (Nat.Prime 7),
      Nonempty (↥Xbar ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
    Nonempty (↥Xbar ≃* alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2)

@[expose] def KS1411HJCore : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (Ybar Abar Xbar Rbar : Subgroup M) (abar : M),
    HJCoreSetting Ybar Abar Xbar Rbar abar → HJCoreType Xbar →
      ∀ S T : Subgroup M, Maximal (Wales1411W.InvTwo Abar Ybar) S →
        Maximal (Wales1411W.InvTwo Abar Ybar) T → S ⊔ T = Ybar →
        (∀ e ∈ Abar, ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) →
          S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥ ∨
            T ⊓ Subgroup.centralizer ({e} : Set M) = ⊥) →
        ∃ n ∈ Ybar ⊓ Subgroup.normalizer (Abar : Set M), T = S.map (MulAut.conj n).toMonoidHom

@[expose] def KS1411HJCoreFor (P : ∀ {M : Type} [Group M], Subgroup M → Prop) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (Ybar Abar Xbar Rbar : Subgroup M) (abar : M),
    HJCoreSetting Ybar Abar Xbar Rbar abar → P Xbar →
      ∀ S T : Subgroup M, Maximal (Wales1411W.InvTwo Abar Ybar) S →
        Maximal (Wales1411W.InvTwo Abar Ybar) T → S ⊔ T = Ybar →
        (∀ e ∈ Abar, ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) →
          S ⊓ Subgroup.centralizer ({e} : Set M) = ⊥ ∨
            T ⊓ Subgroup.centralizer ({e} : Set M) = ⊥) →
        ∃ n ∈ Ybar ⊓ Subgroup.normalizer (Abar : Set M), T = S.map (MulAut.conj n).toMonoidHom

@[expose] def KS1411HJCoreON : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar =>
    Sec4.IsTripleCover ↥Xbar CFSG.Blueprint.NativeSporadic.ON

@[expose] def KS1411HJCoreA6A6 : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar => IsCentralProductA6Covers ↥Xbar

@[expose] def KS1411HJCoreA6A5 : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar => IsA6CoverTimesA5 ↥Xbar

@[expose] def KS1411HJCoreA5A5 : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar =>
    Nonempty (↥Xbar ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))

@[expose] def KS1411HJCoreA7 : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar => Nonempty (↥Xbar ≃* alternatingGroup (Fin 7))

@[expose] def KS1411HJCoreL37 : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar => ∃ _ : Fact (Nat.Prime 7),
    Nonempty (↥Xbar ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))

@[expose] def KS1411HJCoreA5J2 : Prop :=
  KS1411HJCoreFor fun {M} _ Xbar =>
    Nonempty (↥Xbar ≃* alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2)

theorem ks1411HJCore_of_types (hON : KS1411HJCoreON) (h66 : KS1411HJCoreA6A6)
    (h65 : KS1411HJCoreA6A5) (h55 : KS1411HJCoreA5A5) (h7 : KS1411HJCoreA7)
    (hL : KS1411HJCoreL37) (hJ : KS1411HJCoreA5J2) : KS1411HJCore := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset htype S T hS hT hST hsupp
  rcases htype with h | h | h | h | h | h | h
  · exact hON M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp
  · exact h66 M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp
  · exact h65 M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp
  · exact h55 M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp
  · exact h7 M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp
  · exact hL M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp
  · exact hJ M Ybar Abar Xbar Rbar abar hset h S T hS hT hST hsupp

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_le {Y O : Subgroup G} {e : G}
    (heO : e ∈ Subgroup.normalizer (O : Set G)) (h : ∀ y ∈ Y, ⁅y, e⁆ ∈ O) :
    ⁅Y, Subgroup.zpowers e⁆ ≤ O := by
  let H : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (O : Set G) ∧ ∀ y ∈ Y, ⁅y, g⁆ ∈ O}
      one_mem' := ⟨one_mem _, fun y _ => by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro g h ⟨hgO, hg⟩ ⟨hhO, hh⟩
        refine ⟨mul_mem hgO hhO, fun y hy => ?_⟩
        have e1 : ⁅y, g * h⁆ = ⁅y, g⁆ * (g * ⁅y, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        exact mul_mem (hg y hy) ((Subgroup.mem_normalizer_iff.mp hgO _).mp (hh y hy))
      inv_mem' := by
        rintro g ⟨hgO, hg⟩
        refine ⟨inv_mem hgO, fun y hy => ?_⟩
        have e1 : ⁅y, g⁻¹⁆ = g⁻¹ * (⁅y, g⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem hgO) _).mp (inv_mem (hg y hy)) }
  have hZ : Subgroup.zpowers e ≤ H := Subgroup.zpowers_le.mpr ⟨heO, h⟩
  rw [Subgroup.commutator_le]
  intro y hy z hz
  exact (hZ hz).2 y hy

theorem commutator_zpowers_le_of_eq_sup {Y D : Subgroup G} {e : G}
    (hdec : Y = pPrimeCoreOf 3 Y ⊔ D)
    (heO : e ∈ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G))
    (heD : D ≤ Subgroup.centralizer ({e} : Set G)) :
    ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y := by
  refine commutator_zpowers_le heO fun y hy => ?_
  have hY : y ∈ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) := le_normalizer_pPrimeCoreOf 3 Y hy
  have e1 : ⁅y, e⁆ = y * (e * y⁻¹ * e⁻¹ * y) * y⁻¹ := by
    simp only [commutatorElement_def]
    group
  have h2 : e * y⁻¹ * e⁻¹ * y ∈ pPrimeCoreOf 3 Y := by
    have := Sec15.Wales154.conj_mul_inv_mem_of_eq_sup hdec heO heD y⁻¹ (inv_mem hy)
    simpa using this
  rw [e1]
  exact (Subgroup.mem_normalizer_iff.mp hY _).mp h2

section Frame

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_sup_eq_top : img148 A Y Y ⊔ img148 A Y A = ⊤ := by
  rw [← YFrame.img_sup le_sup_left le_sup_right]
  rw [img148, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']

theorem exists_of_mem_img {X : Subgroup G} {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hx : x ∈ img148 A Y X) :
    ∃ (g : G) (hg : g ∈ Y ⊔ A), g ∈ X ∧ QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ = x := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, k.2, Subgroup.mem_subgroupOf.mp hk, rfl⟩

theorem mem_pCore_of_mk_eq {g h : G} (hg : g ∈ Y ⊔ A) (hh : h ∈ Y ⊔ A)
    (he : QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ = QuotientGroup.mk' (ker148 A Y) ⟨h, hh⟩) :
    g⁻¹ * h ∈ pPrimeCoreOf 3 Y := by
  have h1 := QuotientGroup.eq.mp he
  have h2 := Subgroup.mem_subgroupOf.mp h1
  simpa using h2

theorem not_three_dvd_card_img148 {X : Subgroup G} (hXK : X ≤ Y ⊔ A) (hX : ¬ 3 ∣ Nat.card X) :
    ¬ 3 ∣ Nat.card (img148 A Y X) := fun h3 => by
  apply hX
  refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]

theorem img_le_centralizer_img {U V : Subgroup G} (hU : U ≤ Y ⊔ A) (hV : V ≤ Y ⊔ A)
    (hUV : U ≤ Subgroup.centralizer (V : Set G)) :
    img148 A Y U ≤ Subgroup.centralizer (img148 A Y V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  have huv : (u : G) * v = v * u :=
    (Subgroup.mem_centralizer_iff.mp (hUV (Subgroup.mem_subgroupOf.mp hu)) v
      (Subgroup.mem_subgroupOf.mp hv)).symm
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext huv.symm

theorem eq_of_mk_eq_of_mem_A (hA3 : IsPGroup 3 A) {g h : G} (hgA : g ∈ A) (hhA : h ∈ A)
    (he : QuotientGroup.mk' (ker148 A Y) ⟨g, le_sup_right (a := Y) hgA⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨h, le_sup_right (a := Y) hhA⟩) : g = h := by
  have hmem := mem_pCore_of_mk_eq _ _ he
  have hk : (⟨g⁻¹ * h, mul_mem (inv_mem (le_sup_right (a := Y) hgA)) (le_sup_right (a := Y) hhA)⟩ :
      ↥(Y ⊔ A)) ∈ ker148 A Y := Subgroup.mem_subgroupOf.mpr hmem
  obtain ⟨m, hm⟩ := hA3 ⟨g⁻¹ * h, mul_mem (inv_mem hgA) hhA⟩
  have h1 := YFrame.eq_one_of_mem_ker hk (m := m)
    (Subtype.ext (by simpa using congrArg Subtype.val hm))
  have h2 : g⁻¹ * h = 1 := by simpa using h1
  exact (inv_mul_eq_one.mp h2)

theorem card_img148_A (hA3 : IsPGroup 3 A) : Nat.card (img148 A Y A) = Nat.card A := by
  have hinj : Function.Injective ((QuotientGroup.mk' (ker148 A Y)).comp
      (Subgroup.inclusion (le_sup_right : A ≤ Y ⊔ A))) := by
    intro x y hxy
    exact Subtype.ext (eq_of_mk_eq_of_mem_A hA3 x.2 y.2 hxy)
  have h1 : img148 A Y A = ((QuotientGroup.mk' (ker148 A Y)).comp
      (Subgroup.inclusion (le_sup_right : A ≤ Y ⊔ A))).range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion le_sup_right a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  rw [h1, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem isElemAbelian_img148 (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    CFSG.Assembly.IsElemAbelian 3 (img148 A Y A) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨g, hg, hgA, hgu⟩ := exists_of_mem_img u.2
    obtain ⟨h, hh, hhA, hhv⟩ := exists_of_mem_img v.2
    apply Subtype.ext
    change (u : ↥(Y ⊔ A) ⧸ ker148 A Y) * v = v * u
    rw [← hgu, ← hhv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * h = h * g
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨g, hgA⟩ ⟨h, hhA⟩)
  · obtain ⟨g, hg, hgA, rfl⟩ := exists_of_mem_img hx
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hA.2 g hgA)
    rw [this, map_one]

theorem eq_bot_of_le_img148 (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {U : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (hUY : U ≤ img148 A Y Y)
    (hYU : img148 A Y Y ≤ Subgroup.normalizer (U : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hU3 : ¬ 3 ∣ Nat.card U) : U = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Uh := YFrame.pbY U Y with hUh
  have hUh3 : ¬ 3 ∣ Nat.card Uh := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Uh) 3 h3
    have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    obtain ⟨hxK, hxU, hxY⟩ := YFrame.mem_pbY.mp x.2
    set k : ↥(Y ⊔ A) := ⟨(x : G), hxK⟩ with hk
    have hk3 : k ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxG, pow_orderOf_eq_one]
    have hq3 : (⟨_, hxU⟩ : U) ^ 3 = 1 := Subtype.ext (by
      change (QuotientGroup.mk' (ker148 A Y) k) ^ 3 = 1
      rw [← map_pow, hk3, map_one])
    have hq1 : QuotientGroup.mk' (ker148 A Y) k = 1 := by
      have hdvd := orderOf_dvd_of_pow_eq_one hq3
      have hcard : orderOf (⟨_, hxU⟩ : U) ∣ Nat.card U := orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · have := orderOf_eq_one_iff.mp h1
        exact congrArg Subtype.val this
      · rw [h1] at hcard
        exact absurd hcard hU3
    have hkN : k ∈ ker148 A Y := (QuotientGroup.eq_one_iff k).mp hq1
    have h1 : (x : G) = 1 := YFrame.eq_one_of_mem_ker hkN (m := 1) (by rw [pow_one]; exact hk3)
    rw [h1, orderOf_one] at hxG
    exact absurd hxG (by norm_num)
  have hYn : ∀ y ∈ Y, ∀ u ∈ Uh, y * u * y⁻¹ ∈ Uh := by
    intro y hy u hu
    obtain ⟨huK, huU, huY⟩ := YFrame.mem_pbY.mp hu
    have hyK : y ∈ Y ⊔ A := le_sup_left (a := Y) hy
    refine YFrame.mem_pbY.mpr ⟨mul_mem (mul_mem hyK huK) (inv_mem hyK), ?_,
      mul_mem (mul_mem hy huY) (inv_mem hy)⟩
    have hyimg : QuotientGroup.mk' (ker148 A Y) ⟨y, hyK⟩ ∈ img148 A Y Y :=
      ⟨⟨y, hyK⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hYU hyimg) _).mp huU
    rw [← map_inv, ← map_mul, ← map_mul] at h
    exact h
  have hUhO : Uh ≤ pPrimeCoreOf 3 Y :=
    Sec15.F153L3C2.le_pPrimeCoreOf_of_normalized inf_le_right hYn
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hUh3)
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨g, hg, hgY, rfl⟩ := exists_of_mem_img (hUY hu)
  have hgUh : g ∈ Uh := YFrame.mem_pbY.mpr ⟨hg, hu, hgY⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hUhO hgUh))

theorem mem_img_A_of_three (hAmax : A ∈ partTwoF G) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hxY : x ∈ img148 A Y Y)
    (hxA : x ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hx3 : orderOf x = 3) : x ∈ img148 A Y A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAmax.1.2 a a.2)⟩
  set O := pPrimeCoreOf 3 Y with hO
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  obtain ⟨y, hyK, hyY, rfl⟩ := exists_of_mem_img hxY
  have hcos : ∀ b ∈ A, y⁻¹ * (b * y * b⁻¹) ∈ O := by
    intro b hb
    have hbK : b ∈ Y ⊔ A := le_sup_right (a := Y) hb
    have hc := Subgroup.mem_centralizer_iff.mp hxA _ (YFrame.mk_mem_img_A hb)
    have hmk : QuotientGroup.mk' (ker148 A Y) ⟨y, hyK⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨b * y * b⁻¹, mul_mem (mul_mem hbK hyK) (inv_mem hbK)⟩ := by
      rw [show (⟨b * y * b⁻¹, mul_mem (mul_mem hbK hyK) (inv_mem hbK)⟩ : ↥(Y ⊔ A)) =
        ⟨b, hbK⟩ * ⟨y, hyK⟩ * (⟨b, hbK⟩ : ↥(Y ⊔ A))⁻¹ from Subtype.ext rfl, map_mul, map_mul,
        map_inv, hc, mul_inv_cancel_right]
    exact mem_pCore_of_mk_eq hyK _ hmk
  obtain ⟨m, hmO, hmC⟩ := Res4L34.exists_mem_centralizer_of_coset hA3 hO3 hAO hcos
  have hmY : m ∈ Y := by
    have h1 : m = y * (y⁻¹ * m) := by group
    rw [h1]
    exact mul_mem hyY (pPrimeCoreOf_le 3 Y hmO)
  have hmK : m ∈ Y ⊔ A := le_sup_left (a := Y) hmY
  have hmx : QuotientGroup.mk' (ker148 A Y) ⟨m, hmK⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨y, hyK⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply Subgroup.mem_subgroupOf.mpr
    have : (((⟨m, hmK⟩ : ↥(Y ⊔ A))⁻¹ * ⟨y, hyK⟩ : ↥(Y ⊔ A)) : G) = (y⁻¹ * m)⁻¹ := by
      simp [mul_inv_rev]
    rw [this]
    exact inv_mem hmO
  set t := Nat.card O with ht
  have ht3 : ¬ 3 ∣ t := hO3
  set m' := m ^ (t * t) with hm'
  have hm'K : m' ∈ Y ⊔ A := pow_mem hmK _
  have hm'C : m' ∈ Subgroup.centralizer (A : Set G) := pow_mem hmC _
  set q := QuotientGroup.mk' (ker148 A Y) with hq
  have hxq3 : (q ⟨y, hyK⟩) ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  have htt : t * t % 3 = 1 := by
    have h1 : t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> simp [Nat.mul_mod, h1]
  have hm'x : q ⟨m', hm'K⟩ = q ⟨y, hyK⟩ := by
    rw [show (⟨m', hm'K⟩ : ↥(Y ⊔ A)) = (⟨m, hmK⟩ : ↥(Y ⊔ A)) ^ (t * t) from Subtype.ext rfl,
      map_pow, hmx, ← Nat.div_add_mod (t * t) 3, htt, pow_add, pow_mul, hxq3, one_pow, one_mul,
      pow_one]
  have hm3 : m ^ 3 ∈ O := by
    have h1 : q ⟨m ^ 3, pow_mem hmK 3⟩ = 1 := by
      rw [show (⟨m ^ 3, pow_mem hmK 3⟩ : ↥(Y ⊔ A)) = (⟨m, hmK⟩ : ↥(Y ⊔ A)) ^ 3 from
        Subtype.ext rfl, map_pow, hmx, hxq3]
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hm'3 : m' ^ 3 = 1 := by
    have h1 : (m ^ 3) ^ t = 1 := by
      have h' := congrArg Subtype.val (pow_card_eq_one' (G := ↥O) (x := ⟨m ^ 3, hm3⟩))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
      exact h'
    rw [hm', ← pow_mul, show t * t * 3 = 3 * t * t by ring, pow_mul, pow_mul, h1, one_pow]
  have hm'A : m' ∈ A :=
    Sec4.mem_of_maximal_of_commute ⟨hAmax.1, fun B hB hAB => (hAmax.2.1 B hB hAB).le⟩ hm'3
      fun a ha => Subgroup.mem_centralizer_iff.mp hm'C a ha
  rw [← hm'x]
  exact ⟨⟨m', hm'K⟩, Subgroup.mem_subgroupOf.mpr hm'A, rfl⟩

theorem commutator_mem_pCore_of_commute {y e : G} (hy : y ∈ Y ⊔ A) (he : e ∈ Y ⊔ A)
    (hc : QuotientGroup.mk' (ker148 A Y) ⟨y, hy⟩ * QuotientGroup.mk' (ker148 A Y) ⟨e, he⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨e, he⟩ * QuotientGroup.mk' (ker148 A Y) ⟨y, hy⟩) :
    ⁅y, e⁆ ∈ pPrimeCoreOf 3 Y := by
  have hmem : ⁅(⟨y, hy⟩ : ↥(Y ⊔ A)), (⟨e, he⟩ : ↥(Y ⊔ A))⁆ ∈ ker148 A Y := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (ker148 A Y) ⁅(⟨y, hy⟩ : ↥(Y ⊔ A)), (⟨e, he⟩ : ↥(Y ⊔ A))⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hc]
    group
  have h := Subgroup.mem_subgroupOf.mp hmem
  simpa [commutatorElement_def] using h

theorem coset_zpowers {T : Subgroup G} {n e : G} (heT : e ∈ Subgroup.normalizer (T : Set G))
    (hn : n⁻¹ * (e * n * e⁻¹) ∈ T) : ∀ b ∈ Subgroup.zpowers e, n⁻¹ * (b * n * b⁻¹) ∈ T := by
  let H : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (T : Set G) ∧ n⁻¹ * (g * n * g⁻¹) ∈ T}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro g h ⟨hgT, hg⟩ ⟨hhT, hh⟩
        refine ⟨mul_mem hgT hhT, ?_⟩
        have e1 : n⁻¹ * (g * h * n * (g * h)⁻¹) =
            (n⁻¹ * (g * n * g⁻¹)) * (g * (n⁻¹ * (h * n * h⁻¹)) * g⁻¹) := by group
        rw [e1]
        exact mul_mem hg ((Subgroup.mem_normalizer_iff.mp hgT _).mp hh)
      inv_mem' := by
        rintro g ⟨hgT, hg⟩
        refine ⟨inv_mem hgT, ?_⟩
        have e1 : n⁻¹ * (g⁻¹ * n * g⁻¹⁻¹) = g⁻¹ * (n⁻¹ * (g * n * g⁻¹))⁻¹ * g⁻¹⁻¹ := by group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem hgT) _).mp (inv_mem hg) }
  have hZ : Subgroup.zpowers e ≤ H := Subgroup.zpowers_le.mpr ⟨heT, hn⟩
  exact fun b hb => (hZ hb).2

theorem img_inf_centralizer_eq_bot (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {S D : Subgroup G}
    (hSY : S ≤ Y) (hAS : A ≤ Subgroup.normalizer (S : Set G)) {e : G} (heA : e ∈ A)
    (he3 : IsPGroup 3 (Subgroup.zpowers e))
    (hSD : S ⊓ Subgroup.centralizer ({e} : Set G) ≤ D) (hDK : D ≤ Y ⊔ A)
    (hDbot : img148 A Y D = ⊥) :
    img148 A Y S ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (ker148 A Y) ⟨e, le_sup_right (a := Y) heA⟩} :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxC⟩
  obtain ⟨s, hsK, hsS, rfl⟩ := exists_of_mem_img hxS
  set T' := S ⊓ pPrimeCoreOf 3 Y with hT'
  have hT'3 : ¬ 3 ∣ Nat.card T' := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
      (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have heK : e ∈ Y ⊔ A := le_sup_right (a := Y) heA
  have heT' : e ∈ Subgroup.normalizer (T' : Set G) :=
    Late.le_normalizer_inf hAS (hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)) heA
  have hes : e * s * e⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS heA) s).mp hsS
  have hesK : e * s * e⁻¹ ∈ Y ⊔ A := mul_mem (mul_mem heK hsK) (inv_mem heK)
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hmk : QuotientGroup.mk' (ker148 A Y) ⟨s, hsK⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨e * s * e⁻¹, hesK⟩ := by
    rw [show (⟨e * s * e⁻¹, hesK⟩ : ↥(Y ⊔ A)) = ⟨e, heK⟩ * ⟨s, hsK⟩ * (⟨e, heK⟩ : ↥(Y ⊔ A))⁻¹ from
      Subtype.ext rfl, map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right]
  have hcos : s⁻¹ * (e * s * e⁻¹) ∈ T' :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hsS) hes, mem_pCore_of_mk_eq hsK hesK hmk⟩
  obtain ⟨m, hmT, hmC⟩ := Res4L34.exists_mem_centralizer_of_coset he3 hT'3
    (Subgroup.zpowers_le.mpr heT') (coset_zpowers heT' hcos)
  have hmS : m ∈ S := by
    have h1 : m = s * (s⁻¹ * m) := by group
    rw [h1]
    exact mul_mem hsS (Subgroup.mem_inf.mp hmT).1
  have hmCe : m ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers e)) hmC
  have hmD : m ∈ D := hSD (Subgroup.mem_inf.mpr ⟨hmS, hmCe⟩)
  have hmK : m ∈ Y ⊔ A := hDK hmD
  have hmx : QuotientGroup.mk' (ker148 A Y) ⟨s, hsK⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨m, hmK⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hmT).2
  have h1 : QuotientGroup.mk' (ker148 A Y) ⟨m, hmK⟩ ∈ img148 A Y D :=
    ⟨⟨m, hmK⟩, Subgroup.mem_subgroupOf.mpr hmD, rfl⟩
  rw [hDbot] at h1
  rw [hmx]
  exact h1

end Frame

theorem commutator_zpowers_le_of_dec {A Y : Subgroup G} (hA : Late.IsE27 A)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYΔ : Y = delta A (lB A) Y) {e : G} (heA : e ∈ A) {D : Subgroup G}
    (hdec : deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔ D)
    (hDe : D ≤ Subgroup.centralizer ({e} : Set G)) :
    ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, -, h3⟩ := rank3II_14_5_lB hA hbot hAY
  set X0 := deltaZero A (lB A) Y with hX0
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hR
  have hYX0 : Y ≤ Subgroup.normalizer (X0 : Set G) := by
    have h := h3
    rw [← hYΔ] at h
    exact h
  have hX0Y : X0 ≤ Y := deltaZero_le Y
  have hnorm : (X0.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX0Y).mpr hYX0
  have hOO : pPrimeCoreOf 3 X0 ≤ pPrimeCoreOf 3 Y :=
    CFSG.GH74.GLS.pPrimeCoreOf_le_of_normal 3 hX0Y hnorm
  have hDY : D ≤ Y := (le_sup_right.trans hdec.symm.le).trans hX0Y
  have hYeq : Y = pPrimeCoreOf 3 Y ⊔ (D ⊔ R) := by
    refine le_antisymm ?_ (sup_le (pPrimeCoreOf_le 3 Y) (sup_le hDY inf_le_right))
    calc Y = X0 ⊔ R := hYΔ.trans h1
      _ = pPrimeCoreOf 3 X0 ⊔ D ⊔ R := by rw [← hdec]
      _ ≤ pPrimeCoreOf 3 Y ⊔ (D ⊔ R) := by
        rw [sup_assoc]
        exact sup_le_sup_right hOO _
  have hDR : D ⊔ R ≤ Subgroup.centralizer ({e} : Set G) := by
    refine sup_le hDe (inf_le_left.trans ((pPrimeCoreOf_le 3 _).trans ?_))
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA)
  exact commutator_zpowers_le_of_eq_sup hYeq
    ((normalizer_le_normalizer_pPrimeCoreOf 3 Y) (hAY heA)) hDR

end Wales1411W

open Wales1411W in
theorem claim1411HJConfCoreR_of_kfact
    (h148 : Item148R) (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hbot : Item145BotS14) (hKF : KS1411HJCore) : Claim1411HJConfCoreR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT ha hΔ
    hYST hker
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYa := hres a haA ha1 haS haT
  have hA : Late.IsE27 A := hR.isE27
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2)⟩
  have hbot' := hbot G A c L hR.toSec14Std
  have h143a : Ronan148Q.Item143QAt A (lB A) a := h143 G A c L hR.toSec14Std a haA ha1 ha
  have hYK : Y ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := by
    rw [hYΔ]
    exact delta_mono hYa
  have hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) →
      ¬ 3 ∣ Nat.card Z → Z ∈ scriptQ A (lB A) :=
    fun Z hZY hAZ hZ3 => mem_scriptQ_of_le_delta h143a hYK hZY hAZ hZ3
  have hHJ : AllPointsHJ A := allPointsHJ_of_hjConf h134 h48 hR.toSec14Std h143a hΔ
  letI : (ker148 A Y).Normal := ker148_normal hY.2
  have hSα := YFrame.maximal_img hA3 hY.2 hQY hS
  have hTα := YFrame.maximal_img hA3 hY.2 hQY hT
  have hYimg : img148 A Y Y = img148 A Y S ⊔ img148 A Y T :=
    (congrArg (img148 A Y) hYST.symm).trans
      (YFrame.img_sup (hS.prop.1.2.trans le_sup_left) (hT.prop.1.2.trans le_sup_left))
  obtain ⟨h145a, h145b, h145c⟩ := rank3II_14_5_lB hA hbot' hY.2
  have hAX0 : A ≤ Subgroup.normalizer ((deltaZero A (lB A) Y : Subgroup G) : Set G) := by
    rw [h145b, ← hYΔ]
    exact Wales1411W.le_normalizer_commutator hY.2
  set X0 := deltaZero A (lB A) Y with hX0
  set R := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hR'
  have hYeq : Y = X0 ⊔ R := hYΔ.trans h145a
  have hYX0 : Y ≤ Subgroup.normalizer (X0 : Set G) := by
    have h := h145c
    rw [← hYΔ] at h
    exact h
  have hX0Y : X0 ≤ Y := deltaZero_le Y
  have hRY : R ≤ Y := inf_le_right
  have hRA : R ≤ Subgroup.centralizer (A : Set G) := inf_le_left.trans (pPrimeCoreOf_le 3 _)
  have hR3 : ¬ 3 ∣ Nat.card R := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hfin : HJCoreType (img148 A Y X0) → IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
    intro htype
    have haK : a ∈ Y ⊔ A := le_sup_right (a := Y) haA
    set abar := QuotientGroup.mk' (ker148 A Y) ⟨a, haK⟩ with habar
    have hset : HJCoreSetting (img148 A Y Y) (img148 A Y A) (img148 A Y X0) (img148 A Y R) abar :=
      { le_normalizer_Y := YFrame.img_le_normalizer_img hY.2
        sup_eq_top := img148_sup_eq_top
        le_normalizer_X := sup_le (YFrame.img_le_normalizer_img hYX0)
          (YFrame.img_le_normalizer_img hAX0)
        le_Y := Subgroup.map_mono (Subgroup.comap_mono hX0Y)
        eq_sup := (congrArg (img148 A Y) hYeq).trans
          (YFrame.img_sup (hX0Y.trans le_sup_left) (hRY.trans le_sup_left))
        le_centralizer_R := img_le_centralizer_img (hRY.trans le_sup_left) le_sup_right hRA
        not_three_dvd_R := not_three_dvd_card_img148 (hRY.trans le_sup_left) hR3
        isElemAbelian := isElemAbelian_img148 hA.1
        card_A := (card_img148_A hA3).trans hA.2
        mem_A := YFrame.mk_mem_img_A haA
        ne_one := by
          intro h1
          apply ha1
          have h1' : QuotientGroup.mk' (ker148 A Y) ⟨a, haK⟩ =
              QuotientGroup.mk' (ker148 A Y) ⟨1, le_sup_right (a := Y) (one_mem A)⟩ := by
            rw [← habar, h1]
            exact (map_one _).symm
          exact eq_of_mk_eq_of_mem_A hA3 haA (one_mem A) h1'
        le_centralizer_a := by
          intro x hx
          obtain ⟨y, hyK, hyY, rfl⟩ := exists_of_mem_img hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hYa hyY)
          rw [habar, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hya
        mem_zpowers := by
          intro e' he' hYe'
          obtain ⟨e, heK, heA, rfl⟩ := exists_of_mem_img he'
          have hcomm : ∀ y ∈ Y, ⁅y, e⁆ ∈ pPrimeCoreOf 3 Y := by
            intro y hy
            have hyK : y ∈ Y ⊔ A := le_sup_left (a := Y) hy
            have hc := Subgroup.mem_centralizer_singleton_iff.mp
              (hYe' ⟨⟨y, hyK⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
            exact commutator_mem_pCore_of_commute hyK heK hc
          have hle := commutator_zpowers_le
            ((normalizer_le_normalizer_pPrimeCoreOf 3 Y) (hY.2 heA)) hcomm
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hker e heA hle)
          refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
          rw [habar, ← map_zpow]
          congr 1
          apply Subtype.ext
          simpa using hk
        mem_A_of_three := fun x hxY hxA hx3 =>
          mem_img_A_of_three hR.mem_partTwoF hY.2 hxY hxA hx3
        eq_bot_of_three := fun U hUY hYU hU3 => eq_bot_of_le_img148 hY.2 hUY hYU hU3
        perfect := Sec15.Read148Perf.isPerfect_img148 hR.toSec14Std (h148 G A c L hR) hY }
    have hSY : S ≤ Y := hS.prop.1.2
    have hTY : T ≤ Y := hT.prop.1.2
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.prop.1.1.1.2.2
    have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
    have hSTK : S ⊓ T ≤ Y ⊔ A := (inf_le_left.trans hSY).trans le_sup_left
    have hDbot : img148 A Y (S ⊓ T) = ⊥ :=
      eq_bot_of_le_img148 hY.2 (Subgroup.map_mono (Subgroup.comap_mono (inf_le_left.trans hSY)))
        (YFrame.img_le_normalizer_img hD)
        (not_three_dvd_card_img148 hSTK
          (not_three_dvd_card_of_isPGroup (hS2.to_le inf_le_left)))
    have hsupp : ∀ e' ∈ img148 A Y A, ¬ img148 A Y Y ≤ Subgroup.centralizer ({e'} : Set _) →
        img148 A Y S ⊓ Subgroup.centralizer ({e'} : Set _) = ⊥ ∨
          img148 A Y T ⊓ Subgroup.centralizer ({e'} : Set _) = ⊥ := by
      intro e' he' hne
      obtain ⟨e, heK, heA, rfl⟩ := exists_of_mem_img he'
      have he3 : IsPGroup 3 (Subgroup.zpowers e) := hA3.to_le (Subgroup.zpowers_le.mpr heA)
      have hYe : ¬ Y ≤ Subgroup.centralizer ({e} : Set G) := by
        intro h
        apply hne
        intro x hx
        obtain ⟨y, hyK, hyY, rfl⟩ := exists_of_mem_img hx
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h hyY))
      have he1 : e ≠ 1 := by
        rintro rfl
        exact hYe fun y _ => by simp [Subgroup.mem_centralizer_singleton_iff]
      by_cases hSe : S ⊓ Subgroup.centralizer {e} ≤ S ⊓ T
      · exact Or.inl (img_inf_centralizer_eq_bot hY.2 hSY hAS heA he3 hSe hSTK hDbot)
      · by_cases hTe : T ⊓ Subgroup.centralizer {e} ≤ S ⊓ T
        · exact Or.inr (img_inf_centralizer_eq_bot hY.2 hTY hAT heA he3 hTe hSTK hDbot)
        · exact (hYe (hres e heA he1 hSe hTe)).elim
    obtain ⟨ñ, hñ, hñT⟩ := hKF _ _ _ _ _ _ hset htype _ _ hSα hTα hYimg.symm hsupp
    exact YFrame.isConjIn_of_img_conj hA hbot' hY.2 hQY hS hT hñ hñT
  obtain ⟨-, hcases⟩ := h148 G A c L hR Y hY
  rcases hcases with h1 | ⟨c', hc', hdec, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, h3t⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', -, L', n, m, hc', hL', -, -, -, -, -, -, hε, -⟩ |
      ⟨h6, -⟩ | ⟨a₁, -, L₁, -, -, -, p₁, f₁, e₁, -, -, -, _, -, ha₁, -, hL₁, -, -, -, -, -, -, -,
        -, -, -, -, -, hiso₁, -⟩
  ·
    exfalso
    have hle : Y ≤ pPrimeCoreOf 3 Y ⊔ R := hYeq.le.trans (sup_le_sup_right h1 _)
    have hRO : R ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
      hRY.trans (le_normalizer_pPrimeCoreOf 3 Y)
    have hcard := Sec15.not_three_dvd_card_sup hRO
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)) hR3
    exact hcard (h3.trans (Subgroup.card_dvd_of_le hle))
  ·
    exfalso
    obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc'o : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
    have hDc : deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ≤
        Subgroup.centralizer ({c'} : Set G) :=
      sSup_le fun Q hQ => le_centralizer_of_mem_invariantPiSubgroups hc'A hc'o
        ⟨hQ.2.trans inf_le_right, hQ.1.1.1.2.1, hQ.1.1.1.2.2⟩
    have htriv := commutator_zpowers_le_of_dec hA hbot' hY.2 hYΔ hc'A hdec hDc
    have hc'a := hker c' hc'A htriv
    have hle : Subgroup.zpowers c' ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hc'a
    have ha3 : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hA.1.2 a haA) ha1
    have heq : Subgroup.zpowers c' = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [ha3, hc'3])
    exact ha (heq ▸ hc')
  ·
    rcases h3t with h | h | h | h | h | h
    · exact hfin (Or.inl h)
    · exact hfin (Or.inr (Or.inl h))
    · exact hfin (Or.inr (Or.inr (Or.inl h)))
    · exact hfin (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  ·
    obtain ⟨φJ⟩ := Wales154.quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    exact (KFacts.KS14.ks17J2NotList.2.1.false (φJ.symm.trans φ7)).elim
  ·
    obtain ⟨φJ⟩ := Wales154.quot_j2_of_allPointsHJ hR.toSec14Std hHJ hc' hL'
    exact (KFacts.KS14.not_isLThreeEpsAt_j2 2 (n * m) (Sec15.IsLThreeEpsAt.of_mulEquiv φJ hε)).elim
  ·
    exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))))
  ·
    obtain ⟨φJ⟩ := Wales154.quot_j2_of_allPointsHJ hR.toSec14Std hHJ ha₁ hL₁
    have hJ : Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 p₁ (f₁ * e₁) := by
      rcases hiso₁ with ⟨h3, ⟨ψ⟩⟩ | ⟨h3, ⟨ψ⟩⟩
      · exact Or.inl ⟨h3, ⟨φJ.symm.trans ψ⟩⟩
      · exact Or.inr ⟨h3, ⟨φJ.symm.trans ψ⟩⟩
    exact (KFacts.KS14.ks17J2NotList.1 p₁ (f₁ * e₁) hJ).elim

end CFSG.RankThree.PartTwo.Sec14
