module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesModel
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Item148PtRes2 Res5Types
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Base142 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  std : Sec14Std G A c L
  eq_k : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  cent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
    ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L
  le_k : ∀ V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
    (piCompl 3), V ≤ k142 A (lB A) c

namespace Base142

variable {A L : Subgroup G} {c : G} (d : Base142 A c L)
include d

theorem l_le : L ≤ k142 A (lB A) c := by
  rw [d.eq_k]
  exact le_sup_left.trans le_sup_left

theorem o'_le : pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
    k142 A (lB A) c := by
  rw [d.eq_k]
  exact le_sup_right.trans le_sup_left

theorem o''_le : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ k142 A (lB A) c := by
  rw [d.eq_k]
  exact le_sup_right

theorem k_le_centralizer : k142 A (lB A) c ≤ Subgroup.centralizer ({c} : Set G) := by
  have hD := d.std.toSec13Data
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hRc := le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq
    (sup_mem_invariantPiSubgroups hD.mem_A hAab)
  rw [d.eq_k, sup_assoc]
  exact sup_le hD.le_centralizer hRc

theorem k_le_normalizer : k142 A (lB A) c ≤ Subgroup.normalizer (L : Set G) := by
  have hD := d.std.toSec13Data
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (d.std.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).1
  exact d.k_le_centralizer.trans (centralizer_le_normalizer_of_three_dvd d.std h3L)

theorem theta_le : inSubgroup (aschbacherSolvableCore 3) L ≤ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    Sec4.aschbacherSolvableCore_characteristic _
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  refine le_pPrimeCoreOf ((Subgroup.map_subtype_le _).trans d.l_le)
    (d.k_le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
  rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3

theorem sup_le_pCore :
    pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      pPrimeCoreOf 3 (k142 A (lB A) c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O' := pPrimeCoreOf 3 H with hO'
  set O'' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO''
  set OK := pPrimeCoreOf 3 K with hOK
  have hKH : K ≤ H := delta_le _
  have hO'K : O' ≤ K := d.o'_le
  have hO''K : O'' ≤ K := d.o''_le
  have hπ : ∀ X : Subgroup G, Nat.Coprime 3 (Nat.card (pPrimeCoreOf 3 X)) := fun X =>
    coprime_card_pPrimeCoreOf 3 X
  have h1 : O' ≤ OK :=
    le_pPrimeCoreOf hO'K (hKH.trans (le_normalizer_pPrimeCoreOf 3 H)) (hπ H)
  have hKOK : K ≤ Subgroup.normalizer (OK : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hO''N : O'' ≤ Subgroup.normalizer (OK : Set G) := hO''K.trans hKOK
  set M := O'' ⊔ OK with hM
  have hMK : M ≤ K := sup_le hO''K (pPrimeCoreOf_le 3 K)
  have hM3 : IsPiSubgroup (piCompl 3) M := by
    refine isPiSubgroup_piCompl_sup ?_ ?_ hO''N
    · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hπ _))
    · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hπ _))
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have hle : M ≤ M.comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun r hr => ?_) (fun o ho => ?_)
      · show l * r * l⁻¹ ∈ M
        have hc := d.cent r⁻¹ (inv_mem hr) l hl
        have hθ := d.theta_le hc
        rw [show l * r * l⁻¹ = r * ⁅r⁻¹, l⁆ by
          rw [commutatorElement_def]; group]
        exact mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hθ)
      · show l * o * l⁻¹ ∈ M
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (hKOK (d.l_le hl)) o).mp ho)
    exact hle hm
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := by
    rw [hKdef, d.eq_k]
    refine sup_le (sup_le hLM ?_) ?_
    · exact h1.trans (le_sup_right.trans Subgroup.le_normalizer)
    · exact le_sup_left.trans Subgroup.le_normalizer
  have h2 : M ≤ OK := le_pPrimeCoreOf hMK hKM
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three M).mp hM3))
  exact sup_le h1 (le_sup_left.trans h2)

theorem eq_l_sup : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  refine le_antisymm ?_ (sup_le d.l_le (pPrimeCoreOf_le 3 _))
  conv_lhs => rw [d.eq_k]
  rw [sup_assoc]
  exact sup_le_sup_left d.sup_le_pCore L

theorem l_le_kA : L ≤ kA142 A (lB A) c := d.l_le.trans le_sup_left

theorem zpow_eq_one_of_mem {i : ℤ} (hci : c ^ i ∈ k142 A (lB A) c) : c ^ i = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := d.std.toSec13Data
  have hci' := hci
  rw [d.eq_l_sup] at hci'
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hOK3 : ¬ 3 ∣ Nat.card OK :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hLOK : L ≤ Subgroup.normalizer (OK : Set G) :=
    d.l_le.trans (le_normalizer_pPrimeCoreOf 3 K)
  have hOKc : OK ≤ Subgroup.centralizer ({c} : Set G) :=
    (pPrimeCoreOf_le 3 K).trans d.k_le_centralizer
  have hx : c ^ i ∈ (L : Set G) * (OK : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L OK hLOK]
    exact hci'
  obtain ⟨l, hl, o, ho, hlo⟩ := hx
  have hl' : (⟨l, hl⟩ : ↥L) ∈ (OK ⊔ Subgroup.zpowers c).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    change l ∈ OK ⊔ Subgroup.zpowers c
    rw [show l = c ^ i * o⁻¹ by rw [← hlo]; group]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c i))
      (Subgroup.mem_sup_left (inv_mem ho))
  have hlθ := inf_le_theta Sec13.sporadicModels131 d.std hOK3 hLOK hOKc hl'
  have hlOK : l ∈ OK := d.theta_le ⟨⟨l, hl⟩, hlθ, rfl⟩
  have hcOK : c ^ i ∈ OK := hlo ▸ mul_mem hlOK ho
  by_contra hne
  have h3 : (c ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show c ^ 3 = 1 from (orderOf_eq_iff (by norm_num)).mp hD.orderOf_eq |>.1, one_zpow]
  have ho3 : orderOf (c ^ i) = 3 := orderOf_eq_prime h3 hne
  exact hOK3 (ho3 ▸ Subgroup.orderOf_dvd_natCard OK hcOK)

theorem mem_pCore_of_mem {k : G} (hk : k ∈ k142 A (lB A) c)
    (hker : k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c) :
    k ∈ pPrimeCoreOf 3 (k142 A (lB A) c) := by
  set K := k142 A (lB A) c with hKdef
  set OK := pPrimeCoreOf 3 K with hOK
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (OK : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun o ho => ?_
    have hoc : Commute o c :=
      Subgroup.mem_centralizer_singleton_iff.mp ((pPrimeCoreOf_le 3 K).trans
        d.k_le_centralizer ho)
    rw [hoc.symm.eq, mul_inv_cancel_right]
    exact ho
  have hx : k ∈ (OK : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OK _ hcN]
    exact hker
  obtain ⟨o, ho, z, hz, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hzK : c ^ i ∈ K := by
    rw [show c ^ i = o⁻¹ * (o * c ^ i) by group]
    exact mul_mem (inv_mem (pPrimeCoreOf_le 3 K ho)) hk
  rw [d.zpow_eq_one_of_mem hzK]
  simpa using ho

end Base142

namespace Base142

variable {A L : Subgroup G} {c : G} (d : Base142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem img_k : img142 A (lB A) c (k142 A (lB A) c) = img142 A (lB A) c L := by
  conv_lhs => rw [d.eq_l_sup]
  exact img_sup_pCore d.l_le_kA

theorem ker_toKα : (toKα d.l_le_kA).ker = aschbacherSolvableCore 3 ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (k142 A (lB A) c)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  ext l
  rw [MonoidHom.mem_ker, toKα, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ker142, Subgroup.mem_subgroupOf]
  change (l : G) ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c ↔ _
  constructor
  · intro hl
    exact inf_le_theta Sec13.sporadicModels131 d.std hO3
      (d.l_le.trans (le_normalizer_pPrimeCoreOf 3 _))
      ((pPrimeCoreOf_le 3 _).trans d.k_le_centralizer) (Subgroup.mem_subgroupOf.mpr hl)
  · intro hl
    exact Subgroup.mem_sup_left (d.theta_le ⟨l, hl, rfl⟩)

@[expose] noncomputable def lbarEquiv :
    (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥(img142 A (lB A) c L) :=
  (QuotientGroup.quotientMulEquivOfEq d.ker_toKα).symm.trans
    ((QuotientGroup.quotientKerEquivRange (toKα d.l_le_kA)).trans
      (MulEquiv.subgroupCongr (range_toKα d.l_le_kA)))

theorem lbarEquiv_mk (l : ↥L) :
    ((d.lbarEquiv (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l) :
        ↥(img142 A (lB A) c L)) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) =
      QuotientGroup.mk' (ker142 A (lB A) c) (Subgroup.inclusion d.l_le_kA l) :=
  rfl

@[expose] noncomputable def bar (W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :
    Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (W.subgroupOf (img142 A (lB A) c L)).map d.lbarEquiv.symm.toMonoidHom

theorem card_bar {W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hW : W ≤ img142 A (lB A) c L) : Nat.card (d.bar W) = Nat.card W := by
  rw [bar, Subgroup.card_map_of_injective d.lbarEquiv.symm.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv]

theorem bar_injective {W₁ W₂ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (h₁ : W₁ ≤ img142 A (lB A) c L) (h₂ : W₂ ≤ img142 A (lB A) c L)
    (h : d.bar W₁ = d.bar W₂) : W₁ = W₂ := by
  have h' := Subgroup.map_injective d.lbarEquiv.symm.injective h
  rw [← Subgroup.map_subgroupOf_eq_of_le h₁, ← Subgroup.map_subgroupOf_eq_of_le h₂, h']

theorem le_of_bar_le {W₁ W₂ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (h₁ : W₁ ≤ img142 A (lB A) c L) (h : d.bar W₁ ≤ d.bar W₂) : W₁ ≤ W₂ := by
  intro x hx
  have hx' : d.lbarEquiv.symm ⟨x, h₁ hx⟩ ∈ d.bar W₁ :=
    ⟨⟨x, h₁ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h hx'
  have hyx' : y = ⟨x, h₁ hx⟩ := d.lbarEquiv.symm.injective hyx
  rw [hyx'] at hy
  exact Subgroup.mem_subgroupOf.mp hy

theorem nonempty_bar_equiv {W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hW : W ≤ img142 A (lB A) c L) : Nonempty (↥W ≃* ↥(d.bar W)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hW).symm.trans
    ((W.subgroupOf (img142 A (lB A) c L)).equivMapOfInjective d.lbarEquiv.symm.toMonoidHom
      d.lbarEquiv.symm.injective)⟩

end Base142

@[expose] noncomputable def sigmaOf (L : Subgroup G) {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, haN⟩)

@[expose] noncomputable def fixA (A L : Subgroup G) :
    Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) where
  carrier := {z | ∀ σ ∈ Sec4.autThetaQuot A L, σ z = z}
  mul_mem' := fun {x y} hx hy σ hσ => by rw [map_mul, hx σ hσ, hy σ hσ]
  one_mem' := fun σ _ => map_one σ
  inv_mem' := fun {x} hx σ hσ => by rw [map_inv, hx σ hσ]

namespace Base142

variable {A L : Subgroup G} {c : G} (d : Base142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem lbarEquiv_act {a : G} (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (z : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :
    ((d.lbarEquiv (sigmaOf L haN z) : ↥(img142 A (lB A) c L)) :
        ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) =
      alpha142 A (lB A) c a ha * (d.lbarEquiv z : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) *
        (alpha142 A (lB A) c a ha)⁻¹ := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    have e1 : sigmaOf L haN (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (L.normalizerMonoidHom ⟨a, haN⟩ l) :=
      Sec4.thetaQuotMulAut_mk _ l
    have e2 : (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l := rfl
    rw [e1, d.lbarEquiv_mk, e2, d.lbarEquiv_mk, alpha142, ← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem sigmaOf_eq_one_of_alpha {a : G} (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (h1 : alpha142 A (lB A) c a ha = 1) : sigmaOf L haN = 1 := by
  ext z
  apply d.lbarEquiv.injective
  apply Subtype.ext
  rw [d.lbarEquiv_act ha haN, h1, one_mul, inv_one, mul_one, MulAut.one_apply]

theorem maximal_bar' {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    img142 A (lB A) c Q ≤ img142 A (lB A) c L ∧ ¬ 3 ∣ Nat.card (d.bar (img142 A (lB A) c Q)) ∧
      (∀ σ ∈ Sec4.autThetaQuot A L,
        (d.bar (img142 A (lB A) c Q)).map σ.toMonoidHom ≤ d.bar (img142 A (lB A) c Q)) ∧
      ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
        (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
        d.bar (img142 A (lB A) c Q) ≤ Y → Y = d.bar (img142 A (lB A) c Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set KA := kA142 A (lB A) c with hKAdef
  set N := ker142 A (lB A) c with hN
  set πα := QuotientGroup.mk' N with hπα
  set Lα := img142 A (lB A) c L with hLα
  have hQK : Q ≤ K := d.le_k Q hQ.prop
  have hQKA : Q ≤ KA := hQK.trans le_sup_left
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.prop.2.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hQL : img142 A (lB A) c Q ≤ Lα := by
    rw [hLα, ← d.img_k]
    exact Subgroup.map_mono (Subgroup.comap_mono hQK)
  have hQb3 : ¬ 3 ∣ Nat.card (d.bar (img142 A (lB A) c Q)) := by
    rw [d.card_bar hQL]
    intro h3
    apply hQ3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQKA).toEquiv]
  have hαQ : ∀ (a : G) (ha : a ∈ A), ∀ x ∈ img142 A (lB A) c Q,
      alpha142 A (lB A) c a ha * x * (alpha142 A (lB A) c a ha)⁻¹ ∈ img142 A (lB A) c Q := by
    intro a ha x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' := Subgroup.mem_subgroupOf.mp hk
    have hm : a * (k : G) * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hAQ ha) _).mp hk'
    refine ⟨⟨a, Subgroup.mem_sup_right ha⟩ * k * ⟨a, Subgroup.mem_sup_right ha⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr hm, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hinv : ∀ σ ∈ Sec4.autThetaQuot A L,
      (d.bar (img142 A (lB A) c Q)).map σ.toMonoidHom ≤ d.bar (img142 A (lB A) c Q) := by
    intro σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' := Subgroup.mem_subgroupOf.mp hw
    set z := d.lbarEquiv.symm w with hz
    have hzw : d.lbarEquiv z = w := by rw [hz, MulEquiv.apply_symm_apply]
    have hact := d.lbarEquiv_act haA haN z
    rw [hzw] at hact
    have hmem : ((d.lbarEquiv (sigmaOf L haN z) : ↥Lα) : ↥KA ⧸ N) ∈ img142 A (lB A) c Q := by
      rw [hact]
      exact hαQ a haA _ hw'
    refine ⟨d.lbarEquiv (sigmaOf L haN z), Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨hQL, hQb3, hinv, fun Y hY3 hYinv hQY => ?_⟩
  set Yt : Subgroup (↥KA ⧸ N) := (Y.map d.lbarEquiv.toMonoidHom).map Lα.subtype with hYt
  have hYtL : Yt ≤ Lα := Subgroup.map_subtype_le _
  have hbarYt : d.bar Yt = Y := by
    rw [bar, hYt, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _), Subgroup.map_map]
    ext y
    simp
  have hQYt : img142 A (lB A) c Q ≤ Yt := d.le_of_bar_le hQL (hbarYt ▸ hQY)
  have hαYt : ∀ (a : G) (ha : a ∈ A), ∀ y ∈ Yt,
      alpha142 A (lB A) c a ha * y * (alpha142 A (lB A) c a ha)⁻¹ ∈ Yt := by
    intro a ha y hy
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hy
    have haN : a ∈ Subgroup.normalizer (L : Set G) := d.std.toSec13Data.le_normalizer ha
    have hσ : sigmaOf L haN ∈ Sec4.autThetaQuot A L :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨a, haN, ha, rfl⟩
    have hwY : sigmaOf L haN w ∈ Y := hYinv _ hσ ⟨w, hw, rfl⟩
    refine ⟨d.lbarEquiv (sigmaOf L haN w), ⟨_, hwY, rfl⟩, ?_⟩
    change ((d.lbarEquiv (sigmaOf L haN w) : ↥Lα) : ↥KA ⧸ N) = _
    rw [d.lbarEquiv_act ha haN]
    rfl
  set Yh : Subgroup G := (Yt.comap πα).map KA.subtype ⊓ K with hYh
  have hYhK : Yh ≤ K := inf_le_right
  have hYhKA : Yh ≤ KA := hYhK.trans le_sup_left
  have hmemYh : ∀ {g : G} (hg : g ∈ KA), g ∈ K → πα ⟨g, hg⟩ ∈ Yt → g ∈ Yh := by
    intro g hg hgK hgY
    exact ⟨⟨⟨g, hg⟩, hgY, rfl⟩, hgK⟩
  have hYhmem : ∀ {g : G} (hg : g ∈ Yh), πα ⟨g, hYhKA hg⟩ ∈ Yt := by
    intro g hg
    obtain ⟨⟨x, hx, rfl⟩, -⟩ := hg
    exact hx
  have hQYh : Q ≤ Yh := fun q hq =>
    hmemYh (hQKA hq) (hQK hq) (hQYt ⟨⟨q, hQKA hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩)
  have hAYh : A ≤ Subgroup.normalizer (Yh : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have haKA : a ∈ KA := (le_sup_right : A ≤ KA) ha
    have hy' := hYhmem hy
    have h1 := hαYt a ha _ hy'
    have e : alpha142 A (lB A) c a ha * πα ⟨y, hYhKA hy⟩ * (alpha142 A (lB A) c a ha)⁻¹ =
        πα ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp
          ((le_sup_right : A ≤ KA).trans Subgroup.le_normalizer ha) y).mp (hYhKA hy)⟩ := by
      rw [alpha142, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e] at h1
    exact hmemYh _ ((Subgroup.mem_normalizer_iff.mp (hAK ha) y).mp (hYhK hy)) h1
  have hYh3 : ¬ 3 ∣ Nat.card Yh := by
    set f : ↥Yh →* ↥KA ⧸ N := πα.comp (Subgroup.inclusion hYhKA) with hf
    have hcard : Nat.card Yh = Nat.card f.range * Nat.card f.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    have hrange : f.range ≤ Yt := by
      rintro _ ⟨y, rfl⟩
      exact hYhmem y.2
    have hYt3 : ¬ 3 ∣ Nat.card Yt := by
      rw [hYt, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        Subgroup.card_map_of_injective d.lbarEquiv.injective]
      exact hY3
    have hkerO : f.ker.map Yh.subtype ≤ pPrimeCoreOf 3 K := by
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπα,
        QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hN, ker142, Subgroup.mem_subgroupOf] at hy
      exact d.mem_pCore_of_mem (hYhK y.2) hy
    have hker3 : ¬ 3 ∣ Nat.card f.ker := by
      intro h3
      have h1 := Subgroup.card_dvd_of_le hkerO
      rw [Subgroup.card_map_of_injective Yh.subtype_injective] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
        (h3.trans h1)
    rw [hcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hYt3 (h.trans (Subgroup.card_dvd_of_le hrange))
    · exact hker3 h
  have hYhmemI : Yh ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hYhK.trans (delta_le _), (isPiSubgroup_piCompl_iff Nat.prime_three Yh).mpr hYh3, hAYh⟩
  have hYhQ : Yh ≤ Q := hQ.2 hYhmemI hQYh
  have hYtQ : Yt ≤ img142 A (lB A) c Q := by
    intro z hz
    have hzL := hYtL hz
    rw [hLα, ← d.img_k] at hzL
    obtain ⟨k, hk, rfl⟩ := hzL
    have hkK : ((k : ↥KA) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hkY : ((k : ↥KA) : G) ∈ Yh := hmemYh k.2 hkK hz
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (hYhQ hkY), rfl⟩
  rw [← hbarYt, le_antisymm hYtQ hQYt]

theorem thetaC_bar' {a : G} (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)) :
    thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ≤ img142 A (lB A) c L ∧
      d.bar (thetaC142 A (lB A) c (alpha142 A (lB A) c a ha)) =
        inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN)) := by
  set Lα := img142 A (lB A) c L with hLα
  set x := alpha142 A (lB A) c a ha with hx
  set ψ := d.lbarEquiv with hψ
  set C' : Subgroup ↥Lα := (Res5Types.fixSubgroup (sigmaOf L haN)).map ψ.toMonoidHom with hC'
  have hW : Lα ⊓ Subgroup.centralizer ({x} : Set _) = C'.map Lα.subtype := by
    ext w
    constructor
    · rintro ⟨hwL, hwc⟩
      have hwc' : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hwc
      refine ⟨⟨w, hwL⟩, ⟨ψ.symm ⟨w, hwL⟩, ?_, by simp⟩, rfl⟩
      change sigmaOf L haN (ψ.symm ⟨w, hwL⟩) = ψ.symm ⟨w, hwL⟩
      apply ψ.injective
      apply Subtype.ext
      rw [d.lbarEquiv_act ha haN, MulEquiv.apply_symm_apply]
      change x * w * x⁻¹ = w
      rw [← hwc', mul_inv_cancel_right]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(ψ z).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := d.lbarEquiv_act ha haN z
      rw [Res5Types.mem_fixSubgroup.mp hz] at h1
      change ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) * x =
        x * ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)
      calc ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) * x =
          (x * (ψ z : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) * x⁻¹) * x := by rw [← h1]
        _ = x * ((ψ z : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) := by group
  have hθ : thetaC142 A (lB A) c x =
      (inSubgroup (aschbacherSolvableCore 3) C').map Lα.subtype := by
    rw [thetaC142, d.img_k, ← hLα, hW,
      ← Sec6.map_inSubgroup_theta_of_injective Lα.subtype Lα.subtype_injective]
  refine ⟨?_, ?_⟩
  · rw [hθ]
    exact Subgroup.map_subtype_le _
  · rw [bar, hθ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      Lα.subtype_injective, Sec6.map_inSubgroup_theta_of_injective ψ.symm.toMonoidHom
      ψ.symm.injective, hC', Subgroup.map_map]
    congr 1
    ext z
    simp

theorem thetaCA_eq_bot' (hC : IsPGroup 3 (fixA A L)) : thetaCA142 A (lB A) c = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := img142 A (lB A) c (k142 A (lB A) c) ⊓
    Subgroup.centralizer (img142 A (lB A) c A : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c))
    with hW
  have hWL : W ≤ img142 A (lB A) c L := inf_le_left.trans d.img_k.le
  have hWb : d.bar W ≤ fixA A L := by
    rintro _ ⟨w, hw, rfl⟩ σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    have hw' := (Subgroup.mem_subgroupOf.mp hw).2
    have haα : alpha142 A (lB A) c a haA ∈ img142 A (lB A) c A :=
      ⟨⟨a, Subgroup.mem_sup_right haA⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hw' _ haα
    apply d.lbarEquiv.injective
    apply Subtype.ext
    change ((d.lbarEquiv (sigmaOf L haN (d.lbarEquiv.symm w)) : img142 A (lB A) c L) :
      ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) = _
    rw [d.lbarEquiv_act haA haN, MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, hc, mul_inv_cancel_right]
  have hWp : IsPGroup 3 W := by
    obtain ⟨e⟩ := d.nonempty_bar_equiv hWL
    exact (hC.to_le hWb).of_equiv e.symm
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥W)
    Nat.prime_three
  have hθp : IsPGroup 3 (aschbacherSolvableCore 3 ↥W) := hWp.to_subgroup _
  obtain ⟨k, hk⟩ := hθp.exists_card_eq
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exact absurd (hk ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)) hθ3
  have hbot : aschbacherSolvableCore 3 ↥W = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  rw [thetaCA142, ← hW, inSubgroup, hbot, Subgroup.map_bot]

theorem sigmaOf_comm {a b : G} (haN : a ∈ Subgroup.normalizer (L : Set G))
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hab : a * b = b * a) :
    sigmaOf L haN * sigmaOf L hbN = sigmaOf L hbN * sigmaOf L haN := by
  rw [sigmaOf, sigmaOf, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  exact Subtype.ext hab

theorem typesOne_of_list {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    (hlist : ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
      (∀ σ ∈ Sec4.autThetaQuot A L, Y.map σ.toMonoidHom ≤ Y) →
      ∃ (a : G) (ha : a ∈ A) (haN : a ∈ Subgroup.normalizer (L : Set G)),
        sigmaOf L haN ≠ 1 ∧
          Y ≤ inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN)))
    (hC : IsPGroup 3 (fixA A L)) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have hD := d.std.toSec13Data
  obtain ⟨hQL, hQ3, hQinv, hQmax⟩ := d.maximal_bar' hQ
  obtain ⟨a, ha, haN, hσ1, hle⟩ := hlist _ hQ3 hQinv
  set V := inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN)) with hV
  have hV3 : ¬ 3 ∣ Nat.card V :=
    CFSG.RankThree.PartOne.Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore Nat.prime_three _
  have hVinv : ∀ σ ∈ Sec4.autThetaQuot A L, V.map σ.toMonoidHom ≤ V := by
    intro σ hσ
    obtain ⟨b, hbN, hbA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    have hcomm := sigmaOf_comm d haN hbN (hD.commute ha hbA)
    have hfix : (Res5Types.fixSubgroup (sigmaOf L haN)).map (sigmaOf L hbN).toMonoidHom ≤
        Res5Types.fixSubgroup (sigmaOf L haN) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : sigmaOf L haN z = z := hz
      change sigmaOf L haN (sigmaOf L hbN z) = sigmaOf L hbN z
      rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hz']
    change (inSubgroup (aschbacherSolvableCore 3) (Res5Types.fixSubgroup (sigmaOf L haN))).map
      (sigmaOf L hbN).toMonoidHom ≤ V
    rw [Sec6.map_inSubgroup_theta_of_injective (sigmaOf L hbN).toMonoidHom
      (sigmaOf L hbN).injective]
    have heq : (Res5Types.fixSubgroup (sigmaOf L haN)).map (sigmaOf L hbN).toMonoidHom =
        Res5Types.fixSubgroup (sigmaOf L haN) :=
      Subgroup.eq_of_le_of_card_ge hfix (Subgroup.card_map_of_injective
        (f := (sigmaOf L hbN).toMonoidHom) (sigmaOf L hbN).injective).ge
    rw [heq]
  have hQV : V = d.bar (img142 A (lB A) c Q) := hQmax V hV3 hVinv hle
  obtain ⟨hθL, hθbar⟩ := d.thetaC_bar' ha haN
  refine ⟨a, ha, fun h1 => hσ1 (d.sigmaOf_eq_one_of_alpha ha haN h1), ?_⟩
  rw [d.thetaCA_eq_bot' hC, sup_bot_eq]
  exact d.bar_injective hQL hθL (by rw [hθbar, ← hV, hQV])

end Base142

end CFSG.RankThree.PartTwo.Sec14.L3PGL
