module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofLower
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Item148PtRes2
open scoped commutatorElement Pointwise

namespace Res5Types

variable {G : Type} [Group G] [Finite G]

structure Inner142 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop where
  std : Sec14Std G A c L
  eq_sup : A = Subgroup.zpowers c ⊔ (A ⊓ L)
  eq_k : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  cent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
    ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L

namespace Inner142

variable {A L : Subgroup G} {c : G} (d : Inner142 A c L)
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

theorem le_k_of_mem {Q : Subgroup G}
    (hQ : Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) : Q ≤ k142 A (lB A) c :=
  (Item148Point.le_sup_of_eq_zpowers_sup142 d.std d.eq_sup hQ).trans (sup_le d.l_le d.o''_le)

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

end Inner142

section Quot

variable {A L : Subgroup G} {c : G} [(ker142 A (lB A) c).Normal]

@[expose] noncomputable def toKα (hL : L ≤ kA142 A (lB A) c) :
    ↥L →* ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c :=
  (QuotientGroup.mk' (ker142 A (lB A) c)).comp (Subgroup.inclusion hL)

theorem range_toKα (hL : L ≤ kA142 A (lB A) c) : (toKα hL).range = img142 A (lB A) c L := by
  rw [toKα, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem centralizer_subgroupOf {X : Type*} [Group X] {M : Subgroup X} {x : X} (hx : x ∈ M) :
    (Subgroup.centralizer ({x} : Set X)).subgroupOf M =
      Subgroup.centralizer ({(⟨x, hx⟩ : M)} : Set M) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem img_sup_pCore {X : Subgroup G} (hX : X ≤ kA142 A (lB A) c) :
    img142 A (lB A) c (X ⊔ pPrimeCoreOf 3 (k142 A (lB A) c)) = img142 A (lB A) c X := by
  have hO : pPrimeCoreOf 3 (k142 A (lB A) c) ≤ kA142 A (lB A) c :=
    (pPrimeCoreOf_le 3 _).trans le_sup_left
  rw [img142, img142, Subgroup.subgroupOf_sup hX hO, Subgroup.map_sup]
  have hbot : ((pPrimeCoreOf 3 (k142 A (lB A) c)).subgroupOf (kA142 A (lB A) c)).map
      (QuotientGroup.mk' (ker142 A (lB A) c)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    rw [ker142, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)
  rw [hbot, sup_bot_eq]

theorem img_inf_le : img142 A (lB A) c (A ⊓ L) ≤ img142 A (lB A) c L := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).2, rfl⟩

end Quot

namespace Inner142

variable {A L : Subgroup G} {c : G} (d : Inner142 A c L)
include d

variable [(ker142 A (lB A) c).Normal]

theorem img_k : img142 A (lB A) c (k142 A (lB A) c) = img142 A (lB A) c L := by
  conv_lhs => rw [d.eq_l_sup]
  exact img_sup_pCore d.l_le_kA

theorem img_A : img142 A (lB A) c A = img142 A (lB A) c (A ⊓ L) := by
  have hcA := d.std.toSec13Data.mem_A
  have hZ : Subgroup.zpowers c ≤ kA142 A (lB A) c :=
    (Subgroup.zpowers_le.mpr hcA).trans le_sup_right
  have hAL : A ⊓ L ≤ kA142 A (lB A) c := inf_le_left.trans le_sup_right
  have h : img142 A (lB A) c A = img142 A (lB A) c (Subgroup.zpowers c ⊔ (A ⊓ L)) :=
    congrArg (fun X => img142 A (lB A) c X) d.eq_sup
  rw [h, img142, img142, Subgroup.subgroupOf_sup hZ hAL, Subgroup.map_sup]
  have hbot : ((Subgroup.zpowers c).subgroupOf (kA142 A (lB A) c)).map
      (QuotientGroup.mk' (ker142 A (lB A) c)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    rw [ker142, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)
  rw [hbot, bot_sup_eq]

theorem img_A_le : img142 A (lB A) c A ≤ img142 A (lB A) c L := d.img_A ▸ img_inf_le

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

theorem map_lbarEquiv_inf :
    (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
        d.lbarEquiv.toMonoidHom =
      (img142 A (lB A) c A).subgroupOf (img142 A (lB A) c L) := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, d.img_A]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    change ((d.lbarEquiv (QuotientGroup.mk' _ l) : ↥(img142 A (lB A) c L)) :
      ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) ∈ img142 A (lB A) c (A ⊓ L)
    rw [d.lbarEquiv_mk]
    exact ⟨Subgroup.inclusion d.l_le_kA l, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hl), rfl⟩
  · intro hz
    obtain ⟨x, hx, hxz⟩ := hz
    have hxAL : ((x : ↥(kA142 A (lB A) c)) : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hx
    refine ⟨QuotientGroup.mk' _ ⟨(x : G), hxAL.2⟩,
      ⟨⟨(x : G), hxAL.2⟩, Subgroup.mem_subgroupOf.mpr hxAL, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom, d.lbarEquiv_mk, ← hxz]
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

theorem bar_sup {W₁ W₂ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (h₁ : W₁ ≤ img142 A (lB A) c L) (h₂ : W₂ ≤ img142 A (lB A) c L) :
    d.bar (W₁ ⊔ W₂) = d.bar W₁ ⊔ d.bar W₂ := by
  rw [bar, bar, bar, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem bar_inf (W₁ W₂ : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) :
    d.bar (W₁ ⊓ W₂) = d.bar W₁ ⊓ d.bar W₂ := by
  rw [bar, bar, bar, ← Subgroup.map_inf_eq _ _ _ d.lbarEquiv.symm.injective]
  rfl

theorem bar_bot : d.bar ⊥ = ⊥ := by
  rw [bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem nonempty_bar_equiv {W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hW : W ≤ img142 A (lB A) c L) : Nonempty (↥W ≃* ↥(d.bar W)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hW).symm.trans
    ((W.subgroupOf (img142 A (lB A) c L)).equivMapOfInjective d.lbarEquiv.symm.toMonoidHom
      d.lbarEquiv.symm.injective)⟩

theorem bar_A : d.bar (img142 A (lB A) c A) =
    ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
  rw [bar, ← d.map_lbarEquiv_inf, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id (((A ⊓ L).subgroupOf L).map _)]
  congr 1
  ext x
  simp

theorem maximal_bar {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    img142 A (lB A) c Q ≤ img142 A (lB A) c L ∧ ¬ 3 ∣ Nat.card (d.bar (img142 A (lB A) c Q)) ∧
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
        Subgroup.normalizer (d.bar (img142 A (lB A) c Q) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ∧
      ∀ Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), ¬ 3 ∣ Nat.card Y →
        ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
          Subgroup.normalizer (Y : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
        d.bar (img142 A (lB A) c Q) ≤ Y → Y = d.bar (img142 A (lB A) c Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := k142 A (lB A) c with hKdef
  set KA := kA142 A (lB A) c with hKAdef
  set N := ker142 A (lB A) c with hN
  set πα := QuotientGroup.mk' N with hπα
  set Lα := img142 A (lB A) c L with hLα
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
    with hEb
  have hQK : Q ≤ K := d.le_k_of_mem hQ.prop
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
  have hAαQ : img142 A (lB A) c A ≤
      Subgroup.normalizer (img142 A (lB A) c Q : Set (↥KA ⧸ N)) := by
    have h1 : A.subgroupOf KA ≤ Subgroup.normalizer (Q.subgroupOf KA : Set ↥KA) := by
      intro a ha
      refine Subgroup.mem_normalizer_fintype fun q hq => ?_
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hq ⊢
      simpa using (Subgroup.mem_normalizer_iff.mp (hAQ (Subgroup.mem_subgroupOf.mp ha)) q).mp hq
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map πα)
  have hbarN : ∀ U V : Subgroup (↥KA ⧸ N), U ≤ Lα → V ≤ Lα →
      U ≤ Subgroup.normalizer (V : Set (↥KA ⧸ N)) →
      d.bar U ≤ Subgroup.normalizer (d.bar V : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    intro U V hU hV hUV
    rw [bar, bar, ← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.map_mono fun u hu => ?_
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hUV (Subgroup.mem_subgroupOf.mp hu)) v).mp hv
  have hEbN : Eb ≤ Subgroup.normalizer (d.bar (img142 A (lB A) c Q) :
      Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
    rw [hEb, ← d.bar_A]
    exact hbarN _ _ d.img_A_le hQL hAαQ
  refine ⟨hQL, hQb3, hEbN, fun Y hY3 hEY hQY => ?_⟩
  set Yt : Subgroup (↥KA ⧸ N) := (Y.map d.lbarEquiv.toMonoidHom).map Lα.subtype with hYt
  have hYtL : Yt ≤ Lα := Subgroup.map_subtype_le _
  have hbarYt : d.bar Yt = Y := by
    rw [bar, hYt, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _), Subgroup.map_map]
    ext y
    simp
  have hQYt : img142 A (lB A) c Q ≤ Yt := d.le_of_bar_le hQL (hbarYt ▸ hQY)
  have hAYt : img142 A (lB A) c A ≤ Subgroup.normalizer (Yt : Set (↥KA ⧸ N)) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hy' : d.lbarEquiv.symm ⟨y, hYtL hy⟩ ∈ Y := by
      rw [← hbarYt]
      exact ⟨⟨y, hYtL hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have ha' : d.lbarEquiv.symm ⟨a, d.img_A_le ha⟩ ∈ Eb := by
      rw [hEb, ← d.bar_A]
      exact ⟨⟨a, d.img_A_le ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hEY ha') _).mp hy'
    rw [← map_mul, ← map_inv, ← map_mul] at h1
    rw [← hbarYt] at h1
    obtain ⟨z, hz, hze⟩ := h1
    have hze' : z = ⟨a, d.img_A_le ha⟩ * ⟨y, hYtL hy⟩ * ⟨a, d.img_A_le ha⟩⁻¹ :=
      d.lbarEquiv.symm.injective hze
    have hz' := Subgroup.mem_subgroupOf.mp hz
    rw [hze'] at hz'
    exact hz'
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
    have haα : πα ⟨a, haKA⟩ ∈ img142 A (lB A) c A :=
      ⟨⟨a, haKA⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hAYt haα) _).mp hy'
    rw [← map_mul, ← map_inv, ← map_mul] at h1
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

theorem thetaC_bar (β : G) (hβ : β ∈ A ⊓ L) :
    thetaC142 A (lB A) c (alpha142 A (lB A) c β hβ.1) ≤ img142 A (lB A) c L ∧
      d.bar (thetaC142 A (lB A) c (alpha142 A (lB A) c β hβ.1)) =
        inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨β, hβ.2⟩} :
            Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
  set Lα := img142 A (lB A) c L with hLα
  set x := alpha142 A (lB A) c β hβ.1 with hx
  set ψ := d.lbarEquiv with hψ
  have hxeq : (ψ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨β, hβ.2⟩) :
      ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) = x := d.lbarEquiv_mk ⟨β, hβ.2⟩
  have hxL : x ∈ Lα := hxeq ▸ (ψ _).2
  have hψx : ψ.symm ⟨x, hxL⟩ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨β, hβ.2⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hxeq.symm
  set C' : Subgroup ↥Lα := Subgroup.centralizer ({(⟨x, hxL⟩ : ↥Lα)} : Set ↥Lα) with hC'
  have hW : Lα ⊓ Subgroup.centralizer ({x} : Set _) = C'.map Lα.subtype := by
    rw [hC', ← centralizer_subgroupOf hxL, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hθ : thetaC142 A (lB A) c x = (inSubgroup (aschbacherSolvableCore 3) C').map Lα.subtype := by
    rw [thetaC142, d.img_k, ← hLα, hW,
      Sec6.map_inSubgroup_theta_of_injective Lα.subtype Lα.subtype_injective]
  refine ⟨?_, ?_⟩
  · rw [hθ]
    exact Subgroup.map_subtype_le _
  · rw [bar, hθ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      Lα.subtype_injective, Sec6.map_inSubgroup_theta_of_injective ψ.symm.toMonoidHom
      ψ.symm.injective, hC', CFSG.RankThree.PartTwo.map_centralizer_singleton, hψx]

theorem bar_closure_pair {x y : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c}
    (hx : x ∈ img142 A (lB A) c L) (hy : y ∈ img142 A (lB A) c L) :
    d.bar (Subgroup.closure {x, y}) =
      Subgroup.closure {d.lbarEquiv.symm ⟨x, hx⟩, d.lbarEquiv.symm ⟨y, hy⟩} := by
  have hcl : Subgroup.closure ({x, y} : Set (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)) =
      (Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set ↥(img142 A (lB A) c L))).map
        (img142 A (lB A) c L).subtype := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [bar, hcl, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
    (Subgroup.subtype_injective _), MonoidHom.map_closure, Set.image_pair]
  rfl

theorem isElemAbelian_of_bar {p : ℕ} {W : Subgroup (↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c)}
    (hW : W ≤ img142 A (lB A) c L) (h : CFSG.Assembly.IsElemAbelian p (d.bar W)) :
    CFSG.Assembly.IsElemAbelian p W := by
  obtain ⟨e⟩ := d.nonempty_bar_equiv hW
  refine ⟨⟨⟨fun u v => e.injective ?_⟩⟩, fun w hw => ?_⟩
  · rw [map_mul, map_mul]
    exact h.1.is_comm.comm (e u) (e v)
  · have h1 : (e ⟨w, hw⟩ : ↥(d.bar W)) ^ p = 1 := Subtype.ext (h.2 _ (e ⟨w, hw⟩).2)
    rw [← map_pow, ← map_one e] at h1
    exact congrArg Subtype.val (e.injective h1)

end Inner142

end Res5Types

end CFSG.RankThree.PartTwo.Sec14
