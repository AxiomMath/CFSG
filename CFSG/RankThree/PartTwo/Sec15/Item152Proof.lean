module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec15.Ronan152StellIIIKP
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec15.Item153
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.GH74.GLS.LU.Local.FiveSL2
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.PartTwo.Sec14.Item1411
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.S4Free.Statement

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def oTwoOddIn (X : Subgroup G) : Subgroup G :=
  ((CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map
    X.subtype

@[expose] def IsSL25Case (X : Subgroup G) : Prop :=
  Nonempty (↥X ⧸ Sec4.oTwoFitting ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
    Nonempty (↥X ⧸ Sec4.oTwoP 5 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))

@[expose] def Step152Comp (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, ∀ M ∈ scriptY2 A, Y ≤ M →
    generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ∃ X ∈ thetaComponentsIn M, Y ≤ X ∧ X = delta A LB X

@[expose] def Step152Excl (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, ∀ M ∈ scriptY2 A, Y ≤ M → generalizedFitting ↥M = CFSG.pCore 2 ↥M →
    ∀ X ∈ thetaComponentsIn M, Y ≤ X → X = delta A LB X →
      ((∃ p : ℕ, p.Prime ∧ 5 < p ∧
          Nonempty (↥X ⧸ Sec4.oTwoP p ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ∨
        Nonempty (↥X ⧸ Sec4.oTwoP 3 ↥X ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 3 1)) ∨
        Sec4.IsExtOf (↥X ⧸ Sec4.oTwoP 3 ↥X) (alternatingGroup (Fin 5)) Sec4.Q8D8) →
      IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)

structure Ctx152 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y M X : Subgroup G) :
    Prop where
  mem_y4 : Y ∈ scriptY4 A LB
  mem_y2 : M ∈ scriptY2 A
  le_m : Y ≤ M
  fstar : generalizedFitting ↥M = CFSG.pCore 2 ↥M
  mem_comp : X ∈ thetaComponentsIn M
  le_x : Y ≤ X
  norm_x : A ≤ Subgroup.normalizer (X : Set G)
  delta_x : X = delta A LB X
  sl25 : IsSL25Case X
  not_quasi : ¬ IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)

structure Data152 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (X : Subgroup G) (c' : G)
    (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G) : Prop where
  omega : Subgroup.zpowers c' ∈ omegaA A
  mem_lA : L' ∈ lA A c'
  hj : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem_d : d ∈ A
  ne_d : d ≠ 1
  central_d : IsThreeCentralIn L' d
  cent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
    (Subgroup.closure {c', d} : Set G)
  prime : p.Prime
  odd : p ≠ 2
  le_px : P ≤ X
  char_p : ∃ R : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype) ∧ P ≤ R ∧
      (P.subgroupOf R).Characteristic
  norm_p : A ≤ Subgroup.normalizer (P : Set G)
  type_p : (IsElementaryAbelian p ↥P ∧ Nat.card P = p ^ 2) ∨
    (CFSG.IsExtraspecialPGroup p ↥P ∧ Nat.card P = p ^ 3)
  cent_p : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X
  mem_t : T ∈ scriptQPiStar A LB X (piOf 2)
  tp_eq : ((T ⊔ P : Subgroup G) : Set G) = (T : Set G) * (P : Set G)
  eq_comm_p : P = ⁅⁅T ⊓ Subgroup.normalizer (P : Set G), A⁆, P⁆
  le_k : T ⊔ P ≤ K
  mem_k : K ∈ scriptY2 A
  le_ts : T ≤ S
  mem_sk : S ∈ scriptQPiStar A LB K (piOf 2)
  s_max : ∀ K' ∈ scriptY2 A, T ⊔ P ≤ K' → ∀ S' ∈ scriptQPiStar A LB K' (piOf 2), S ≤ S' →
    S' = S
  le_theta : P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype
  normal_pk : ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal
  ps_eq : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G)
  fstar_ps : generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S)
  frattini_p : P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype
  norm_w : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G)

@[expose] def Step152Conf (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y M X : Subgroup G, Ctx152 A LB Y M X →
    ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
      deltaZero A LB X = pPrimeCoreOf 3 (deltaZero A LB X) ⊔
        deltaZero A LB (X ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) →
      ∃ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A LB X c' L' d p P T K S

@[expose] def KS152HJGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ∀ Y M X : Subgroup G, Ctx152 A (lB A) Y M X →
    ∀ (d : G) (p : ℕ) (P T K S : Subgroup G), Data152 A (lB A) X c L d p P T K S →
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∈
        scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2) →
      L ≤ (S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔ X

@[expose] def Step152End (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y M X : Subgroup G, Ctx152 A LB Y M X →
    ∀ (c' : G) (L' : Subgroup G) (d : G) (p : ℕ) (P T K S : Subgroup G),
      Data152 A LB X c' L' d p P T K S →
      S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G) ∈
        scriptQPiStar A LB (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) (piOf 2) →
      L' ≤ (S ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ⊔ X → False

theorem map_conj_mem_thetaComponentsIn {M : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (M : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaComponentsIn M) :
    X.map (MulAut.conj a).toMonoidHom ∈ thetaComponentsIn M := by
  have hM : M.map (MulAut.conj a).toMonoidHom = M := Late.map_conj_eq_of_mem_normalizer ha
  set σ : ↥M ≃* ↥M := ((MulAut.conj a).subgroupMap M).trans (MulEquiv.subgroupCongr hM)
  obtain ⟨X', hX', rfl⟩ := hX
  refine ⟨X'.map σ.toMonoidHom, map_mulEquiv_mem_thetaComponents Nat.prime_three σ hX', ?_⟩
  change (X'.map σ.toMonoidHom).map M.subtype = (X'.map M.subtype).map (MulAut.conj a).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_normalizer_of_mem_thetaComponentsIn {A M X Y : Subgroup G}
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X)
    (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  intro a ha
  have hXa := map_conj_mem_thetaComponentsIn (hAM ha) hX
  obtain ⟨hXM, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  obtain ⟨hXaM, hXa'⟩ := mem_thetaComponentsIn_iff.mp hXa
  have hYM : Y ≤ M := hYX.trans hXM
  have hYa : Y.map (MulAut.conj a).toMonoidHom = Y := Late.map_conj_eq_of_mem_normalizer (hAY ha)
  have hYXa : Y ≤ X.map (MulAut.conj a).toMonoidHom := by
    rw [← hYa]
    exact Subgroup.map_mono hYX
  have hP1 : Y.subgroupOf M ≠ ⊥ := by
    intro h
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hYM hy⟩ : M) ∈ Y.subgroupOf M := hy
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have hPp : Group.IsPerfect (Y.subgroupOf M) := by
    have := hYp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hYM).symm.toMonoidHom) (MulEquiv.surjective _)
  have heq := theta_component_eq_of_perfect_le Nat.prime_three hX' hXa' hP1 hPp
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hYX (Subgroup.mem_subgroupOf.mp hy)))
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hYXa (Subgroup.mem_subgroupOf.mp hy)))
  have hXeq : X = X.map (MulAut.conj a).toMonoidHom := by
    have h1 := congrArg (Subgroup.map M.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hXM, Subgroup.map_subgroupOf_eq_of_le hXaM] at h1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hXeq.symm

theorem isCharacteristicP_of_isSubnormal {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hK : IsCharacteristicP p K) {H : Subgroup K} (hH : H.IsSubnormal) :
    IsCharacteristicP p ↥H := by
  induction hH with
  | top => exact Sec14.isCharacteristicP_of_mulEquiv' Subgroup.topEquiv.symm hK
  | step H K' hle _ hN ih =>
    have := Sec14.isCharacteristicP_of_normal (H.subgroupOf K') ih
    exact Sec14.isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hle) this

theorem isCharacteristicP_of_mem_thetaComponentsIn {M X : Subgroup G}
    (hM : generalizedFitting ↥M = CFSG.pCore 2 ↥M) (hX : X ∈ thetaComponentsIn M) :
    IsCharacteristicP 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hXM, hX'⟩ := mem_thetaComponentsIn_iff.mp hX
  have hMc : IsCharacteristicP 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mpr hM
  exact Sec14.isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hXM)
    (isCharacteristicP_of_isSubnormal hMc hX'.2.1)

theorem pCore_ne_bot_of_isCharacteristicP {K : Type*} [Group K] [Nontrivial K] {p : ℕ}
    (h : IsCharacteristicP p K) : CFSG.pCore p K ≠ ⊥ := by
  intro hb
  obtain ⟨x, hx⟩ := exists_ne (1 : K)
  have hxc : x ∈ Subgroup.centralizer ((CFSG.pCore p K : Subgroup K) : Set K) := by
    rw [hb, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [(Subgroup.mem_bot).mp hy, one_mul, mul_one]
  have := h hxc
  rw [hb] at this
  exact hx ((Subgroup.mem_bot).mp this)

omit [Finite G] in
theorem pCoreOf_ne_bot_of_pCore_ne_bot {X : Subgroup G} (h : CFSG.pCore 2 ↥X ≠ ⊥) :
    CFSG.Open.pCoreOf 2 X ≠ ⊥ := by
  rw [CFSG.Open.pCoreOf]
  intro hb
  exact h ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb)

theorem isQuasisimple_theta_of_mem_thetaComponentsIn {M K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set e := Subgroup.subgroupOfEquivOfLe hKM
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
      Nat.prime_three e)) hK'.2.2

omit [Finite G] in
theorem ne_bot_of_mem_scriptY4 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : Y ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, -, hq⟩ := hY
  obtain ⟨-, hs, -⟩ := hq
  have hnt := hs.toNontrivial
  have : Subsingleton ((↥(⊥ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊥ : Subgroup G)) ⧸
      Subgroup.center (↥(⊥ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊥ : Subgroup G))) := by
    refine ⟨fun u v => ?_⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [Subsingleton.elim u v]
  exact not_nontrivial_iff_subsingleton.mpr this hnt

theorem isPerfect_of_mem_scriptY4 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : Group.IsPerfect ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h3, -, hq⟩ := hY
  set O := CFSG.pCore 2 ↥Y with hO
  set D := commutator ↥Y with hD
  have hmap : D.map (QuotientGroup.mk' O) = ⊤ := by
    rw [hD, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)]
    exact hq.1.commutator_eq_top
  have hDO : D ⊔ O = ⊤ := by
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' O) D
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  refine ⟨?_⟩
  by_contra hne
  have h3' := three_dvd_card_quotient_of_eq_oPrimeResidualOf h3 D hne
  have hsurj : Function.Surjective ((QuotientGroup.mk' D).comp O.subtype) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D q
    have hy : y ∈ D ⊔ O := hDO ▸ Subgroup.mem_top y
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨d, hd, o, ho, rfl⟩ := hy
    refine ⟨⟨o, ho⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d).mpr hd, one_mul]
  have hdvd : Nat.card (↥Y ⧸ D) ∣ Nat.card O := Subgroup.card_dvd_of_surjective hsurj
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
  rw [hk] at hdvd
  have := (Nat.prime_three.dvd_of_dvd_pow (h3'.trans hdvd))
  omega

theorem oPrimeResidual_normal (p : ℕ) (X : Type*) [Group X] : (oPrimeResidual p X).Normal := by
  constructor
  intro n hn g
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem isSolvable_comap_center {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (hN : Group.IsSolvable N) :
    Group.IsSolvable ((Subgroup.center (Q ⧸ N)).comap (QuotientGroup.mk' N)) := by
  set K := (Subgroup.center (Q ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hNK : N ≤ K := fun x hx => by
    rw [hK, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  let g : K →* Subgroup.center (Q ⧸ N) :=
    ((QuotientGroup.mk' N).comp K.subtype).codRestrict _ (fun x => x.2)
  have hker : g.ker ≤ (Subgroup.inclusion hNK).range := by
    intro x hx
    have hx' : QuotientGroup.mk' N (x : Q) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact ⟨⟨x, hx'⟩, rfl⟩
  have : Group.IsSolvable (Subgroup.center (Q ⧸ N)) := Group.isSolvable_of_comm (fun a b => by
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp b.2 a)
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNK) g hker

noncomputable def quotientComapEquiv {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (M : Subgroup (Q ⧸ N)) [M.Normal] [(M.comap (QuotientGroup.mk' N)).Normal] :
    Q ⧸ M.comap (QuotientGroup.mk' N) ≃* (Q ⧸ N) ⧸ M :=
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp (QuotientGroup.mk' N)) :=
    (QuotientGroup.mk'_surjective M).comp (QuotientGroup.mk'_surjective N)
  have hker : ((QuotientGroup.mk' M).comp (QuotientGroup.mk' N)).ker =
      M.comap (QuotientGroup.mk' N) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

theorem eq_oPrimeResidualOf_of_le {X Y : Subgroup G} (hXp : Group.IsPerfect ↥X)
    (hXq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X)) (hYX : Y ≤ X)
    (hY3 : Y = oPrimeResidualOf 3 Y) (hYp : Group.IsPerfect ↥Y) (hY1 : Y ≠ ⊥) :
    X = oPrimeResidualOf 3 X := by
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  set N := oPrimeResidual 3 ↥X with hNdef
  have hNn : N.Normal := oPrimeResidual_normal 3 ↥X
  have hYN : Y ≤ oPrimeResidualOf 3 X :=
    calc Y = oPrimeResidualOf 3 Y := hY3
      _ ≤ oPrimeResidualOf 3 X := oPrimeResidualOf_mono 3 hYX
  have hYN' : Y.subgroupOf X ≤ N := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hYN (Subgroup.mem_subgroupOf.mp hy)
    rwa [show z = y from Subtype.ext hzy] at hz
  have hmapn : (N.map (QuotientGroup.mk' θ)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hmapn with htop | hcen
  ·
    have hsup : N ⊔ θ = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp θ.subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
      have hx : x ∈ N ⊔ θ := hsup ▸ Subgroup.mem_top x
      rw [Subgroup.mem_sup_of_normal_left] at hx
      obtain ⟨n, hn, t, ht, rfl⟩ := hx
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have : Group.IsSolvable θ := hθ.1
    have hsolv : Group.IsSolvable (↥X ⧸ N) := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (↥X ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have hNtop : N = ⊤ := by
      by_contra hne
      have : Nontrivial (↥X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
      exact Group.IsPerfect.not_isSolvable (↥X ⧸ N) hsolv
    rw [oPrimeResidualOf, ← hNdef, hNtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  ·
    exfalso
    have hKs : Group.IsSolvable
        ((Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ)) :=
      isSolvable_comap_center θ hθ.1
    have hNK : N ≤ (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ) :=
      fun x hx => hcen (Subgroup.mem_map_of_mem _ hx)
    have hYs : Group.IsSolvable (Y.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hYN'.trans hNK))
        (Subgroup.inclusion_injective _)
    have hYs' : Group.IsSolvable ↥Y := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom) (MulEquiv.surjective _)
    have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
    exact Group.IsPerfect.not_isSolvable ↥Y hYs'

theorem mem_scriptY0_of_isQuasisimple {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y M X : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hM : M ∈ scriptY2 A)
    (hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M) (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hΔ : X = delta A LB X)
    (hq : IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) : X ∈ scriptY0 A LB := by
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h => hM.1.1 (top_le_iff.mp (h ▸ hXM))
  have hXY : X ∈ scriptY A := ⟨hXtop, hAX⟩
  have hY1 := ne_bot_of_mem_scriptY4 hY
  have hX1 : X ≠ ⊥ := fun h => hY1 (le_bot_iff.mp (h ▸ hYX))
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hO2 : CFSG.Open.pCoreOf 2 X ≠ ⊥ := pCoreOf_ne_bot_of_pCore_ne_bot
    (pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hX))
  have hX3 : X = oPrimeResidualOf 3 X :=
    eq_oPrimeResidualOf_of_le (isPerfect_of_mem_thetaComponentsIn hX)
      (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hYX hY.2.1
      (isPerfect_of_mem_scriptY4 hY) hY1
  exact ⟨⟨hXY, hX3, hΔ, hq⟩, ⟨hXY, hO2⟩⟩

theorem isQuasisimple_or_isSL25Case {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hG : TheoremFourHyp G) (h44 : Sec4.Item4_4) (hexcl : Step152Excl A LB)
    {Y M X : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hM : M ∈ scriptY2 A) (hYM : Y ≤ M)
    (hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M) (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X)
    (hΔ : X = delta A LB X) :
    IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) ∨ IsSL25Case X := by
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h => hM.1.1 (top_le_iff.mp (h ▸ hXM))
  have hS4 : SectionFourHyp ↥X := hG.sectionFourHyp hXtop
  have hXp : Group.IsPerfect ↥X := isPerfect_of_mem_thetaComponentsIn hX
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hX
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X
  set K := (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ) with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
  have : IsSimpleGroup ((↥X ⧸ θ) ⧸ Subgroup.center (↥X ⧸ θ)) := hXq.2.1
  have hKsimp : IsSimpleGroup (↥X ⧸ K) :=
    (quotientComapEquiv θ (Subgroup.center (↥X ⧸ θ))).isSimpleGroup
  have hX1 : X ≠ ⊥ := fun h => ne_bot_of_mem_scriptY4 hY (le_bot_iff.mp (h ▸ hYX))
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hO2 : CFSG.pCore 2 ↥X ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hX)
  rcases h44 ↥X hS4 hXp K hKs hKsimp with h1 | h2 | ⟨p, hp, hp3, hφ⟩ | h4 | ⟨h5, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rcases Nat.lt_or_ge 5 p with hp5 | hp5
    · exact Or.inl (hexcl Y hY M hM hYM hF X hX hYX hΔ (Or.inl ⟨p, hp, hp5, hφ⟩))
    · obtain rfl : p = 5 := by
        have h45 : p = 4 ∨ p = 5 := by omega
        rcases h45 with rfl | rfl
        · exact absurd hp (by norm_num)
        · rfl
      exact Or.inr (Or.inr hφ)
  · exact Or.inl (hexcl Y hY M hM hYM hF X hX hYX hΔ (Or.inr h4))
  · exact absurd h5 hO2

theorem oTwo_eq_pCore (X : Type*) [Group X] [Finite X] : S4Free.oTwo X = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold S4Free.oTwo CFSG.piCore
  rw [CFSG.pCore]
  congr 1
  ext K
  constructor
  · rintro ⟨hKn, hKπ⟩
    exact ⟨hKn, CFSG.isPGroup_of_isPiSubgroup_singleton hKπ⟩
  · rintro ⟨hKn, hKp⟩
    exact ⟨hKn, CFSG.isPiSubgroup_singleton_of_isPGroup hKp⟩

omit [Finite G] in
theorem card_quotient_dvd_of_coe_sup_eq_mul {P S : Subgroup G}
    (hPS : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G)) :
    Nat.card (↥(P ⊔ S) ⧸ S.subgroupOf (P ⊔ S)) ∣ Nat.card P := by
  set X := P ⊔ S with hX
  set S' := S.subgroupOf X with hS'
  set P' := P.subgroupOf X with hP'
  have hcos : ∀ x : ↥X, ∃ p : ↥P', (x : ↥X ⧸ S') = ((p : ↥X) : ↥X ⧸ S') := by
    intro x
    have hx : (x : G) ∈ (P : Set G) * (S : Set G) := by
      rw [← hPS]
      exact x.2
    obtain ⟨p, hp, s, hs, hps⟩ := hx
    have hpX : p ∈ X := (le_sup_left : P ≤ X) hp
    refine ⟨⟨⟨p, hpX⟩, Subgroup.mem_subgroupOf.mpr hp⟩, ?_⟩
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have : ((x⁻¹ * ⟨p, hpX⟩ : ↥X) : G) = s⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hps]
      change (p * s)⁻¹ * p = s⁻¹
      group
    rw [this]
    exact S.inv_mem hs
  have hpre : MulAction.IsPretransitive P' (↥X ⧸ S') := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨p, hp⟩ := hcos x
    obtain ⟨q, hq⟩ := hcos y
    refine ⟨q * p⁻¹, ?_⟩
    rw [hp, hq, Subgroup.smul_def, MulAction.Quotient.smul_mk]
    congr 1
    simp
  have h := MulAction.index_stabilizer_of_transitive P' ((1 : ↥X) : ↥X ⧸ S')
  rw [← h]
  refine (Subgroup.index_dvd_card _).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ X)).toEquiv]

theorem exists_char_of_stellmacher (hst : StellmacherKP)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {P S : Subgroup G} (hP : IsPGroup p P)
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hPS : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G))
    (hF : generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S)) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧
      P ⊔ S ≤ Subgroup.normalizer (C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set X := P ⊔ S with hX
  set S' := S.subgroupOf X with hS'
  have hSX : S ≤ X := le_sup_right
  have hidx := card_quotient_dvd_of_coe_sup_eq_mul hPS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk] at hidx
  have hS'2 : IsPGroup 2 S' := hS2.comap_subtype
  have hodd : ¬ 2 ∣ S'.index := by
    intro h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hidx)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  set Q : Sylow 2 ↥X := hS'2.toSylow hodd with hQ
  have h3 : ¬ 3 ∣ Nat.card ↥X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup S']
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h.trans hidx)
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this).symm
    · obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS'2
      rw [hm] at h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  have hC : Subgroup.centralizer (S4Free.oTwo ↥X : Set ↥X) ≤ S4Free.oTwo ↥X := by
    rw [oTwo_eq_pCore]
    exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X 2).mpr hF
  set ι : ↥S →* ↥X := Subgroup.inclusion hSX with hι
  have hrange : ι.range = S' := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr s.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hadm : S4Free.IsAdmissibleHost ι :=
    S4Free.isAdmissibleHost_of_not_three_dvd h3 (Subgroup.inclusion_injective hSX)
      ⟨Q, by rw [hrange]; rfl⟩ hC
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  have hsolv : Group.IsSolvable ↥X := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hidx
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS'2
    letI := Fintype.ofFinite ↥X
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp
      Nat.prime_two hp2 (a := j) (b := m) ?_
    rw [Fintype.card_eq_nat_card, Subgroup.card_eq_card_quotient_mul_card_subgroup S', hj, hm]
  obtain ⟨W, hWc, hW1, hWn⟩ := hst.1 ↥S hS2 hnt
  have hWX : (W.map ι).Normal := hWn ↥X ι hadm (@S4Free.SzSections.of_isSolvable ↥X _ hsolv)
  refine ⟨W.map S.subtype, ?_, Subgroup.map_subtype_le W, ?_, ?_⟩
  · intro h
    exact hW1 ((Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).mp h)
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
    exact hWc
  · have hCX : W.map S.subtype ≤ X := (Subgroup.map_subtype_le W).trans hSX
    have heq : (W.map S.subtype).subgroupOf X = W.map ι := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨w, hw, hwx⟩
        exact ⟨w, hw, Subtype.ext hwx⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hCX, heq]
    exact hWX

theorem mem_scriptQPiStar_top_of_maximal {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hsimp : IsSimpleGroup G) {T P K S C : Subgroup G}
    (hK : K ∈ scriptY2 A) (hS : S ∈ scriptQPiStar A LB K (piOf 2))
    (hmax : ∀ K' ∈ scriptY2 A, T ⊔ P ≤ K' → ∀ S' ∈ scriptQPiStar A LB K' (piOf 2), S ≤ S' →
      S' = S)
    (hTS : T ≤ S) (hC1 : C ≠ ⊥) (hCS : C ≤ S) (hCchar : (C.subgroupOf S).Characteristic)
    (hPSC : P ⊔ S ≤ Subgroup.normalizer (C : Set G)) :
    S ∈ scriptQPiStar A LB ⊤ (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hNSC : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h' := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := S) (C.subgroupOf S)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCS] at h'
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAS.trans hNSC
  set K' := Subgroup.normalizer (C : Set G) with hK'def
  have hCp : IsPGroup 2 C := hSp.to_le hCS
  have hK' : K' ∈ scriptY2 A := by
    refine ⟨⟨fun htop => ?_, hAC.trans Subgroup.le_normalizer⟩, ?_⟩
    · have hn : C.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      have hCt : C = ⊤ := (hsimp.eq_bot_or_eq_top_of_normal C).resolve_left hC1
      apply hK.1.1
      rw [eq_top_iff, ← hCt]
      exact hCS.trans hS.prop.1.2
    · intro h0
      apply hC1
      rw [eq_bot_iff, ← h0]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hCp
  have hTPK' : T ⊔ P ≤ K' := sup_le (hTS.trans (le_sup_right.trans hPSC)) (le_sup_left.trans hPSC)
  refine ⟨⟨⟨hS.prop.1.1, le_top⟩, hS.prop.2⟩, fun S₂ hS₂ hSS₂ => ?_⟩
  have hS₂p : IsPGroup 2 S₂ := isPGroup_of_mem_scriptQPi Nat.prime_two hS₂
  have hNmem : S₂ ⊓ Subgroup.normalizer (S : Set G) ∈ scriptQPi A LB K' (piOf 2) := by
    have hAN : A ≤ Subgroup.normalizer
        ((S₂ ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
      Late.le_normalizer_inf hS₂.1.1.1.2.2
        (hAS.trans (Sec6.normalizer_le_normalizer_normalizer S))
    exact ⟨⟨mem_scriptQ_of_le hS₂.1.1 inf_le_left hAN, inf_le_right.trans hNSC⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS₂p.to_le inf_le_left)⟩
  obtain ⟨S₃, hNS₃, hS₃⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A LB K' (piOf 2))) hNmem
  have hSS₃ : S ≤ S₃ := (le_inf hSS₂ Subgroup.le_normalizer).trans hNS₃
  have hNS : S₂ ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
    hNS₃.trans (hmax K' hK' hTPK' S₃ hS₃ hSS₃).le
  by_contra hS₂S
  have hlt : S.subgroupOf S₂ < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hS₂S fun x hx => ?_
    have : (⟨x, hx⟩ : S₂) ∈ S.subgroupOf S₂ := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent S₂ := hS₂p.isNilpotent
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hSS₂, Subgroup.mem_subgroupOf] at hyN
  exact hyS (Subgroup.mem_subgroupOf.mpr (hNS ⟨y.2, hyN⟩))

theorem Data152.mem_scriptQPiStar_top (hst : StellmacherKP)
    (hsimp : IsSimpleGroup G) {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {X : Subgroup G} {c' : G} {L' : Subgroup G} {d : G} {p : ℕ} {P T K S : Subgroup G}
    (D : Data152 A LB X c' L' d p P T K S) : S ∈ scriptQPiStar A LB ⊤ (piOf 2) := by
  have : Fact p.Prime := ⟨D.prime⟩
  obtain ⟨n, hn, hPn⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nat.card P = p ^ n := by
    rcases D.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨2, le_rfl, h⟩
    · exact ⟨3, by norm_num, h⟩
  have hPp : IsPGroup p P := IsPGroup.of_card hPn
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPn
    have := Nat.one_lt_pow (by omega : n ≠ 0) D.prime.one_lt
    omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    have hθ3 := (solvable_prime_complement_core_characterization (H := ↥K)
      Nat.prime_three).2.2.1
    have hdvd : Nat.card P ∣ Nat.card (aschbacherSolvableCore 3 ↥K) := by
      have h := Subgroup.card_dvd_of_le D.le_theta
      rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
    rw [hPn] at hdvd
    exact hθ3 ((dvd_pow_self 3 (by omega : n ≠ 0)).trans hdvd)
  have hT1 : T ≠ ⊥ := by
    intro hT
    apply hP1
    rw [D.eq_comm_p, hT, bot_inf_eq, Subgroup.commutator_bot_left,
      Subgroup.commutator_bot_left]
  have hS1 : S ≠ ⊥ := fun h => hT1 (le_bot_iff.mp (h ▸ D.le_ts))
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two D.mem_sk.prop
  obtain ⟨C, hC1, hCS, hCchar, hPSC⟩ :=
    exists_char_of_stellmacher hst D.prime D.odd hp3 hPp hS2 hS1 D.ps_eq D.fstar_ps
  exact mem_scriptQPiStar_top_of_maximal hsimp D.mem_k D.mem_sk D.s_max D.le_ts hC1 hCS hCchar
    hPSC

theorem sl25_theta
    {X₀ : Type} [Group X₀] [Finite X₀]
    (hq : IsQuasisimple (X₀ ⧸ aschbacherSolvableCore 3 X₀)) {R : Subgroup X₀} [R.Normal]
    (e : X₀ ⧸ R ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    Nat.card (X₀ ⧸ aschbacherSolvableCore 3 X₀) = 60 ∧
      CFSG.pPrimeCore 3 X₀ = aschbacherSolvableCore 3 X₀ := by
  have hθ := solvable_prime_complement_core_characterization (H := X₀) Nat.prime_three
  set θ := aschbacherSolvableCore 3 X₀ with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hSLp : ⁅(⊤ : Subgroup (X₀ ⧸ R)), ⊤⁆ = ⊤ :=
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_perfect e.symm
  have hSL120 : Nat.card (X₀ ⧸ R) = 120 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm
  have hSLnt : Nontrivial (X₀ ⧸ R) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hSL120]
    norm_num
  have hSLns : ¬ Group.IsSolvable (X₀ ⧸ R) := by
    intro hs
    have : Group.IsPerfect (X₀ ⧸ R) := ⟨hSLp⟩
    exact Group.IsPerfect.not_isSolvable (X₀ ⧸ R) hs
  have hRn : (R.map π).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective θ)
  have hRc : R.map π ≤ Subgroup.center (X₀ ⧸ θ) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hRn with htop | hc
    · exfalso
      have hsup : R ⊔ θ = ⊤ := by
        have h1 := Subgroup.comap_map_eq π R
        rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
        exact h1.symm
      have hsurj : Function.Surjective ((QuotientGroup.mk' R).comp θ.subtype) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
        have hx : x ∈ R ⊔ θ := hsup ▸ Subgroup.mem_top x
        rw [Subgroup.mem_sup_of_normal_left] at hx
        obtain ⟨n, hn, t, ht, rfl⟩ := hx
        refine ⟨⟨t, ht⟩, ?_⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply]
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
      have : Group.IsSolvable θ := hθ.1
      exact hSLns (Group.isSolvable_of_surjective hsurj)
    · exact hc
  set K := (Subgroup.center (X₀ ⧸ θ)).comap π with hK
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hRK : R ≤ K := fun x hx => hRc (Subgroup.mem_map_of_mem π hx)
  have : IsSimpleGroup ((X₀ ⧸ θ) ⧸ Subgroup.center (X₀ ⧸ θ)) := hq.2.1
  have hKs : IsSimpleGroup (X₀ ⧸ K) :=
    (quotientComapEquiv θ (Subgroup.center (X₀ ⧸ θ))).isSimpleGroup
  have hKnt : Nontrivial (X₀ ⧸ K) := hKs.toNontrivial
  set N := K.map (QuotientGroup.mk' R) with hN
  have hNn : N.Normal := Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective R)
  set eK := QuotientGroup.quotientQuotientEquivQuotient R K hRK with heK
  have hcardK : Nat.card (X₀ ⧸ K) = 60 := by
    rcases CFSG.GH74.GLS.LU.Local.Five.sl2_five_normal_cases e.symm N with h0 | hZ | htop
    ·
      exfalso
      have hc2 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm
      have e2 : (X₀ ⧸ R) ≃* (X₀ ⧸ K) := by
        refine (QuotientGroup.quotientBot.symm.trans
          (QuotientGroup.quotientMulEquivOfEq h0.symm)).trans eK
      have hs : IsSimpleGroup (X₀ ⧸ R) := e2.isSimpleGroup
      rcases (inferInstance : (Subgroup.center (X₀ ⧸ R)).Normal).eq_bot_or_eq_top with h | h
      · rw [h, Subgroup.card_bot] at hc2
        omega
      · rw [h, Subgroup.card_top, hSL120] at hc2
        omega
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hSL120, hZ, CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm] at h1
      have h2 : Nat.card ((X₀ ⧸ R) ⧸ N) = 60 := by
        rw [hZ]
        omega
      rw [← Nat.card_congr eK.toEquiv]
      exact h2
    · exfalso
      have hsub : Subsingleton ((X₀ ⧸ R) ⧸ N) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      have : Subsingleton (X₀ ⧸ K) := eK.symm.toEquiv.subsingleton
      exact not_nontrivial_iff_subsingleton.mpr this hKnt
  set eZ := quotientComapEquiv θ (Subgroup.center (X₀ ⧸ θ)) with heZ
  have hQZ : Nat.card ((X₀ ⧸ θ) ⧸ Subgroup.center (X₀ ⧸ θ)) = 60 := by
    rw [← Nat.card_congr eZ.toEquiv]
    exact hcardK
  obtain ⟨eA⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hQZ
  have hZ2 : Nat.card (Subgroup.center (X₀ ⧸ θ)) ∣ 2 := by
    have h := CFSG.ComponentClassification.RankTwoAlt.card_ker_dvd_two_five hq.1.commutator_eq_top
      (CFSG.ComponentClassification.RankTwoAlt.quotCenterHom_surjective eA)
      (CFSG.ComponentClassification.RankTwoAlt.ker_quotCenterHom eA).le
    rwa [CFSG.ComponentClassification.RankTwoAlt.ker_quotCenterHom] at h
  have hKcard : Nat.card K = Nat.card (Subgroup.center (X₀ ⧸ θ)) * Nat.card θ := by
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index (Subgroup.center (X₀ ⧸ θ))
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    have hidx : K.index = (Subgroup.center (X₀ ⧸ θ)).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective θ)
    have hpos : 0 < (Subgroup.center (X₀ ⧸ θ)).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    rw [← h2] at h3
    rw [h3] at h1
    have h4 : Nat.card K * (Subgroup.center (X₀ ⧸ θ)).index =
        (Nat.card (Subgroup.center (X₀ ⧸ θ)) * Nat.card θ) *
          (Subgroup.center (X₀ ⧸ θ)).index := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · have := Nat.le_of_dvd (by norm_num) (h.trans hZ2)
      omega
    · exact hθ.2.2.1 h
  have hKθ : K ≤ θ := hθ.2.2.2.1 K hKn (isSolvable_comap_center θ hθ.1) hK3
  have hZ1 : Subgroup.center (X₀ ⧸ θ) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ z
    have hx : x ∈ K := hz
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hKθ hx
  have e1 : (X₀ ⧸ θ) ≃* (X₀ ⧸ θ) ⧸ Subgroup.center (X₀ ⧸ θ) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ1.symm)
  have hQ60 : Nat.card (X₀ ⧸ θ) = 60 := by
    rw [Nat.card_congr e1.toEquiv]
    exact hQZ
  have hQs : IsSimpleGroup (X₀ ⧸ θ) := e1.isSimpleGroup
  refine ⟨hQ60, le_antisymm ?_ ?_⟩
  ·
    have hN' : ((CFSG.pPrimeCore 3 X₀).map π).Normal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := X₀)).map _ (QuotientGroup.mk'_surjective θ)
    have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 X₀).map π)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _)
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := X₀))
    have hle : (CFSG.pPrimeCore 3 X₀).map π ≤ CFSG.pPrimeCore 3 (X₀ ⧸ θ) := le_sSup ⟨hN', hcop⟩
    rw [pPrimeCore_three_eq_bot_of_isSimpleGroup hQs (by rw [hQ60]; norm_num), le_bot_iff,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle
    exact hle
  · have hcopθ : Nat.Coprime 3 (Nat.card θ) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1
    exact le_sSup ⟨inferInstance, hcopθ⟩

end CFSG.RankThree.PartTwo.Sec15
