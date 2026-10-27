module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofSeven
public import CFSG.RankThree.PartTwo.Sec17.Item172Proof
import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofSec
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec17.Item17Res4ProofSeven
public import Certificates.Certificate8166
public import Certificates.Certificate8169
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.PartTwo.Sec17.Item1711Proof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofKM
import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofKMd
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof
open scoped commutatorElement

@[expose] noncomputable def Step177OThreeSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → Item176 A (lB A) c L →
    omegaA A = {Subgroup.zpowers c} →
    ∀ V : Subgroup G, V ≤ Subgroup.normalizer (Y₀ : Set G) →
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) →
      CFSG.Assembly.IsElemAbelian 2 V →
      ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) →
      ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
      ⁅V, Subgroup.zpowers c⁆ ⊓
          pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥ →
      ∀ b ∈ A ⊓ L, b ≠ 1 →
        Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))

namespace Proof17Res11

variable {G : Type} [Group G] [Finite G]

theorem card_le_three_of_pRank_le_one {K E : Subgroup G} (hK : CFSG.Open.pRank 3 K ≤ 1)
    (hEK : E ≤ K) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank 3 K :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three K)
      ⟨E, hEK, hE, hk⟩
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hkle.trans hK)
    _ = 3 := by norm_num

theorem mem_zpowers_of_commute_of_pRank {K : Subgroup G} (hK : CFSG.Open.pRank 3 K ≤ 1)
    {x z : G} (hxK : x ∈ K) (hzK : z ∈ K) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hxz : x * z = z * x) : x ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers z) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hE := Sec15.isElemAbelian_sup_zpowers hZ hx3 fun e he => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ((Commute.zpow_left hxz.symm k).eq)
  have hcard := card_le_three_of_pRank_le_one hK
    (sup_le (Subgroup.zpowers_le.mpr hzK) (Subgroup.zpowers_le.mpr hxK)) hE
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have heq : Subgroup.zpowers z = Subgroup.zpowers z ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hord]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem mem_zpowers_of_mem_pGroup {K P : Subgroup G} (hK : CFSG.Open.pRank 3 K ≤ 1)
    (hP3 : IsPGroup 3 P) (hPK : P ≤ K) {c y : G} (hcP : c ∈ P) (hyP : y ∈ P) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hy3 : y ^ 3 = 1) : y ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial P := ⟨⟨⟨c, hcP⟩, 1, fun h1 => hc1 (congrArg Subtype.val h1)⟩⟩
  have hZnt := hP3.center_nontrivial
  have h3Z : 3 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨b, hb⟩ := (hP3.to_subgroup (Subgroup.center P)).exists_card_eq
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hb
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hb
    rw [hb]
    exact dvd_pow_self 3 hb0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 3 h3Z
  set z' : G := ((z : P) : G) with hz'
  have hz'P : z' ∈ P := (z : P).2
  have hz'3 : z' ^ 3 = 1 := by
    rw [hz', ← Subgroup.coe_pow, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]
    rfl
  have hz'1 : z' ≠ 1 := by
    intro h1
    have hz1 : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hcomm : ∀ y ∈ P, y * z' = z' * y := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨y, hy⟩)
  have hmem : ∀ y ∈ P, y ^ 3 = 1 → y ∈ Subgroup.zpowers z' := fun y hy hy3 =>
    mem_zpowers_of_commute_of_pRank hK (hPK hy) (hPK hz'P) hy3 hz'3 hz'1 (hcomm y hy)
  have hzc : Subgroup.zpowers z' = Subgroup.zpowers c := by
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers z' :=
      Subgroup.zpowers_le.mpr (hmem c hcP hc3)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hc3 hc1,
      orderOf_eq_prime hz'3 hz'1]
  rw [← hzc]
  exact hmem y hyP hy3

theorem exists_conj_mem_zpowers_of_pRank {X : Subgroup G} (hX : CFSG.Open.pRank 3 X ≤ 1)
    {c y : G} (hcX : c ∈ X) (hyX : y ∈ X) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hy3 : y ^ 3 = 1) :
    ∃ g ∈ X, g * y * g⁻¹ ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : (⟨c, hcX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hy3' : (⟨y, hyX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  obtain ⟨S, hcS⟩ := (isPGroup_zpowers_of_pow_three hc3').exists_le_sylow
  obtain ⟨S', hyS'⟩ := (isPGroup_zpowers_of_pow_three hy3').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X S' S
  have hz : g * ⟨y, hyX⟩ * g⁻¹ ∈ (S : Subgroup ↥X) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, hyS' (Subgroup.mem_zpowers _), rfl⟩
  set SG : Subgroup G := (S : Subgroup ↥X).map X.subtype with hSG
  have hSG3 : IsPGroup 3 SG := S.isPGroup'.map X.subtype
  have hSGX : SG ≤ X := Subgroup.map_subtype_le _
  have hcSG : c ∈ SG := ⟨⟨c, hcX⟩, hcS (Subgroup.mem_zpowers _), rfl⟩
  have hySG : (g : G) * y * (g : G)⁻¹ ∈ SG := ⟨_, hz, by simp⟩
  have hgy3 : ((g : G) * y * (g : G)⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; group
  exact ⟨g, g.2, mem_zpowers_of_mem_pGroup hX hSG3 hSGX hcSG hySG hc3 hc1 hgy3⟩

theorem mul_conj_mul_conj_eq_one {V : Subgroup G} {c : G} (hc3 : c ^ 3 = 1) (hV : IsPGroup 2 V)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hcV : c ∈ Subgroup.normalizer (V : Set G)) {u : G}
    (hu : u ∈ ⁅V, Subgroup.zpowers c⁆) :
    u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUV : ⁅V, Subgroup.zpowers c⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcV)
  have hcU : c ∈ Subgroup.normalizer ((⁅V, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of (Γ := Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcV)
      Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card V) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_zpowers_of_pow_three hc3)
    rw [hn, hm]
    exact Nat.Coprime.pow m n (by norm_num)
  have hfit := CFSG.RankThree.Coprime.commutator_inf_centralizer_eq_bot hVab
    (Subgroup.zpowers_le.mpr hcV) hcop
  rw [Subgroup.commutator_comm] at hfit
  have hu1 : c * u * c⁻¹ ∈ ⁅V, Subgroup.zpowers c⁆ := conj_mem hcU hu
  have hu2 : c * (c * u * c⁻¹) * c⁻¹ ∈ ⁅V, Subgroup.zpowers c⁆ := conj_mem hcU hu1
  have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
  have e1 : c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = u := by
    rw [show c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * u * (c * c * c)⁻¹ by group,
      hc3']
    group
  have hfix : c * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) * c⁻¹ =
      u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) := by
    rw [show c * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) * c⁻¹ =
        (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) * (c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹) by
        group, e1, hVab _ (mul_mem (hUV hu1) (hUV hu2)) u (hUV hu)]
    exact (mul_assoc _ _ _).symm
  have hcen : u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    calc u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) * c =
        c * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) * c⁻¹ * c := by rw [hfix]
      _ = c * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) := by group
  have hmem : u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈
      ⁅V, Subgroup.zpowers c⁆ ⊓ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    ⟨mul_mem (mul_mem hu hu1) hu2, hcen⟩
  rw [hfit] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem mem_of_normalClosureIn {K U : Subgroup G} {c : G} (hcK : c ∈ K) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hrank : CFSG.Open.pRank 3 (normalClosureIn K c) ≤ 1) (hUK : U ≤ K)
    (hUU : U = ⁅U, Subgroup.zpowers c⁆) (hUO : ¬ U ≤ pPrimeCoreOf 3 K) :
    U ≤ normalClosureIn K c ∧ ∀ C : Subgroup G, C ≤ normalClosureIn K c →
      normalClosureIn K c ≤ Subgroup.normalizer (C : Set G) → U ≤ C → c ∈ C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := normalClosureIn K c with hXdef
  have hcX : c ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by group⟩
  have hXK : X ≤ K := by
    rw [hXdef, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem hg hcK) (inv_mem hg)
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := Proof17Res8.le_normalizer_normalClosureIn' K c
  have hUX : U ≤ X := by
    rw [hUU, Subgroup.commutator_le]
    intro u hu y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have huc : u * c * u⁻¹ ∈ X := Subgroup.subset_closure ⟨u, hUK hu, rfl⟩
    rw [commutatorElement_def, show u * c ^ k * u⁻¹ = (u * c * u⁻¹) ^ k by rw [conj_zpow]]
    exact mul_mem (zpow_mem huc k) (inv_mem (zpow_mem hcX k))
  have hOX : pPrimeCoreOf 3 X ≤ pPrimeCoreOf 3 K :=
    le_pPrimeCoreOf ((pPrimeCoreOf_le 3 X).trans hXK)
      (hKX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)) (coprime_card_pPrimeCoreOf 3 X)
  refine ⟨hUX, fun C hCX hXC hUC => ?_⟩
  by_cases h3 : 3 ∣ Nat.card C
  · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
    have hy3 : (y : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one]
      rfl
    have hy1 : (y : G) ≠ 1 := by
      intro h1
      have : y = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hy
      exact absurd hy (by norm_num)
    obtain ⟨g, hgX, hgy⟩ := exists_conj_mem_zpowers_of_pRank hrank hcX (hCX y.2) hc3 hc1 hy3
    have hgyC : g * (y : G) * g⁻¹ ∈ C := conj_mem (hXC hgX) y.2
    have hgy1 : g * (y : G) * g⁻¹ ≠ 1 := by
      intro h1
      apply hy1
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    have hgy3 : (g * (y : G) * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; group
    have heq : Subgroup.zpowers (g * (y : G) * g⁻¹) = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hc3 hc1,
          orderOf_eq_prime hgy3 hgy1])
    have hcmem : c ∈ Subgroup.zpowers (g * (y : G) * g⁻¹) := heq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hgyC) hcmem
  · exfalso
    apply hUO
    have hCO : C ≤ pPrimeCoreOf 3 X :=
      le_pPrimeCoreOf hCX hXC ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    exact hUC.trans (hCO.trans hOX)

theorem pPrimeCoreOf_centralizer_le_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h176 : Item176 A (lB A) c L)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {T U : Subgroup G}
    (hTM : T ≤ Subgroup.normalizer (Y₀ : Set G))
    (hMT : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (T : Set G))
    (hT2 : IsPGroup 2 T) (hUT : U ≤ T) (hUab : ∀ u ∈ U, ∀ w ∈ U, u * w = w * u)
    (hU2 : ∀ u ∈ U, u * u = 1) (hcU : c ∈ Subgroup.normalizer (U : Set G))
    (hUc : ∀ u ∈ U, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) = 1)
    (hUU : U = ⁅U, Subgroup.zpowers c⁆) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hUb : U ≤ Subgroup.centralizer ({b} : Set G))
    (hUO : ¬ U ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))
    (hsol : Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set Cb := Subgroup.centralizer ({b} : Set G) with hCbdef
  set O := pPrimeCoreOf 3 Cb with hOdef
  set Xb := normalClosureIn Cb c with hXbdef
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : c ^ 3 = 1 := pow_three_of_std h hcA
  have hc1 : c ≠ 1 := h.toSec13Data.ne_one
  have hACb : A ≤ Cb := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hbA)
  have hcCb : c ∈ Cb := hACb hcA
  have hCbne : Cb ≠ ⊤ :=
    centralizer_singleton_ne_top h.toSec14Std.isSimpleGroup h.toSec14Std.nonabelian hb1
  have hrank : CFSG.Open.pRank 3 Xb = 1 := (h176 hΩ).1 Cb hCbne hcCb
  have hcM : c ∈ M := h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hCcM : Subgroup.centralizer ({c} : Set G) ≤ M :=
    (centralizer_singleton_le_normalizer_zpowers c).trans h.normalizer_c_le
  have hcX : c ∈ Xb := Subgroup.subset_closure ⟨1, one_mem _, by group⟩
  have hXbCb : Xb ≤ Cb := by
    rw [hXbdef, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem hg hcCb) (inv_mem hg)
  obtain ⟨hUX, hCX⟩ := mem_of_normalClosureIn hcCb hc3 hc1 hrank.le hUb hUU hUO
  have hOQ : O ∈ scriptQ A (lB A) := Proof172.pPrimeCoreOf_centralizer_mem_scriptQ hA hbA
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  set n := Nat.card O with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  have hcard : n = 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) :=
    (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hm : Odd (n / 2 ^ n.factorization 2) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hn0)
  refine le_of_isSolvable (Γ := Cb) hsol (le_normalizer_pPrimeCoreOf 3 Cb) hcard ?_ ?_
  ·
    intro R P hRP hPO hΓR hΓP hPP hodd hRM
    exact le_of_odd_section hm hRP hPP hodd
      (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le hPO))) hRM hc3 hcM hCcM hcX hUX
      (hXbCb.trans hΓP) (hXbCb.trans hΓR) hUT hT2 hMT hU2 (hUT.trans hTM) hcU hUab hUc hCX
  ·
    intro R P hRP hPO hΓR hΓP hPP h2 hRM
    have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
      Subgroup.mem_normalizer_fintype fun r hr =>
        conj_mem_of_commutator_le hPP hx (hRP hr) hr
    refine le_of_two_section hRP hPR h2 hRM hA.isPGroup (hACb.trans hΓP)
      (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le hPO))) fun S hSP hS2 hAS => ?_
    have hSQ : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le hOQ (hSP.trans hPO) hAS
    obtain ⟨T', hST, hT'⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2)))
      (a := S) ⟨⟨hSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩
    exact hST.trans (h.qStar_le T' hT')

theorem pPrimeCoreOf_centralizer_le {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h176 : Item176 A (lB A) c L)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {V : Subgroup G}
    (hVM : V ≤ Subgroup.normalizer (Y₀ : Set G))
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V)
    (hUC : ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (hU1 : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥)
    (hUB : ⁅V, Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥)
    {b : G} (hb : b ∈ A ⊓ L) (hb1 : b ≠ 1)
    (hsol : Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)))) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set U := ⁅V, Subgroup.zpowers c⁆ with hUdef
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : c ^ 3 = 1 := pow_three_of_std h hcA
  have hcM : c ∈ M := h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hVab.2 v hv
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := hMV hcM
  have hUV : U ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcV)
  have hcU : c ∈ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of (Γ := Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcV)
      Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hUU : U = ⁅U, Subgroup.zpowers c⁆ :=
    eq_commutator_of_le_commutator hc3 hV2 hVcomm hcV hcU le_rfl
  have hUCb : U ≤ Subgroup.centralizer ({b} : Set G) := fun u hu =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb) (hUC hu)
  have hUO : ¬ U ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    intro hle
    apply hU1
    rw [eq_bot_iff, ← hUB]
    exact (le_inf le_rfl hle).trans (Proof17Res.inf_pPrimeCoreOf_le hb hUC)
  exact pPrimeCoreOf_centralizer_le_of h h176 hΩ hVM hMV hV2 hUV
    (fun u hu w hw => hVcomm u (hUV hu) w (hUV hw)) (fun u hu => hVsq u (hUV hu)) hcU
    (fun u hu => mul_conj_mul_conj_eq_one hc3 hV2 hVcomm hcV hu) hUU hb.1 hb1 hUCb hUO hsol

theorem xb172_le_sup {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hbal : Step143Balance)
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) (hcL : c ∉ L) {b : G}
    (hb : b ∈ A ⊓ L) (hb1 : b ≠ 1) {X : Subgroup G}
    (hX : ∀ D : Subgroup G, IsHyperplane A D → b ∈ D → lB A D ≤ X)
    (hOAX : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (X : Set G)) :
    xb172 A b ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbL : b ∈ L := hb.2
  have hbA : b ∈ A := hb.1
  have hbΩ : Subgroup.zpowers b ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro hbc
    exact hcL ((Subgroup.zpowers_le.mpr hbL) (hbc ▸ Subgroup.mem_zpowers c))
  set Cb := Subgroup.centralizer ({b} : Set G) with hCbdef
  set Ob := pPrimeCoreOf 3 Cb with hObdef
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOAdef
  have hΔ : delta A (lB A) Cb ≤ Ob ⊔ OA ⊔ X :=
    Proof17Res9.delta_le_sup_of_lB_le hbal h.toSec14Std hbA hb1 hbΩ fun D hD hbD =>
      (hX D hD hbD).trans le_sup_right
  have hCAb : Subgroup.centralizer (A : Set G) ≤ Cb :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
  have hOAOb : OA ≤ Subgroup.normalizer (Ob : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans hCAb).trans (le_normalizer_pPrimeCoreOf 3 Cb)
  have hOAJ : OA ≤ Subgroup.normalizer ((Ob ⊔ X : Subgroup G) : Set G) :=
    Sec14.le_normalizer_sup hOAOb hOAX
  have hOA3 : ¬ 3 ∣ Nat.card OA :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hO3 : oPrimeResidualOf 3 (delta A (lB A) Cb) ≤ Ob ⊔ X := by
    rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hyD, k, hyk⟩
    have hy : y ∈ OA ⊔ (Ob ⊔ X) := by
      have := hΔ hyD
      rwa [sup_comm Ob OA, sup_assoc] at this
    exact Proof176Steps.mem_of_three_element_sup hOAJ hOA3 hy hyk
  exact sup_le le_sup_left hO3

theorem xb172_le_residual {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hbal : Step143Balance)
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L) {b : G} (hb : b ∈ A ⊓ L)
    (hb1 : b ≠ 1) :
    xb172 A b ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have h14 : Sec14Std G A c L := h.toSec14Std
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD13.mem_partTwoE
  have hcA : c ∈ A := hD13.mem_A
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set Cb := Subgroup.centralizer ({b} : Set G) with hCbdef
  set Lb := inSubgroup perfectResidual (L ⊓ Cb) with hLbdef
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  have hCAb : Subgroup.centralizer (A : Set G) ≤ Cb :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb.1)
  have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)
  have hOALb : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (Lb : Set G) := by
    have hOAL : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (L : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans hCAc).trans (centralizer_le_normalizer_of_three_dvd h14 h3L)
    have hOACb : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (Cb : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans hCAb).trans Subgroup.le_normalizer
    exact (Late.le_normalizer_inf hOAL hOACb).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  exact xb172_le_sup hbal h hΩ hcL hb hb1 (X := Lb) (fun D hD hbD =>
    Proof17Res9.lB_le_ld hΩ hc3 hcL hD13.mem_lA hb.2 hcA hAcomm hD.1 hbD) hOALb

theorem xb172_le {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hbal : Step143Balance)
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hcL : c ∉ L) {b : G} (hb : b ∈ A ⊓ L)
    (hb1 : b ≠ 1)
    (hOM : pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G)) :
    xb172 A b ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hLbM : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    (Subgroup.map_subtype_le _).trans (inf_le_left.trans (h.le_y0.trans Subgroup.le_normalizer))
  exact (xb172_le_residual hbal h hΩ h9 hcL hb hb1).trans (sup_le hOM hLbM)

theorem le_normalizer_xB172 {A B K : Subgroup G}
    (h : ∀ b ∈ B, b ≠ 1 → K ≤ Subgroup.normalizer (xb172 A b : Set G)) :
    K ≤ Subgroup.normalizer (xB172 A B : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : xB172 A B ≤ (xB172 A B).comap (MulAut.conj g).toMonoidHom :=
    iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => fun y hy =>
      (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)) :
        xb172 A b ≤ xB172 A B) (conj_mem (h b hb hb1 hg) hy)
  exact hle hx

theorem centralizer_le_normalizer_xB172_of_lB_eq_bot {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (hbal : Step143Balance) (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hcL : c ∉ L)
    (hbot : ∀ D : Subgroup G, IsHyperplane A D → lB A D = ⊥) :
    Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (xB172 A (A ⊓ L) : Set G) := by
  refine le_normalizer_xB172 fun b hb hb1 => ?_
  have hle := xb172_le_sup hbal h hΩ hcL hb hb1 (X := ⊥) (fun D hD _ => (hbot D hD).le)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
  have heq : xb172 A b = pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
    le_antisymm (hle.trans (by rw [sup_bot_eq])) le_sup_left
  rw [heq]
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)).trans
    (le_normalizer_pPrimeCoreOf 3 _)

end Proof17Res11

namespace Proof17Res11

variable {G : Type} [Group G] [Finite G]

theorem not_mem_L_of_config {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V)
    (hUC : ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (hU1 : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥) : c ∉ L := by
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : c ^ 3 = 1 := pow_three_of_std h hcA
  have hcM : c ∈ Subgroup.normalizer (Y₀ : Set G) :=
    h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hcNV : c ∈ Subgroup.normalizer (V : Set G) := hMV hcM
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcU : c ∈ Subgroup.normalizer ((⁅V, Subgroup.zpowers c⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of (Γ := Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcNV)
      Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hUU := eq_commutator_of_le_commutator hc3 hV2 hVcomm hcNV hcU le_rfl
  intro hcL
  apply hU1
  have hcB : Subgroup.zpowers c ≤ A ⊓ L := Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩
  rw [hUU, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hUC.trans (Subgroup.centralizer_le hcB)

theorem xb172_le_of_config {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (hbal : Step143Balance)
    (h : Sec17Std G A c L Y₀) (h176 : Item176 A (lB A) c L)
    (hΩ : omegaA A = {Subgroup.zpowers c}) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    {V : Subgroup G} (hVM : V ≤ Subgroup.normalizer (Y₀ : Set G))
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V)
    (hUC : ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (hU1 : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥)
    (hUB : ⁅V, Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥)
    (hsol : ∀ b ∈ A ⊓ L, b ≠ 1 →
      Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))))
    {b : G} (hb : b ∈ A ⊓ L) (hb1 : b ≠ 1) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      xb172 A b ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hOM := pPrimeCoreOf_centralizer_le h h176 hΩ hVM hMV hVab hUC hU1 hUB hb hb1
    (hsol b hb hb1)
  exact ⟨hOM, xb172_le hbal h hΩ h9 (not_mem_L_of_config h hMV hVab hUC hU1) hb hb1 hOM⟩

theorem false_of_le_normalizer {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G} (hVM : V ≤ Subgroup.normalizer (Y₀ : Set G))
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Assembly.IsElemAbelian 2 V)
    (hUC : ⁅V, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (hU1 : ⁅V, Subgroup.zpowers c⁆ ≠ ⊥)
    (hUB : ⁅V, Subgroup.zpowers c⁆ ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) = ⊥)
    {N : Subgroup G} (hYN : Y₀ ≤ N) (hNM : N ≤ Subgroup.normalizer (Y₀ : Set G))
    (hCN : Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (N : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set B := A ⊓ L with hBdef
  set U := ⁅V, Subgroup.zpowers c⁆ with hUdef
  set X := normalClosureIn (Subgroup.centralizer (B : Set G)) c with hXdef
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hc3 : c ^ 3 = 1 := pow_three_of_std h hcA
  have hcM : c ∈ M := h.normalizer_c_le (Subgroup.le_normalizer (Subgroup.mem_zpowers c))
  have hcNV : c ∈ Subgroup.normalizer (V : Set G) := hMV hcM
  have hUV : U ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcNV)
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcU : c ∈ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of (Γ := Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcNV)
      Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hUU : U = ⁅U, Subgroup.zpowers c⁆ :=
    eq_commutator_of_le_commutator hc3 hV2 hVcomm hcNV hcU le_rfl
  have hcB : c ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (h.toSec13Data.commute hcA hx.1).symm
  have hXCB : X ≤ Subgroup.centralizer (B : Set G) := by
    rw [hXdef, normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem hg hcB) (inv_mem hg)
  have hACB : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => (h.toSec13Data.commute ha hx.1).symm
  have hXAN : X ⊔ A ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (hXCB.trans hCN) (hACB.trans hCN)
  have hXM : X ≤ M :=
    le_sup_left.trans (Proof172.le_M_of_le_normalizer h hYN hNM le_sup_right hXAN)
  have hcX : c ∈ X := Subgroup.subset_closure ⟨1, one_mem _, by group⟩
  have hUX : U ≤ X := by
    rw [hUU, Subgroup.commutator_le]
    intro u hu y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have huc : u * c * u⁻¹ ∈ X := Subgroup.subset_closure ⟨u, hUC hu, rfl⟩
    rw [commutatorElement_def, show u * c ^ k * u⁻¹ = (u * c * u⁻¹) ^ k by rw [conj_zpow]]
    exact mul_mem (zpow_mem huc k) (inv_mem (zpow_mem hcX k))
  have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM hMV hV2
  have hle : X ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer
        (hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)
  have hUO : U ≤ CFSG.Open.pCoreOf 2 X := fun u hu => hle ⟨hUX hu, hVO (hUV hu)⟩
  apply hU1
  rw [eq_bot_iff, ← hUB]
  exact le_inf le_rfl (hUO.trans (Proof17Res.pCoreOf_le_pPrimeCoreOf_centralizer hcB))

end Proof17Res11

end CFSG.RankThree.PartTwo.Sec17
