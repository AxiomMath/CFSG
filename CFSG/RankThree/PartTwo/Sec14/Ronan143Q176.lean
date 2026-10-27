module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Use
public import CFSG.RankThree.PartTwo.Sec17.Item176ProofTwo
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTwo
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec17.Item172Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step176CommQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Q ∈ scriptQ A (lB A), ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G),
      Q.map (MulAut.conj r).toMonoidHom ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      ∀ e ∈ Subgroup.closure {c, d}, e ∉ Subgroup.zpowers c → e ∉ Subgroup.zpowers d →
        ⁅Q.map (MulAut.conj r).toMonoidHom ⊓ Subgroup.centralizer ({e} : Set G),
          Subgroup.zpowers d⁆ ∈ scriptQ A (lB A)

@[expose] noncomputable def Step176OdQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ Q ∈ scriptQ A (lB A), Q ≤ Subgroup.centralizer ({d} : Set G) →
      Q = ⁅Q, Subgroup.zpowers c⁆ → Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))

section Steps

open Proof176Steps in
theorem step176OdQ_of (hbal : Step143Balance) : Step176OdQ := by
  intro G _ _ A c L Y₀ h hΩ _ d hdA hd1 hd3 Q hQ hQd hQc
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hdc : d ∉ Subgroup.zpowers c := fun hdc => hcL ((Subgroup.zpowers_le.mpr hd3.1) (by
    have := eq_zpowers_of_card_three (by rw [Nat.card_zpowers, hc]) hdc hd1
    exact this ▸ Subgroup.mem_zpowers c))
  exact hQc.le.trans (commutator_le_pPrimeCoreOf hbal h.toSec14Std hΩ hdA hdc h.c_mem
    (Subgroup.subset_closure (Set.mem_insert c {d})) hQ hQd)

open Proof176Steps in
theorem step176CommQ_of (hbal : Step143Balance) : Step176CommQ := by
  intro G _ _ A c L Y₀ h hΩ _ Q hQ d hdA hd1 hd3 r hr hQr e he hec _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h14 : Sec14Std G A c L := h.toSec14Std
  have hA : IsE27 A := h.isE27
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hc3 : c ^ 3 = 1 := h.c_pow_three
  have hcA : c ∈ A := h.c_mem
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hdL : d ∈ L := hd3.1
  have hdo : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  have hdc : d ∉ Subgroup.zpowers c := fun hdc => hcL ((Subgroup.zpowers_le.mpr hdL) (by
    have := eq_zpowers_of_card_three (by rw [Nat.card_zpowers, hc]) hdc hd1
    exact this ▸ Subgroup.mem_zpowers c))
  set B₀ := Subgroup.closure ({c, d} : Set G) with hB₀def
  have hBA : B₀ ≤ A := by
    rw [hB₀def, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcA
    · exact hdA
  have heA : e ∈ A := hBA he
  have hrH : r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := (Subgroup.mem_inf.mp hr).1
  have hrB : r ∈ Subgroup.normalizer (B₀ : Set G) := (Subgroup.mem_inf.mp hr).2
  set e' := r⁻¹ * e * r with he'def
  have he'B : e' ∈ B₀ := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hrB) e).mp he
    rwa [inv_inv] at this
  have he'A : e' ∈ A := hBA he'B
  have hφe' : (MulAut.conj r) e' = e := by
    rw [MulAut.conj_apply, he'def]
    group
  have he'c : e' ∉ Subgroup.zpowers c := by
    intro hmem
    apply hec
    have h1 := (Subgroup.mem_normalizer_iff.mp hrH e').mp hmem
    rwa [← MulAut.conj_apply, hφe'] at h1
  have he'1 : e' ≠ 1 := fun h1 => he'c (h1 ▸ one_mem _)
  have he'o : orderOf e' = 3 := orderOf_eq_prime (hA.1.2 e' he'A) he'1
  have hdcl : d ∈ Subgroup.closure ({c, e'} : Set G) := by
    have hle : Subgroup.closure ({c, e'} : Set G) ≤ B₀ := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.subset_closure (Set.mem_insert x {d})
      · exact he'B
    have heq : Subgroup.closure ({c, e'} : Set G) = B₀ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hB₀def, card_closure_pair hc hdo (h.toSec13Data.commute hcA hdA) hdc,
        card_closure_pair hc he'o (h.toSec13Data.commute hcA he'A) he'c]
    rw [heq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  set Q₁ := Q ⊓ Subgroup.centralizer ({e'} : Set G) with hQ₁def
  have hAQ₁ : A ≤ Subgroup.normalizer (Q₁ : Set G) :=
    le_normalizer_inf hQ.1.2.2 (Proof176.le_normalizer_centralizer hA he'A)
  have hQ₁ : Q₁ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ inf_le_left hAQ₁
  have hQ₁d : ⁅Q₁, Subgroup.zpowers d⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({e'} : Set G)) :=
    commutator_le_pPrimeCoreOf hbal h14 hΩ he'A he'c hdA hdcl hQ₁ inf_le_right
  have h3L : 3 ∣ Nat.card L := hdo ▸ Subgroup.orderOf_dvd_natCard L hdL
  have hrL : r ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L hrH
  have hcd_eq : B₀ = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [hB₀def, show ({c, d} : Set G) = {c} ∪ {d} from rfl, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  have hcCd : c ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h.toSec13Data.commute hdA hcA
  have hrd : r * d * r⁻¹ ∈ Subgroup.zpowers d := by
    have h1 : r * d * r⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [← hcd_eq]
      exact (Subgroup.mem_normalizer_iff.mp hrB d).mp
        (Subgroup.subset_closure (Set.mem_insert_of_mem c rfl))
    obtain ⟨k, ℓ, hℓ, hkℓ⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcCd h1
    have hrdL : r * d * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL d).mp hdL
    have hck : c ^ k ∈ L := by
      have : c ^ k = r * d * r⁻¹ * ℓ⁻¹ := by rw [hkℓ]; group
      rw [this]
      exact mul_mem hrdL (inv_mem (Subgroup.zpowers_le.mpr hdL hℓ))
    rw [hkℓ, KFacts.KS14.zpow_eq_one_of_mem hcL hc3 hck, one_mul]
    exact hℓ
  have hzd : (Subgroup.zpowers d).map (MulAut.conj r).toMonoidHom = Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hrd) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  have hR : Q.map (MulAut.conj r).toMonoidHom ⊓ Subgroup.centralizer ({e} : Set G) =
      Q₁.map (MulAut.conj r).toMonoidHom := by
    rw [hQ₁def, Subgroup.map_inf _ _ _ (MulAut.conj r).injective,
      map_centralizer_singleton (MulAut.conj r) e', hφe']
  have hWO : ⁅Q.map (MulAut.conj r).toMonoidHom ⊓ Subgroup.centralizer ({e} : Set G),
      Subgroup.zpowers d⁆ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) := by
    rw [hR, ← hzd, ← Subgroup.map_commutator]
    refine (Subgroup.map_mono hQ₁d).trans (le_of_eq ?_)
    rw [map_pPrimeCoreOf 3 (MulAut.conj r), map_centralizer_singleton (MulAut.conj r) e', hφe']
  have hAR : A ≤ Subgroup.normalizer
      ((Q.map (MulAut.conj r).toMonoidHom ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :
        Set G) :=
    le_normalizer_inf hQr.2.2 (Proof176.le_normalizer_centralizer hA heA)
  have hAW := Sec14.le_normalizer_commutator hAR (Proof176.le_normalizer_zpowers hA hdA)
  have hOO := (Sec14.sup_pPrimeCoreOf_mem_scriptQ (LB := lB A) hA h14.maximal_isElemAbelian
    heA).1
  exact mem_scriptQ_of_le hOO (hWO.trans le_sup_left) hAW

end Steps

section Item176Two

variable {G : Type} [Group G] [Finite G]

open Proof176 in
theorem rank3II_17_6_two_ofQ {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h142 : Concl142 A (lB A)) (h143c : Concl143 A (lB A))
    (hα : Step176CommQ) (hγ : Step176OdQ) (hΩ : omegaA A = {Subgroup.zpowers c}) :
    ∀ Q ∈ scriptQ A (lB A),
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
      ∀ r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G),
        Q.map (MulAut.conj r).toMonoidHom ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
          Q.map (MulAut.conj r).toMonoidHom ∈ scriptQ A (lB A) := by
  intro Q hQ hJ d hdA hd1 hd3 r hr hQr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.isE27
  have h1443 : Item1443 A (lB A) :=
    rank3II_14_4_3_reduction h142 h143c
  have hc : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hc3 : c ^ 3 = 1 := h.c_pow_three
  have hcA : c ∈ A := h.c_mem
  have hcΩ : Subgroup.zpowers c ∈ omegaA A := h.zpowers_mem_omegaA
  set Y := Q.map (MulAut.conj r).toMonoidHom with hYdef
  have hY3 : ¬ 3 ∣ Nat.card Y := (isPiSubgroup_piCompl_iff Nat.prime_three Y).mp hQr.2.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hQr.2.2
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
    obtain ⟨φJ⟩ := hJ
    exact center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data hZ
  have hdL : d ∈ L := hd3.1
  have hd3' : d ^ 3 = 1 := hA.1.2 d hdA
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3' hd1
  have hLc : L ⊓ Subgroup.zpowers c = ⊥ := inf_zpowers_eq_bot hc hcL
  have hdc : d ∉ Subgroup.zpowers c := fun hmem => hd1 (by
    have : d ∈ L ⊓ Subgroup.zpowers c := ⟨hdL, hmem⟩
    rwa [hLc, Subgroup.mem_bot] at this)
  set B₀ := Subgroup.closure ({c, d} : Set G) with hB₀def
  have hB₀eq : B₀ = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [hB₀def, show ({c, d} : Set G) = {c} ∪ {d} from rfl, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  have hcdcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hA.1.1.is_comm.comm
      ⟨x, Subgroup.zpowers_le.mpr hcA hx⟩ ⟨y, Subgroup.zpowers_le.mpr hdA hy⟩)
  have hB₀ : IsHyperplane A B₀ := by
    refine ⟨hB₀eq ▸ sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA), ?_⟩
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcdcomm
    rw [inf_zpowers_eq_bot hdo hdc, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      Nat.card_zpowers, hc, hdo] at hcard
    rw [hA.2, hB₀eq, hcard]
  have h3L : 3 ∣ Nat.card L := hdo ▸ (Subgroup.orderOf_dvd_natCard L hdL)
  have hrH : r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := (Subgroup.mem_inf.mp hr).1
  have hrB : r ∈ Subgroup.normalizer (B₀ : Set G) := (Subgroup.mem_inf.mp hr).2
  have hrL : r ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L hrH
  have hrd : r * d * r⁻¹ ∈ Subgroup.zpowers d := by
    have h1 : r * d * r⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [← hB₀eq]
      exact (Subgroup.mem_normalizer_iff.mp hrB d).mp
        (Subgroup.subset_closure (Set.mem_insert_of_mem c rfl))
    have hcC : c ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hcdcomm c (Subgroup.mem_zpowers c) y hy).symm
    obtain ⟨k, ℓ, hℓ, hkℓ⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hcC h1
    have hrdL : r * d * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL d).mp hdL
    have hck : c ^ k ∈ L := by
      have : c ^ k = r * d * r⁻¹ * ℓ⁻¹ := by rw [hkℓ]; group
      rw [this]
      exact mul_mem hrdL (inv_mem (Subgroup.zpowers_le.mpr hdL hℓ))
    rw [hkℓ, KFacts.KS14.zpow_eq_one_of_mem hcL hc3 hck, one_mul]
    exact hℓ
  have hzd : Subgroup.zpowers (r * d * r⁻¹) = Subgroup.zpowers d := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hrd) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, show r * d * r⁻¹ = (MulAut.conj r) d from rfl,
      MulEquiv.orderOf_eq]
  have hCd : (Subgroup.centralizer ({d} : Set G)).map (MulAut.conj r).toMonoidHom =
      Subgroup.centralizer ({d} : Set G) := by
    rw [map_centralizer_singleton (MulAut.conj r) d]
    exact centralizer_singleton_eq_of_zpowers_eq hzd
  have hOd : (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))).map
      (MulAut.conj r).toMonoidHom = pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
    rw [map_pPrimeCoreOf 3 (MulAut.conj r), hCd]
  have hcr : (Subgroup.zpowers c).map (MulAut.conj r).toMonoidHom = Subgroup.zpowers c :=
    Late.map_conj_eq_of_mem_normalizer hrH
  have hYd : Y ⊓ Subgroup.centralizer ({d} : Set G) ∈ scriptQ A (lB A) := by
    set Yd := Y ⊓ Subgroup.centralizer ({d} : Set G) with hYddef
    have hAYd : A ≤ Subgroup.normalizer (Yd : Set G) :=
      le_normalizer_inf hAY (le_normalizer_centralizer hA hdA)
    have hYd3 : ¬ 3 ∣ Nat.card Yd := fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le
      inf_le_left))
    set Q₁ := Q ⊓ Subgroup.centralizer ({d} : Set G) with hQ₁def
    have hYdQ₁ : Yd = Q₁.map (MulAut.conj r).toMonoidHom := by
      rw [hQ₁def, Subgroup.map_inf _ _ _ (MulAut.conj r).injective, hCd]
    have hAQ₁ : A ≤ Subgroup.normalizer (Q₁ : Set G) :=
      le_normalizer_inf hQ.1.2.2 (le_normalizer_centralizer hA hdA)
    have hQ₁ : Q₁ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ inf_le_left hAQ₁
    set Q₂ := ⁅Q₁, Subgroup.zpowers c⁆ with hQ₂def
    have hQ₂Q₁ : Q₂ ≤ Q₁ := commutator_le_left hcA hAQ₁
    have hAQ₂ : A ≤ Subgroup.normalizer (Q₂ : Set G) :=
      Sec14.le_normalizer_commutator hAQ₁ (le_normalizer_zpowers hA hcA)
    have hQ₂ : Q₂ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ₁ hQ₂Q₁ hAQ₂
    have hQ₁3 : ¬ 3 ∣ Nat.card Q₁ :=
      (isPiSubgroup_piCompl_iff Nat.prime_three Q₁).mp hQ₁.1.2.1
    have hQ₂idem : Q₂ = ⁅Q₂, Subgroup.zpowers c⁆ :=
      (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
        (Subgroup.zpowers c) Q₁ (hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA)) hQ₁3
        (Subgroup.zpowers_le.mpr (hAQ₁ hcA))).symm
    have hQ₂O : Q₂ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) :=
      hγ G A c L Y₀ h hΩ hJ d hdA hd1 hd3 Q₂ hQ₂ (hQ₂Q₁.trans inf_le_right) hQ₂idem
    have hP₁ : ⁅Yd, Subgroup.zpowers c⁆ ∈ scriptQ A (lB A) := by
      have heq : ⁅Yd, Subgroup.zpowers c⁆ = Q₂.map (MulAut.conj r).toMonoidHom := by
        rw [hQ₂def, Subgroup.map_commutator, hcr, ← hYdQ₁]
      refine mem_scriptQ_of_le (Proof172.pPrimeCoreOf_centralizer_mem_scriptQ hA hdA) ?_
        (Sec14.le_normalizer_commutator hAYd (le_normalizer_zpowers hA hcA))
      rw [heq, ← hOd]
      exact Subgroup.map_mono hQ₂O
    have hP₂ : Yd ⊓ Subgroup.centralizer ({c} : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le_centralizer h142 hcΩ
        (fun h3 => hYd3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
        (le_normalizer_inf hAYd (le_normalizer_centralizer hA hcA)) inf_le_right
    have hdec := eq_commutator_sup hA hcA hYd3 hAYd
    rw [hdec]
    refine sup_mem_scriptQ h1443 hdA hd1 hP₁ hP₂
      ((commutator_le_left hcA hAYd).trans inf_le_right) (inf_le_left.trans inf_le_right) ?_
    rw [← hdec]
    exact mem_invariantPiSubgroups_of_le hY3 inf_le_left hAYd
  refine mem_scriptQ_of_forall_centralizer hA hB₀ hQr fun e he he1 => ?_
  have heA : e ∈ A := hB₀.1 he
  have hAYe : A ≤ Subgroup.normalizer
      ((Y ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf hAY (le_normalizer_centralizer hA heA)
  have hYe3 : ¬ 3 ∣ Nat.card (Y ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :=
    fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  by_cases hec : e ∈ Subgroup.zpowers c
  ·
    have hze : Subgroup.zpowers e = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hec) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hc, orderOf_eq_prime (hA.1.2 e heA) he1]
    rw [centralizer_singleton_eq_of_zpowers_eq hze]
    rw [centralizer_singleton_eq_of_zpowers_eq hze] at hAYe hYe3
    exact mem_scriptQ_of_le_centralizer h142 hcΩ hYe3 hAYe inf_le_right
  · set Ye := Y ⊓ Subgroup.centralizer ({e} : Set G) with hYedef
    have hP₁ : ⁅Ye, Subgroup.zpowers d⁆ ∈ scriptQ A (lB A) := by
      by_cases hed : e ∈ Subgroup.zpowers d
      ·
        have hze : Subgroup.zpowers e = Subgroup.zpowers d := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hed) ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hdo, orderOf_eq_prime (hA.1.2 e heA) he1]
        have hbot : ⁅Ye, Subgroup.zpowers d⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x hx
          have hx' := hx.2
          rw [centralizer_singleton_eq_of_zpowers_eq hze] at hx'
          show x ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G)
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          exact hx'
        rw [hbot]
        exact bot_mem_scriptQ
      · exact hα G A c L Y₀ h hΩ hJ Q hQ d hdA hd1 hd3 r hr hQr e he hec hed
    have hP₂ : Ye ⊓ Subgroup.centralizer ({d} : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hYd (inf_le_inf_right _ inf_le_left)
        (le_normalizer_inf hAYe (le_normalizer_centralizer hA hdA))
    have hdec := eq_commutator_sup hA hdA hYe3 hAYe
    rw [hdec]
    refine sup_mem_scriptQ h1443 heA he1 hP₁ hP₂
      ((commutator_le_left hdA hAYe).trans inf_le_right) (inf_le_left.trans inf_le_right) ?_
    rw [← hdec]
    exact mem_invariantPiSubgroups_of_le hY3 inf_le_left hAYe

end Item176Two

section Item176Comp

variable {G : Type} [Group G] [Finite G]

theorem rank3II_17_6_of_compQ {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h175 : Item175 A c) (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hexcl : Step176Excl) (h142 : Concl142 A (lB A))
    (h143c : Concl143 A (lB A)) (hα : Step176CommQ) (hγ : Step176OdQ) :
    Item176 A (lB A) c L :=
  fun hΩ => ⟨rank3II_17_6_one_of_comp h h175 h432 h41 hexcl hΩ,
    rank3II_17_6_two_ofQ h h142 h143c hα hγ hΩ⟩

theorem item176R_of_compQ (h169 : Item169R) (h163 : Item163R) (h164 : Item164R)
    (hM : Claim17MR) (h175 : Item175R) (h432 : Sec4.Item4_32Comp)
    (h41 : Sec4.Item4_1LargePrime) (hexcl : Step176Excl) (h142 : Concl142S14)
    (h143c : Concl143S14) (hα : Step176CommQ) (hγ : Step176OdQ) : Item176R := by
  intro G _ _ A c L hR
  obtain ⟨Y₀, h0⟩ := exists_sec17Std hR (h169 G A c L hR) (h163 G A c L hR) (h164 G A c L hR)
    (hM G A c L hR)
  exact rank3II_17_6_of_compQ h0 (h175 G A c L hR) h432 h41 hexcl (h142 G A c L hR.toSec14Std)
    (h143c G A c L hR.toSec14Std) hα hγ

end Item176Comp

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
