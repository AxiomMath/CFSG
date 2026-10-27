module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148DInvObs
import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofW
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DInvTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem mem_zpowers_of_trivial {A L B Lb Q : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hc : IsLBConfig A B b d Lb)
    (hQ : IsPGroup 3 Q) (hAQ : A ≤ Q) (hQb : Q ≤ Subgroup.centralizer ({b} : Set G))
    {g : G} (hgQ : g ∈ Q) (hg3 : g ^ 3 = 1)
    (htriv : ∀ l ∈ Lb, l⁻¹ * (g * l * g⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Lb) :
    g ∈ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  obtain ⟨φJ⟩ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, -, hAb⟩ := j2_point_facts hS.toSec13Data ⟨φJ⟩
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLb.1
  have hZ : Subgroup.center (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hθ3' : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) Lb) := by
    rw [show inSubgroup (aschbacherSolvableCore 3) Lb =
      (aschbacherSolvableCore 3 ↥Lb).map Lb.subtype from rfl,
      Subgroup.card_map_of_injective Lb.subtype_injective]
    exact hθ3
  have hcf : ∀ f0 ∈ A ⊓ Lb, f0 * g = g * f0 := by
    intro f0 hf0
    have h1 := htriv f0 hf0.2
    have hwQ : f0⁻¹ * (g * f0 * g⁻¹) ∈ Q :=
      Q.mul_mem (Q.inv_mem (hAQ hf0.1)) (Q.mul_mem (Q.mul_mem hgQ (hAQ hf0.1)) (Q.inv_mem hgQ))
    obtain ⟨k, hk⟩ := hQ ⟨_, hwQ⟩
    have hk' : (f0⁻¹ * (g * f0 * g⁻¹)) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hw1 := eq_one_of_mem_of_pow_three_pow hθ3' h1 hk'
    have h2 : g * f0 * g⁻¹ = f0 := by
      calc g * f0 * g⁻¹ = f0 * (f0⁻¹ * (g * f0 * g⁻¹)) := by group
        _ = f0 := by rw [hw1, mul_one]
    calc f0 * g = g * f0 * g⁻¹ * g := by rw [h2]
      _ = g * f0 := by group
  have hgb : b * g = g * b := (Subgroup.mem_centralizer_singleton_iff.mp (hQb hgQ)).symm
  have hle : Subgroup.zpowers b ⊔ (A ⊓ Lb) ≤ Subgroup.centralizer ({g} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgb))
      fun f0 hf0 => Subgroup.mem_centralizer_singleton_iff.mpr (hcf f0 hf0)
  have hgA : g ∈ A := by
    refine Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian hg3 fun α hα => ?_
    have hα' : α ∈ Subgroup.zpowers b ⊔ (A ⊓ Lb) := hAb ▸ hα
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hα')
  have hbC : b ∈ Subgroup.centralizer ((A ⊓ Lb : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLbC hy.2)
  have hgsup : g ∈ Subgroup.zpowers b ⊔ (A ⊓ Lb) := hAb ▸ hgA
  obtain ⟨k, ℓ, hℓ, hgk⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hbC hgsup
  have hℓtriv : ∀ l ∈ Lb, l⁻¹ * (ℓ * l * ℓ⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Lb := by
    intro l hl
    have hgl : g * l * g⁻¹ ∈ Lb := by
      have h1 : l⁻¹ * (g * l * g⁻¹) ∈ Lb := Subgroup.map_subtype_le _ (htriv l hl)
      simpa using Lb.mul_mem hl h1
    have hbc : Commute b (g * l * g⁻¹) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLbC hgl)).symm
    have hbk := (Commute.zpow_left hbc k).eq
    have hℓg : ℓ * l * ℓ⁻¹ = g * l * g⁻¹ := by
      have hℓ' : ℓ = (b ^ k)⁻¹ * g := by rw [hgk]; group
      calc ℓ * l * ℓ⁻¹ = (b ^ k)⁻¹ * (g * l * g⁻¹) * b ^ k := by rw [hℓ']; group
        _ = (b ^ k)⁻¹ * (b ^ k * (g * l * g⁻¹)) := by rw [mul_assoc, ← hbk]
        _ = g * l * g⁻¹ := by group
    rw [hℓg]
    exact htriv l hl
  set ℓ' : ↥Lb := ⟨ℓ, hℓ.2⟩ with hℓ'
  have hmem : (ℓ' : ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) ∈
      Subgroup.center (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hz, hzc⟩ := hℓtriv l l.2
    have hz' : z = l⁻¹ * (ℓ' * l * ℓ'⁻¹) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzc
    have h2 : (l : ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) = ((ℓ' * l * ℓ'⁻¹ : ↥Lb) :
        ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) := QuotientGroup.eq.mpr (hz' ▸ hz)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    calc (l : ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) * ℓ' =
          ℓ' * l * (ℓ' : ↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb)⁻¹ * ℓ' := by rw [← h2]
      _ = ℓ' * l := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  have hℓ3 : ℓ' ^ 3 = 1 := Subtype.ext (by simpa using h.isE27'.1.2 ℓ hℓ.1)
  have hℓ1 : ℓ' = 1 := eq_one_of_mem_aschbacherSolvableCore hmem hℓ3
  have hℓ1' : ℓ = 1 := congrArg Subtype.val hℓ1
  rw [hgk, hℓ1', mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k

theorem lb_conj_facts {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) (y : G) :
    Lb.map (MulAut.conj y).toMonoidHom ∈ thetaComponentsAt 3 (y * b * y⁻¹) ∧
      Nonempty (↥(Lb.map (MulAut.conj y).toMonoidHom) ⧸
        aschbacherSolvableCore 3 ↥(Lb.map (MulAut.conj y).toMonoidHom) ≃*
          CFSG.Blueprint.NativeSporadic.J2) ∧
      Subgroup.centralizer ({y * b * y⁻¹} : Set G) ≤
        Subgroup.normalizer ((Lb.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  obtain ⟨φJ⟩ := Item148HJ.j2_of_isLBConfig hc
  refine ⟨Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three hLb.1 y,
    ⟨(Sec13.thetaQuotEquiv (MulAut.conj y) Lb).symm.trans φJ⟩, fun g hg => ?_⟩
  have hgb : (y⁻¹ * g * y) * b = b * (y⁻¹ * g * y) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc (y⁻¹ * g * y) * b = y⁻¹ * (g * (y * b * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * b * y⁻¹) * g) * y := by rw [h1]
      _ = b * (y⁻¹ * g * y) := by group
  have hN := centralizer_le_normalizer_lb h hB hc
    (Subgroup.mem_centralizer_singleton_iff.mpr hgb)
  refine mem_normalizer_of_conj_mem fun s hs => ?_
  obtain ⟨l, hl, rfl⟩ := hs
  have h1 := (Subgroup.mem_normalizer_iff.mp hN l).mp hl
  refine ⟨(y⁻¹ * g * y) * l * (y⁻¹ * g * y)⁻¹, h1, ?_⟩
  show y * ((y⁻¹ * g * y) * l * (y⁻¹ * g * y)⁻¹) * y⁻¹ = g * (y * l * y⁻¹) * g⁻¹
  group

theorem mem_zpowers_of_trivial_conj {A L B Lb Q : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hc : IsLBConfig A B b d Lb)
    (hQ : IsPGroup 3 Q) (hAQ : A ≤ Q) (hQb : Q ≤ Subgroup.centralizer ({b} : Set G))
    {y : G} (hyQ : ∀ q ∈ Q, y⁻¹ * q * y ∈ Q) :
    ∀ α ∈ A, (∀ x ∈ Lb.map (MulAut.conj y).toMonoidHom, x⁻¹ * (α * x * α⁻¹) ∈
      inSubgroup (aschbacherSolvableCore 3) (Lb.map (MulAut.conj y).toMonoidHom)) →
      α ∈ Subgroup.zpowers (y * b * y⁻¹) := by
  intro α hα htr
  have hg3 : (y⁻¹ * α * y) ^ 3 = 1 := by
    rw [show y⁻¹ * α * y = y⁻¹ * α * y⁻¹⁻¹ by rw [inv_inv], conj_pow, h.isE27'.1.2 α hα,
      mul_one, mul_inv_cancel]
  have htriv : ∀ l ∈ Lb, l⁻¹ * ((y⁻¹ * α * y) * l * (y⁻¹ * α * y)⁻¹) ∈
      inSubgroup (aschbacherSolvableCore 3) Lb := by
    intro l hl
    have hx : y * l * y⁻¹ ∈ Lb.map (MulAut.conj y).toMonoidHom := ⟨l, hl, rfl⟩
    have h1 := htr _ hx
    rw [← map_inSubgroup_aschbacherSolvableCore] at h1
    obtain ⟨t, ht, hteq⟩ := h1
    have hteq' : y * t * y⁻¹ = (y * l * y⁻¹)⁻¹ * (α * (y * l * y⁻¹) * α⁻¹) := hteq
    have : l⁻¹ * ((y⁻¹ * α * y) * l * (y⁻¹ * α * y)⁻¹) = t := by
      calc l⁻¹ * ((y⁻¹ * α * y) * l * (y⁻¹ * α * y)⁻¹) =
            y⁻¹ * ((y * l * y⁻¹)⁻¹ * (α * (y * l * y⁻¹) * α⁻¹)) * y := by group
        _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [hteq']
        _ = t := by group
    rw [this]
    exact ht
  have hmem := mem_zpowers_of_trivial h hc hQ hAQ hQb (hyQ α (hAQ hα)) hg3 htriv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, hk]
  group

theorem exists_isSylowOf_le_centralizer_b {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    (ha : a ∈ A) {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D)
    (hc : IsLBConfig A D b d Lb) (had : Subgroup.zpowers a = Subgroup.zpowers d)
    (hΩ1 : omegaA A = {Subgroup.zpowers b}) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer ({a} : Set G)) ∧
      A ≤ P ∧ P ≤ Subgroup.centralizer ({b} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  obtain ⟨hb1, -⟩ := hc.ne_one hD hA
  have hbD : b ∈ D := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdD : d ∈ D := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hbA : b ∈ A := hD.1 hbD
  have hb3 := hA3 b hbA
  have hDab : D = Subgroup.zpowers b ⊔ Subgroup.zpowers a := by
    rw [hc.1, closure_pair_eq_sup, had]
  have hD9 : Nat.card D = 9 := by have := hD.2; rw [hA.2] at this; omega
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  have hACa : A ≤ Ca := Desc143X.le_centralizer_of_isE27 hA ha
  have hACb : A ≤ Cb := Desc143X.le_centralizer_of_isE27 hA hbA
  obtain ⟨Q, hQsyl, hAQ⟩ := exists_isSylowOf_ge (le_inf hACa hACb) hAp
  have hQa : Q ≤ Ca := hQsyl.le.trans inf_le_left
  have hQb : Q ≤ Cb := hQsyl.le.trans inf_le_right
  refine ⟨Q, ?_, hAQ, hQb⟩
  obtain ⟨P, hPsyl, hQP⟩ := exists_isSylowOf_ge hQa hQsyl.isPGroup
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP (fun heq => hne (heq ▸ hPsyl))
  obtain ⟨y, hyP, hyQ, hyN⟩ := Sec3.exists_conj_mem_of_lt hPsyl.isPGroup hlt
  have hyCa : y ∈ Ca := hPsyl.le hyP
  obtain ⟨m, hm⟩ := hPsyl.isPGroup ⟨y, hyP⟩
  have hym : y ^ 3 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hyNQ : y ∈ Subgroup.normalizer (Q : Set G) := mem_normalizer_of_conj_mem hyN
  have hyQ' : ∀ q ∈ Q, y⁻¹ * q * y ∈ Q := fun q hq => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyNQ) q).mp hq
    simpa using this
  set Z₁ := A ⊓ Subgroup.centralizer (Q : Set G) with hZ₁
  have hcent : ∀ z ∈ Subgroup.centralizer (Q : Set G),
      y * z * y⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro q hq
    have h1 := hz _ (hyQ' q hq)
    calc q * (y * z * y⁻¹) = y * ((y⁻¹ * q * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * q * y)) * y⁻¹ := by rw [h1]
      _ = y * z * y⁻¹ * q := by group
  have hZ : ∀ z ∈ Z₁, y * z * y⁻¹ ∈ Z₁ := by
    rintro z ⟨hzA, hzC⟩
    have hc' := hcent z hzC
    refine ⟨?_, hc'⟩
    refine Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian ?_ fun α hα => ?_
    · rw [conj_pow, hA3 z hzA, mul_one, mul_inv_cancel]
    · exact Subgroup.mem_centralizer_iff.mp hc' α (hAQ hα)
  have haZ : a ∈ Z₁ := ⟨ha, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQa hq)⟩
  have hbZ : b ∈ Z₁ := ⟨hbA, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mp (hQb hq)⟩
  have hDZ : D ≤ Z₁ := by
    rw [hDab]
    exact sup_le (Subgroup.zpowers_le.mpr hbZ) (Subgroup.zpowers_le.mpr haZ)
  have hZA : Z₁ ≤ A := inf_le_left
  have hZcard : Nat.card Z₁ = 9 ∨ Nat.card Z₁ = 27 := by
    have h1 : Nat.card Z₁ ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le hZA
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have h2 : 9 ∣ Nat.card Z₁ := hD9 ▸ Subgroup.card_dvd_of_le hDZ
    rw [hik] at h2 ⊢
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · norm_num at h2
    · norm_num at h2
    · left; norm_num
    · right; norm_num
  have hyb : y * b * y⁻¹ = b := by
    rcases hZcard with h9 | h27
    · have hZD : Z₁ = D := (Subgroup.eq_of_le_of_card_ge hDZ (by rw [h9, hD9])).symm
      have hybD : y * b * y⁻¹ ∈ D := hZD ▸ hZ b hbZ
      by_cases hbb : y * b * y⁻¹ ∈ Subgroup.zpowers b
      · exact conj_eq_of_mem_zpowers hym hb3 hbb
      · exfalso
        have heA : y * b * y⁻¹ ∈ A := hD.1 hybD
        have he1 : y * b * y⁻¹ ≠ 1 := fun h1 => hb1 (by
          calc b = y⁻¹ * (y * b * y⁻¹) * y := by group
            _ = 1 := by rw [h1]; group)
        have hΩe : Subgroup.zpowers (y * b * y⁻¹) ∉ omegaA A := by
          rw [hΩ1, Set.mem_singleton_iff]
          intro hmem
          apply hbb
          rw [← hmem]
          exact Subgroup.mem_zpowers _
        obtain ⟨hX, hφ, hNX⟩ := lb_conj_facts h hD hc y
        exact false_of_j2_of_inner h heA he1 hΩe hX hφ hNX
          (mem_zpowers_of_trivial_conj h hc hQsyl.isPGroup hAQ hQb hyQ')
    · have hZA' : Z₁ = A := Subgroup.eq_of_le_of_card_ge hZA (by rw [h27, hA.2])
      have hyA : y ∈ Subgroup.normalizer (A : Set G) := by
        refine mem_normalizer_of_conj_mem fun z hz => ?_
        have h1 := hZ z (hZA' ▸ hz)
        rwa [hZA'] at h1
      have h1 : (Subgroup.zpowers b).map (MulAut.conj y).toMonoidHom ∈ omegaA A :=
        (Sec13.map_conj_mem_omegaA_iff hyA).mpr (hΩ1 ▸ Set.mem_singleton _)
      rw [hΩ1, Set.mem_singleton_iff] at h1
      have h2 : y * b * y⁻¹ ∈ Subgroup.zpowers b := by
        rw [← h1]
        exact ⟨b, Subgroup.mem_zpowers b, rfl⟩
      exact conj_eq_of_mem_zpowers hym hb3 h2
  have hyCb : y ∈ Cb := by
    rw [hCb, Subgroup.mem_centralizer_singleton_iff]
    calc y * b = y * b * y⁻¹ * y := by group
      _ = b * y := by rw [hyb]
  have hR : Q ⊔ Subgroup.zpowers y ≤ Ca ⊓ Cb :=
    sup_le hQsyl.le (Subgroup.zpowers_le.mpr ⟨hyCa, hyCb⟩)
  have heq := hQsyl.eq_of_le le_sup_left hR
    (hPsyl.isPGroup.to_le (sup_le hQP (Subgroup.zpowers_le.mpr hyP)))
  exact hyQ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

theorem exists_nonabelian_le_map {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (hc : IsLBConfig A D b d Lb)
    {K : Subgroup G} (hDK : lB A D ≤ K) (g : G) :
    ∃ E : Subgroup G, E ≤ K.map (MulAut.conj g).toMonoidHom ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
  obtain ⟨E, hEK, hE3, x, hx, y, hy, hxy⟩ := exists_nonabelian_le_lB h hD hc
  refine ⟨E.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono (hEK.trans hDK), ?_,
    g * x * g⁻¹, ⟨x, hx, rfl⟩, g * y * g⁻¹, ⟨y, hy, rfl⟩, fun h' => hxy ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    show (g * z * g⁻¹) ^ 3 = 1
    rw [conj_pow, hE3 z hz, mul_one, mul_inv_cancel]
  · have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h'
        _ = g * (y * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem false_of_le_commute {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (hc : IsLBConfig A D b d Lb)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (hDK : lB A D ≤ K) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) {S : Subgroup G} (hAS : A ≤ S)
    (hSC : S ≤ Subgroup.centralizer ({a} : Set G))
    (hSK : ∀ s ∈ S, ∀ k ∈ K.map (MulAut.conj g).toMonoidHom, ⁅k, s⁆ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) : False := by
  have hA := h.isE27'
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2)⟩
  have hK' : K.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 a :=
    Sec6.map_conj_mem_thetaComponentsAt hg hK
  obtain ⟨T, hT, hTA⟩ := exists_isSylowOf_commute_of_le hAp hAS hSC
    (le_centralizer_of_mem_thetaComponentsAt hK') hSK
  obtain ⟨E, hEK, hE3, hEc⟩ := exists_nonabelian_le_map h hD hc hDK g
  exact false_of_isSylowOf_commute h.maximal_isElemAbelian hT hTA (hEK.trans le_sup_left) hE3 hEc

theorem false_of_isSylowOf_le_centralizer_b {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (hc : IsLBConfig A D b d Lb)
    {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer ({a} : Set G)))
    (hAP : A ≤ P) (hPb : P ≤ Subgroup.centralizer ({b} : Set G))
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (hDK : lB A D ≤ K) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta C
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK' : K' ∈ thetaComponentsAt 3 a := Sec6.map_conj_mem_thetaComponentsAt hg hK
  have hK'C : K' ≤ C := le_centralizer_of_mem_thetaComponentsAt hK'
  set 𝒪 := orbitIn C K with h𝒪
  have h𝒪mem : ∀ K'' ∈ 𝒪, K'' ∈ thetaComponentsAt 3 a := by
    rintro _ ⟨h', hh', rfl⟩
    exact Sec6.map_conj_mem_thetaComponentsAt hh' hK
  set N₀ := sSup 𝒪 ⊔ T with hN₀
  have hN₀C : N₀ ≤ C := sup_le (sSup_le fun K'' hK'' =>
    le_centralizer_of_mem_thetaComponentsAt (h𝒪mem K'' hK'')) hTC
  have hCN₀ : C ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun n hn => ?_
    have hle : N₀ ≤ N₀.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (sSup_le fun K'' hK'' => ?_) ?_
      · obtain ⟨h', hh', rfl⟩ := hK''
        intro z hz
        rw [Subgroup.mem_comap]
        apply Subgroup.mem_sup_left
        have hmem : K.map (MulAut.conj (x * h')).toMonoidHom ∈ 𝒪 := ⟨x * h', C.mul_mem hx hh', rfl⟩
        refine le_sSup hmem ?_
        rw [← Late.map_conj_map_conj]
        exact ⟨z, hz, rfl⟩
      · intro t ht
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hCT hx) t).mp ht)
    exact hle hn
  have hK'𝒪 : K' ∈ 𝒪 := ⟨g, hg, rfl⟩
  have hK'N₀ : K' ⊔ T ≤ N₀ := sup_le ((le_sSup hK'𝒪).trans le_sup_left) le_sup_right
  have hN₀N : N₀ ≤ Subgroup.normalizer ((K' ⊔ T : Subgroup G) : Set G) := by
    refine sup_le (sSup_le fun K'' hK'' => ?_) (le_sup_right.trans Subgroup.le_normalizer)
    by_cases heq : K'' = K'
    · rw [heq]
      exact le_sup_left.trans Subgroup.le_normalizer
    · intro x hx
      exact mem_normalizer_sup_theta
        (le_centralizer_of_mem_thetaComponentsAt (h𝒪mem K'' hK'') hx) hK'C
        fun k hk => Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK' (h𝒪mem K'' hK'')
          (Ne.symm heq) (Subgroup.commutator_mem_commutator hk hx)
  have hT₁ := (hP.inf_of_le_normalizer hN₀C hCN₀).inf_of_le_normalizer hK'N₀ hN₀N
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  obtain ⟨-, -, hAb⟩ := j2_point_facts hS.toSec13Data (Item148HJ.j2_of_isLBConfig hc)
  have hFK : A ⊓ Lb ≤ K :=
    (Item148HJ.inf_le_residual h hD hc).trans ((Item148HJ.lB_eq_residual h hD hc) ▸ hDK)
  have hACa : A ≤ C := fun x hx => hP.le (hAP hx)
  have hcomm : ∀ t ∈ P ⊓ N₀ ⊓ (K' ⊔ T), ∀ x ∈ A, t * x = x * t := by
    intro t ht x hx
    have htP : t ∈ P := ht.1.1
    have htN : t ∈ K' ⊔ T := ht.2
    have hle : Subgroup.zpowers b ⊔ (A ⊓ Lb) ≤ Subgroup.centralizer ({t} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun f0 hf0 => ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hPb htP)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := commutator_mem_theta_of_mem_sup (hACa hf0.1) hK'C
          (fun k hk => Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK' hK hne
            (Subgroup.commutator_mem_commutator hk (hFK hf0))) htN
        have h2 : ⁅t, f0⁆ ∈ P := by
          rw [commutatorElement_def]
          exact P.mul_mem (P.mul_mem (P.mul_mem htP (hAP hf0.1)) (P.inv_mem htP))
            (P.inv_mem (hAP hf0.1))
        exact (commutatorElement_eq_one_iff_mul_comm.mp
          (eq_one_of_mem_theta_of_isPGroup hP.isPGroup h2 h1)).symm
    have hx' : x ∈ Subgroup.zpowers b ⊔ (A ⊓ Lb) := hAb ▸ hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx')).symm
  obtain ⟨E, hEK, hE3, hEc⟩ := exists_nonabelian_le_map h hD hc hDK g
  exact false_of_isSylowOf_commute h.maximal_isElemAbelian hT₁ hcomm (hEK.trans le_sup_left)
    hE3 hEc

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
