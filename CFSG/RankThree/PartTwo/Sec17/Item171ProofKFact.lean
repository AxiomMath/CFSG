module

public import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def gen171 (A X : Subgroup G) : Subgroup G :=
  sSup {Q | Q ∈ invariantPiSubgroups X A (piCompl 3) ∧ Q = ⁅Q, A⁆}

end Defs

namespace Proof171

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_gen171_le {A X : Subgroup G} {y : G} (hyX : y ∈ X)
    (hyA : y ∈ Subgroup.centralizer (A : Set G)) :
    (gen171 A X).map (MulAut.conj y).toMonoidHom ≤ gen171 A X := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun Q hQ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨⟨hQX, hQ3, hAQ⟩, hQA⟩ := hQ
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hyA
  refine le_sSup ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · calc Q.map (MulAut.conj y).toMonoidHom ≤ X.map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_mono hQX
      _ = X := Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyX)
  · intro q hq
    apply hQ3 q
    rwa [Subgroup.card_map_of_injective (MulAut.conj y).injective] at hq
  · intro α hα
    refine mem_normalizer_of_map_conj_eq ?_
    have hαy : α * y = y * α := (Subgroup.mem_centralizer_iff.mp hyA α hα)
    rw [Late.map_conj_map_conj, hαy, ← Late.map_conj_map_conj,
      Late.map_conj_eq_of_mem_normalizer (hAQ hα)]
  · conv_lhs => rw [hQA]
    rw [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer hyN]

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem mem_scriptQ_of_le_L (hD : Sec13Data G A c L) (h142 : Concl142 A (lB A))
    {R : Subgroup G} (hRL : R ≤ L) (hR3 : ¬ 3 ∣ Nat.card R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : R ∈ scriptQ A (lB A) := by
  have hRH : R ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hRL.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  obtain ⟨R', hR', hRR'⟩ := exists_le_mem_maxInvariantPiSubgroups hRH
  exact mem_scriptQ_of_le (h142 c hD.zpowers_mem_omegaA R' hR').1 hRR' hAR

theorem gen171_le_deltaZero (hD : Sec13Data G A c L) (h142 : Concl142 A (lB A)) (b : G) :
    gen171 A (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      deltaZero A (lB A) (Subgroup.centralizer ({b} : Set G)) := by
  refine sSup_le fun Q hQ => ?_
  obtain ⟨⟨hQX, hQ3, hAQ⟩, hQA⟩ := hQ
  exact le_deltaZero ⟨mem_scriptQ_of_le_L hD h142 (hQX.trans inf_le_left)
    ((isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ3) hAQ, hQA⟩ (hQX.trans inf_le_right)

theorem le_delta_of_cover (hD : Sec13Data G A c L) (h142 : Concl142 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A)) (hLY : L ≤ Y) (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) :
    L ≤ delta A (lB A) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set D := delta A (lB A) L with hDdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hO3 : ¬ 3 ∣ Nat.card O := not_three_dvd_of_isPGroup_two hO2
  have hmem : ∀ R : Subgroup G, R ≤ L → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ≤ D := fun R hRL hR3 hAR =>
    le_delta (mem_scriptQ_of_le_L hD h142 hRL hR3 hAR) hRL
  have hDL : D ≤ L := delta_le L
  have hQ : ∀ Q ∈ collectionIn (scriptQ A (lB A)) Y, Q ≤ D ⊔ O := by
    rintro Q ⟨hQ, hQY⟩
    have hQO : IsPiSubgroup (piCompl 3) (Q ⊔ O) := isPiSubgroup_piCompl_sup hQ.1.2.1
      ((isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3) (hQY.trans hYO)
    have hR : (Q ⊔ O) ⊓ L ≤ D := hmem _ inf_le_right
      (fun h3 => (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQO
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      ((le_inf (le_normalizer_sup hQ.1.2.2 hAO) hD.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
    intro q hq
    have hqY : q ∈ ((L ⊔ O : Subgroup G) : Set G) := hcov (hQY hq)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L O (hLY.trans hYO)] at hqY
    obtain ⟨l, hl, o, ho, rfl⟩ := hqY
    have hlR : l ∈ (Q ⊔ O) ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, hl⟩
      have hlo : l = (l * o) * o⁻¹ := by group
      rw [hlo]
      exact mul_mem (Subgroup.mem_sup_left hq) (inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left (hR hlR)) (Subgroup.mem_sup_right ho)
  have hYle : Y ≤ D ⊔ O :=
    hY.2.2.1.le.trans (show delta A (lB A) Y ≤ D ⊔ O from sSup_le hQ)
  have hLO : L ⊓ O ≤ D := hmem _ inf_le_left
    (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right)))
    ((le_inf hD.le_normalizer hAO).trans Subgroup.inf_normalizer_le_normalizer_inf)
  intro l hl
  have hl' : l ∈ ((D ⊔ O : Subgroup G) : Set G) := hYle (hLY hl)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D O (hDL.trans (hLY.trans hYO))] at hl'
  obtain ⟨d, hd, o, ho, rfl⟩ := hl'
  have hoL : o ∈ L := by
    have := mul_mem (inv_mem (hDL hd)) hl
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hd (hLO ⟨hoL, ho⟩)

omit [Finite G] in
theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimp, -⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro n hn
    have h1 : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff n).mp h1
  · right
    have hdec : ∀ g : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, g = n * z := by
      intro g
      have hg : π g ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      have : π (n⁻¹ * g) = 1 := by rw [map_mul, map_inv, hng, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    rw [eq_top_iff, ← hperf.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
    intro g _ g' _
    obtain ⟨n, hn, z, hz, rfl⟩ := hdec g
    obtain ⟨n', hn', z', hz', rfl⟩ := hdec g'
    set ρ := QuotientGroup.mk' N with hρ
    have h1 : ρ ⁅n * z, n' * z'⁆ = 1 := by
      rw [map_commutatorElement, map_mul, map_mul,
        show ρ n = 1 from (QuotientGroup.eq_one_iff n).mpr hn,
        show ρ n' = 1 from (QuotientGroup.eq_one_iff n').mpr hn', one_mul, one_mul,
        commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.mp hz z').symm]
    exact (QuotientGroup.eq_one_iff _).mp h1

omit [Finite G] in
theorem commutatorElement_mul_center {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) (a b : Q) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
      = (z * (a * w * b * a⁻¹)) * z⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = ((a * w * b * a⁻¹) * z) * z⁻¹ * (b⁻¹ * w⁻¹) := by rw [← hz' (a * w * b * a⁻¹)]
    _ = (a * w) * (b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = (w * a) * (b * a⁻¹ * b⁻¹) * w⁻¹ := by rw [hw' a]
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * w * w⁻¹ := by rw [← hw' (a * b * a⁻¹ * b⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_iSup_gen171 (hD : Sec13Data G A c L) (hLΔ : L ≤ delta A (lB A) L) {B : Subgroup G}
    (hB : IsHyperplane A B) :
    L ≤ ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), gen171 A (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_mem_partTwoE hD.mem_partTwoE
  set N := ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
    gen171 A (L ⊓ Subgroup.centralizer ({b} : Set G)) with hN
  set C := L ⊓ Subgroup.centralizer (A : Set G) with hC
  have hNL : N ≤ L := iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
    sSup_le fun Q hQ => hQ.1.1.trans inf_le_left
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.le_normalizer
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hA.2] at this
    omega
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from hD.commute (hB.1 x.2) (hB.1 y.2))⟩⟩,
      fun x hx => hA.1.2 x (hB.1 hx)⟩
  have hcov : L ≤ N ⊔ C := by
    refine hLΔ.trans (sSup_le fun Q hQ => ?_)
    obtain ⟨hQQ, hQL⟩ := hQ
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQQ.1.2.1
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQQ.1.2.2
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hBe (by rw [hB9]; norm_num)
      (hB.1.trans hAQ) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ3)
      fun b hb hb1 => ?_
    set R := Q ⊓ Subgroup.centralizer ({b} : Set G) with hR
    have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun α hα =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hα (hB.1 hb))
    have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
      Late.le_normalizer_inf hAQ (hAb.trans Subgroup.le_normalizer)
    have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three A R hA.isPGroup hR3 hAR]
    have hRA : ⁅R, A⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hAR
    refine sup_le (le_sup_of_le_left (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1
      (le_sSup ⟨⟨?_, ?_, ?_⟩, ?_⟩))))) (le_sup_of_le_right ?_)
    · exact le_inf (hRA.trans (inf_le_left.trans hQL)) (hRA.trans inf_le_right)
    · exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr fun h3 =>
        hR3 (h3.trans (Subgroup.card_dvd_of_le hRA))
    · rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A R
    · exact (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
        Nat.prime_three A R hA.isPGroup hR3 hAR).symm
    · exact le_inf (inf_le_left.trans (inf_le_left.trans hQL)) inf_le_right
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := by
    have hle : ∀ y ∈ C, N.map (MulAut.conj y).toMonoidHom ≤ N := by
      intro y hy
      rw [hN, Subgroup.map_iSup]
      refine iSup_le fun b => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hb => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hb1 => ?_
      have hyb : y ∈ L ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨hy.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hB.1 hb)) hy.2⟩
      exact (map_conj_gen171_le hyb hy.2).trans
        (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))
    intro y hy
    refine mem_normalizer_of_map_conj_eq (le_antisymm (hle y hy) ?_)
    have h2 := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) (hle y⁻¹ (inv_mem hy))
    rwa [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one] at h2
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := hcov.trans (sup_le Subgroup.le_normalizer hCN)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set T := θ.map L.subtype with hT
  set N₀ : Subgroup ↥L := N.subgroupOf L with hN₀
  set C₀ : Subgroup ↥L := C.subgroupOf L with hC₀
  have hN₀n : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hLp := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hdec : ∀ x : ↥L, ∃ n ∈ N₀, ∃ y ∈ C₀, x = n * y := by
    intro x
    have hx : (x : G) ∈ ((N ⊔ C : Subgroup G) : Set G) := hcov x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N C hCN] at hx
    obtain ⟨n, hn, y, hy, hxy⟩ := hx
    exact ⟨⟨n, hNL hn⟩, hn, ⟨y, hy.1⟩, hy, Subtype.ext hxy.symm⟩
  rcases normal_le_center_or_eq_top hq
      (hN₀n.map (QuotientGroup.mk' θ) (QuotientGroup.mk'_surjective θ)) with hZ | htop
  ·
    exfalso
    have hCtop : C₀.map (QuotientGroup.mk' θ) = ⊤ := by
      rw [eq_top_iff, ← hq.1.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
      intro p _ q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ p
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective θ q
      obtain ⟨n, hn, y, hy, rfl⟩ := hdec x
      obtain ⟨n', hn', y', hy', rfl⟩ := hdec x'
      rw [map_mul, map_mul, commutatorElement_mul_center (hZ ⟨n, hn, rfl⟩) (hZ ⟨n', hn', rfl⟩),
        ← map_commutatorElement]
      refine ⟨⁅y, y'⁆, ?_, rfl⟩
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
    have := Sec4.aschbacherSolvableCore_characteristic ↥L
    have hLT : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (T : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic θ
    have hAC : ∀ α ∈ A, α ∈ Late.sectionCentralizer A L T := by
      intro α hα
      refine ⟨hα, fun x hx => ?_⟩
      have hxt : QuotientGroup.mk' θ (⟨x, hx⟩ : ↥L) ∈ C₀.map (QuotientGroup.mk' θ) :=
        hCtop ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hxt
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have htT : ((y⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ T := ⟨_, hyx, rfl⟩
      have hxyt : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by
        simp
      set t : G := ((y⁻¹ * ⟨x, hx⟩ : ↥L) : G) with htdef
      have hyα : α * (y : G) = (y : G) * α := Subgroup.mem_centralizer_iff.mp hy.2 α hα
      have hTα : α * t * α⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hLT (hAL hα)) t).mp htT
      have hkey : α * x * α⁻¹ * x⁻¹ = (y : G) * (α * t * α⁻¹ * t⁻¹) * (y : G)⁻¹ := by
        rw [hxyt]
        calc α * ((y : G) * t) * α⁻¹ * ((y : G) * t)⁻¹
            = (α * (y : G)) * t * α⁻¹ * t⁻¹ * (y : G)⁻¹ := by group
          _ = ((y : G) * α) * t * α⁻¹ * t⁻¹ * (y : G)⁻¹ := by rw [hyα]
          _ = (y : G) * (α * t * α⁻¹ * t⁻¹) * (y : G)⁻¹ := by group
      rw [hkey]
      exact (Subgroup.mem_normalizer_iff.mp (hLT (Subgroup.le_normalizer y.2)) _).mp
        (mul_mem hTα (inv_mem htT))
    have hsc : Late.sectionCentralizer A L T = (Subgroup.zpowers c : Set G) :=
      hD.sectionCentralizer_eq
    have hsub : A ≤ Subgroup.zpowers c := fun α hα => by
      have h1 := hAC α hα
      rw [hsc] at h1
      exact h1
    have hcard := Subgroup.card_le_of_le hsub
    rw [hA.2, Nat.card_zpowers, hD.orderOf_eq] at hcard
    omega
  ·
    have hsup : N₀ ⊔ θ = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N₀
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' N₀).comp θ.subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ q
      have hx : x ∈ N₀ ⊔ θ := hsup ▸ Subgroup.mem_top x
      rw [Subgroup.mem_sup_of_normal_left] at hx
      obtain ⟨n, hn, t, ht, rfl⟩ := hx
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    have hsolv : Group.IsSolvable (↥L ⧸ N₀) := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (↥L ⧸ N₀) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N₀) (QuotientGroup.mk'_surjective N₀)
    have hNtop : N₀ = ⊤ := by
      by_contra hne
      have : Nontrivial (↥L ⧸ N₀) := QuotientGroup.nontrivial_iff.mpr hne
      exact Group.IsPerfect.not_isSolvable (↥L ⧸ N₀) hsolv
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥L) ∈ N₀ := hNtop ▸ Subgroup.mem_top _
    exact hmem

end Proof171

end CFSG.RankThree.PartTwo.Sec17
