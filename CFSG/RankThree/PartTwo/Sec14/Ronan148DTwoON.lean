module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwo
import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofYB
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofGen
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofW
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section ON


theorem eq_of_le_of_isPerfect {a : G} {K K' J : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hK' : K' ∈ thetaComponentsAt 3 a) (hJK : J ≤ K) (hJK' : J ≤ K')
    (hJp : Group.IsPerfect ↥J) (hJ : J ≠ ⊥) : K = K' := by
  by_contra hne
  set C := Subgroup.centralizer ({a} : Set G) with hC
  have h1 : ⁅J, J⁆ ≤ inSubgroup (aschbacherSolvableCore 3) C :=
    (Subgroup.commutator_mono hJK hJK').trans
      (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hK' hne)
  rw [(Subgroup.isPerfect_iff).mp hJp] at h1
  have hs : Group.IsSolvable ↥J := by
    haveI := (Sec6.theta_solvable_and_not_dvd C).1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)
  haveI : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ
  exact Group.IsPerfect.not_isSolvable ↥J hs

theorem mem_normalizer_of_normalizes_lB {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (hBK : lB A B ≤ K) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hgB : (lB A B).map (MulAut.conj g).toMonoidHom = lB A B) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hres := Item148HJ.lB_eq_residual h hB hc
  have hJp : Group.IsPerfect ↥(lB A B) := by
    rw [hres]
    exact Item148HJ.isPerfect_inSubgroup_perfectResidual _
  have hJ : lB A B ≠ ⊥ := by
    obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27'
    obtain ⟨hdL, -⟩ := hc.2.2.2.2
    have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
    have hdJ : d ∈ lB A B := hres ▸ Item148HJ.inf_le_residual h hB hc ⟨hdA, hdL⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hdJ
    exact hd1 hdJ
  refine eq_of_le_of_isPerfect (Sec6.map_conj_mem_thetaComponentsAt hg hK) hK ?_ hBK hJp hJ
  rw [← hgB]
  exact Subgroup.map_mono hBK

theorem exists_isLBConfig_of_twelve (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c a : G} (h : Sec14Std G A c L) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (haB : a ∈ B) (hc : IsLBConfig A B b d Lb) (hda : Subgroup.zpowers a = Subgroup.zpowers d)
    (h12 : (omegaA A).ncard = 12) {D : Subgroup G} (hD : IsHyperplane A D) (haD : a ∈ D) :
    ∃ (b' d' : G) (L' : Subgroup G), IsLBConfig A D b' d' L' := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD13 := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27'
  obtain ⟨K, hKmem, hBK⟩ := exists_mem_lbMembers h48 h ha ha1 hΩ hB haB hc
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hc.2.1, mem_lA := hLb }
  have hres := Item148HJ.lB_eq_residual h hB hc
  obtain ⟨hdL, S, hdS, hSd⟩ := hc.2.2.2.2
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hKd : K ∈ thetaComponentsAt 3 d := by
    rw [← thetaComponentsAt_congr (p := 3) (centralizer_singleton_eq_of_zpowers_eq hda)]
    exact hKmem.1
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hKd (hres ▸ hBK) with
    ⟨-, -, hΩ1⟩ | ⟨-, -, -, -, -, -, hΩ'⟩ | ⟨-, hWd, hΩeq, -⟩
  · rw [hΩ1, Set.ncard_singleton] at h12
    norm_num at h12
  · rcases hΩ' with ⟨-, h3⟩ | ⟨-, -, -, -, -, -, -, -, h6, -⟩ <;> omega
  obtain ⟨u, huD, hua⟩ :=
    Item148PtRes.exists_mem_not_mem_zpowers hD13.card_eq hD13.isElemAbelian.2 hD ha
  have huA : u ∈ A := hD.1 huD
  have hu1 : u ≠ 1 := fun h1 => hua (h1 ▸ one_mem _)
  set T := {F : Subgroup G | F ≤ A ∧ Nat.card F = 3} with hTdef
  have hΩT : omegaA A ⊆ T := fun F hF => ⟨hF.1, hF.2.1⟩
  have haT : Subgroup.zpowers a ∈ T :=
    ⟨Subgroup.zpowers_le.mpr ha, card_zpowers_eq_three hA.1 ha ha1⟩
  have huT : Subgroup.zpowers u ∈ T :=
    ⟨Subgroup.zpowers_le.mpr huA, card_zpowers_eq_three hA.1 huA hu1⟩
  have hau : Subgroup.zpowers a ≠ Subgroup.zpowers u := fun he =>
    hua (he ▸ Subgroup.mem_zpowers u)
  have huΩ : Subgroup.zpowers u ∈ omegaA A := by
    by_contra huΩ
    have hsub : omegaA A ⊆ T \ {Subgroup.zpowers a, Subgroup.zpowers u} := by
      intro F hF
      refine ⟨hΩT hF, ?_⟩
      rintro (rfl | rfl)
      · exact hΩ hF
      · exact huΩ hF
    have hpair : ({Subgroup.zpowers a, Subgroup.zpowers u} : Set (Subgroup G)) ⊆ T := by
      rintro F (rfl | rfl)
      · exact haT
      · exact huT
    have : Finite (Subgroup G) :=
      Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_add_ncard_of_subset hpair
    rw [Set.ncard_pair hau] at h2
    have h3 := Item148PtRes.ncard_subgroups_card_three_le (A := A) hD13.card_eq
    rw [← hTdef] at h3
    omega
  have hbΩ : Subgroup.zpowers b ∈ omegaA A := hc.2.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
  rw [hΩeq] at hbΩ huΩ
  obtain ⟨w₁, hw₁, hbw⟩ := hbΩ
  obtain ⟨w₂, hw₂, huw⟩ := huΩ
  have hwN : w₂ * w₁⁻¹ ∈ Subgroup.normalizer (A : Set G) := mul_mem hw₂ (inv_mem hw₁)
  have hwb : MulAut.conj (w₂ * w₁⁻¹) b ∈ D := by
    have hb : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rw [hbw] at hb
    obtain ⟨x, hx, hxb⟩ := hb
    have h1 : MulAut.conj (w₂ * w₁⁻¹) b = MulAut.conj w₂ x := by
      rw [← hxb]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h2 : MulAut.conj w₂ x ∈ Subgroup.zpowers u := by
      rw [huw]
      exact ⟨x, hx, rfl⟩
    rw [h1]
    exact Subgroup.zpowers_le.mpr huD h2
  have hwa : MulAut.conj (w₂ * w₁⁻¹) a ∈ D := by
    have h1 : w₂ * w₁⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      rw [hda]
      exact hWd hwN
    rw [MulAut.conj_apply]
    exact Subgroup.zpowers_le.mpr haD
      ((Subgroup.mem_normalizer_iff.mp h1 a).mp (Subgroup.mem_zpowers a))
  have hbB : b ∈ B := by
    rw [hc.1]
    exact Subgroup.subset_closure (Set.mem_insert b {d})
  have hba : b ∉ Subgroup.zpowers a := by
    intro hb
    apply hΩ
    have h1 : Subgroup.zpowers b = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
        ((card_zpowers_eq_three hA.1 ha ha1).trans hb3.symm).le
    rw [← h1]
    exact hc.2.1
  have hab : IsHyperplane A (Subgroup.closure {a, b}) :=
    Main148.isHyperplane_closure_pair148 hA ha hbA ha1 hba
  have hBab : Subgroup.closure {a, b} = B := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact haB
      · exact hbB
    · have h1 := hab.2
      have h2 := hB.2
      omega
  have hBw : B.map (MulAut.conj (w₂ * w₁⁻¹)).toMonoidHom = D := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [← hBab, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hwa
      · exact hwb
    · have h1 := (hB.map_conj hwN).2
      have h2 := hD.2
      omega
  have hc' := hc.map (MulAut.conj (w₂ * w₁⁻¹))
  rw [Sec13.map_conj_eq_of_mem_normalizer hwN, hBw] at hc'
  exact ⟨_, _, _, hc'⟩


theorem le_of_on {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L) (ha : a ∈ A)
    (ha1 : a ≠ 1) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (haB : a ∈ B)
    (hc : IsLBConfig A B b d Lb) (hda : Subgroup.zpowers a = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (hBK : lB A B ≤ K)
    (hON : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K)
      CFSG.Blueprint.NativeSporadic.ON) : A ≤ K := by
  have hA := h.isE27'
  have hS' := Item148HJ.sec14Std_of_isLBConfig h hc
  obtain ⟨-, h9, hAb⟩ := j2_point_facts hS'.toSec13Data (Item148HJ.j2_of_isLBConfig hc)
  have hres := Item148HJ.lB_eq_residual h hB hc
  have hALK : A ⊓ Lb ≤ K := (Item148HJ.inf_le_residual h hB hc).trans (hres ▸ hBK)
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hbA : b ∈ A := hB.1 hbB
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Desc143X.le_centralizer_of_isE27 hA ha hbA
  have hbfix : (lB A B).map (MulAut.conj b).toMonoidHom = lB A B := by
    have hfix : ∀ x ∈ lB A B, (MulAut.conj b).toMonoidHom x = x := by
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.mp (lB_le_centralizer A B hx) b hbB
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h1]
      group
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hfix y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hfix x hx⟩
  have hbN := mem_normalizer_of_normalizes_lB h hB hc hK hBK hbC hbfix
  obtain ⟨hdL, -⟩ := hc.2.2.2.2
  have haL : a ∈ A ⊓ Lb :=
    ⟨ha, Subgroup.zpowers_le.mpr hdL (hda ▸ Subgroup.mem_zpowers a)⟩
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  have hmax : ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → A ≤ E → E = A :=
    fun E hE hAE => le_antisymm (h.maximal_isElemAbelian.2 hE hAE) hAE
  have hbK := Sec13.ON134.mem_of_maximal hA.1 hmax hbA inf_le_left h9 hALK hAb hbN haL ha1 hKa
    hq hON
  rw [hAb]
  exact sup_le (Subgroup.zpowers_le.mpr hbK) hALK

theorem lB_le_of_le {A L : Subgroup G} {c a : G} (h48 : Sec4.Item4_8) (h : Sec14Std G A c L)
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 a) (hAK : A ≤ K) {D : Subgroup G} (hD : IsHyperplane A D)
    (haD : a ∈ D) : lB A D ≤ K := by
  by_cases hconf : ∃ (b' d' : G) (L' : Subgroup G), IsLBConfig A D b' d' L'
  · obtain ⟨b', d', L', hc'⟩ := hconf
    obtain ⟨K', hK', hDK'⟩ := exists_mem_lbMembers h48 h ha ha1 hΩ hD haD hc'
    by_cases hKK : K' = K
    · exact hKK ▸ hDK'
    · exfalso
      refine false_of_commutator_mem h hD haD hc' hDK' (S := K) (inf_le_left.trans hAK)
        fun y hy s hs => ?_
      exact Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK'.1 hK hKK
        (Subgroup.commutator_mem_commutator hy hs)
  · push Not at hconf
    rw [lB_eq_bot hconf]
    exact bot_le

theorem eq_of_mem_lbMembers_of_le {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (hAK : A ≤ K) {K' : Subgroup G}
    (hK' : K' ∈ lbMembers A a) : K' = K := by
  obtain ⟨hK'a, D, b', d', L', hD, haD, hc', hDK'⟩ := hK'
  by_contra hKK
  refine false_of_commutator_mem h hD haD hc' hDK' (S := K) (inf_le_left.trans hAK)
    fun y hy s hs => ?_
  exact Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK'a hK hKK
    (Subgroup.commutator_mem_commutator hy hs)

theorem le_delta_of_on (hS2 : ONTripleGenE27) (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (haB : a ∈ B) (hc : IsLBConfig A B b d Lb) (hda : Subgroup.zpowers a = Subgroup.zpowers d)
    (h12 : (omegaA A).ncard = 12) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hBK : lB A B ≤ K)
    (hON : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K)
      CFSG.Blueprint.NativeSporadic.ON) :
    K ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h.isE27'
  have hAK := le_of_on h ha ha1 hB haB hc hda hK hBK hON
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
  have haK : a ∈ K := hAK ha
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  set π := QuotientGroup.mk' θK with hπ
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hπinj : ∀ x : ↥K, x ^ 3 = 1 → π x = 1 → x = 1 := by
    intro x hx3 hx1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact eq_one_of_mem_of_pow_three_pow hθ3 hx1 (k := 1) (by rw [pow_one]; exact hx3)
  set E := (A.subgroupOf K).map π with hEdef
  have hE : Late.IsE27 E := by
    refine ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π _
      (isElemAbelian_subgroupOf hA.1), ?_⟩
    rw [hEdef, card_map_eq_of_ker148 fun x hx hx1 => hπinj x (Subtype.ext (by
      simpa using hA.1.2 _ hx)) hx1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv,
      hA.2]
  set 𝒦 : Set (Subgroup (↥K ⧸ θK)) :=
    {Q | ∃ D : Subgroup G, IsHyperplane A D ∧ a ∈ D ∧ Q = ((lB A D).subgroupOf K).map π}
    with h𝒦
  have haZ : π ⟨a, haK⟩ ∈ Subgroup.center (↥K ⧸ θK) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective θK q
    rw [hπ, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKa k.2)
  have hgen : sSup 𝒦 = ⊤ := by
    refine hS2 (↥K ⧸ θK) (Sec6.isQuasisimple_of_mem_thetaComponentsAt hK).1 hON E hE 𝒦
      fun u hu huZ => ?_
    obtain ⟨x, hxA, rfl⟩ := hu
    have hxA' : (x : G) ∈ A := hxA
    have hxa : (x : G) ∉ Subgroup.zpowers a := by
      intro hxa
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxa
      apply huZ
      have hx' : x = (⟨a, haK⟩ : ↥K) ^ k := Subtype.ext (by simpa using hk.symm)
      rw [hx', map_zpow]
      exact Subgroup.zpow_mem _ haZ k
    set D := Subgroup.closure {a, (x : G)} with hDdef
    have hD : IsHyperplane A D := Main148.isHyperplane_closure_pair148 hA ha hxA' ha1 hxa
    have haD : a ∈ D := Subgroup.subset_closure (Set.mem_insert a _)
    have hxD : (x : G) ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
    obtain ⟨b', d', L', hc'⟩ := exists_isLBConfig_of_twelve h134 h48 h ha ha1 hΩ hB haB hc hda
      h12 hD haD
    have hDK : lB A D ≤ K := lB_le_of_le h48 h ha ha1 hΩ hK hAK hD haD
    have hres := Item148HJ.lB_eq_residual h hD hc'
    set J := lB A D with hJdef
    refine ⟨(J.subgroupOf K).map π, ⟨D, hD, haD, rfl⟩, ?_, ?_, ?_, ?_⟩
    ·
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (y : G) * x = x * y
      exact (Subgroup.mem_centralizer_iff.mp (lB_le_centralizer A D hy) (x : G) hxD).symm
    ·
      have hJp : Group.IsPerfect ↥J := by
        rw [hres]
        exact Item148HJ.isPerfect_inSubgroup_perfectResidual _
      have hJp' : Group.IsPerfect ↥(J.subgroupOf K) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hDK).symm.toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.IsPerfect.ofSurjective (f := π.subgroupMap (J.subgroupOf K))
        (π.subgroupMap_surjective _)
    ·
      set ψ : ↥J →* ↥K ⧸ θK := π.comp (Subgroup.inclusion hDK) with hψ
      have hrange : ψ.range = (J.subgroupOf K).map π := by
        rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
      have hcard := Subgroup.card_ker_mul_card_range ψ
      rw [hrange] at hcard
      obtain ⟨-, -, -, hmaxJ, -⟩ :=
        solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
      have hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 ↥J := by
        let ι : ↥ψ.ker →* ↥θK :=
          { toFun := fun y => ⟨Subgroup.inclusion hDK y,
              (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have hι : Function.Injective ι := fun y z hyz => by
          have h1 := congrArg (fun w => ((w : ↥K) : G)) (congrArg Subtype.val hyz)
          exact Subtype.ext (Subtype.ext h1)
        obtain ⟨hθKs, -, -, -, -⟩ :=
          solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
        refine hmaxJ _ (MonoidHom.normal_ker ψ) ?_ ?_
        · haveI := hθKs
          exact Group.isSolvable_of_isSolvable_injective hι
        · exact fun h3 => hθ3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))
      have hle := Subgroup.card_le_of_le hkerθ
      have hJ2 := Item148HJ.j2_of_isLBConfig hc'
      obtain ⟨hdL', S', hdS', hSd'⟩ := hc'.2.2.2.2
      have hd'1' : d' ≠ 1 := (hc'.ne_one hD hA).2
      obtain ⟨-, htc, -, -⟩ := residual_facts h415 hJ2 hdL' hd'1' ⟨S', hdS', hSd'⟩
      rw [← hres] at htc
      have h1080 := Sec13.card_eq_of_isTripleCover_six htc
      have hJcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (aschbacherSolvableCore 3 ↥J)
      rw [h1080] at hJcard
      have hpos : 0 < Nat.card ↥(aschbacherSolvableCore 3 ↥J) := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : Nat.card ↥ψ.ker * Nat.card ↥((J.subgroupOf K).map π) <
          Nat.card ↥(aschbacherSolvableCore 3 ↥J) * 1080 := by
        calc Nat.card ↥ψ.ker * Nat.card ↥((J.subgroupOf K).map π)
            ≤ Nat.card ↥(aschbacherSolvableCore 3 ↥J) * Nat.card ↥((J.subgroupOf K).map π) :=
              Nat.mul_le_mul_right _ hle
          _ < Nat.card ↥(aschbacherSolvableCore 3 ↥J) * 1080 :=
              Nat.mul_lt_mul_of_pos_left hlt hpos
      rw [hcard, hJcard] at this
      linarith
    ·
      intro hEC
      obtain ⟨e, he, hed, -⟩ := Item148HJ.exists_mem_not_mem_zpowers h hD hc'
      obtain ⟨j, hj, hjθ⟩ := Item148HJ.exists_commutator_not_mem h hD hc' he hed
      have hjJ : j ∈ J := hres ▸ hj
      have heK : e ∈ K := hAK he.1
      have hjK : j ∈ K := hDK hjJ
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (hEC (show π ⟨e, heK⟩ ∈ E from ⟨⟨e, heK⟩, he.1, rfl⟩)) (π ⟨j, hjK⟩) ⟨⟨j, hjK⟩, hjJ, rfl⟩
      rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, hπ,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcomm
      have hθmem : ⁅j, e⁆ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
        refine ⟨⟨j, hjK⟩ * ⟨e, heK⟩ * (⟨e, heK⟩ * ⟨j, hjK⟩)⁻¹, hcomm, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
          commutatorElement_def]
        group
      have hJN : inSubgroup perfectResidual (L' ⊓ Subgroup.centralizer ({d'} : Set G)) ≤
          Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
        (hres ▸ hDK).trans (Sec6.le_normalizer_theta K)
      have heJ : e ∈ inSubgroup perfectResidual (L' ⊓ Subgroup.centralizer ({d'} : Set G)) :=
        Item148HJ.inf_le_residual h hD hc' he
      have h5 : ⁅j, e⁆ ∈ inSubgroup perfectResidual (L' ⊓ Subgroup.centralizer ({d'} : Set G)) := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hj heJ)
          (Subgroup.inv_mem _ hj)) (Subgroup.inv_mem _ heJ)
      exact hjθ (Desc143X.residual_inf_le_theta h hD hc' hJN
        (Sec6.theta_solvable_and_not_dvd K).2 ⟨h5, hθmem⟩)
  set J := (⨆ (D : Subgroup G) (_ : IsHyperplane A D ∧ a ∈ D), lB A D) ⊔
    inSubgroup (aschbacherSolvableCore 3) K with hJdef
  have hKJ : K ≤ J := by
    intro k hk
    have hmem : π ⟨k, hk⟩ ∈ sSup 𝒦 := hgen ▸ Subgroup.mem_top _
    have hle : sSup 𝒦 ≤ (J.subgroupOf K).map π := by
      refine sSup_le fun Q ⟨D, hD, haD, hQ⟩ => ?_
      rw [hQ]
      refine Subgroup.map_mono fun y hy => ?_
      exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem D (Subgroup.mem_iSup_of_mem ⟨hD, haD⟩ hy))
    obtain ⟨j, hj, hjk⟩ := hle hmem
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hjk
    have h1 : ((j⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ J := Subgroup.mem_sup_right ⟨_, hjk, rfl⟩
    have h2 : k = (j : G) * ((j⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [h2]
    exact J.mul_mem hj h1
  refine hKJ.trans (sup_le (iSup₂_le fun D hD => ?_) ?_)
  · obtain ⟨b', d', L', hc'⟩ := exists_isLBConfig_of_twelve h134 h48 h ha ha1 hΩ hB haB hc hda
      h12 hD.1 hD.2
    exact Desc143X.lB_le_delta h hD.1 hc' hD.2
  · have hθO : inSubgroup (aschbacherSolvableCore 3) K ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hK]
      exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)
    have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := lB A) hA h.maximal_isElemAbelian ha
    exact hθO.trans (le_sup_left.trans (le_delta hmem.1 hmem.2))

end ON

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
