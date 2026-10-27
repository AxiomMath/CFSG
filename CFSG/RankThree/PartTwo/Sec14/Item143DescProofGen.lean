module

import CFSG.RankThree.PartTwo.Sec14.Item143DescProofA6
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Desc143X

theorem card_comap_of_surjective {K M : Type*} [Group K] [Group M] [Finite K] {f : K →* M}
    (hf : Function.Surjective f) (Y : Subgroup M) :
    Nat.card (Y.comap f) = Nat.card Y * Nat.card f.ker := by
  have : Finite M := Finite.of_surjective f hf
  have h1 := (Y.comap f).card_mul_index
  rw [Subgroup.index_comap_of_surjective Y hf] at h1
  have h2 := Y.card_mul_index
  have h3 : Nat.card K = Nat.card M * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hpos : 0 < Y.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (Y.comap f) * Y.index = (Nat.card Y * Nat.card f.ker) * Y.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h4

variable {G : Type} [Group G] [Finite G]


theorem lB_le_delta_centralizer {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    lB A B ≤ delta A (lB A) (Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Item148HJ.lB_eq_residual h hB hc]
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  have hA := h.isE27'
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  have hJ2 := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, h9, hAeq⟩ := j2_point_facts hS.toSec13Data hJ2
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  have hJC : J ≤ Subgroup.centralizer (B : Set G) := Item148HJ.residual_le_centralizer hc
  have hCJ := Item148HJ.centralizer_le_normalizer_residual h hc
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨y, hB.1 hy⟩ ⟨x, hx⟩)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hAB.trans hCJ
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hJL : J ≤ Lb := Item148HJ.residual_le Lb d
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLb.1
  have hEJ : A ⊓ Lb ≤ J := Item148HJ.inf_le_residual h hB hc
  set 𝒬 := {Q : Subgroup G | Q ≤ J ∧ ¬ 3 ∣ Nat.card Q ∧ A ≤ Subgroup.normalizer (Q : Set G)}
    with h𝒬
  set T := sSup 𝒬 with hT
  have hTΔ : T ≤ delta A (lB A) (Subgroup.centralizer (B : Set G)) := by
    refine sSup_le fun Q hQ => ?_
    obtain ⟨hQJ, hQ3, hAQ⟩ := hQ
    have hQb : Q ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      intro q hq
      have hqb : q ∈ Subgroup.centralizer ({b} : Set G) := hLbC (hJL (hQJ hq))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hcomm : q * b = b * q := Subgroup.mem_centralizer_singleton_iff.mp hqb
      constructor
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        rw [(Commute.zpow_right hcomm k).eq, mul_inv_cancel_right]
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        have e : q * y * q⁻¹ = q * b ^ k * q⁻¹ := by
          rw [← hk, (Commute.zpow_right hcomm k).eq, mul_inv_cancel_right]
        exact (mul_left_cancel (mul_right_cancel e)).symm
    have hmem := mem_scriptQ_of_hj_point hS hJ2 (Q := Q)
      ⟨hQb, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩
    exact le_delta hmem.1 (hQJ.trans hJC)
  obtain ⟨hdL, hrange, -, -, -, -, -⟩ := Item148HJ.resProj_facts h hB hc
  set φ := Item148HJ.resProj Lb d with hφ
  set θL := aschbacherSolvableCore 3 ↥Lb with hθL
  set z := QuotientGroup.mk' θL ⟨d, hdL⟩ with hz
  set C := Subgroup.centralizer ({z} : Set (↥Lb ⧸ θL)) with hC
  have hφC : ∀ j, φ j ∈ C := fun j => hrange ▸ MonoidHom.mem_range.mpr ⟨j, rfl⟩
  set φ' : ↥J →* ↥C := φ.codRestrict C hφC with hφ'
  have hφ's : Function.Surjective φ' := by
    rintro ⟨w, hw⟩
    rw [← hrange] at hw
    obtain ⟨j, rfl⟩ := hw
    exact ⟨j, rfl⟩
  have hφ'ker : ∀ j : ↥J, φ' j = 1 ↔ (j : G) ∈ inSubgroup (aschbacherSolvableCore 3) Lb := by
    intro j
    rw [← Item148HJ.mem_ker_resProj, MonoidHom.mem_ker]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hd3 : d ^ 3 = 1 := hA.1.2 d (hB.1 hdB)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hz, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  obtain ⟨S, hdS, hSd⟩ := (hc.2.2.2.2).2
  obtain ⟨hCq, -, hCtc, -⟩ :=
    Item148HJ.centralizer_facts hJ2 hz1 (Item148HJ.exists_sylow_quot hdL ⟨S, hdS, hSd⟩)
  set E₀ : Subgroup ↥J := (A ⊓ Lb).subgroupOf J with hE₀
  set E : Subgroup ↥C := E₀.map φ' with hE
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow]
    have : e ^ 3 = 1 := Subtype.ext (by
      simpa using hA.1.2 (e : G) (Subgroup.mem_subgroupOf.mp he).1)
    rw [this, map_one]
  have hE₀card : Nat.card E₀ = 9 := by
    rw [hE₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, h9]
  have hE9 : Nat.card E = 9 := by
    have h1 := Subgroup.relIndex_ker E₀ φ'
    rw [show Nat.card E = Nat.card (E₀.map φ') from rfl, ← h1]
    have hbot : φ'.ker.subgroupOf E₀ = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨e, he⟩ hek
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      have hek' : (e : G) ∈ inSubgroup (aschbacherSolvableCore 3) Lb :=
        (hφ'ker e).mp (MonoidHom.mem_ker.mp (Subgroup.mem_subgroupOf.mp hek))
      have heA : (e : G) ∈ A ⊓ Lb := Subgroup.mem_subgroupOf.mp he
      obtain ⟨u, hu, hue⟩ := hek'
      have hu3 : u ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, show (u : G) = (e : G) from hue]
        exact hA.1.2 _ heA.1)
      have hu1 := eq_one_of_mem_aschbacherSolvableCore hu hu3
      apply Subtype.ext
      show ((e : ↥J) : G) = 1
      rw [← hue, hu1]
      rfl
    rw [Subgroup.relIndex, hbot, Subgroup.index_bot, hE₀card]
  have hdJ : d ∈ J := hEJ (Subgroup.mem_inf.mpr ⟨hB.1 hdB, hdL⟩)
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  have hdcen : φ' dJ ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨j, rfl⟩ := hφ's w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Item148HJ.residual_le_centralizer_singleton Lb d j.2)
  have hdJ3 : dJ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hdne : φ' dJ ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hue⟩ := (hφ'ker dJ).mp h1
    have hu3 : u ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, show (u : G) = d from hue]
      exact hd3)
    apply hd1
    rw [← show (u : G) = d from hue, eq_one_of_mem_aschbacherSolvableCore hu hu3]
    rfl
  have hdo : orderOf (φ' dJ) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hdJ3, map_one]) hdne
  have hZE : Subgroup.center ↥C ≤ E := by
    have hle : Subgroup.zpowers (φ' dJ) ≤ Subgroup.center ↥C := Subgroup.zpowers_le.mpr hdcen
    have heq : Subgroup.zpowers (φ' dJ) = Subgroup.center ↥C :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hCtc.1, Nat.card_zpowers, hdo])
    rw [← heq, Subgroup.zpowers_le]
    exact ⟨dJ, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hB.1 hdB, hdL⟩), rfl⟩
  have hgen := Desc143X.A6.sSup_eq_top hCq hCtc hE3 hE9 hZE
  have hθJ : inSubgroup (aschbacherSolvableCore 3) Lb ⊓ J ∈ 𝒬 := by
    refine ⟨inf_le_right, fun h3 => (Sec6.theta_solvable_and_not_dvd Lb).2
      (h3.trans (Subgroup.card_dvd_of_le inf_le_left)), fun α hα => ?_⟩
    have hαL : α ∈ Subgroup.normalizer (Lb : Set G) := hLb.2.1 hα
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyθ, hyJ⟩
      exact ⟨Sec12.conj_mem_inSubgroup_theta hαL hyθ,
        (Subgroup.mem_normalizer_iff.mp (hAJ hα) y).mp hyJ⟩
    · rintro ⟨hyθ, hyJ⟩
      have h1 := Sec12.conj_mem_inSubgroup_theta (inv_mem hαL) hyθ
      refine ⟨by simpa [mul_assoc] using h1, (Subgroup.mem_normalizer_iff.mp (hAJ hα) y).mpr hyJ⟩
  have hker3 : ¬ 3 ∣ Nat.card φ'.ker := by
    intro h3
    apply (Sec6.theta_solvable_and_not_dvd Lb).2
    refine h3.trans ?_
    have hle : φ'.ker.map J.subtype ≤ inSubgroup (aschbacherSolvableCore 3) Lb := by
      rintro _ ⟨j, hj, rfl⟩
      exact (hφ'ker j).mp (MonoidHom.mem_ker.mp hj)
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hY : ∀ Y : Subgroup ↥C, ¬ 3 ∣ Nat.card Y → E ≤ Subgroup.normalizer (Y : Set ↥C) →
      (Y.comap φ').map J.subtype ∈ 𝒬 := by
    intro Y hY3 hEY
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective J.subtype_injective,
        card_comap_of_surjective hφ's Y]
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
      · exact hY3 h3
      · exact hker3 h3
    ·
      set Q := (Y.comap φ').map J.subtype with hQ
      have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (Q : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨j, hj, rfl⟩
          have hjb : (j : G) * b = b * j :=
            Subgroup.mem_centralizer_singleton_iff.mp (hLbC (hJL j.2))
          refine ⟨j, hj, ?_⟩
          simp only [Subgroup.coe_subtype]
          rw [← hjb, mul_inv_cancel_right]
        · rintro ⟨j, hj, hjy⟩
          have hjb : (j : G) * b = b * j :=
            Subgroup.mem_centralizer_singleton_iff.mp (hLbC (hJL j.2))
          refine ⟨j, hj, ?_⟩
          simp only [Subgroup.coe_subtype] at hjy ⊢
          have e : b * y * b⁻¹ = b * (j : G) * b⁻¹ := by
            rw [← hjy, ← hjb, mul_inv_cancel_right]
          exact (mul_left_cancel (mul_right_cancel e)).symm
      have heN : A ⊓ Lb ≤ Subgroup.normalizer (Q : Set G) := by
        intro e he
        have heJ : e ∈ J := hEJ he
        set e' : ↥J := ⟨e, heJ⟩ with he'
        have he'E : φ' e' ∈ E := ⟨e', Subgroup.mem_subgroupOf.mpr he, rfl⟩
        have hNY := hEY he'E
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨j, hj, rfl⟩
          have hj' : φ' j ∈ Y := hj
          refine ⟨e' * j * e'⁻¹, ?_, rfl⟩
          show φ' (e' * j * e'⁻¹) ∈ Y
          rw [map_mul, map_mul, map_inv]
          exact (Subgroup.mem_normalizer_iff.mp hNY _).mp hj'
        · intro hy
          have hyJ : y ∈ J := by
            have h1 : e * y * e⁻¹ ∈ J := Subgroup.map_subtype_le _ hy
            have := J.mul_mem (J.mul_mem (J.inv_mem heJ) h1) heJ
            simpa [mul_assoc] using this
          obtain ⟨j, hj, hjy⟩ := hy
          refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
          have hje : j = e' * ⟨y, hyJ⟩ * e'⁻¹ := Subtype.ext (by simpa using hjy)
          have hj' : φ' j ∈ Y := hj
          show φ' ⟨y, hyJ⟩ ∈ Y
          rw [hje, map_mul, map_mul, map_inv] at hj'
          exact (Subgroup.mem_normalizer_iff.mp hNY _).mpr hj'
      intro α hα
      have hα' : α ∈ Subgroup.zpowers b ⊔ (A ⊓ Lb) := hAeq ▸ hα
      exact (sup_le hbN heN) hα'
  have hTmap : ((T.subgroupOf J).map φ') = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sSup_le fun Y hY' => ?_
    intro y hy
    obtain ⟨j, rfl⟩ := hφ's y
    have hjQ : (j : G) ∈ (Y.comap φ').map J.subtype := ⟨j, hy, rfl⟩
    exact ⟨j, Subgroup.mem_subgroupOf.mpr (le_sSup (hY Y hY'.1 hY'.2) hjQ), rfl⟩
  intro x hxJ
  have h1 : φ' ⟨x, hxJ⟩ ∈ (T.subgroupOf J).map φ' := hTmap ▸ Subgroup.mem_top _
  obtain ⟨t, ht, hte⟩ := h1
  have hker : t⁻¹ * ⟨x, hxJ⟩ ∈ φ'.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
  have hθ : ((t⁻¹ * ⟨x, hxJ⟩ : ↥J) : G) ∈ inSubgroup (aschbacherSolvableCore 3) Lb ⊓ J :=
    ⟨(hφ'ker _).mp (MonoidHom.mem_ker.mp hker), (t⁻¹ * ⟨x, hxJ⟩).2⟩
  have hxt : x = (t : G) * ((t⁻¹ * ⟨x, hxJ⟩ : ↥J) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hxt]
  exact hTΔ (T.mul_mem (Subgroup.mem_subgroupOf.mp ht) (le_sSup hθJ hθ))

theorem lB_le_delta {A L B Lb : Subgroup G} {c a b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) (haB : a ∈ B) :
    lB A B ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) :=
  (lB_le_delta_centralizer h hB hc).trans
    (delta_mono (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)))

end Desc143X

end CFSG.RankThree.PartTwo.Sec14
