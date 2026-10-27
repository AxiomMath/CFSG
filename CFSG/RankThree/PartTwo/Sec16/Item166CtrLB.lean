module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrKcd
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofA6
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofFix
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private abbrev lBJ (Lb : Subgroup G) (d : G) : Subgroup G :=
  inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G))

private lemma lB_E_pow_three {A L Lb : Subgroup G} {c d : G} (h : Sec14Std G A c L) :
    ∀ x ∈ ((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
      (Item148HJ.resProj Lb d).rangeRestrict, x ^ 3 = 1 := by
  rintro _ ⟨e, he, rfl⟩
  rw [← map_pow]
  have he3 : e ^ 3 = 1 := Subtype.ext (by
    simpa using h.isE27'.1.2 (e : G) (Subgroup.mem_subgroupOf.mp he).1)
  rw [he3, map_one]

private lemma lB_E_card {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Nat.card (((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
      (Item148HJ.resProj Lb d).rangeRestrict) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := lBJ Lb d with hJ
  set φ := Item148HJ.resProj Lb d with hφ
  set E₀ : Subgroup ↥J := (A ⊓ Lb).subgroupOf J with hE₀
  have hA := h.isE27'
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  obtain ⟨-, h9, -⟩ := j2_point_facts hS.toSec13Data (Item148HJ.j2_of_isLBConfig hc)
  have hEJ : A ⊓ Lb ≤ J := Item148HJ.inf_le_residual h hB hc
  have hE₀card : Nat.card E₀ = 9 := by
    rw [hE₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, h9]
  have hbot : φ.rangeRestrict.ker.subgroupOf E₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨e, he⟩ hek
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hek' : (e : G) ∈ inSubgroup (aschbacherSolvableCore 3) Lb := by
      have h1 : φ.rangeRestrict e = 1 :=
        MonoidHom.mem_ker.mp (Subgroup.mem_subgroupOf.mp hek)
      exact (Item148HJ.mem_ker_resProj e).mp (congrArg Subtype.val h1)
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
  have h1 := Subgroup.relIndex_ker E₀ φ.rangeRestrict
  rw [← h1, Subgroup.relIndex, hbot, Subgroup.index_bot, hE₀card]

private lemma lB_center_le_E {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Subgroup.center (Item148HJ.resProj Lb d).range ≤
      ((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
        (Item148HJ.resProj Lb d).rangeRestrict := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := lBJ Lb d with hJ
  set φ := Item148HJ.resProj Lb d with hφ
  set E₀ : Subgroup ↥J := (A ⊓ Lb).subgroupOf J with hE₀
  set E : Subgroup φ.range := E₀.map φ.rangeRestrict with hE
  obtain ⟨hdL, -, -, hCcard, -, -, -⟩ := Item148HJ.resProj_facts h hB hc
  obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27'
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hEJ : A ⊓ Lb ≤ J := Item148HJ.inf_le_residual h hB hc
  have hdJ : d ∈ J := hEJ (Subgroup.mem_inf.mpr ⟨hdA, hdL⟩)
  set dJ : ↥J := ⟨d, hdJ⟩ with hdJdef
  have hdcen : φ.rangeRestrict dJ ∈ Subgroup.center φ.range := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨j, rfl⟩ := MonoidHom.rangeRestrict_surjective φ w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Item148HJ.residual_le_centralizer_singleton Lb d j.2)
  have hdJ3 : dJ ^ 3 = 1 := Subtype.ext (by
    simpa using h.isE27'.1.2 d hdA)
  have hdne : φ.rangeRestrict dJ ≠ 1 := by
    intro h1
    have h1' : φ dJ = 1 := congrArg Subtype.val h1
    obtain ⟨u, hu, hue⟩ := (Item148HJ.mem_ker_resProj dJ).mp (MonoidHom.mem_ker.mpr h1')
    have hu3 : u ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, show (u : G) = d from hue]
      exact h.isE27'.1.2 d hdA)
    apply hd1
    rw [← show (u : G) = d from hue, eq_one_of_mem_aschbacherSolvableCore hu hu3]
    rfl
  have hdo : orderOf (φ.rangeRestrict dJ) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hdJ3, map_one]) hdne
  have hle : Subgroup.zpowers (φ.rangeRestrict dJ) ≤ Subgroup.center φ.range :=
    Subgroup.zpowers_le.mpr hdcen
  have heq : Subgroup.zpowers (φ.rangeRestrict dJ) = Subgroup.center φ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hCcard, Nat.card_zpowers, hdo])
  rw [← heq, Subgroup.zpowers_le]
  exact Subgroup.mem_map_of_mem φ.rangeRestrict
    (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hdA, hdL⟩))

private lemma lB_sSup_E_top {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    sSup {Y : Subgroup (Item148HJ.resProj Lb d).range |
        ¬ 3 ∣ Nat.card Y ∧
          ((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
            (Item148HJ.resProj Lb d).rangeRestrict ≤
          Subgroup.normalizer (Y : Set (Item148HJ.resProj Lb d).range)} = ⊤ := by
  obtain ⟨-, -, hq, -, -, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  exact Desc143X.A6.sSup_eq_top hq htc (lB_E_pow_three h) (lB_E_card h hB hc)
    (lB_center_le_E h hB hc)

private lemma lB_preimage_le_card {Lb : Subgroup G} {d : G}
    (Y : Subgroup (Item148HJ.resProj Lb d).range) (hY3 : ¬ 3 ∣ Nat.card Y) :
    (Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map (lBJ Lb d).subtype ≤ lBJ Lb d ∧
      ¬ 3 ∣ Nat.card
        ((Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map (lBJ Lb d).subtype) := by
  have hφs : Function.Surjective (Item148HJ.resProj Lb d).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective (Item148HJ.resProj Lb d)
  have hker3 : ¬ 3 ∣ Nat.card (Item148HJ.resProj Lb d).rangeRestrict.ker := by
    intro h3
    apply (Sec6.theta_solvable_and_not_dvd Lb).2
    refine h3.trans ?_
    have hle : (Item148HJ.resProj Lb d).rangeRestrict.ker.map (lBJ Lb d).subtype ≤
        inSubgroup (aschbacherSolvableCore 3) Lb := by
      rintro _ ⟨j, hj, rfl⟩
      have h1 : (Item148HJ.resProj Lb d) j = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
      exact (Item148HJ.mem_ker_resProj j).mp h1
    rw [← Subgroup.card_map_of_injective (lBJ Lb d).subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective (lBJ Lb d).subtype_injective,
    Desc143X.card_comap_of_surjective hφs Y]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
  · exact hY3 h3
  · exact hker3 h3

private lemma lB_preimage_zpowers {A B Lb : Subgroup G} {b d : G}
    (hc : IsLBConfig A B b d Lb) (Y : Subgroup (Item148HJ.resProj Lb d).range) :
    Subgroup.zpowers b ≤ Subgroup.normalizer
      (((Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map
        (lBJ Lb d).subtype) : Set G) := by
  set Q := (Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map (lBJ Lb d).subtype with hQ
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLb.1
  have hJL : lBJ Lb d ≤ Lb := Item148HJ.residual_le Lb d
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

private lemma lB_preimage_inf_normalizes {A L B Lb : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (Y : Subgroup (Item148HJ.resProj Lb d).range)
    (hEY : (((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
        (Item148HJ.resProj Lb d).rangeRestrict) ≤
      Subgroup.normalizer (Y : Set (Item148HJ.resProj Lb d).range)) :
    A ⊓ Lb ≤ Subgroup.normalizer
      (((Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map
        (lBJ Lb d).subtype) : Set G) := by
  set Q := (Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map (lBJ Lb d).subtype with hQ
  have hEJ : A ⊓ Lb ≤ lBJ Lb d := Item148HJ.inf_le_residual h hB hc
  intro e he
  have heJ : e ∈ lBJ Lb d := hEJ he
  set e' : ↥(lBJ Lb d) := ⟨e, heJ⟩ with he'
  have he'E : (Item148HJ.resProj Lb d).rangeRestrict e' ∈
      ((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
        (Item148HJ.resProj Lb d).rangeRestrict :=
    Subgroup.mem_map_of_mem (Item148HJ.resProj Lb d).rangeRestrict
      (Subgroup.mem_subgroupOf.mpr he)
  have hNY := hEY he'E
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : (Item148HJ.resProj Lb d).rangeRestrict j ∈ Y := hj
    refine ⟨e' * j * e'⁻¹, ?_, rfl⟩
    show (Item148HJ.resProj Lb d).rangeRestrict (e' * j * e'⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hNY _).mp hj'
  · intro hy
    have hyJ : y ∈ lBJ Lb d := by
      have h1 : e * y * e⁻¹ ∈ lBJ Lb d := Subgroup.map_subtype_le _ hy
      have := (lBJ Lb d).mul_mem ((lBJ Lb d).mul_mem ((lBJ Lb d).inv_mem heJ) h1) heJ
      simpa [mul_assoc] using this
    obtain ⟨j, hj, hjy⟩ := hy
    refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
    have hje : j = e' * ⟨y, hyJ⟩ * e'⁻¹ := Subtype.ext (by simpa using hjy)
    have hj' : (Item148HJ.resProj Lb d).rangeRestrict j ∈ Y := hj
    show (Item148HJ.resProj Lb d).rangeRestrict ⟨y, hyJ⟩ ∈ Y
    rw [hje, map_mul, map_mul, map_inv] at hj'
    exact (Subgroup.mem_normalizer_iff.mp hNY _).mpr hj'

private lemma lB_preimage_mem {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (Y : Subgroup (Item148HJ.resProj Lb d).range) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hEY : (((A ⊓ Lb).subgroupOf (lBJ Lb d)).map
        (Item148HJ.resProj Lb d).rangeRestrict) ≤
      Subgroup.normalizer (Y : Set (Item148HJ.resProj Lb d).range)) :
    (Y.comap (Item148HJ.resProj Lb d).rangeRestrict).map (lBJ Lb d).subtype ∈
      {Q : Subgroup G | Q ≤ lBJ Lb d ∧ ¬ 3 ∣ Nat.card Q ∧
        A ≤ Subgroup.normalizer (Q : Set G)} := by
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  have hJ2 := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, -, hAeq⟩ := j2_point_facts hS.toSec13Data hJ2
  have hle := lB_preimage_le_card Y hY3
  have hbN := lB_preimage_zpowers hc Y
  have heN := lB_preimage_inf_normalizes h hB hc Y hEY
  exact ⟨hle.1, hle.2, fun α hα => (sup_le hbN heN) (hAeq ▸ hα)⟩
private lemma lB_theta_inf_mem {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    inSubgroup (aschbacherSolvableCore 3) Lb ⊓ lBJ Lb d ∈
      {Q : Subgroup G | Q ≤ lBJ Lb d ∧ ¬ 3 ∣ Nat.card Q ∧
        A ≤ Subgroup.normalizer (Q : Set G)} := by
  have hA := h.isE27'
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨y, hB.1 hy⟩ ⟨x, hx⟩)
  have hCJ := Item148HJ.centralizer_le_normalizer_residual h hc
  have hAJ : A ≤ Subgroup.normalizer (lBJ Lb d : Set G) := hAB.trans hCJ
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
    refine ⟨by simpa [mul_assoc] using h1,
      (Subgroup.mem_normalizer_iff.mp (hAJ hα) y).mpr hyJ⟩

theorem lB_le_sSup_invariant {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    lB A B ≤ sSup {Q : Subgroup G | Q ≤ lB A B ∧ ¬ 3 ∣ Nat.card Q ∧
      A ≤ Subgroup.normalizer (Q : Set G)} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Item148HJ.lB_eq_residual h hB hc]
  set J := lBJ Lb d with hJ
  set φ := Item148HJ.resProj Lb d with hφ
  set 𝒬 := {Q : Subgroup G | Q ≤ J ∧ ¬ 3 ∣ Nat.card Q ∧
    A ≤ Subgroup.normalizer (Q : Set G)} with h𝒬
  set T := sSup 𝒬 with hT
  have hθJ : inSubgroup (aschbacherSolvableCore 3) Lb ⊓ J ∈ 𝒬 := lB_theta_inf_mem h hB hc
  have hY : ∀ Y : Subgroup φ.range, ¬ 3 ∣ Nat.card Y →
      ((A ⊓ Lb).subgroupOf J).map φ.rangeRestrict ≤
        Subgroup.normalizer (Y : Set φ.range) →
      (Y.comap φ.rangeRestrict).map J.subtype ∈ 𝒬 := by
    intro Y hY3 hEY
    exact lB_preimage_mem h hB hc Y hY3 hEY
  have hgen := lB_sSup_E_top h hB hc
  have hTmap : (T.subgroupOf J).map φ.rangeRestrict = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sSup_le fun Y hY' => ?_
    intro y hy
    obtain ⟨j, rfl⟩ := MonoidHom.rangeRestrict_surjective φ y
    have hjQ : (j : G) ∈ (Y.comap φ.rangeRestrict).map J.subtype := ⟨j, hy, rfl⟩
    exact ⟨j, Subgroup.mem_subgroupOf.mpr (le_sSup (hY Y hY'.1 hY'.2) hjQ), rfl⟩
  have hker_le : φ.rangeRestrict.ker ≤ T.subgroupOf J := by
    intro j hj
    have hjθ : (j : G) ∈ inSubgroup (aschbacherSolvableCore 3) Lb ⊓ J :=
      ⟨(Item148HJ.mem_ker_resProj j).mp
        (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hj))), j.2⟩
    exact Subgroup.subgroupOf_mono J (le_sSup hθJ) (Subgroup.mem_subgroupOf.mpr hjθ)
  have htop : T.subgroupOf J = ⊤ := by
    have hcm := Subgroup.comap_map_eq_self (f := φ.rangeRestrict)
      (H := T.subgroupOf J) hker_le
    rw [hTmap, Subgroup.comap_top] at hcm
    exact hcm.symm
  exact Subgroup.subgroupOf_eq_top.mp htop

section

theorem lB_le_delta_lB {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    lB A B ≤ delta A (lB A) (lB A B) := by
  refine (lB_le_sSup_invariant h hB hc).trans (sSup_le fun Q hQ => ?_)
  obtain ⟨hQJ, hQ3, hAQ⟩ := hQ
  have hS := Item148HJ.sec14Std_of_isLBConfig h hc
  have hJ2 := Item148HJ.j2_of_isLBConfig hc
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hQb : Q ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    have hQC : Q ≤ Subgroup.centralizer ({b} : Set G) :=
      (hQJ.trans (lB_le_centralizer A B)).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcomm : q * b = b * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)
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
  exact le_delta hmem.1 hQJ

end

theorem isTripleCover_lB {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Sec4.IsTripleCover (↥(lB A B) ⧸ CFSG.pCore 2 ↥(lB A B)) (alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Item148HJ.lB_eq_residual h hB hc]
  set J := lBJ Lb d with hJ
  set φ := Item148HJ.resProj Lb d with hφ
  obtain ⟨hdL, -, hq, hZ, -, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  obtain ⟨-, -, -, ⟨φJ⟩, -⟩ := hc
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hJ2s := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJ2c := KFacts.KS14.center_nativeJ2_eq_bot h415
  have hc0 : Subgroup.center (↥Lb ⧸ CFSG.pCore 2 ↥Lb) = ⊥ := by
    have hmap := Subgroup.map_center_eq φJ
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φJ.injective).mp hmap
  have hqL : CFSG.IsQuasisimple (↥Lb ⧸ CFSG.pCore 2 ↥Lb) :=
    isQuasisimple_of_mulEquiv_nativeJ2 hJ2s hJ2c φJ
  have hθO : aschbacherSolvableCore 3 ↥Lb = CFSG.pCore 2 ↥Lb :=
    aschbacherSolvableCore_eq_pCore_two hqL hc0
  have hsub : inSubgroup (aschbacherSolvableCore 3) Lb =
      inSubgroup (CFSG.pCore 2) Lb := by
    simp only [inSubgroup, hθO]
  have hker_eq : φ.ker = (inSubgroup (CFSG.pCore 2) Lb).subgroupOf J := by
    ext j
    exact (Item148HJ.mem_ker_resProj j).trans (by
      rw [hsub]
      exact Subgroup.mem_subgroupOf.symm)
  have hker_p : IsPGroup 2 φ.ker := by
    rw [hker_eq]
    exact ((CFSG.pCore_isPGroup (p := 2) (G := ↥Lb)).map Lb.subtype).comap_subtype
  have hpcore_le : CFSG.pCore 2 ↥J ≤ φ.ker := by
    refine Item148HJ.le_ker_of_normal φ hq hZ (CFSG.pCore_normal (p := 2) (G := ↥J)) ?_
    have hp : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    intro h3
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hker_le : φ.ker ≤ CFSG.pCore 2 ↥J := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le φ.ker (le_iSup_of_le (MonoidHom.normal_ker φ)
      (le_iSup_of_le hker_p le_rfl))
  have hpcore_eq : CFSG.pCore 2 ↥J = φ.ker := le_antisymm hpcore_le hker_le
  let e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hpcore_eq).trans
      (QuotientGroup.quotientKerEquivRange φ)
  exact KFacts.KS14.isTripleCover_congr e.symm htc

section

theorem lB_closure_eq_residual {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
  Item148HJ.lB_eq_residual h.toSec14Std
    (isHyperplane_closure_cd h hJ hdA hd1 hdc)
    (isLBConfig_closure_cd_of_threeCentral h hJ hdc)

theorem lB_closure_le {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    lB A (Subgroup.closure {c, d}) ≤ L := by
  rw [lB_closure_eq_residual h hJ hdA hd1 hdc]
  exact Item148HJ.residual_le L d

theorem mem_lB_closure {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    d ∈ lB A (Subgroup.closure {c, d}) := by
  rw [lB_closure_eq_residual h hJ hdA hd1 hdc]
  exact mem_ld_of_threeCentral h hJ hdA hd1 hdc

theorem le_normalizer_lB_closure {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    A ≤ Subgroup.normalizer ((lB A (Subgroup.closure {c, d}) : Subgroup G) : Set G) := by
  intro w hw
  refine Sec14.Res9Fix.mem_normalizer_lB
    (isHyperplane_closure_cd h hJ hdA hd1 hdc) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (h.toSec14Std.isE27'.1.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)

end

end CFSG.RankThree.PartTwo.Sec16.Ctr166
