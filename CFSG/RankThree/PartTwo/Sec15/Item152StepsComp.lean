module

public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Step450
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item153
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Step152CompJ (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY4 A LB, ∀ M ∈ scriptY2 A, Y ≤ M → generalizedFitting ↥M = CFSG.pCore 2 ↥M →
    ¬ IsQuasisimple ↥(((deltaZero A LB M).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) →
      ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
        (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J

theorem eq_of_le_of_subgroupOf_normal {X N Y : Subgroup G} (hXp : Group.IsPerfect ↥X)
    (hXq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X)) (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) (hYN : Y ≤ N) (hYp : Group.IsPerfect ↥Y) (hY1 : Y ≠ ⊥) :
    N = X := by
  have hθ := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥X with hθdef
  set N' := N.subgroupOf X with hN'
  have hYX : Y ≤ X := hYN.trans hNX
  have hYN' : Y.subgroupOf X ≤ N' := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hYN (Subgroup.mem_subgroupOf.mp hy))
  have hmapn : (N'.map (QuotientGroup.mk' θ)).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hmapn with htop | hcen
  ·
    have hsup : N' ⊔ θ = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N'
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' N').comp θ.subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' q
      have hx : x ∈ N' ⊔ θ := hsup ▸ Subgroup.mem_top x
      rw [Subgroup.mem_sup_of_normal_left] at hx
      obtain ⟨n, hn, t, ht, rfl⟩ := hx
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have : Group.IsSolvable θ := hθ.1
    have hsolv : Group.IsSolvable (↥X ⧸ N') := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (↥X ⧸ N') :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N') (QuotientGroup.mk'_surjective N')
    have hNtop : N' = ⊤ := by
      by_contra hne
      have : Nontrivial (↥X ⧸ N') := QuotientGroup.nontrivial_iff.mpr hne
      exact Group.IsPerfect.not_isSolvable (↥X ⧸ N') hsolv
    refine le_antisymm hNX fun x hx => ?_
    have : (⟨x, hx⟩ : ↥X) ∈ N' := hNtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  ·
    exfalso
    have hKs : Group.IsSolvable
        ((Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ)) :=
      isSolvable_comap_center θ hθ.1
    have hNK : N' ≤ (Subgroup.center (↥X ⧸ θ)).comap (QuotientGroup.mk' θ) :=
      fun x hx => hcen (Subgroup.mem_map_of_mem _ hx)
    have hYs : Group.IsSolvable (Y.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hYN'.trans hNK))
        (Subgroup.inclusion_injective _)
    have hYs' : Group.IsSolvable ↥Y := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom) (MulEquiv.surjective _)
    have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
    exact Group.IsPerfect.not_isSolvable ↥Y hYs'

theorem eq_delta_of_item149 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h149 : Item149 A LB) {Y M X : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hM : M ∈ scriptY2 A)
    (hX : X ∈ thetaComponentsIn M) (hYX : Y ≤ X) : X = delta A LB X := by
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn hM.1.2 hX hYX (isPerfect_of_mem_scriptY4 hY)
      (ne_bot_of_mem_scriptY4 hY) hY.1.2
  have hXM : X ≤ M := le_of_mem_thetaComponentsIn hX
  have hXtop : X ≠ ⊤ := fun h => hM.1.1 (top_le_iff.mp (h ▸ hXM))
  obtain ⟨h1, h2, -⟩ := h149 X ⟨hXtop, hAX⟩
  set N := oPrimeResidualOf 3 (delta A LB X) with hNdef
  have hNΔ : N ≤ delta A LB X := oPrimeResidualOf_le_self 3 _
  have hNX : N ≤ X := hNΔ.trans (delta_le X)
  have hNn : (N.subgroupOf X).Normal := by
    rw [h1]
    exact h2
  have hYN : Y ≤ N :=
    calc Y = oPrimeResidualOf 3 Y := hY.2.1
      _ ≤ oPrimeResidualOf 3 (delta A LB X) :=
        oPrimeResidualOf_mono 3 (hY.2.2.1.le.trans (delta_mono hYX))
  have hNeq := eq_of_le_of_subgroupOf_normal (isPerfect_of_mem_thetaComponentsIn hX)
    (isQuasisimple_theta_of_mem_thetaComponentsIn hX) hNX hNn hYN (isPerfect_of_mem_scriptY4 hY)
    (ne_bot_of_mem_scriptY4 hY)
  exact le_antisymm (hNeq ▸ hNΔ) (delta_le X)

omit [Finite G] in
theorem mem_of_mem_sup_of_pow_eq_one [Finite G] {L U : Subgroup G}
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hU3 : Nat.Coprime 3 (Nat.card U)) {m : G}
    (hm : m ∈ L ⊔ U) {k : ℕ} (hk : m ^ 3 ^ k = 1) : m ∈ L := by
  set N := L ⊔ U with hN
  have hLN : L ≤ N := le_sup_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hUL
  have hLn : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  have hm' : m ∈ ((L : Set G) * (U : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L U hUL]
    exact hm
  obtain ⟨l, hl, u, hu, rfl⟩ := hm'
  have hlN : l ∈ N := hLN hl
  have huN : u ∈ N := (le_sup_right : U ≤ N) hu
  let π : N →* N ⧸ L.subgroupOf N := QuotientGroup.mk' (L.subgroupOf N)
  have hπl : π ⟨l, hlN⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := L.subgroupOf N) _).mpr (Subgroup.mem_subgroupOf.mpr hl)
  have hπm : π ⟨l * u, hm⟩ = π ⟨u, huN⟩ := by
    have hxlu : (⟨l * u, hm⟩ : N) = ⟨l, hlN⟩ * ⟨u, huN⟩ := rfl
    rw [hxlu, map_mul, hπl, one_mul]
  have hu1 : (⟨u, huN⟩ : N) ^ Nat.card U = 1 := by
    have h : (⟨u, hu⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h' ⊢
    exact h'
  have h1 : π ⟨l * u, hm⟩ ^ Nat.card U = 1 := by rw [hπm, ← map_pow, hu1, map_one]
  have h2 : π ⟨l * u, hm⟩ ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨l * u, hm⟩ : N) ^ 3 ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hk)
    rw [this, map_one]
  have hord : orderOf (π ⟨l * u, hm⟩) = 1 :=
    Nat.dvd_one.mp ((Nat.Coprime.pow_left k hU3).gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1))
  rw [orderOf_eq_one_iff] at hord
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := L.subgroupOf N) _).mp hord)

theorem exists_mem_thetaComponentsIn_of_component
    (hSz : KFacts.KPSz) {M : Subgroup G} (hM4 : SectionFourHyp ↥M) {Y : Subgroup G}
    (hYM : Y ≤ M) (hY3 : Y = oPrimeResidualOf 3 Y)
    {J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)} (hJ : IsComponent J)
    (hYJ : (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J) :
    ∃ X ∈ thetaComponentsIn M, Y ≤ X := by
  obtain ⟨L, hL, hLJ⟩ := Sec4.exists_mem_thetaComponents_map_eq hSz hM4.kGroup
    (Sec4.localRank_theta_quotient_le hM4) hJ
  set U := CFSG.pPrimeCore 3 ↥M with hU
  set π : ↥M →* ↥M ⧸ U := QuotientGroup.mk' U with hπ
  have hUs : U.IsSubnormal := (CFSG.pPrimeCore_normal (p := 3) (G := ↥M)).isSubnormal
  have hUL : U ≤ Subgroup.normalizer (L : Set ↥M) := by
    rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hL hUs with
      hLU | ⟨hUL, -⟩
    · exfalso
      have hJb : J = ⊥ := by
        rw [← hLJ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        exact hLU
      have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
      exact (Subgroup.nontrivial_iff_ne_bot J).mp this hJb
    · exact hUL
  have hU3 : Nat.Coprime 3 (Nat.card U) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M)
  have hYLU : Y.subgroupOf M ≤ L ⊔ U := by
    have h := Subgroup.comap_map_eq π L
    rw [QuotientGroup.ker_mk'] at h
    rw [← h, ← Subgroup.map_le_iff_le_comap, hLJ]
    exact hYJ
  have hYL : Y ≤ L.map M.subtype := by
    rw [hY3, oPrimeResidualOf, oPrimeResidual, Subgroup.map_le_iff_le_comap,
      Subgroup.closure_le]
    rintro y ⟨k, hk⟩
    have hyM : (y : G) ∈ M := hYM y.2
    have hyLU : (⟨y, hyM⟩ : ↥M) ∈ L ⊔ U := hYLU (Subgroup.mem_subgroupOf.mpr y.2)
    have hk' : (⟨y, hyM⟩ : ↥M) ^ 3 ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      have h := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h)
    exact ⟨⟨y, hyM⟩, mem_of_mem_sup_of_pow_eq_one hUL hU3 hyLU hk', rfl⟩
  exact ⟨L.map M.subtype, ⟨L, hL, rfl⟩, hYL⟩

omit [Finite G] in
theorem exists_component_of_isQuasisimple {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h148 : Item148Normal A LB) {Y M : Subgroup G} (hM : M ∈ scriptY A)
    (hYD : Y ≤ deltaZero A LB M)
    (hq : IsQuasisimple ↥(((deltaZero A LB M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))) :
    ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
      (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J := by
  refine ⟨_, ⟨hq, (h148 M hM).isSubnormal⟩, Subgroup.map_mono fun y hy => ?_⟩
  exact Subgroup.mem_subgroupOf.mpr (hYD (Subgroup.mem_subgroupOf.mp hy))

theorem step152Comp_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h149 : Item149 A (lB A))
    (h148 : Item148Normal A (lB A)) (hSz : KFacts.KPSz) (hJ : Step152CompJ A (lB A)) :
    Step152Comp A (lB A) := by
  intro Y hY M hM hYM hF
  have hMtop : M ≠ ⊤ := hM.1.1
  have hM4 : SectionFourHyp ↥M := h.toTheoremFourHyp.sectionFourHyp hMtop
  have hYD : Y ≤ deltaZero A (lB A) M := by
    have h151 := rank3II_15_1_of' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415
      (KFacts.KS14.center_nativeJ2_eq_bot h415) h hY
    rw [h151]
    exact deltaZero_mono hYM
  obtain ⟨J, hJc, hYJ⟩ : ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
      (Y.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ J := by
    by_cases hq : IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))
    · exact exists_component_of_isQuasisimple h148 hM.1 hYD hq
    · exact hJ Y hY M hM hYM hF hq
  obtain ⟨X, hX, hYX⟩ :=
    exists_mem_thetaComponentsIn_of_component hSz hM4 hYM hY.2.1 hJc hYJ
  exact ⟨X, hX, hYX, eq_delta_of_item149 h149 hY hM hX hYX⟩

@[expose] noncomputable def Step152CompJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152CompJ A (lB A)

end CFSG.RankThree.PartTwo.Sec15
