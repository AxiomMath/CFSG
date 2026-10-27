module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNormalCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Holds
public import CFSG.Timmesfeld.Bridge.RootClosureRankOne
public import CFSG.GroupTheory.PowMemSupOfPGroup
public import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_range_eq_of_ker_eq {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : X →* Z) (h : f.ker = g.ker) :
    Nat.card f.range = Nat.card g.range := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, h]

theorem closure_twoElements_map_eq_top {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) {S : Set X} (hS : ∀ x ∈ S, ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hgen : Subgroup.closure S = ⊤) :
    Subgroup.closure {y : Y | ∃ n : ℕ, y ^ 2 ^ n = 1} = ⊤ := by
  have h1 : Subgroup.closure (f '' S) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective f hf]
  refine top_le_iff.mp ?_
  rw [← h1]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := hS x hx
  exact ⟨n, by rw [← map_pow, hn, map_one]⟩

theorem isPGroup_quotient_map_quotient {R : Type*} [Group R] {p : ℕ} {K M : Subgroup R}
    [K.Normal] [M.Normal] (hKM : K ≤ M) (h : IsPGroup p (R ⧸ M)) :
    IsPGroup p ((R ⧸ K) ⧸ M.map (QuotientGroup.mk' K)) :=
  IsPGroup.of_equiv h (QuotientGroup.quotientQuotientEquivQuotient K M hKM).symm

theorem isPGroup_quotient_inf_of_isPGroup_quotient {p : ℕ} {H R L : Subgroup G}
    [hL : (L.subgroupOf H).Normal] [hN : ((R ⊓ L).subgroupOf R).Normal] (hLH : L ≤ H) (hRH : R ≤ H)
    (h : IsPGroup p (↥H ⧸ L.subgroupOf H)) :
    IsPGroup p (↥R ⧸ (R ⊓ L).subgroupOf R) := by
  let N : Subgroup ↥R := (R ⊓ L).subgroupOf R
  let f : ↥R →* ↥H ⧸ L.subgroupOf H :=
    (QuotientGroup.mk' (L.subgroupOf H)).comp (Subgroup.inclusion hRH)
  have hker : f.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hx' : (Subgroup.inclusion hRH x : ↥H) ∈ L.subgroupOf H := by
        have h := hx
        rw [show f x = (QuotientGroup.mk' (L.subgroupOf H))
          (Subgroup.inclusion hRH x) from rfl] at h
        exact (QuotientGroup.eq_one_iff _).mp h
      exact ⟨x.2, Subgroup.mem_subgroupOf.mp hx'⟩
    · rintro ⟨-, hx⟩
      show (QuotientGroup.mk' (L.subgroupOf H)) (Subgroup.inclusion hRH x) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
  exact IsPGroup.of_injective h (QuotientGroup.lift N f hker.symm.le)
    ((QuotientGroup.injective_lift_iff N f hker.symm.le).2 hker.symm)

private theorem Ctx23L.le_normalizer_inf_L0 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) :
    c.L0 ⊔ D.T ≤ Subgroup.normalizer ((R ⊓ c.L0 : Subgroup G) : Set G) := by
  have hHnR : c.L0 ⊔ D.T ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR).mp hRn
  have hHnL : c.L0 ⊔ D.T ≤ Subgroup.normalizer (c.L0 : Set G) :=
    sup_le Subgroup.le_normalizer c.hL0.1.1
  exact (le_inf hHnR hHnL).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem Ctx23L.le_normalizer_pCoreOf_L0 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) :
    c.L0 ⊔ D.T ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 c.L0 : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · exact (Subgroup.le_normalizer : c.L0 ≤ Subgroup.normalizer (c.L0 : Set G)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) c.L0)
  · exact c.hL0.1.1.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) c.L0)

private theorem Ctx23L.normal_inf_L0_R {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) :
    ((R ⊓ c.L0).subgroupOf R).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (hR.trans (le_normalizer_inf_L0 c hR hRn))

private theorem Ctx23L.normal_inf_L0_L0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) :
    ((R ⊓ c.L0).subgroupOf c.L0).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    (le_sup_left.trans (le_normalizer_inf_L0 c hR hRn))

private theorem Ctx23L.normal_inf_pCoreOf {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) :
    ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R).Normal := by
  have hR₀n : ((R ⊓ c.L0).subgroupOf R).Normal := normal_inf_L0_R c hR hRn
  have hRnK₀ : R ≤ Subgroup.normalizer
      ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0 : Subgroup G) : Set G) :=
    (le_inf ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hR₀n)
      (hR.trans (le_normalizer_pCoreOf_L0 c))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans inf_le_left)).mpr hRnK₀

private theorem Ctx23L.isPGroup_sup_quotient_L0 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) [(c.L0.subgroupOf (D.T ⊔ c.L0)).Normal] :
    IsPGroup 2 (↥(D.T ⊔ c.L0) ⧸ c.L0.subgroupOf (D.T ⊔ c.L0)) :=
  CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2) (T := D.T) (C := c.L0)
    (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG)

private theorem closure_twoElements_subgroup_eq_top {R : Subgroup G}
    (hgen : ∃ S : Set G, (∀ x ∈ S, ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ R = Subgroup.closure S) :
    (⊤ : Subgroup ↥R) ≤ Subgroup.closure {x : ↥R | ∃ n : ℕ, x ^ 2 ^ n = 1} := by
  obtain ⟨S, hS2, hSR⟩ := hgen
  have hSsub : ∀ x ∈ S, x ∈ R := fun x hx => by
    rw [hSR]
    exact Subgroup.subset_closure hx
  let S' : Set ↥R := {x | (x : G) ∈ S}
  have hS'2 : ∀ x ∈ S', ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    rintro x hx
    obtain ⟨n, hn⟩ := hS2 (x : G) hx
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hS'gen : Subgroup.closure S' = ⊤ := by
    have himg : R.subtype '' S' = S := by
      ext x
      exact ⟨fun h => by obtain ⟨y, hy, rfl⟩ := h; exact hy,
        fun hx => ⟨⟨x, hSsub x hx⟩, hx, rfl⟩⟩
    have hmap : (Subgroup.closure S').map R.subtype = R := by
      rw [MonoidHom.map_closure, himg]
      exact hSR.symm
    refine Subgroup.map_injective R.subtype_injective ?_
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hS'gen]
  exact Subgroup.closure_mono hS'2

private theorem closure_twoElements_quotient_eq_top {R : Type*} [Group R] {N : Subgroup R}
    [N.Normal]
    (hgen : (⊤ : Subgroup R) ≤ Subgroup.closure {x : R | ∃ n : ℕ, x ^ 2 ^ n = 1}) :
    (⊤ : Subgroup (R ⧸ N)) ≤ Subgroup.closure {y : R ⧸ N | ∃ n : ℕ, y ^ 2 ^ n = 1} := by
  have hS : Subgroup.closure {x : R | ∃ n : ℕ, x ^ 2 ^ n = 1} = ⊤ := top_le_iff.mp hgen
  rw [← closure_twoElements_map_eq_top (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (fun x hx => hx) hS]

private theorem Ctx23L.odd_card_image_inf_M {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) (hRM : R ≤ D.M)
    [hKn : ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R).Normal] :
    Odd (Nat.card (((R ⊓ c.L0).subgroupOf R).map
      (QuotientGroup.mk' ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R)))) := by
  classical
  let R₀ : Subgroup G := R ⊓ c.L0
  let K₀ : Subgroup G := R₀ ⊓ CFSG.Open.pCoreOf 2 c.L0
  have hR₀n : (R₀.subgroupOf c.L0).Normal := normal_inf_L0_L0 c hR hRn
  haveI : Group.IsSolvable ↥(c.L0 ⊓ D.M) :=
    isSolvable_inf_M c h2010 h207 h1930 kRankOneBorel_holds
  have hR₀solv : Group.IsSolvable ↥R₀ :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (le_inf inf_le_right (inf_le_left.trans hRM)))
      (Subgroup.inclusion_injective _)
  haveI := hR₀solv
  let f₁ : ↥R₀ →* ↥R ⧸ K₀.subgroupOf R :=
    (QuotientGroup.mk' (K₀.subgroupOf R)).comp (Subgroup.inclusion inf_le_left)
  let f₂ : ↥R₀ →* Bar2 c.L0 :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L0)).comp (Subgroup.inclusion inf_le_right)
  have hker₁ : f₁.ker = K₀.subgroupOf R₀ := by
    ext x
    simp only [f₁, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hker₂ : f₂.ker = K₀.subgroupOf R₀ := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hiff : (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L0))
        (Subgroup.inclusion inf_le_right x) = 1 ↔
        (x : G) ∈ CFSG.Open.pCoreOf 2 c.L0 :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥c.L0)
        (Subgroup.inclusion inf_le_right x)).trans (CFSG.mem_openPCoreOf_iff _).symm
    rw [hiff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcard : Nat.card f₁.range = Nat.card f₂.range :=
    card_range_eq_of_ker_eq f₁ f₂ (by rw [hker₁, hker₂])
  have hf₁range : f₁.range =
      (R₀.subgroupOf R).map (QuotientGroup.mk' (K₀.subgroupOf R)) := by
    change ((QuotientGroup.mk' (K₀.subgroupOf R)).comp
      (Subgroup.inclusion inf_le_left)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hf₂range : f₂.range = barImage c.L0 R₀ := by
    change ((QuotientGroup.mk' (CFSG.pCore 2 ↥c.L0)).comp
      (Subgroup.inclusion inf_le_right)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hNnormal : (barImage c.L0 R₀).Normal := by
    rw [barImage]
    exact hR₀n.map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L0))
      (QuotientGroup.mk'_surjective _)
  have hsolvRange : Group.IsSolvable ↥(barImage c.L0 R₀) := by
    rw [← hf₂range]
    exact Group.isSolvable_of_surjective f₂.rangeRestrict_surjective
  have hcenter : barImage c.L0 R₀ ≤ Subgroup.center (Bar2 c.L0) :=
    Ctx23L.solvable_normal_le_center_bar2 c hNnormal hsolvRange
  have hoddCenter : Odd (Nat.card (Subgroup.center (Bar2 c.L0))) :=
    odd_card_center_bar2 (Bar2 c.L0)
      (CFSG.Timmesfeld.Bridge.RootClosure.pCore_quotient_pCore_eq_bot (K := ↥c.L0))
  have hoddBar : Odd (Nat.card ↥(barImage c.L0 R₀)) :=
    hoddCenter.of_dvd_nat (Subgroup.card_dvd_of_le hcenter)
  have hoddRange : Odd (Nat.card ↥f₂.range) := by
    rw [hf₂range]
    exact hoddBar
  rw [← hf₁range, hcard]
  exact hoddRange

private theorem Ctx23L.image_inf_L0_le_center {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) (hRM : R ≤ D.M)
    [hKn : ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R).Normal] :
    ((R ⊓ c.L0).subgroupOf R).map
      (QuotientGroup.mk' ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R)) ≤
      Subgroup.center (↥R ⧸ (R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R) := by
  classical
  let R₀ : Subgroup G := R ⊓ c.L0
  let K₀ : Subgroup G := R₀ ⊓ CFSG.Open.pCoreOf 2 c.L0
  have hR₀n : (R₀.subgroupOf R).Normal := normal_inf_L0_R c hR hRn
  have hcomm : ⁅R, c.L0⁆ ≤ CFSG.Open.pCoreOf 2 c.L0 :=
    Ctx23L.commutator_le_pCoreOf c hR hRn hRM
  intro y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  have hmR₀ : (m : G) ∈ R₀ := Subgroup.mem_subgroupOf.mp hm
  have hmL : (m : G) ∈ c.L0 := (Subgroup.mem_inf.mp hmR₀).2
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (K₀.subgroupOf R) x
  have hmemK₀ : ⁅(QuotientGroup.mk' (K₀.subgroupOf R)) r,
      (QuotientGroup.mk' (K₀.subgroupOf R)) m⁆ = 1 := by
    rw [← map_commutatorElement]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rw [commutatorElement_def]
      exact R₀.mul_mem (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hR₀n r.2) (m : G) |>.mp
          hmR₀) (R₀.inv_mem hmR₀)
    · exact hcomm (Subgroup.commutator_mem_commutator r.2 hmL)
  exact commutatorElement_eq_one_iff_mul_comm.mp hmemK₀

private theorem Ctx23L.isPGroup_quotient_inf_M {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) (hRM : R ≤ D.M)
    (hgen : ∃ S : Set G, (∀ x ∈ S, ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ R = Subgroup.closure S)
    [hKn : ((R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R).Normal] :
    IsPGroup 2 (↥R ⧸ (R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0).subgroupOf R) := by
  classical
  let H : Subgroup G := D.T ⊔ c.L0
  let R₀ : Subgroup G := R ⊓ c.L0
  let K₀ : Subgroup G := R₀ ⊓ CFSG.Open.pCoreOf 2 c.L0
  have hHnL : H ≤ Subgroup.normalizer (c.L0 : Set G) :=
    sup_le c.hL0.1.1 Subgroup.le_normalizer
  have hL0nH : (c.L0.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hHnL
  haveI := hL0nH
  have hHL : IsPGroup 2 (↥H ⧸ c.L0.subgroupOf H) := isPGroup_sup_quotient_L0 c
  have hR' : R ≤ H := by
    rw [show H = c.L0 ⊔ D.T from sup_comm D.T c.L0]
    exact hR
  have hR₀n : (R₀.subgroupOf R).Normal := normal_inf_L0_R c hR hRn
  haveI := hR₀n
  have hRR₀ : IsPGroup 2 (↥R ⧸ R₀.subgroupOf R) :=
    isPGroup_quotient_inf_of_isPGroup_quotient (p := 2) le_sup_right hR' hHL
  let K : Subgroup (↥R ⧸ K₀.subgroupOf R) :=
    (R₀.subgroupOf R).map (QuotientGroup.mk' (K₀.subgroupOf R))
  have hKnormal : K.Normal := hR₀n.map _ (QuotientGroup.mk'_surjective _)
  haveI := hKnormal
  have hquot : IsPGroup 2 ((↥R ⧸ K₀.subgroupOf R) ⧸ K) :=
    isPGroup_quotient_map_quotient (K := K₀.subgroupOf R) (M := R₀.subgroupOf R)
      (Subgroup.subgroupOf_mono R inf_le_left) hRR₀
  have hKcenter : K ≤ Subgroup.center (↥R ⧸ K₀.subgroupOf R) :=
    image_inf_L0_le_center c hR hRn hRM
  have hKodd : Odd (Nat.card K) := odd_card_image_inf_M c h2010 h207 h1930 hR hRn hRM
  have hgenR : (⊤ : Subgroup ↥R) ≤ Subgroup.closure {x : ↥R | ∃ n : ℕ, x ^ 2 ^ n = 1} :=
    closure_twoElements_subgroup_eq_top hgen
  have hgenH : (⊤ : Subgroup (↥R ⧸ K₀.subgroupOf R)) ≤
      Subgroup.closure {x : ↥R ⧸ K₀.subgroupOf R | ∃ n : ℕ, x ^ 2 ^ n = 1} :=
    closure_twoElements_quotient_eq_top (N := K₀.subgroupOf R) hgenR
  exact isPGroup_two_of_central_odd_quotient hKcenter hKodd hquot hgenH

theorem Ctx23L.le_pCore_of_normal {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D)
    {R : Subgroup G} (hR : R ≤ c.L0 ⊔ D.T)
    (hRn : (R.subgroupOf (c.L0 ⊔ D.T)).Normal) (hRM : R ≤ D.M)
    (hgen : ∃ S : Set G, (∀ x ∈ S, ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ R = Subgroup.closure S) :
    R ≤ CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) := by
  classical
  let K₀ : Subgroup G := R ⊓ c.L0 ⊓ CFSG.Open.pCoreOf 2 c.L0
  have hK₀n : (K₀.subgroupOf R).Normal := normal_inf_pCoreOf c hR hRn
  haveI := hK₀n
  have hK₀p : IsPGroup 2 (K₀.subgroupOf R) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) c.L0).to_inf_right.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).symm
  have hquot : IsPGroup 2 (↥R ⧸ K₀.subgroupOf R) :=
    isPGroup_quotient_inf_M c h2010 h207 h1930 hR hRn hRM hgen
  have hR2 : IsPGroup 2 ↥R := IsPGroup.of_subgroup_of_quotient hK₀p hquot
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hR
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hR).mp hRn) hR2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
