module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeNormalCoreTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.Quasithin.E1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S231

theorem commutator_le_pCoreOf {D : Data G} {L R : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hR : R ≤ L ⊔ D.T) (hRn : L ⊔ D.T ≤ normalizer (R : Set G)) (hRM : R ≤ D.M) :
    ⁅R, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  have hLnotM : ¬ L ≤ D.M :=
    fun h => hL.2.2.1.2.1 (sup_le h D.sylowM.le)
  have hRnL : R ≤ Subgroup.normalizer (L : Set G) :=
    hR.trans (sup_le Subgroup.le_normalizer hL.1)
  have hleL : ⁅R, L⁆ ≤ L :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hRnL
  have hleR : ⁅R, L⁆ ≤ R :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left : L ≤ L ⊔ D.T).trans hRn)
  have hLR : L ≤ Subgroup.normalizer ((⁅R, L⁆ : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer L R L
      ((le_sup_left : L ≤ L ⊔ D.T).trans hRn) Subgroup.le_normalizer
  have hTR : D.T ≤ Subgroup.normalizer ((⁅R, L⁆ : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer D.T R L
      ((le_sup_right : D.T ≤ L ⊔ D.T).trans hRn) hL.1
  have hQleL : CFSG.Open.pCoreOf 2 L ≤ L :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQleH : CFSG.Open.pCoreOf 2 L ≤ L ⊔ D.T := hQleL.trans le_sup_left
  have hQleTL : CFSG.Open.pCoreOf 2 L ≤ D.T ⊓ L :=
    pCoreOf_two_le_of_isSylowIn
      (Ctx23L.isSylowIn_inf_of_le_normalizer (D := D) hL.1)
  have hQleT : CFSG.Open.pCoreOf 2 L ≤ D.T := hQleTL.trans inf_le_left
  have hQleM : CFSG.Open.pCoreOf 2 L ≤ D.M := hQleT.trans D.sylowM.le
  have hHnQ : L ⊔ D.T ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L))
      (hL.1.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L))
  have hR1not : ¬ L ≤ ⁅R, L⁆ ⊔ CFSG.Open.pCoreOf 2 L := by
    intro hle
    exact hLnotM (hle.trans (sup_le (hleR.trans hRM) hQleM))
  have hdouble : ⁅⁅R, L⁆, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
    commutator_le_pCoreOf_of_mem_calL hL hleL hLR hTR hR1not
  exact commutator_le_pCoreOf_of_rotate (H := L ⊔ D.T) le_sup_left hR hQleH hHnQ
    hL.2.1 hdouble

private theorem le_normalizer_inf_L0_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G)) :
    L ⊔ D.T ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
  have hHnL : L ⊔ D.T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hL.1
  exact (le_inf hRn hHnL).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem le_normalizer_pCoreOf_L_S01 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) :
    L ⊔ D.T ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · exact (Subgroup.le_normalizer : L ≤ Subgroup.normalizer (L : Set G)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L)
  · exact hL.1.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L)

private theorem normal_inf_L0_R_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hR : R ≤ L ⊔ D.T)
    (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G)) :
    ((R ⊓ L).subgroupOf R).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (hR.trans (le_normalizer_inf_L0_S01 hL hRn))

private theorem normal_inf_pCoreOf_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hR : R ≤ L ⊔ D.T)
    (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G)) :
    ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R).Normal := by
  have hR₀n : ((R ⊓ L).subgroupOf R).Normal := normal_inf_L0_R_S01 hL hR hRn
  have hRnK₀ : R ≤ Subgroup.normalizer
      ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) :=
    (le_inf ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hR₀n)
      (hR.trans (le_normalizer_pCoreOf_L_S01 hL))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (inf_le_left.trans inf_le_left)).mpr hRnK₀

private theorem isPGroup_sup_quotient_L_S01 {D : Data G} {L : Subgroup G}
    [(L.subgroupOf (D.T ⊔ L)).Normal] :
    IsPGroup 2 (↥(D.T ⊔ L) ⧸ L.subgroupOf (D.T ⊔ L)) :=
  CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2) (T := D.T) (C := L)
    (CFSG.ABGLocalTools.IsSylowOf.isPGroup D.sylowG)

omit [Finite G] in
private theorem closure_twoElements_subgroup_eq_top_S01 {R : Subgroup G}
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

private theorem closure_twoElements_quotient_eq_top_S01 {R : Type*} [Group R]
    {N : Subgroup R} [N.Normal]
    (hgen : (⊤ : Subgroup R) ≤ Subgroup.closure {x : R | ∃ n : ℕ, x ^ 2 ^ n = 1}) :
    (⊤ : Subgroup (R ⧸ N)) ≤ Subgroup.closure {y : R ⧸ N | ∃ n : ℕ, y ^ 2 ^ n = 1} := by
  have hS : Subgroup.closure {x : R | ∃ n : ℕ, x ^ 2 ^ n = 1} = ⊤ := top_le_iff.mp hgen
  rw [← closure_twoElements_map_eq_top (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (fun x hx => hx) hS]

omit [Finite G] in
private theorem card_image_eq_card_barImage_S01 {L R : Subgroup G}
    [hKn : ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R).Normal] :
    Nat.card (((R ⊓ L).subgroupOf R).map
      (QuotientGroup.mk' ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R))) =
      Nat.card (barImage L (R ⊓ L)) := by
  classical
  let R₀ : Subgroup G := R ⊓ L
  let K₀ : Subgroup G := R₀ ⊓ CFSG.Open.pCoreOf 2 L
  have : (K₀.subgroupOf R).Normal := hKn
  let f₁ : ↥R₀ →* ↥R ⧸ K₀.subgroupOf R :=
    (QuotientGroup.mk' (K₀.subgroupOf R)).comp (Subgroup.inclusion inf_le_left)
  let f₂ : ↥R₀ →* Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion inf_le_right)
  have hker₁ : f₁.ker = K₀.subgroupOf R₀ := by
    ext x
    simp only [f₁, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hker₂ : f₂.ker = K₀.subgroupOf R₀ := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hiff : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (Subgroup.inclusion inf_le_right x) = 1 ↔
        (x : G) ∈ CFSG.Open.pCoreOf 2 L :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L)
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
  have hf₂range : f₂.range = barImage L R₀ := by
    change ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion inf_le_right)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hf₂range' : Nat.card f₂.range = Nat.card (barImage L (R ⊓ L)) := by
    rw [hf₂range]
  rw [← hf₁range]
  exact hcard.trans hf₂range'

private theorem odd_card_barImage_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G))
    (hRM : R ≤ D.M) :
    Odd (Nat.card (barImage L (R ⊓ L))) := by
  let R₀ : Subgroup G := R ⊓ L
  have hLR₀ : L ≤ Subgroup.normalizer (R₀ : Set G) :=
    le_sup_left.trans (le_normalizer_inf_L0_S01 hL hRn)
  have hTR₀ : D.T ≤ Subgroup.normalizer (R₀ : Set G) :=
    le_sup_right.trans (le_normalizer_inf_L0_S01 hL hRn)
  have hLnotM : ¬ L ≤ D.M :=
    fun h => hL.2.2.1.2.1 (sup_le h D.sylowM.le)
  have hQleM : CFSG.Open.pCoreOf 2 L ≤ D.M :=
    (((pCoreOf_two_le_of_isSylowIn
      (Ctx23L.isSylowIn_inf_of_le_normalizer (D := D) hL.1)).trans inf_le_left).trans
        D.sylowM.le)
  have hR₀M : R₀ ≤ D.M := inf_le_left.trans hRM
  have hR₀not : ¬ L ≤ R₀ ⊔ CFSG.Open.pCoreOf 2 L :=
    fun hle => hLnotM (hle.trans (sup_le hR₀M hQleM))
  have hcenter : barImage L R₀ ≤ Subgroup.center (Bar2 L) :=
    barImage_le_center_of_mem_calL hL inf_le_right hLR₀ hTR₀ hR₀not
  have hoddCenter : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    odd_card_center_bar2 (Bar2 L)
      (CFSG.Timmesfeld.Bridge.RootClosure.pCore_quotient_pCore_eq_bot (K := ↥L))
  exact hoddCenter.of_dvd_nat (Subgroup.card_dvd_of_le hcenter)

private theorem odd_card_image_inf_M_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G))
    (hRM : R ≤ D.M) [hKn : ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R).Normal] :
    Odd (Nat.card (((R ⊓ L).subgroupOf R).map
      (QuotientGroup.mk' ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R)))) := by
  rw [card_image_eq_card_barImage_S01 (L := L) (R := R)]
  exact odd_card_barImage_S01 hL hRn hRM

private theorem image_inf_L0_le_center_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hR : R ≤ L ⊔ D.T)
    (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G)) (hRM : R ≤ D.M)
    [hKn : ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R).Normal] :
    ((R ⊓ L).subgroupOf R).map
      (QuotientGroup.mk' ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R)) ≤
      Subgroup.center (↥R ⧸ (R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R) := by
  classical
  let R₀ : Subgroup G := R ⊓ L
  let K₀ : Subgroup G := R₀ ⊓ CFSG.Open.pCoreOf 2 L
  have hR₀n : (R₀.subgroupOf R).Normal := normal_inf_L0_R_S01 hL hR hRn
  have hcomm : ⁅R, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
    commutator_le_pCoreOf hL hR hRn hRM
  intro y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  have hmR₀ : (m : G) ∈ R₀ := Subgroup.mem_subgroupOf.mp hm
  have hmL : (m : G) ∈ L := (Subgroup.mem_inf.mp hmR₀).2
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

private theorem isPGroup_quotient_inf_M_S01 {D : Data G} {L R : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hR : R ≤ L ⊔ D.T)
    (hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G)) (hRM : R ≤ D.M)
    (hgen : ∃ S : Set G, (∀ x ∈ S, ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ R = Subgroup.closure S)
    [hKn : ((R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R).Normal] :
    IsPGroup 2 (↥R ⧸ (R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L).subgroupOf R) := by
  classical
  let H : Subgroup G := D.T ⊔ L
  let R₀ : Subgroup G := R ⊓ L
  let K₀ : Subgroup G := R₀ ⊓ CFSG.Open.pCoreOf 2 L
  have hHnL : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hL.1 Subgroup.le_normalizer
  have hLnH : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hHnL
  have := hLnH
  have hHL : IsPGroup 2 (↥H ⧸ L.subgroupOf H) := isPGroup_sup_quotient_L_S01
  have hR' : R ≤ H := by
    rw [show H = L ⊔ D.T from sup_comm D.T L]
    exact hR
  have hR₀n : (R₀.subgroupOf R).Normal := normal_inf_L0_R_S01 hL hR hRn
  have := hR₀n
  have hRR₀ : IsPGroup 2 (↥R ⧸ R₀.subgroupOf R) :=
    isPGroup_quotient_inf_of_isPGroup_quotient (p := 2) le_sup_right hR' hHL
  let K : Subgroup (↥R ⧸ K₀.subgroupOf R) :=
    (R₀.subgroupOf R).map (QuotientGroup.mk' (K₀.subgroupOf R))
  have hKnormal : K.Normal := hR₀n.map _ (QuotientGroup.mk'_surjective _)
  have := hKnormal
  have hquot : IsPGroup 2 ((↥R ⧸ K₀.subgroupOf R) ⧸ K) :=
    isPGroup_quotient_map_quotient (K := K₀.subgroupOf R) (M := R₀.subgroupOf R)
      (Subgroup.subgroupOf_mono R inf_le_left) hRR₀
  have hKcenter : K ≤ Subgroup.center (↥R ⧸ K₀.subgroupOf R) :=
    image_inf_L0_le_center_S01 hL hR hRn hRM
  have hKodd : Odd (Nat.card K) := odd_card_image_inf_M_S01 hL hRn hRM
  have hgenR : (⊤ : Subgroup ↥R) ≤ Subgroup.closure {x : ↥R | ∃ n : ℕ, x ^ 2 ^ n = 1} :=
    closure_twoElements_subgroup_eq_top_S01 hgen
  have hgenH : (⊤ : Subgroup (↥R ⧸ K₀.subgroupOf R)) ≤
      Subgroup.closure {x : ↥R ⧸ K₀.subgroupOf R | ∃ n : ℕ, x ^ 2 ^ n = 1} :=
    closure_twoElements_quotient_eq_top_S01 (N := K₀.subgroupOf R) hgenR
  exact isPGroup_two_of_central_odd_quotient hKcenter hKodd hquot hgenH

theorem isPGroup_of_normal {D : Data G} {L R : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hR : R ≤ L ⊔ D.T) (hRn : L ⊔ D.T ≤ normalizer (R : Set G)) (hRM : R ≤ D.M)
    (hgen : ∃ S : Set G, (∀ x ∈ S, ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ R = Subgroup.closure S) :
    IsPGroup 2 R := by
  classical
  let K₀ : Subgroup G := R ⊓ L ⊓ CFSG.Open.pCoreOf 2 L
  have hK₀n : (K₀.subgroupOf R).Normal := normal_inf_pCoreOf_S01 hL hR hRn
  have := hK₀n
  have hK₀p : IsPGroup 2 (K₀.subgroupOf R) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L).to_inf_right.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).symm
  have hquot : IsPGroup 2 (↥R ⧸ K₀.subgroupOf R) :=
    isPGroup_quotient_inf_M_S01 hL hR hRn hRM hgen
  exact IsPGroup.of_subgroup_of_quotient hK₀p hquot

theorem le_pCoreOf_of_normal {D : Data G} {L R : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hR : R ≤ L ⊔ D.T) (hRn : L ⊔ D.T ≤ normalizer (R : Set G)) (hRM : R ≤ D.M)
    (hgen : ∃ S : Set G, (∀ x ∈ S, ∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ R = Subgroup.closure S) :
    R ≤ CFSG.Open.pCoreOf 2 (L ⊔ D.T) := by
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hR hRn
    (isPGroup_of_normal hL hR hRn hRM hgen)

end S231

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
