module

public import CFSG.Quasithin.EmptyFaithful.S14117Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Star

omit [Finite G] in
theorem mem_imageOTwoQuot_iff {M X : Subgroup G} {u : OTwoQuot M} :
    u ∈ imageOTwoQuot M X ↔
      ∃ (x : G) (hx : x ∈ M), x ∈ X ∧ (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M) = u := by
  unfold imageOTwoQuot
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩

omit [Finite G] in
theorem imageOTwoQuot_mono {M X Y : Subgroup G} (h : X ≤ Y) :
    imageOTwoQuot M X ≤ imageOTwoQuot M Y :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono M h)

omit [Finite G] in
theorem imageOTwoQuot_sup {M X Y : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M) :
    imageOTwoQuot M (X ⊔ Y) = imageOTwoQuot M X ⊔ imageOTwoQuot M Y := by
  have h1 : (X ⊔ Y).subgroupOf M = X.subgroupOf M ⊔ Y.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (sup_le hX hY),
      Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]
  unfold imageOTwoQuot
  rw [h1, Subgroup.map_sup]

omit [Finite G] in
theorem mk_eq_one_iff_mem_pCoreOf {M : Subgroup G} (x : M) :
    (QuotientGroup.mk x : OTwoQuot M) = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
  rw [QuotientGroup.eq_one_iff]
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm

omit [Finite G] in
theorem mk_commute_iff {M : Subgroup G} (a b : M) :
    (QuotientGroup.mk a : OTwoQuot M) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a ↔
      ((a * b * a⁻¹ * b⁻¹ : M) : G) ∈ pCoreOf 2 M := by
  rw [← mk_eq_one_iff_mem_pCoreOf]
  have e : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : OTwoQuot M) =
      ⁅(QuotientGroup.mk a : OTwoQuot M), (QuotientGroup.mk b : OTwoQuot M)⁆ := by
    simp [commutatorElement_def]
  rw [e]
  exact commutatorElement_eq_one_iff_mul_comm.symm

omit [Finite G] in
theorem imageOTwoQuot_le_centralizer {M X C : Subgroup G}
    (h : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 M) :
    imageOTwoQuot M X ≤ Subgroup.centralizer (imageOTwoQuot M C : Set (OTwoQuot M)) := by
  intro u hu
  obtain ⟨x, hx, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨c, hc, hcC, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
  exact ((mk_commute_iff ⟨x, hx⟩ ⟨c, hc⟩).mpr (h x hxX c hcC)).symm

theorem odd_orderOf_of_central_of_normal {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.pCore 2 Q = ⊥)
    {C : Subgroup Q} (hC : C.Normal) {u : Q} (huC : u ∈ C) (hcomm : ∀ c ∈ C, c * u = u * c) :
    Odd (orderOf u) := by
  by_contra hodd
  obtain ⟨n, hn⟩ := Nat.not_odd_iff_even.mp hodd
  have hnpos : 0 < n := by
    have := orderOf_pos u
    omega
  set z : Q := u ^ n with hz
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, show n * 2 = orderOf u by omega]
    exact pow_orderOf_eq_one u
  have hz1 : z ≠ 1 := by
    intro h1
    have := orderOf_le_of_pow_eq_one hnpos h1
    omega
  set X : Subgroup Q := C ⊓ Subgroup.centralizer (C : Set Q) with hX
  have hzC : z ∈ C := Subgroup.pow_mem C huC n
  have hzcomm : ∀ c ∈ C, c * z = z * c := fun c hc =>
    ((Commute.pow_right (show Commute c u from hcomm c hc) n).eq)
  have hzX : z ∈ X := ⟨hzC, Subgroup.mem_centralizer_iff.mpr fun c hc => hzcomm c hc⟩
  have hXn : ∀ g : Q, g ∈ Subgroup.normalizer (X : Set Q) := fun g =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.normalizer_eq_top_iff.mpr hC ▸ Subgroup.mem_top g,
        normalizer_le_normalizer_centralizer C (Subgroup.normalizer_eq_top_iff.mpr hC ▸ Subgroup.mem_top g)⟩
  have hKn : (pCoreOf 2 X).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp fun g _ => ?_)
    exact normalizer_le_normalizer_pCoreOf 2 X (hXn g)
  have hKle : pCoreOf 2 X ≤ CFSG.Open.pCore 2 Q :=
    le_pCore 2 hKn (pCoreOf_isPGroup 2 X)
  have hKbot : pCoreOf 2 X = ⊥ := by
    refine le_bot_iff.mp (hKle.trans ?_)
    rw [hQ]
  have hzK : z ∈ pCoreOf 2 X := by
    have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
      intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨1, Subtype.ext ?_⟩
      have e : ((z ^ k) ^ 2 : Q) = (z ^ 2) ^ k := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hk, e, hz2, one_zpow]
    have hle : Subgroup.zpowers z ≤ pCoreOf 2 X := by
      refine le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hzX) ?_ hzp
      intro x hx
      have hxc : x ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Q) : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left (show Commute z x from Subgroup.mem_centralizer_iff.mp hx.2 z hzC) k).eq
      exact Subgroup.centralizer_le_normalizer _ hxc
    exact hle (Subgroup.mem_zpowers z)
  rw [hKbot, Subgroup.mem_bot] at hzK
  exact hz1 hzK

end Star

section Main

variable {T Mc M M₁ V Y₀ : Subgroup G}

theorem Hyp14117.commutator_conjClosure_le (h : quasithinQTFE14Cat G T Mc)
    (hyp : Hyp14117 T Mc M M₁ V) (hY₀M : Y₀ ≤ M) :
    ⁅M ⊓ Subgroup.centralizer (V : Set G), conjClosure (pCoreOf 2 (M₁ ⊓ M)) (Y₀ ⊔ T)⁆ ≤
      pCoreOf 2 M := by
  set R : Subgroup G := pCoreOf 2 (M₁ ⊓ M) with hR
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hC
  have hTM : T ≤ M := hyp.inM.2
  have hRM : R ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hOC : pCoreOf 2 M ≤ C := _root_.le_inf (pCoreOf_le 2 M) hyp.pCoreOf_le_centralizer
  have hW : conjClosure R (Y₀ ⊔ T) ≤ centralizerSection M C (pCoreOf 2 M) := by
    refine conjClosure_le fun g hg z hz => ?_
    have hgM : g ∈ M := sup_le hY₀M hTM hg
    have hzD : z ∈ centralizerSection M C (pCoreOf 2 M) := by
      refine ⟨hRM hz, hyp.le_normalizer_inf_centralizer (hRM hz),
        le_normalizer_pCoreOf 2 M (hRM hz), fun c hc => ?_⟩
      have h1 : c * z * c⁻¹ * z⁻¹ ∈ R :=
        R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hyp.centralizer_le_normalizer h hc) z).mp hz)
          (R.inv_mem hz)
      have h2 : c * z * c⁻¹ * z⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        have hzN : z ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
          normalizer_le_normalizer_centralizer V (hyp.le_normalizer (hRM hz))
        have h3 : z * c⁻¹ * z⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
          (Subgroup.mem_normalizer_iff.mp hzN c⁻¹).mp (Subgroup.inv_mem _ hc.2)
        have e : c * z * c⁻¹ * z⁻¹ = c * (z * c⁻¹ * z⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hc.2 h3
      rw [← hyp.inf_centralizer_eq h]
      exact ⟨h1, h2⟩
    exact conj_mem_centralizerSection (Subgroup.le_normalizer hgM)
      (hyp.le_normalizer_inf_centralizer hgM) (le_normalizer_pCoreOf 2 M hgM) hzD
  exact ((le_centralizerSection_iff hOC).mp hW).2

theorem lemma_14_1_17_three (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V)
    (hY₀M : Y₀ ≤ M) :
    ⁅imageOTwoQuot M (M ⊓ Subgroup.centralizer (V : Set G)),
        imageOTwoQuot M (oTwoUpper (conjClosure (pCoreOf 2 (M₁ ⊓ M)) (Y₀ ⊔ T))) ⊔
          imageOTwoQuot M (pCoreOf 2 (M₁ ⊓ M))⁆ = ⊥ ∧
      ∀ u ∈ imageOTwoQuot M (oTwoUpper (conjClosure (pCoreOf 2 (M₁ ⊓ M)) (Y₀ ⊔ T)) ⊓
          Subgroup.centralizer (V : Set G)),
        u ∈ imageOTwoQuot M ((M ⊓ Subgroup.centralizer (V : Set G)) ⊔ pCoreOf 2 (M₁ ⊓ M)) ∧
          Odd (orderOf u) ∧
          ∀ w ∈ imageOTwoQuot M ((M ⊓ Subgroup.centralizer (V : Set G)) ⊔ pCoreOf 2 (M₁ ⊓ M)),
            w * u = u * w := by
  set R : Subgroup G := pCoreOf 2 (M₁ ⊓ M) with hR
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hC
  set W : Subgroup G := conjClosure R (Y₀ ⊔ T) with hW
  have hTM : T ≤ M := hyp.inM.2
  have hRM : R ≤ M := (pCoreOf_le 2 _).trans inf_le_right
  have hCM : C ≤ M := inf_le_left
  have hWM : W ≤ M :=
    conjClosure_le fun g hg z hz =>
      M.mul_mem (M.mul_mem (sup_le hY₀M hTM hg) (hRM hz)) (M.inv_mem (sup_le hY₀M hTM hg))
  have hYW : oTwoUpper W ≤ W := oTwoUpper_le W
  have hRW : R ≤ W := le_conjClosure R (Y₀ ⊔ T)
  have hcomm : ⁅C, W⁆ ≤ pCoreOf 2 M := hyp.commutator_conjClosure_le h hY₀M
  have hWC : ∀ x ∈ W, ∀ c ∈ C, x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 M := by
    intro x hx c hc
    have := Subgroup.commutator_mem_commutator hx hc
    rw [Subgroup.commutator_comm] at this
    exact hcomm this
  refine ⟨?_, fun u hu => ?_⟩
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine sup_le ?_ ?_
    · exact imageOTwoQuot_le_centralizer fun x hx c hc => hWC x (hYW hx) c hc
    · exact imageOTwoQuot_le_centralizer fun x hx c hc => hWC x (hRW hx) c hc
  · obtain ⟨y, hyM, ⟨hyY, hyV⟩, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have hyC : y ∈ C := ⟨hyM, hyV⟩
    have hyW : y ∈ W := hYW hyY
    have hsup : imageOTwoQuot M (C ⊔ R) = imageOTwoQuot M C ⊔ imageOTwoQuot M R :=
      imageOTwoQuot_sup hCM hRM
    have hcentral : ∀ w ∈ imageOTwoQuot M (C ⊔ R),
        w * (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) = QuotientGroup.mk ⟨y, hyM⟩ * w := by
      intro w hw
      rw [hsup] at hw
      have hle : imageOTwoQuot M C ⊔ imageOTwoQuot M R ≤
          Subgroup.centralizer ({(QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M)} : Set (OTwoQuot M)) := by
        refine sup_le (fun v hv => ?_) (fun v hv => ?_)
        · obtain ⟨c, hc, hcC, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff.mp hg]
          exact (mk_commute_iff ⟨y, hyM⟩ ⟨c, hc⟩).mpr (hWC y hyW c hcC)
        · obtain ⟨r, hr, hrR, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff.mp hg]
          exact ((mk_commute_iff ⟨r, hr⟩ ⟨y, hyM⟩).mpr (hWC r (hRW hrR) y hyC)).symm
      have := Subgroup.mem_centralizer_iff.mp (hle hw) _ (Set.mem_singleton _)
      exact this.symm
    have huC : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈ imageOTwoQuot M C :=
      mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hyC, rfl⟩
    have hCnorm : (imageOTwoQuot M C).Normal := by
      have : (C.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mpr
          hyp.le_normalizer_inf_centralizer
      exact Subgroup.Normal.map this (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    refine ⟨imageOTwoQuot_mono le_sup_left huC, ?_, hcentral⟩
    exact odd_orderOf_of_central_of_normal (pCore_two_quot_eq_bot M) hCnorm huC
      (fun c hc => hcentral c (imageOTwoQuot_mono le_sup_left hc))

end Main

end CFSG.Quasithin
