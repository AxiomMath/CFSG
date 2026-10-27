module

public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

variable {G : Type} [Group G] {A L Y₀ : Subgroup G}

@[expose] noncomputable def kimg (Y₀ X : Subgroup G) : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :=
  (X.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))

theorem mem_kimg {X : Subgroup G} {z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀} :
    z ∈ kimg Y₀ X ↔ ∃ y : ↥Y₀, (y : G) ∈ X ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y = z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem mk_inclusion_eq_iff_mk_eq [(kerAO2 A Y₀).Normal] (y y' : ↥Y₀) :
    QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) =
        QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y') ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y' := by
  rw [Step163Alt.mk_eq_mk_iff, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    kerAO2, Subgroup.mem_subgroupOf]
  rfl

theorem mem_imgY0_iff' [(kerAO2 A Y₀).Normal] {X : Subgroup G} (hX : X ≤ Y₀)
    (x : ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀) :
    x ∈ imgY0 A Y₀ X ↔ ∃ y : ↥Y₀, (y : G) ∈ X ∧
      QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) =
        x := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvX : (v : G) ∈ X := Subgroup.mem_subgroupOf.mp hv
    exact ⟨⟨v, hX hvX⟩, hvX, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem imgY0_le_of_kimg_le [(kerAO2 A Y₀).Normal] {X X' : Subgroup G} (hX : X ≤ Y₀)
    (h : kimg Y₀ X ≤ kimg Y₀ X') : imgY0 A Y₀ X ≤ imgY0 A Y₀ X' := by
  intro x hx
  obtain ⟨y, hyX, rfl⟩ := (mem_imgY0_iff' hX x).mp hx
  obtain ⟨z, hzX', hze⟩ := mem_kimg.mp (h (mem_kimg.mpr ⟨y, hyX, rfl⟩))
  refine ⟨Subgroup.inclusion le_sup_right z, Subgroup.mem_subgroupOf.mpr hzX', ?_⟩
  exact (mk_inclusion_eq_iff_mk_eq z y).mpr hze

theorem imgY0_eq_of_kimg_eq [(kerAO2 A Y₀).Normal] {X X' : Subgroup G} (hX : X ≤ Y₀)
    (hX' : X' ≤ Y₀) (h : kimg Y₀ X = kimg Y₀ X') : imgY0 A Y₀ X = imgY0 A Y₀ X' :=
  le_antisymm (imgY0_le_of_kimg_le hX h.le) (imgY0_le_of_kimg_le hX' h.ge)

theorem card_imgY0_eq_card_kimg [(kerAO2 A Y₀).Normal] {X : Subgroup G} (hX : X ≤ Y₀) :
    Nat.card (imgY0 A Y₀ X) = Nat.card (kimg Y₀ X) := by
  set φ₁ : ↥X →* ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀ :=
    (QuotientGroup.mk' (kerAO2 A Y₀)).comp (Subgroup.inclusion (hX.trans le_sup_right))
    with hφ₁
  set φ₂ : ↥X →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hX) with hφ₂
  have hk : φ₁.ker = φ₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφ₁, hφ₂, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ← map_one (QuotientGroup.mk' (kerAO2 A Y₀)),
      ← map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))]
    have e1 : Subgroup.inclusion (hX.trans le_sup_right) x =
        Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) (Subgroup.inclusion hX x) := rfl
    have e2 : (1 : ↥(A ⊔ Y₀)) = Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) 1 := rfl
    rw [e1, e2]
    exact mk_inclusion_eq_iff_mk_eq _ _
  have h1 : φ₁.range = imgY0 A Y₀ X := by
    ext z
    rw [MonoidHom.mem_range, mem_imgY0_iff' hX]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hX x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have h2 : φ₂.range = kimg Y₀ X := by
    ext z
    rw [MonoidHom.mem_range, mem_kimg]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hX x, x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← h1, ← h2]
  exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange φ₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivRange φ₂))).toEquiv

theorem kimg_sup {X X' : Subgroup G} (hX : X ≤ Y₀) (hX' : X' ≤ Y₀) :
    kimg Y₀ (X ⊔ X') = kimg Y₀ X ⊔ kimg Y₀ X' := by
  simp only [kimg]
  rw [Subgroup.subgroupOf_sup hX hX', Subgroup.map_sup]

theorem mk_mem_normalizer_kimg [Finite G] {X : Subgroup G} {b : ↥Y₀}
    (hb : (b : G) ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) b ∈ Subgroup.normalizer (kimg Y₀ X : Set _) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨y, hyX, rfl⟩ := mem_kimg.mp hz
  refine mem_kimg.mpr ⟨b * y * b⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.mp hb (y : G)).mp hyX
  simpa using this

theorem kimg_le_normalizer_kimg [Finite G] {B X : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (X : Set G)) :
    kimg Y₀ B ≤ Subgroup.normalizer (kimg Y₀ X : Set _) := by
  rintro _ ⟨b, hb, rfl⟩
  exact mk_mem_normalizer_kimg (hB (Subgroup.mem_subgroupOf.mp hb))

theorem kimg_map_conj {T : Subgroup G} (hTY : T ≤ Y₀) (w : ↥Y₀) :
    kimg Y₀ (T.map (MulAut.conj (w : G)).toMonoidHom) =
      (kimg Y₀ T).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) w)).toMonoidHom := by
  ext z
  rw [mem_kimg]
  constructor
  · rintro ⟨y, ⟨t, ht, hty⟩, rfl⟩
    have htY : t ∈ Y₀ := hTY ht
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) ⟨t, htY⟩,
      mem_kimg.mpr ⟨⟨t, htY⟩, ht, rfl⟩, ?_⟩
    have hy : y = w * ⟨t, htY⟩ * w⁻¹ := Subtype.ext (by simpa using hty.symm)
    rw [hy]
    simp [MulAut.conj_apply]
  · rintro ⟨_, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_kimg.mp hz
    refine ⟨w * t * w⁻¹, ⟨t, ht, by simp [MulAut.conj_apply]⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem card_kimg_map_conj {T : Subgroup G} (hTY : T ≤ Y₀) (w : ↥Y₀) :
    Nat.card (kimg Y₀ (T.map (MulAut.conj (w : G)).toMonoidHom)) = Nat.card (kimg Y₀ T) := by
  rw [kimg_map_conj hTY w, Subgroup.card_map_of_injective (MulAut.conj _).injective]

variable [Finite G]

theorem three_dvd_of_maximal [(kerAO2 A Y₀).Normal] {T : Subgroup G} (hTY : T ≤ Y₀) {w : G}
    (hwY : w ∈ Y₀) {B : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)}
    (hB : B ≤ Subgroup.normalizer (kimg Y₀ T : Set _))
    (hB' : B ≤ Subgroup.normalizer (kimg Y₀ (T.map (MulAut.conj w).toMonoidHom) : Set _))
    (hmax : ∀ X : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀), B ≤ Subgroup.normalizer (X : Set _) →
      ¬ 3 ∣ Nat.card X → kimg Y₀ T ≤ X → X ≤ kimg Y₀ T)
    (hne : imgY0 A Y₀ (T.map (MulAut.conj w).toMonoidHom) ≠ imgY0 A Y₀ T) :
    3 ∣ Nat.card ↥(imgY0 A Y₀ T ⊔ imgY0 A Y₀ (T.map (MulAut.conj w).toMonoidHom)) := by
  set T' := T.map (MulAut.conj w).toMonoidHom with hT'
  have hT'Y : T' ≤ Y₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hwY (hTY hx)) (inv_mem hwY)
  by_contra h3
  rw [← Proof1712.imgY0_sup (hTY.trans le_sup_right) (hT'Y.trans le_sup_right),
    card_imgY0_eq_card_kimg (sup_le hTY hT'Y), kimg_sup hTY hT'Y] at h3
  have hBX : B ≤ Subgroup.normalizer ((kimg Y₀ T ⊔ kimg Y₀ T' : Subgroup _) : Set _) :=
    Sec14.le_normalizer_sup hB hB'
  have hle := hmax _ hBX h3 le_sup_left
  have hT'T : kimg Y₀ T' ≤ kimg Y₀ T := le_sup_right.trans hle
  have hcard : Nat.card (kimg Y₀ T') = Nat.card (kimg Y₀ T) := by
    rw [hT']
    exact card_kimg_map_conj hTY ⟨w, hwY⟩
  have heq : kimg Y₀ T' = kimg Y₀ T := Subgroup.eq_of_le_of_card_ge hT'T hcard.ge
  exact hne (imgY0_eq_of_kimg_eq hT'Y hTY heq)

variable {c : G}

theorem le_kimg_of_le {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    {X : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)} (hX2 : IsPGroup 2 X)
    (hBX : kimg Y₀ (A ⊓ L) ≤ Subgroup.normalizer (X : Set _)) (hSX : kimg Y₀ (S ⊓ Y₀) ≤ X) :
    X ≤ kimg Y₀ (S ⊓ Y₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set T : Subgroup G := (X.comap κ).map Y₀.subtype with hT
  have hmemT : ∀ y : ↥Y₀, (y : G) ∈ T ↔ κ y ∈ X := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hLY : L ≤ Y₀ := h.toSec17Std.le_y0
  set L₁ := L ⊓ T with hL₁
  have hker : IsPGroup 2 κ.ker := by
    rw [hκ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hT2 : IsPGroup 2 T := (hX2.comap_of_ker_isPGroup κ hker).map Y₀.subtype
  have hL₁2 : IsPGroup 2 L₁ := hT2.to_le inf_le_right
  have hALT : A ⊓ L ≤ Subgroup.normalizer (T : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have haY : a ∈ Y₀ := hLY ha.2
    have htY : t ∈ Y₀ := (Subgroup.map_subtype_le _) ht
    have ht' := (hmemT ⟨t, htY⟩).mp ht
    have hk : κ ⟨a, haY⟩ * κ ⟨t, htY⟩ * (κ ⟨a, haY⟩)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hBX ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩) _).mp
        ht'
    have hmem := (hmemT (⟨a, haY⟩ * ⟨t, htY⟩ * ⟨a, haY⟩⁻¹)).mpr (by
      rw [map_mul, map_mul, map_inv]
      exact hk)
    simpa using hmem
  have hAL₁ : A ≤ Subgroup.normalizer (L₁ : Set G) :=
    hAnorm L₁ inf_le_left (Late.le_normalizer_inf (inf_le_left.trans hD.le_normalizer) hALT)
  have hL₁H : L₁ ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    inf_le_left.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
  have hL₁inv : L₁ ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hL₁H, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      (Proof171.not_three_dvd_of_isPGroup_two hL₁2), hAL₁⟩
  obtain ⟨Q, hQ, hL₁Q⟩ := exists_le_mem_maxInvariantPiSubgroups hL₁inv
  have hQQ := (h142 c h.zpowers_mem_omegaA Q hQ).1
  have hL₁P : L₁ ∈ scriptQPi A (lB A) L (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hQQ hL₁Q hAL₁, inf_le_left⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hL₁2⟩
  have hSLL₁ : S ⊓ L ≤ L₁ := by
    intro x hx
    have hxY : x ∈ Y₀ := hLY hx.2
    refine ⟨hx.2, (hmemT ⟨x, hxY⟩).mpr (hSX (mem_kimg.mpr ⟨⟨x, hxY⟩, ⟨hx.1, hxY⟩, rfl⟩))⟩
  have hle : L₁ ≤ S ⊓ L := h.inf_L_mem_qStar_two.2 hL₁P hSLL₁
  intro z hz
  obtain ⟨l, hl, rfl⟩ := hLsurj z
  have hlL₁ : (l : G) ∈ L₁ := ⟨hl, (hmemT l).mpr hz⟩
  have hlS := hle hlL₁
  exact mem_kimg.mpr ⟨l, ⟨hlS.1, l.2⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec17.Proof17Res6
