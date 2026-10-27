module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofM22
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

namespace Proof17Res6

variable {G : Type} [Group G] {A L Y₀ : Subgroup G} {c : G}

@[expose] noncomputable def actQ (Y₀ : Subgroup G) :
    Subgroup.normalizer (Y₀ : Set G) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :=
  (Proof171Gen.quotAutTwo ↥Y₀).comp Y₀.normalizerMonoidHom

theorem actQ_mk (m : Subgroup.normalizer (Y₀ : Set G)) (y : ↥Y₀) :
    actQ Y₀ m (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) (Y₀.normalizerMonoidHom m y) :=
  rfl

theorem actQ_of_mem (y : ↥Y₀) :
    actQ Y₀ ⟨y, Y₀.le_normalizer y.2⟩ = MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    change actQ Y₀ ⟨y, Y₀.le_normalizer y.2⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) x) =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y) (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) x)
    rw [actQ_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem mem_cQuot_of_actQ_eq_one {m : Subgroup.normalizer (Y₀ : Set G)} (hm : actQ Y₀ m = 1) :
    (m : G) ∈ cQuot Y₀ := by
  rw [← SetLike.mem_coe, coe_cQuot]
  refine ⟨m.2, fun y hy => ?_⟩
  have h1 := congrArg (fun σ : MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) =>
    σ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) ⟨y, hy⟩)) hm
  simp only [MulAut.one_apply] at h1
  rw [actQ_mk] at h1
  have h2 := (Step163Alt.mk_eq_mk_iff _ _).mp h1.symm
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  have hYO : Y₀ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀
  have h3 := (Subgroup.mem_normalizer_iff.mp (hYO hy) _).mp h2
  have e : y * (y⁻¹ * ((m : G) * y * (m : G)⁻¹)) * y⁻¹ = (m : G) * y * (m : G)⁻¹ * y⁻¹ := by group
  rwa [e] at h3

variable [Finite G]

theorem le_sup_cQuot_of_inner {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hZ : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥)
    (hinner : (S.subgroupOf (Subgroup.normalizer (Y₀ : Set G))).map (actQ Y₀) ≤
      (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)).range) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set Q := (S.subgroupOf M).map (actQ Y₀) with hQ
  set R := Q.comap (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))
    with hR
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hconj : Function.Injective
      (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) => σ z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc)
  have hR2 : IsPGroup 2 R := by
    have hQ2 : IsPGroup 2 Q := (hS2.comap_subtype).map _
    exact hQ2.comap_of_injective _ hconj
  have hBR : kimg Y₀ (A ⊓ L) ≤ Subgroup.normalizer (R : Set _) := by
    rintro _ ⟨b, hb, rfl⟩
    have hbAL : (b : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨s, hs, hsz⟩ := hz
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hbM : (b : G) ∈ M := Y₀.le_normalizer b.2
    set b' : M := ⟨b, hbM⟩ with hb'
    refine ⟨b' * s * b'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hSQ.1.2.2 hbAL.1) (s : G)).mp hsS
      simpa [hb'] using this
    · rw [map_mul, map_mul, map_inv, hsz, show b' = ⟨b, Y₀.le_normalizer b.2⟩ from rfl,
        actQ_of_mem, ← map_inv, ← map_mul, ← map_mul]
  have hSR : kimg Y₀ (S ⊓ Y₀) ≤ R := by
    rintro _ ⟨y, hy, rfl⟩
    have hyS : (y : G) ∈ S ⊓ Y₀ := Subgroup.mem_subgroupOf.mp hy
    exact ⟨⟨y, Y₀.le_normalizer y.2⟩, Subgroup.mem_subgroupOf.mpr hyS.1, actQ_of_mem y⟩
  have hRle := le_kimg_of_le h h142 hLsurj hAnorm hR2 hBR hSR
  intro s hs
  obtain ⟨l0, hl0⟩ := hinner ⟨⟨s, hSM hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have hlR : l0 ∈ R := by
    show MulAut.conj l0 ∈ Q
    rw [hl0]
    exact ⟨⟨s, hSM hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  obtain ⟨y, hyS, hye⟩ := mem_kimg.mp (hRle hlR)
  have hu : actQ Y₀ (⟨y, Y₀.le_normalizer y.2⟩⁻¹ * ⟨s, hSM hs⟩) = 1 := by
    rw [map_mul, map_inv, actQ_of_mem, hye, hl0, inv_mul_cancel]
  have huC := mem_cQuot_of_actQ_eq_one hu
  have hs' : s = (y : G) * ((y : G)⁻¹ * s) := by group
  rw [hs']
  refine Subgroup.mul_mem_sup hyS (Subgroup.mem_inf.mpr
    ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hyS).1) hs, ?_⟩)
  simpa using huC

theorem oTwoCY0_eq_kimg [(kerAO2 A Y₀).Normal] {a : ↥Y₀} (ha : (a : G) ∈ A) :
    oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) = imgY0 A Y₀
      (((CFSG.Open.pCoreOf 2 (Subgroup.centralizer
        {QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a})).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))).map Y₀.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set N := kerAO2 A Y₀ with hN
  set ι : ↥Y₀ →* ↥(A ⊔ Y₀) ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀)) with hι
  set C := Subgroup.centralizer {κ a} with hC
  set V := CFSG.Open.pCoreOf 2 C with hV
  set T : Subgroup G := (V.comap κ).map Y₀.subtype with hT
  set H := imgY0 A Y₀ Y₀ ⊓ Subgroup.centralizer {alphaY0 A Y₀ a ha} with hH
  have hTY : T ≤ Y₀ := Subgroup.map_subtype_le _
  have hmemT : ∀ y : ↥Y₀, (y : G) ∈ T ↔ κ y ∈ V := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hαa : alphaY0 A Y₀ a ha = ι a := rfl
  have hcomm : ∀ y : ↥Y₀, ι y ∈ Subgroup.centralizer {alphaY0 A Y₀ a ha} ↔ κ y ∈ C := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hαa, hι,
      MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact mk_inclusion_eq_iff_mk_eq _ _
  have hmemY : ∀ x, x ∈ imgY0 A Y₀ Y₀ ↔ ∃ y : ↥Y₀, ι y = x := by
    intro x
    rw [mem_imgY0_iff' le_rfl]
    exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, y.2, hy⟩⟩
  have hmemTα : ∀ x, x ∈ imgY0 A Y₀ T ↔ ∃ y : ↥Y₀, κ y ∈ V ∧ ι y = x := by
    intro x
    rw [mem_imgY0_iff' hTY]
    exact ⟨fun ⟨y, hyT, hy⟩ => ⟨y, (hmemT y).mp hyT, hy⟩,
      fun ⟨y, hyV, hy⟩ => ⟨y, (hmemT y).mpr hyV, hy⟩⟩
  have hκsurj : ∀ z, ∃ y : ↥Y₀, κ y = z := QuotientGroup.mk'_surjective _
  apply le_antisymm
  ·
    set P := CFSG.Open.pCoreOf 2 H with hP
    set P' : Subgroup ↥Y₀ := P.comap ι with hP'
    have hιker : IsPGroup 2 ι.ker := by
      intro ⟨y, hy⟩
      have hy1 : κ y = κ 1 := (mk_inclusion_eq_iff_mk_eq y 1).mp
        (by rw [show (QuotientGroup.mk' N) (Subgroup.inclusion le_sup_right y) = ι y from rfl,
          MonoidHom.mem_ker.mp hy]; rfl)
      have hyO : y ∈ CFSG.pCore 2 ↥Y₀ := by
        rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y₀) y]
        simpa [hκ] using hy1
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀)) ⟨y, hyO⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hP'2 : IsPGroup 2 P' :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).comap_of_ker_isPGroup ι hιker
    set P'' : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := P'.map κ with hP''
    have hP''2 : IsPGroup 2 P'' := hP'2.map κ
    have hP''C : P'' ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hcomm y).mp (CFSG.LieType.BorelTits.pCoreOf_le 2 H hy).2
    have hCP'' : C ≤ Subgroup.normalizer (P'' : Set _) := by
      intro z hz
      obtain ⟨y', rfl⟩ := hκsurj z
      have hy'H : ι y' ∈ H := ⟨(hmemY _).mpr ⟨y', rfl⟩, (hcomm y').mpr hz⟩
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y' * y * y'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      change ι (y' * y * y'⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hy'H) _).mp hy
    have hP''V : P'' ≤ V :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP''C hCP'' hP''2
    intro x hx
    have hxH : x ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hx
    obtain ⟨y, rfl⟩ := (hmemY x).mp hxH.1
    exact (hmemTα _).mpr ⟨y, hP''V ⟨y, hx, rfl⟩, rfl⟩
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · intro x hx
      obtain ⟨y, hyV, rfl⟩ := (hmemTα x).mp hx
      exact ⟨(hmemY _).mpr ⟨y, rfl⟩, (hcomm y).mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 C hyV)⟩
    · intro h' hh'
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      obtain ⟨y', rfl⟩ := (hmemY h').mp hh'.1
      obtain ⟨y, hyV, rfl⟩ := (hmemTα t).mp ht
      have hy'C : κ y' ∈ C := (hcomm y').mp hh'.2
      have hV' := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hy'C) _).mp hyV
      refine (hmemTα _).mpr ⟨y' * y * y'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [map_mul, map_mul, map_inv]
      exact hV'
    · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) C).comap_of_ker_isPGroup κ
        (by rw [hκ, QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)).map Y₀.subtype
        |>.comap_subtype |>.map _

omit [Finite G] in
theorem kimg_preimage (V : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) :
    kimg Y₀ ((V.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))).map Y₀.subtype) = V := by
  ext z
  rw [mem_kimg]
  constructor
  · rintro ⟨y, ⟨y', hy', hyy'⟩, rfl⟩
    have : y' = y := Subtype.ext hyy'
    subst this
    exact hy'
  · intro hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) z
    exact ⟨y, ⟨y, hz, rfl⟩, rfl⟩

theorem inSubgroup_pCore_two_eq {X : Type*} [Group X] (H : Subgroup X) :
    inSubgroup (CFSG.pCore 2) H = CFSG.Open.pCoreOf 2 H := by
  rw [inSubgroup]
  rfl

theorem item1717One_of_m22
    [(kerAO2 A Y₀).Normal]
    {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hLsurj : ∀ z : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀, ∃ l : ↥Y₀, (l : G) ∈ L ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l = z)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hB9 : Nat.card (kimg Y₀ (A ⊓ L)) = 9)
    (hΛ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    S = (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) ∧
      (CFSG.Assembly.IsElemAbelian 2 (imgY0 A Y₀ (S ⊓ Y₀)) ∧
        Nat.card (imgY0 A Y₀ (S ⊓ Y₀)) = 16) ∧
      ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A), Subgroup.closure {a, b} = A ⊓ L ∧
        imgY0 A Y₀ (S ⊓ Y₀) =
          oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ∧
        oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊓ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hκ
  set B := kimg Y₀ (A ⊓ L) with hB
  set R := kimg Y₀ (S ⊓ Y₀) with hR
  set ι : ↥Y₀ →* ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀ :=
    (QuotientGroup.mk' (kerAO2 A Y₀)).comp (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀))
    with hι
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hSQ.1.2.2 h.le_normalizer_y0
  have hZ : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥ := by
    obtain ⟨e⟩ := hΛ
    obtain ⟨⟨-, hM22z⟩, -⟩ := Sec13.sporadicModels131
    refine le_bot_iff.mp fun z hz => ?_
    have hez : e z ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.M22 := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, hz w']
    rw [hM22z, Subgroup.mem_bot, map_eq_one_iff e e.injective] at hez
    exact hez
  have hinner : (S.subgroupOf M).map (actQ Y₀) ≤
      (MulAut.conj : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) →* MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)).range := by
    refine KFacts.KP4.m22_aut_threePrime_le_range hΛ hB9 ?_ ?_
    · intro h3
      have hd := Subgroup.card_map_dvd (S.subgroupOf M) (actQ Y₀)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv] at hd
      exact Proof171.not_three_dvd_of_isPGroup_two hS2 (h3.trans hd)
    · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have hbAL : (b : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hb
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨s, hs, rfl⟩ := hz
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      set b' : M := ⟨b, Y₀.le_normalizer b.2⟩ with hb'
      refine ⟨b' * s * b'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hSQ.1.2.2 hbAL.1) (s : G)).mp hsS
        simpa [hb'] using this
      · rw [map_mul, map_mul, map_inv, hb', actQ_of_mem]
  refine ⟨le_antisymm (le_sup_cQuot_of_inner h h142 hLsurj hAnorm hSM hZ hinner)
    (sup_le inf_le_left inf_le_left), ?_⟩
  have hBR : B ≤ Subgroup.normalizer (R : Set _) := kimg_le_normalizer_kimg (inf_le_left.trans hAS)
  have hR2 : IsPGroup 2 R := ((hS2.to_le inf_le_left).comap_subtype).map _
  have hRmax : R ∈ maxInvariantPiSubgroups ⊤ B (piCompl 3) := by
    refine ⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr
      (Proof171.not_three_dvd_of_isPGroup_two hR2), hBR⟩, fun X hX hRX => ?_⟩
    have hX3 : ¬ 3 ∣ Nat.card X := (isPiSubgroup_piCompl_iff Nat.prime_three X).mp hX.2.1
    exact le_kimg_of_le h h142 hLsurj hAnorm (isPGroup_two_of_m22 hΛ hB9 X hX.2.2 hX3) hX.2.2
      hRX
  obtain ⟨hRel, hR16, a', b', ha', hb', hcl, -, -, hθ0, hθR, hθa, hθb⟩ :=
    KFacts.KP4.m22_maxInvariant_structure hΛ hB9 hRmax
  rw [hθa, hθb, inSubgroup_pCore_two_eq, inSubgroup_pCore_two_eq] at hθ0 hθR
  obtain ⟨a, haAL, rfl⟩ := mem_kimg.mp ha'
  obtain ⟨b, hbAL, rfl⟩ := mem_kimg.mp hb'
  set Va := CFSG.Open.pCoreOf 2 (Subgroup.centralizer {κ a}) with hVa
  set Vb := CFSG.Open.pCoreOf 2 (Subgroup.centralizer {κ b}) with hVb
  set Ta : Subgroup G := (Va.comap κ).map Y₀.subtype with hTa
  set Tb : Subgroup G := (Vb.comap κ).map Y₀.subtype with hTb
  have hTaY : Ta ≤ Y₀ := Subgroup.map_subtype_le _
  have hTbY : Tb ≤ Y₀ := Subgroup.map_subtype_le _
  have hOa := oTwoCY0_eq_kimg (A := A) haAL.1
  have hOb := oTwoCY0_eq_kimg (A := A) hbAL.1
  rw [← hκ, ← hVa] at hOa
  rw [← hκ, ← hVb] at hOb
  have hιeq : ∀ y y' : ↥Y₀, ι y = ι y' ↔ κ y = κ y' := fun y y' => mk_inclusion_eq_iff_mk_eq y y'
  have hmemα : ∀ x, x ∈ imgY0 A Y₀ (S ⊓ Y₀) → ∃ y : ↥Y₀, κ y ∈ R ∧ ι y = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_imgY0_iff' inf_le_right x).mp hx
    exact ⟨y, mem_kimg.mpr ⟨y, hy, rfl⟩, rfl⟩
  have hRcomm : ∀ u ∈ R, ∀ v ∈ R, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hRel.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcommα : ∀ x ∈ imgY0 A Y₀ (S ⊓ Y₀), ∀ x' ∈ imgY0 A Y₀ (S ⊓ Y₀), x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨y, hyR, rfl⟩ := hmemα x hx
    obtain ⟨y', hy'R, rfl⟩ := hmemα x' hx'
    rw [← map_mul, ← map_mul, hιeq, map_mul, map_mul]
    exact hRcomm _ hyR _ hy'R
  have hpowα : ∀ x ∈ imgY0 A Y₀ (S ⊓ Y₀), x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hyR, rfl⟩ := hmemα x hx
    have h2 : κ y ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (A := R) (p := 2) (κ y) hyR
    rw [← map_pow, ← map_one ι, hιeq, map_pow, map_one]
    exact h2
  have hmc : IsMulCommutative ↥(imgY0 A Y₀ (S ⊓ Y₀)) :=
    ⟨⟨fun u v => Subtype.ext (hcommα u.1 u.2 v.1 v.2)⟩⟩
  refine ⟨⟨⟨hmc, hpowα⟩, ?_⟩, a, haAL.1, b, hbAL.1, ?_, ?_, ?_⟩
  ·
    rw [card_imgY0_eq_card_kimg inf_le_right]
    exact hR16
  ·
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le _).mpr ?_) ?_
    · rintro _ (rfl | rfl)
      · exact haAL
      · exact hbAL
    · have hle : B ≤ kimg Y₀ (Subgroup.closure {(a : G), (b : G)}) := by
        rw [← hcl, Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact mem_kimg.mpr ⟨a, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
        · exact mem_kimg.mpr ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
      have hclY : Subgroup.closure {(a : G), (b : G)} ≤ Y₀ := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact a.2
        · exact b.2
      have hd : Nat.card (kimg Y₀ (Subgroup.closure {(a : G), (b : G)})) ∣
          Nat.card (Subgroup.closure {(a : G), (b : G)}) := by
        have := Subgroup.card_map_dvd ((Subgroup.closure {(a : G), (b : G)}).subgroupOf Y₀) κ
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hclY).toEquiv] at this
      have hpos : 0 < Nat.card (Subgroup.closure {(a : G), (b : G)}) := Nat.card_pos
      rw [h9]
      calc 9 = Nat.card B := hB9.symm
        _ ≤ Nat.card (kimg Y₀ (Subgroup.closure {(a : G), (b : G)})) := Subgroup.card_le_of_le hle
        _ ≤ Nat.card (Subgroup.closure {(a : G), (b : G)}) := Nat.le_of_dvd hpos hd
  ·
    rw [hOa, hOb, ← Proof1712.imgY0_sup (hTaY.trans le_sup_right) (hTbY.trans le_sup_right)]
    refine imgY0_eq_of_kimg_eq inf_le_right (sup_le hTaY hTbY) ?_
    rw [kimg_sup hTaY hTbY, hTa, hTb, kimg_preimage, kimg_preimage]
    exact hθR.symm
  ·
    have hmemTa : ∀ y : ↥Y₀, (y : G) ∈ Ta → κ y ∈ Va := by
      rintro y ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact hy'
    have hmemTb : ∀ y : ↥Y₀, (y : G) ∈ Tb → κ y ∈ Vb := by
      rintro y ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      subst this
      exact hy'
    rw [hOa, hOb]
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨y, hyTa, rfl⟩ := (mem_imgY0_iff' hTaY x).mp hx.1
    obtain ⟨y', hy'Tb, hy'e⟩ := (mem_imgY0_iff' hTbY _).mp hx.2
    have hyy' : κ y' = κ y := (hιeq y' y).mp hy'e
    have hy0 : κ y ∈ Va ⊓ Vb := ⟨hmemTa y hyTa, hyy' ▸ hmemTb y' hy'Tb⟩
    rw [hθ0, Subgroup.mem_bot] at hy0
    rw [Subgroup.mem_bot]
    have : ι y = ι 1 := (hιeq y 1).mpr (by rw [hy0, map_one])
    rw [map_one] at this
    exact this

end Proof17Res6

@[expose] noncomputable def Item1717OneL3J2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    ((∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) →
    letI := kerAO2_normal h.le_normalizer_y0
    S = (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) ∧
      (((IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) ∧
          ∃ (a : G) (ha : a ∈ A), a ∈ L ∧ a ≠ 1 ∧
            imgY0 A Y₀ (S ⊓ Y₀) = oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha)) ∨
        (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
          (CFSG.Assembly.IsElemAbelian 2 (imgY0 A Y₀ (S ⊓ Y₀)) ∧
            Nat.card (imgY0 A Y₀ (S ⊓ Y₀)) = 16) ∧
          ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A), Subgroup.closure {a, b} = A ⊓ L ∧
            imgY0 A Y₀ (S ⊓ Y₀) =
              oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ∧
            oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊓ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) = ⊥) ∨
        (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
            Nonempty (↥(imgY0 A Y₀ (S ⊓ Y₀)) ≃*
              ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
          ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G),
            Subgroup.closure {a, b} = A ⊓ L ∧ d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
            imgY0 A Y₀ (S ⊓ Y₀) =
              oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ⊔
                imgY0 A Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {d})))

section Provers

theorem item1717One_of_L3J2 (hRes : Item1717OneL3J2) (h1715 : Item1715) (h135 : Item135)
    (h142 : Concl142S14) (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h9 : CardInfNineS17) : Item1717One := by
  intro G _ _ A c L Y₀ Y₁ S p P h hΩ
  have hs := h.toSec17Std
  obtain ⟨hY, htypes⟩ : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      ((∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
          Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
    rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, htypes⟩ | ⟨-, -, -, -, hT⟩
    · exact ⟨hY, htypes⟩
    · exfalso
      have h3 := hT.1
      rw [hΩ, Set.ncard_singleton] at h3
      omega
  rcases htypes with hL3 | hA7 | hM22 | hJ2
  · exact hRes G A c L Y₀ Y₁ S p P h hΩ (Or.inl hL3)
  · obtain ⟨φL⟩ := hA7
    obtain ⟨φ, g, hP⟩ := exists_a7Pic_of h1715 h135 h9 hs hΩ φL
    have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
      (h168 G A c L Y₀ hs)
    have := kerAO2_normal h.le_normalizer_y0
    obtain ⟨h1, a, ha, haL, ha1, heq⟩ := Proof17Res6.item1717One_of_a7 h hP
      (h142 G A c L hs.toSec14Std) (hs.qStar_le S hSG)
    exact ⟨h1, Or.inl ⟨Or.inr ⟨φL⟩, a, ha, haL, ha1, heq⟩⟩
  · obtain ⟨φL⟩ := hM22
    have := kerAO2_normal h.le_normalizer_y0
    have h9' := h9 G A c L Y₀ hs
    have : Nontrivial ↥CFSG.Blueprint.NativeSporadic.M22 := by
      rw [← Finite.one_lt_card_iff_nontrivial, CFSG.Sporadic.Mathieu.card_M22]
      norm_num
    have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
      Proof1515.theta_eq_pCore_two_of_multFree (h135 G A c L hs.toSec13Data hs.hypS_or_hypT)
        ⟨φL⟩ Proof1515.multFree_M22
    have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
      (h168 G A c L Y₀ hs)
    obtain ⟨h1, h2⟩ := Proof17Res6.item1717One_of_m22 h (h142 G A c L hs.toSec14Std)
      (Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY) (Proof17Res6.le_normalizer_of_inf hs h9')
      (hs.qStar_le S hSG) h9' (Proof17Res6.card_kimg_inf hs h9')
      (Proof17Res6.nonempty_quot_equiv_of_theta hs.le_y0 hY hθ φL)
    exact ⟨h1, Or.inr (Or.inl ⟨⟨φL⟩, h2⟩)⟩
  · exact hRes G A c L Y₀ Y₁ S p P h hΩ (Or.inr hJ2)

end Provers

end CFSG.RankThree.PartTwo.Sec17
