module

public import CFSG.Quasithin.Background.C2PushQuot
public import CFSG.Quasithin.EmptyFaithful.S14113Layer

public section

namespace CFSG.Quasithin.C2Push

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def preimageOTwoQuot (M : Subgroup G) (P : Subgroup (OTwoQuot M)) : Subgroup G :=
  (P.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))).map M.subtype

omit [Finite G] in
theorem mem_preimageOTwoQuot_iff {M : Subgroup G} {P : Subgroup (OTwoQuot M)} {x : G} :
    x ∈ preimageOTwoQuot M P ↔ ∃ hx : x ∈ M, (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M) ∈ P := by
  unfold preimageOTwoQuot
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem isPGroup_preimageOTwoQuot_inf {M : Subgroup G} (A : Subgroup G) {P : Subgroup (OTwoQuot M)}
    (hP : IsPGroup 2 P) : IsPGroup 2 (preimageOTwoQuot M P ⊓ A : Subgroup G) := by
  rintro ⟨x, hxP, hxA⟩
  obtain ⟨hxM, hxq⟩ := mem_preimageOTwoQuot_iff.mp hxP
  obtain ⟨k, hk⟩ := hP ⟨_, hxq⟩
  have h0 : (QuotientGroup.mk ⟨x, hxM⟩ : OTwoQuot M) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : (QuotientGroup.mk (⟨x, hxM⟩ ^ 2 ^ k) : OTwoQuot M) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact h0
  have h2 : x ^ 2 ^ k ∈ pCoreOf 2 M := (mk_eq_one_iff_mem_pCoreOf (⟨x, hxM⟩ ^ 2 ^ k)).mp h1
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 M) ⟨x ^ 2 ^ k, h2⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have := congrArg Subtype.val hj
  simpa [pow_add, pow_mul] using this

theorem nonempty_mulEquiv_pCore_quotient_imageOTwoQuot {M L : Subgroup G} (hsub : IsSubnormal L M) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(imageOTwoQuot M L)) := by
  have hLM : L ≤ M := A4.subnormal_le hsub
  let ψ : ↥L →* OTwoQuot M :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)
  have hψ : ∀ l : ↥L, ψ l = (QuotientGroup.mk (Subgroup.inclusion hLM l) : OTwoQuot M) :=
    fun l => rfl
  have hPL : ∀ l : ↥L, (l : G) ∈ pCoreOf 2 L ↔ (l : G) ∈ pCoreOf 2 M := by
    intro l
    constructor
    · intro hl
      exact A4.pCoreOf_le_of_subnormal 2 hsub hl
    · intro hl
      have hnorm : L ≤ Subgroup.normalizer ((L ⊓ pCoreOf 2 M : Subgroup G) : Set G) := fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 M (hLM hx)⟩
      have hle : L ⊓ pCoreOf 2 M ≤ pCoreOf 2 L :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
          ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
      exact hle ⟨l.2, hl⟩
  have hker : CFSG.pCore 2 ↥L = ψ.ker := by
    ext l
    rw [C2Six.mem_pCore_two_iff, hPL, MonoidHom.mem_ker, hψ]
    exact (mk_eq_one_iff_mem_pCoreOf (Subgroup.inclusion hLM l)).symm
  have hrange : ψ.range = imageOTwoQuot M L := by
    ext q
    constructor
    · rintro ⟨l, rfl⟩
      exact mem_imageOTwoQuot_iff.mpr ⟨l.1, hLM l.2, l.2, rfl⟩
    · intro hq
      obtain ⟨x, hx, hxL, rfl⟩ := mem_imageOTwoQuot_iff.mp hq
      exact ⟨⟨x, hxL⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem isSolvable_pCore_two (M : Subgroup G) : Group.IsSolvable (CFSG.Open.pCore 2 ↥M) := by
  have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥M) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥M) := hp.isNilpotent
  infer_instance

theorem isComponent_imageOTwoQuot {M L : Subgroup G} (hL : L ∈ cComp M)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : CFSG.IsComponent (imageOTwoQuot M L) := by
  have hK : imageOTwoQuot M L ∈ cComp (⊤ : Subgroup (OTwoQuot M)) :=
    (cComp_quotient_bijOn (CFSG.Open.pCore 2 ↥M) (isSolvable_pCore_two M)).mapsTo
      (subgroupOf_mem_cComp hL)
  obtain ⟨e⟩ := nonempty_mulEquiv_pCore_quotient_imageOTwoQuot (subnormal_of_mem_cComp hL)
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hLq,
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hK)⟩

theorem imageOTwoQuot_eq_pCoreOf_normalizer {M R : Subgroup G} (hR : IsTwoRadicalIn M R) :
    imageOTwoQuot M R =
      pCoreOf 2 (imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G))) := by
  have hOR : pCoreOf 2 M ≤ R := c2_1_pCore_le hR
  have hRM : R ≤ M := hR.1
  have hRN : R ≤ M ⊓ Subgroup.normalizer (R : Set G) := le_inf hRM Subgroup.le_normalizer
  have hNM : M ⊓ Subgroup.normalizer (R : Set G) ≤ M := inf_le_left
  apply le_antisymm
  · refine le_pCoreOf_of_le_normalizer 2 (imageOTwoQuot_mono hRN) ?_
      ((A4.isPGroup_subgroupOf_of_le hRM hR.isPGroup).map _)
    refine le_normalizer_of_forall_conj_mem ?_
    intro u hu v hv
    obtain ⟨n, hn, hnN, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨r, hr, hrR, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    refine mem_imageOTwoQuot_iff.mpr
      ⟨n * r * n⁻¹, M.mul_mem (M.mul_mem hn hr) (M.inv_mem hn), ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hnN.2 r).mp hrR
  · intro u hu
    obtain ⟨m, hm, hmN, rfl⟩ := mem_imageOTwoQuot_iff.mp
      (pCoreOf_le 2 (imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G))) hu)
    have hP₁2 : IsPGroup 2
        (preimageOTwoQuot M (pCoreOf 2 (imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G)))) ⊓
          (M ⊓ Subgroup.normalizer (R : Set G)) : Subgroup G) :=
      isPGroup_preimageOTwoQuot_inf _ (pCoreOf_isPGroup 2 _)
    have hnorm : M ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer
        ((preimageOTwoQuot M (pCoreOf 2 (imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G)))) ⊓
          (M ⊓ Subgroup.normalizer (R : Set G)) : Subgroup G) : Set G) := by
      refine le_normalizer_of_forall_conj_mem ?_
      intro n hn p hp
      obtain ⟨hp1, hpN⟩ := hp
      obtain ⟨hpM, hpq⟩ := mem_preimageOTwoQuot_iff.mp hp1
      refine ⟨mem_preimageOTwoQuot_iff.mpr
        ⟨M.mul_mem (M.mul_mem (hNM hn) hpM) (M.inv_mem (hNM hn)), ?_⟩,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hpN) (Subgroup.inv_mem _ hn)⟩
      have hnHb : (QuotientGroup.mk ⟨n, hNM hn⟩ : OTwoQuot M) ∈
          imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G)) :=
        mem_imageOTwoQuot_iff.mpr ⟨n, hNM hn, hn, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 _ hnHb) _).mp hpq
    have hP₁R := le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hP₁2
    rw [← hR.2.2] at hP₁R
    exact mem_imageOTwoQuot_iff.mpr ⟨m, hm, hP₁R
      ⟨mem_preimageOTwoQuot_iff.mpr ⟨hm, hu⟩, hmN⟩, rfl⟩

theorem pCoreOf_inf_normalizer_le {M R L : Subgroup G} (hR : IsTwoRadicalIn M R) (hL : L ∈ cComp M)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ≤ R := by
  have hOR : pCoreOf 2 M ≤ R := c2_1_pCore_le hR
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hKc := isComponent_imageOTwoQuot hL hLq
  have hP₀le : pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ≤ L ⊓ Subgroup.normalizer (R : Set G) :=
    pCoreOf_le 2 _
  have hP₀M : pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ≤ M := hP₀le.trans (inf_le_left.trans hLM)
  have hP₀N : pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ≤
      M ⊓ Subgroup.normalizer (R : Set G) := hP₀le.trans (inf_le_inf_right _ hLM)
  have hle : imageOTwoQuot M (pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G))) ≤
      pCoreOf 2 (imageOTwoQuot M L ⊓
        imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G))) := by
    refine le_pCoreOf_of_le_normalizer 2
      (le_inf (imageOTwoQuot_mono (hP₀le.trans inf_le_left)) (imageOTwoQuot_mono hP₀N)) ?_
      ((A4.isPGroup_subgroupOf_of_le hP₀M (pCoreOf_isPGroup 2 _)).map _)
    refine le_normalizer_of_forall_conj_mem ?_
    intro u hu v hv
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hu1
    obtain ⟨m, hm, hmN, hmu⟩ := mem_imageOTwoQuot_iff.mp hu2
    have hlR : l ∈ Subgroup.normalizer (R : Set G) := by
      have h1 : (⟨m, hm⟩ : ↥M)⁻¹ * ⟨l, hl⟩ ∈ CFSG.Open.pCore 2 ↥M := QuotientGroup.eq.mp hmu
      have h2 : m⁻¹ * l ∈ pCoreOf 2 M := by
        unfold pCoreOf
        exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
      have h3 : l = m * (m⁻¹ * l) := by group
      rw [h3]
      exact Subgroup.mul_mem _ hmN.2 (Subgroup.le_normalizer (hOR h2))
    obtain ⟨p, hp, hpP, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    have hlP₀ : l ∈ Subgroup.normalizer
        ((pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) : Subgroup G) : Set G) :=
      le_normalizer_pCoreOf 2 _ ⟨hlL, hlR⟩
    refine mem_imageOTwoQuot_iff.mpr
      ⟨l * p * l⁻¹, M.mul_mem (M.mul_mem hl hp) (M.inv_mem hl), ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hlP₀ p).mp hpP
  have hRb : imageOTwoQuot M (pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G))) ≤
      imageOTwoQuot M R := by
    rw [imageOTwoQuot_eq_pCoreOf_normalizer hR]
    exact hle.trans (pCoreOf_inf_le_pCoreOf_of_isComponent _ hKc)
  intro p hp
  have hpM : p ∈ M := hP₀M hp
  have : (QuotientGroup.mk ⟨p, hpM⟩ : OTwoQuot M) ∈ imageOTwoQuot M R :=
    hRb (mem_imageOTwoQuot_iff.mpr ⟨p, hpM, hp, rfl⟩)
  exact mem_of_mk_mem_imageOTwoQuot hOR this

theorem isSylowTwoOf_inf_of_isSubnormal {T H L : Subgroup G} (h : IsSubnormal L H) :
    IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := A4.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

theorem isSylowTwoOf_imageOTwoQuot_iff {M A S : Subgroup G} (hAM : A ≤ M) (hSA : S ≤ A)
    (hS2 : IsPGroup 2 S) (hQ : A ⊓ pCoreOf 2 M ≤ S) :
    IsSylowTwoOf S A ↔ IsSylowTwoOf (imageOTwoQuot M S) (imageOTwoQuot M A) := by
  rw [A4.isSylowTwoOf_iff_maximal, A4.isSylowTwoOf_iff_maximal]
  have hSM : S ≤ M := hSA.trans hAM
  constructor
  · rintro ⟨-, -, hmax⟩
    refine ⟨imageOTwoQuot_mono hSA, (A4.isPGroup_subgroupOf_of_le hSM hS2).map _,
      fun P' hP'A hP'2 hSP' => ?_⟩
    have hSP'' : S ≤ preimageOTwoQuot M P' ⊓ A := fun s hs =>
      ⟨mem_preimageOTwoQuot_iff.mpr
        ⟨hSM hs, hSP' (mem_imageOTwoQuot_iff.mpr ⟨s, hSM hs, hs, rfl⟩)⟩, hSA hs⟩
    have hP''S := hmax _ inf_le_right (isPGroup_preimageOTwoQuot_inf A hP'2) hSP''
    intro u hu
    obtain ⟨a, ha, haA, rfl⟩ := mem_imageOTwoQuot_iff.mp (hP'A hu)
    exact mem_imageOTwoQuot_iff.mpr
      ⟨a, ha, hP''S ⟨mem_preimageOTwoQuot_iff.mpr ⟨ha, hu⟩, haA⟩, rfl⟩
  · rintro ⟨-, -, hmax⟩
    refine ⟨hSA, hS2, fun P hPA hP2 hSP => ?_⟩
    have hPM : P ≤ M := hPA.trans hAM
    have h1 : imageOTwoQuot M P ≤ imageOTwoQuot M S :=
      hmax _ (imageOTwoQuot_mono hPA) ((A4.isPGroup_subgroupOf_of_le hPM hP2).map _)
        (imageOTwoQuot_mono hSP)
    intro p hp
    obtain ⟨s, hs, hsS, hsp⟩ :=
      mem_imageOTwoQuot_iff.mp (h1 (mem_imageOTwoQuot_iff.mpr ⟨p, hPM hp, hp, rfl⟩))
    have h2 : s⁻¹ * p ∈ pCoreOf 2 M := by
      unfold pCoreOf
      exact Subgroup.mem_map.mpr ⟨_, QuotientGroup.eq.mp hsp, rfl⟩
    have h3 : s⁻¹ * p ∈ A ⊓ pCoreOf 2 M := ⟨A.mul_mem (A.inv_mem (hSA hsS)) (hPA hp), h2⟩
    have h4 : p = s * (s⁻¹ * p) := by group
    rw [h4]
    exact S.mul_mem hsS (hQ h3)

theorem le_normalizer_of_imageOTwoQuot_le_normalizer {M R L : Subgroup G}
    (hRM : R ≤ M) (hL : L ∈ cComp M)
    (h : imageOTwoQuot M R ≤ Subgroup.normalizer (imageOTwoQuot M L : Set (OTwoQuot M))) :
    R ≤ Subgroup.normalizer (L : Set G) := by
  intro r hr
  have hrM : r ∈ M := hRM hr
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hL₁c : L.map (MulAut.conj r).toMonoidHom ∈ cComp M := by
    have h1 := cComp_map_mulEquiv (MulAut.conj r) hL
    have h2 : M.map (MulAut.conj r).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hrM)
    rwa [h2] at h1
  have hr' : (QuotientGroup.mk ⟨r, hrM⟩ : OTwoQuot M) ∈ imageOTwoQuot M R :=
    mem_imageOTwoQuot_iff.mpr ⟨r, hrM, hr, rfl⟩
  have hN := Subgroup.mem_normalizer_iff.mp (h hr')
  have himage : imageOTwoQuot M (L.map (MulAut.conj r).toMonoidHom) = imageOTwoQuot M L := by
    ext u
    constructor
    · intro hu
      obtain ⟨x, hx, hxL₁, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hxL₁
      have hlx' : r * l * r⁻¹ = x := by simpa [MulAut.conj_apply] using hlx
      have hmk : (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M) =
          QuotientGroup.mk ⟨r, hrM⟩ * QuotientGroup.mk ⟨l, hLM hl⟩ *
            (QuotientGroup.mk ⟨r, hrM⟩)⁻¹ := by
        subst hlx'
        rfl
      rw [hmk]
      exact (hN _).mp (mem_imageOTwoQuot_iff.mpr ⟨l, hLM hl, hl, rfl⟩)
    · intro hu
      set v : OTwoQuot M :=
        (QuotientGroup.mk ⟨r, hrM⟩)⁻¹ * u * QuotientGroup.mk ⟨r, hrM⟩ with hv
      have hvK : v ∈ imageOTwoQuot M L := by
        refine (hN v).mpr ?_
        have : QuotientGroup.mk ⟨r, hrM⟩ * v * (QuotientGroup.mk ⟨r, hrM⟩)⁻¹ = u := by
          simp [hv, mul_assoc]
        rwa [this]
      obtain ⟨l, hl, hlL, hlv⟩ := mem_imageOTwoQuot_iff.mp hvK
      refine mem_imageOTwoQuot_iff.mpr
        ⟨r * l * r⁻¹, M.mul_mem (M.mul_mem hrM hl) (M.inv_mem hrM),
          Subgroup.mem_map.mpr ⟨l, hlL, by simp [MulAut.conj_apply]⟩, ?_⟩
      have : QuotientGroup.mk ⟨r, hrM⟩ * v * (QuotientGroup.mk ⟨r, hrM⟩)⁻¹ = u := by
        simp [hv, mul_assoc]
      rw [← this, ← hlv]
      rfl
  have hinj := map_injOn_cComp_top (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M))
    (by rw [QuotientGroup.ker_mk']; exact isSolvable_pCore_two M)
  have h2 : (L.map (MulAut.conj r).toMonoidHom).subgroupOf M = L.subgroupOf M :=
    hinj (subgroupOf_mem_cComp hL₁c) (subgroupOf_mem_cComp hL) himage
  have h3 : L.map (MulAut.conj r).toMonoidHom = L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL₁c), h2,
      Subgroup.map_subgroupOf_eq_of_le hLM]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3

theorem isSylowTwoOf_inf_of_not_le_normalizer {M R T L : Subgroup G} (hR : IsTwoRadicalIn M R)
    (hT : IsSylowTwoOf T M) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hL : L ∈ cComp M)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hRL : ¬ R ≤ Subgroup.normalizer (L : Set G)) : IsSylowTwoOf (R ⊓ L) L := by
  have hOR : pCoreOf 2 M ≤ R := c2_1_pCore_le hR
  have hRM : R ≤ M := hR.1
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hKc := isComponent_imageOTwoQuot hL hLq
  have hRb := imageOTwoQuot_eq_pCoreOf_normalizer hR
  have hmove : ¬ pCoreOf 2 (imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G))) ≤
      Subgroup.normalizer (imageOTwoQuot M L : Set (OTwoQuot M)) := by
    rw [← hRb]
    exact fun h => hRL (le_normalizer_of_imageOTwoQuot_le_normalizer hRM hL h)
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hL) hT
  have hQT : pCoreOf 2 M ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hT' : IsSylowTwoOf (imageOTwoQuot M (T ⊓ L)) (imageOTwoQuot M L) :=
    (isSylowTwoOf_imageOTwoQuot_iff hLM inf_le_right hTL.2.1
      (fun x hx => ⟨hQT hx.2, hx.1⟩)).mp hTL
  have hTH : imageOTwoQuot M (T ⊓ L) ≤
      imageOTwoQuot M (M ⊓ Subgroup.normalizer (R : Set G)) :=
    imageOTwoQuot_mono (fun x hx => ⟨hT.1 hx.1, hTR hx.1⟩)
  have h1 := isSylowTwoOf_inf_pCoreOf_of_not_le_normalizer hKc hmove hT' hTH
  have himg : imageOTwoQuot M (R ⊓ L) = imageOTwoQuot M R ⊓ imageOTwoQuot M L := by
    refine le_antisymm (le_inf (imageOTwoQuot_mono inf_le_left) (imageOTwoQuot_mono inf_le_right)) ?_
    intro u hu
    obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hu.2
    exact mem_imageOTwoQuot_iff.mpr
      ⟨l, hl, ⟨mem_of_mk_mem_imageOTwoQuot hOR hu.1, hlL⟩, rfl⟩
  rw [← hRb, ← himg] at h1
  exact (isSylowTwoOf_imageOTwoQuot_iff hLM inf_le_right (hR.isPGroup.to_le inf_le_left)
    (fun x hx => ⟨hOR hx.2, hx.1⟩)).mpr h1

end CFSG.Quasithin.C2Push
