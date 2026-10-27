module

public import CFSG.RankThree.PartTwo.Sec10.Item103
public import CFSG.RankThree.PartTwo.KFacts.KS10L27
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

theorem IsSylowOf.inf_of_isSubnormal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsSylowOf p P ⊤) {H : Subgroup G} (hH : H.IsSubnormal) :
    IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

theorem exists_isSylowOf_le_normalizer {G : Type*} [Group G] [Finite G] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {E Y : Subgroup G} (hE : IsPGroup p E)
    (hY : ¬ p ∣ Nat.card Y) (hEY : E ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ T : Subgroup G, IsSylowOf q T Y ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  let φ : E →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hEY)
  let : MulDistribMulAction E Y := MulDistribMulAction.compHom Y φ
  have hcard : ¬ p ∣ Nat.card (Sylow q Y) := fun h => hY (h.trans
    ((Sylow.card_dvd_index (Classical.arbitrary (Sylow q Y))).trans (Subgroup.index_dvd_card _)))
  obtain ⟨S, hS⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q Y) hcard
  have hSinv : ∀ e : E, ∀ s ∈ (S : Subgroup Y), e • s ∈ (S : Subgroup Y) := by
    intro e s hs
    have hmem : e • s ∈ ((e • S : Sylow q Y) : Subgroup Y) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hS e] at hmem
  refine ⟨(S : Subgroup Y).map Y.subtype, ⟨S, rfl⟩, fun e he => ?_⟩
  have hconj : ∀ e ∈ E, ∀ t ∈ (S : Subgroup Y).map Y.subtype,
      e * t * e⁻¹ ∈ (S : Subgroup Y).map Y.subtype := by
    rintro e he _ ⟨s, hs, rfl⟩
    exact ⟨_, hSinv ⟨e, he⟩ s hs, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨hconj e he t, fun ht => ?_⟩
  have := hconj e⁻¹ (E.inv_mem he) _ ht
  simpa [mul_assoc] using this

theorem exists_pGroup_le_normalizer {G : Type*} [Group G] [Finite G] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {E Y : Subgroup G} (hE : IsPGroup p E)
    (hY : ¬ p ∣ Nat.card Y) (hqY : q ∣ Nat.card Y) (hEY : E ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ T : Subgroup G, T ≤ Y ∧ T ≠ ⊥ ∧ IsPGroup q T ∧
      E ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨T, ⟨S, rfl⟩, hET⟩ := exists_isSylowOf_le_normalizer (q := q) hE hY hEY
  refine ⟨_, Subgroup.map_subtype_le _, ?_, S.isPGroup'.map _, hET⟩
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective]
  exact Sylow.ne_bot_of_dvd_card S hqY

@[expose] noncomputable def thetaPreimage {G : Type*} [Group G] [Finite G] (L : Subgroup G)
    (V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Subgroup G :=
  (V.comap (QuotientGroup.mk' (aschbacherSolvableCore 3 L))).map L.subtype

section Preimage

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}
  {V : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}

theorem thetaPreimage_le : thetaPreimage L V ≤ L := Subgroup.map_subtype_le _

theorem mem_thetaPreimage_iff {x : G} :
    x ∈ thetaPreimage L V ↔ ∃ hx : x ∈ L, ((⟨x, hx⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxV⟩
    exact ⟨⟨x, hx⟩, hxV, rfl⟩

theorem card_thetaPreimage :
    Nat.card (thetaPreimage L V) = Nat.card (aschbacherSolvableCore 3 L) * Nat.card V := by
  rw [thetaPreimage, Subgroup.card_map_of_injective L.subtype_injective,
    CFSG.ABGLocalTools.card_comap_mk']

theorem not_three_dvd_card_thetaPreimage (hV : IsPGroup 2 V) :
    ¬ 3 ∣ Nat.card (thetaPreimage L V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [card_thetaPreimage]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1 h
  · obtain ⟨k, hk⟩ := hV.exists_card_eq
    rw [hk] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega

theorem two_dvd_card_thetaPreimage (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    2 ∣ Nat.card (thetaPreimage L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_thetaPreimage]
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hV1 (Subgroup.eq_bot_of_card_eq V hk)
  rw [hk]
  exact dvd_mul_of_dvd_right (dvd_pow_self 2 hk0) _

theorem mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer {x : G}
    (hx : x ∈ Sec4.thetaQuotCentralizer L) :
    x ∈ Subgroup.normalizer ((thetaPreimage L V : Subgroup G) : Set G) := by
  obtain ⟨hxN, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
  have key : ∀ x : G, x ∈ Sec4.thetaQuotCentralizer L → ∀ y ∈ thetaPreimage L V,
      x * y * x⁻¹ ∈ thetaPreimage L V := by
    intro x hx y hy
    obtain ⟨hxN, hxl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hx
    obtain ⟨hyL, hyV⟩ := mem_thetaPreimage_iff.mp hy
    have hxy : x * y * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxN y).mp hyL
    refine mem_thetaPreimage_iff.mpr ⟨hxy, ?_⟩
    obtain ⟨t, ht, hteq⟩ := hxl y hyL
    have hq : ((⟨x * y * x⁻¹, hxy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨y, hyL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
      rw [QuotientGroup.eq]
      have : (⟨y, hyL⟩ : L)⁻¹ * ⟨x * y * x⁻¹, hxy⟩ = t := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hteq.symm)
      rw [show (⟨x * y * x⁻¹, hxy⟩ : L)⁻¹ * ⟨y, hyL⟩ =
        ((⟨y, hyL⟩ : L)⁻¹ * ⟨x * y * x⁻¹, hxy⟩)⁻¹ by group, this]
      exact inv_mem ht
    rw [hq]
    exact hyV
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have hxinv : x⁻¹ ∈ Sec4.thetaQuotCentralizer L := (Sec4.thetaQuotCentralizer L).inv_mem hx
  have := key x⁻¹ hxinv _ hy
  simpa [mul_assoc] using this

theorem mem_normalizer_thetaPreimage_of_mem {x : G} (hxL : x ∈ L)
    (hxV : ((⟨x, hxL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.normalizer (V : Set (L ⧸ aschbacherSolvableCore 3 L))) :
    x ∈ Subgroup.normalizer ((thetaPreimage L V : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨hyL, hyV⟩ := mem_thetaPreimage_iff.mp hy
    have hxyL : x * y * x⁻¹ ∈ L := L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL)
    refine mem_thetaPreimage_iff.mpr ⟨hxyL, ?_⟩
    have he : ((⟨x * y * x⁻¹, hxyL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨x, hxL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) * ((⟨y, hyL⟩ : L) :
          L ⧸ aschbacherSolvableCore 3 L) *
          ((⟨x, hxL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [he]
    exact (Subgroup.mem_normalizer_iff.mp hxV _).mp hyV
  · intro hy
    obtain ⟨hyL', hyV⟩ := mem_thetaPreimage_iff.mp hy
    have hyL : y ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem hxL) hyL') hxL
      simpa [mul_assoc] using this
    refine mem_thetaPreimage_iff.mpr ⟨hyL, ?_⟩
    have he : ((⟨x * y * x⁻¹, hyL'⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨x, hxL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) * ((⟨y, hyL⟩ : L) :
          L ⧸ aschbacherSolvableCore 3 L) *
          ((⟨x, hxL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [he] at hyV
    exact (Subgroup.mem_normalizer_iff.mp hxV _).mpr hyV

end Preimage

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem Sec10Std.pow_three (h : Sec10Std G A c L a R) {x : G} (hx : x ∈ A) : x ^ 3 = 1 :=
  h.mem_partTwoF.1.2 x hx

theorem Sec10Std.comm (h : Sec10Std G A c L a R) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem Sec10Std.orderOf_c (h : Sec10Std G A c L a R) : orderOf c = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (h.pow_three h.mem_A) h.ne_one

theorem Sec10Std.le_centralizer_c (h : Sec10Std G A c L a R) :
    L ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt

theorem Sec10Std.isPGroup_R (h : Sec10Std G A c L a R) : IsPGroup 3 R :=
  h.isSylowOf.isPGroup

theorem Sec10Std.R_le_centralizer (h : Sec10Std G A c L a R) :
    R ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec11.le_centralizer_of_le_normalizer_zpowers h.orderOf_c h.isPGroup_R h.isSylowOf.le

theorem Sec10Std.R_le_normalizer (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) :
    R ≤ Subgroup.normalizer (L : Set G) :=
  Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp
    (h.pow_three h.mem_A) h.ne_one h.isPGroup_R h.R_le_centralizer L h.mem_thetaComponentsAt

theorem Sec10Std.A_le_R (h : Sec10Std G A c L a R) : A ≤ R := le_of_hyp91 h.toHyp91

theorem not_three_dvd_card_theta (L : Subgroup G) :
    ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
  (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1

theorem eq_one_of_mem_theta_of_isPGroup {x : G} {k : ℕ}
    (hx : x ∈ inSubgroup (aschbacherSolvableCore 3) L) (hk : x ^ 3 ^ k = 1) : x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hk' : y ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [Sec11.eq_one_of_mem_theta_of_pow_eq_one hy hk']
  rfl

theorem Sec10Std.exists_mulEquiv_psl2 (h : Sec10Std G A c L a R) :
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) := by
  obtain ⟨e⟩ := h.iso
  exact ⟨e.trans (Sec4.projSLEquivPSL _)⟩

theorem Sec10Std.twentyseven_dvd_card (h : Sec10Std G A c L a R) : 27 ∣ Nat.card L := by
  obtain ⟨e⟩ := h.exists_mulEquiv_psl2
  have h1 : 27 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Nat.card_congr e.toEquiv]
    have h2 := Subgroup.card_dvd_of_le (le_top : GorensteinWalter.psl2UpperUnipotentSubgroup
      (GaloisField 3 3) ≤ ⊤)
    rwa [GorensteinWalter.psl2UpperUnipotentSubgroup_card, GaloisField.card 3 3 (by norm_num),
      Subgroup.card_top] at h2
  exact h1.trans (by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 L)]
    exact dvd_mul_right _ _)

theorem Sec10Std.isSylowOf_inf_L (h : Sec10Std G A c L a R) : IsSylowOf 3 (R ⊓ L) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt
  have hCH : C ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun g hg =>
    Sec10.mem_normalizer_zpowers_of_conj_mem (by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c)
  have hRC : IsSylowOf 3 R C := h.isSylowOf.of_le h.R_le_centralizer hCH
  have hR' : IsSylowOf 3 (R.subgroupOf C) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr h.R_le_centralizer, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hRC
  have h1 := IsSylowOf.inf_of_isSubnormal hR' hL'.2.1
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C] at h1
  have e1 : (R.subgroupOf C ⊓ L.subgroupOf C).map C.subtype = R ⊓ L := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyR, hyL⟩, rfl⟩
      exact ⟨hyR, hyL⟩
    · rintro ⟨hxR, hxL⟩
      exact ⟨⟨x, hLC hxL⟩, ⟨hxR, hxL⟩, rfl⟩
  rwa [e1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLC] at h1

theorem Sec10Std.eq_one_of_mem_inf_thetaQuotCentralizer (h : Sec10Std G A c L a R) {x : G}
    (hxR : x ∈ R) (hxL : x ∈ L) (hx : x ∈ Sec4.thetaQuotCentralizer L) : x = 1 := by
  obtain ⟨e⟩ := h.exists_mulEquiv_psl2
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  have hθ := Sec11.mem_theta_of_mem_thetaQuotCentralizer hZ hxL hx
  obtain ⟨k, hk⟩ := h.isPGroup_R ⟨x, hxR⟩
  have hk' : (⟨x, hxL⟩ : L) ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have := Sec11.eq_one_of_mem_theta_of_pow_eq_one hθ hk'
  exact congrArg Subtype.val this

theorem Sec10Std.eq_one_of_mem_R_of_mem_theta (h : Sec10Std G A c L a R) {x : G} (hxR : x ∈ R)
    (hx : x ∈ inSubgroup (aschbacherSolvableCore 3) L) : x = 1 := by
  obtain ⟨k, hk⟩ := h.isPGroup_R ⟨x, hxR⟩
  exact eq_one_of_mem_theta_of_isPGroup hx (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem mem_theta_of_mk_eq_one {x : L}
    (hx : (x : L ⧸ aschbacherSolvableCore 3 L) = 1) :
    (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) L :=
  ⟨x, (QuotientGroup.eq_one_iff x).mp hx, rfl⟩

theorem Sec10Std.isElemAbelian_inf_and_card (h : Sec10Std G A c L a R) :
    CFSG.Assembly.IsElemAbelian 3 (R ⊓ L) ∧ Nat.card (R ⊓ L : Subgroup G) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.exists_mulEquiv_psl2
  set S := (R ⊓ L).subgroupOf L with hS
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hS3 : IsPGroup 3 S := (h.isPGroup_R.to_inf_left).comap_subtype
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  obtain ⟨hSe, hScard⟩ := KFacts.isElemAbelian_of_isPGroup_three_of_mulEquiv hK e
    (hS3.map π)
  rw [hK] at hScard
  have hker : ∀ x ∈ S, π x = 1 → x = 1 := by
    intro x hx hx1
    have h1 := h.eq_one_of_mem_R_of_mem_theta (Subgroup.mem_subgroupOf.mp hx).1
      (mem_theta_of_mk_eq_one hx1)
    exact Subtype.ext h1
  have hinj : Function.Injective (π.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    exact Subtype.ext (by simpa using congrArg Subtype.val (show (x : L) = 1 from
      hker x x.2 hx))
  have hcardS : Nat.card S = Nat.card (S.map π) := by
    rw [show S.map π = (π.comp S.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hcardRL : Nat.card (R ⊓ L : Subgroup G) = Nat.card S := by
    rw [hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  ·
    have hxS : (⟨x, x.2.2⟩ : L) ∈ S := Subgroup.mem_subgroupOf.mpr x.2
    have hyS : (⟨y, y.2.2⟩ : L) ∈ S := Subgroup.mem_subgroupOf.mpr y.2
    have h1 : π ⟨x, x.2.2⟩ * π ⟨y, y.2.2⟩ = π ⟨y, y.2.2⟩ * π ⟨x, x.2.2⟩ :=
      congrArg Subtype.val (hSe.1.is_comm.comm ⟨_, _, hxS, rfl⟩ ⟨_, _, hyS, rfl⟩)
    have h2 : (⟨x, x.2.2⟩ : L) * ⟨y, y.2.2⟩ * (⟨y, y.2.2⟩ * ⟨x, x.2.2⟩)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hxS hyS) (S.inv_mem (S.mul_mem hyS hxS))
    have h3 := hker _ h2 (by rw [map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel])
    have h4 : (⟨x, x.2.2⟩ : L) * ⟨y, y.2.2⟩ = ⟨y, y.2.2⟩ * ⟨x, x.2.2⟩ := mul_inv_eq_one.mp h3
    have h5 : (x : G) * y = y * x := by simpa using congrArg Subtype.val h4
    exact h5
  ·
    have hxS : (⟨x, hx.2⟩ : L) ∈ S := Subgroup.mem_subgroupOf.mpr hx
    have h1 : π ⟨x, hx.2⟩ ^ 3 = 1 := hSe.2 _ ⟨_, hxS, rfl⟩
    have h2 := hker _ (S.pow_mem hxS 3) (by rw [map_pow, h1])
    exact congrArg Subtype.val h2
  ·
    apply le_antisymm
    · rw [hcardRL, hcardS]
      exact hScard
    · have hsyl := h.isSylowOf_inf_L.card_eq
      rw [hsyl]
      have h27 := h.twentyseven_dvd_card
      have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
      have h3 : 3 ≤ (Nat.card L).factorization 3 := by
        have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0).mp
          (show 3 ^ 3 ∣ Nat.card L by simpa using h27)
        exact this
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (Nat.card L).factorization 3 := Nat.pow_le_pow_right (by norm_num) h3

theorem Sec10Std.isElemAbelian_inf (h : Sec10Std G A c L a R) :
    CFSG.Assembly.IsElemAbelian 3 (R ⊓ L) :=
  h.isElemAbelian_inf_and_card.1

theorem Sec10Std.card_inf (h : Sec10Std G A c L a R) : Nat.card (R ⊓ L : Subgroup G) = 27 :=
  h.isElemAbelian_inf_and_card.2

theorem Sec10Std.c_not_mem_L (h : Sec10Std G A c L a R) : c ∉ L := not_mem_of_sec10Std h

theorem Sec10Std.a_not_mem_L (h : Sec10Std G A c L a R) : a ∉ L := by
  intro haL
  obtain ⟨haN, hout⟩ := h.toHyp81.inducesOuterTheta
  apply hout
  rw [show (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, Subgroup.le_normalizer haL⟩ from
    rfl, Sec11.thetaQuotMulAut_compAction_of_mem L haL]
  exact ⟨_, rfl⟩

omit [Finite G] in
theorem disjoint_zpowers_of_pow_three {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxH : x ∉ H) :
    Disjoint H (Subgroup.zpowers x) := by
  rw [Subgroup.disjoint_def]
  intro y hyH hyx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  rw [zpow_eq_zpow_emod k hx3'] at hyH ⊢
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk] at hyH ⊢
  · exact zpow_zero x
  · exact absurd (by simpa using hyH) hxH
  · exfalso
    apply hxH
    have h1 : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, hx3', mul_one, zpow_one]
    rw [h1]
    exact H.zpow_mem hyH 2

omit [Finite G] in
theorem isElemAbelian_zpowers_of_pow_three {x : G} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem Sec10Std.commute_c_of_mem_inf (h : Sec10Std G A c L a R) {x : G} (hx : x ∈ R ⊓ L) :
    x * c = c * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hx.2)

theorem Sec10Std.isElemAbelian_D (h : Sec10Std G A c L a R) :
    CFSG.Assembly.IsElemAbelian 3 (sec10D c R L) := by
  rw [sec10D, sup_comm]
  exact Sec15.isElemAbelian_sup_zpowers h.isElemAbelian_inf (h.pow_three h.mem_A)
    fun e he => h.commute_c_of_mem_inf he

theorem Sec10Std.card_D (h : Sec10Std G A c L a R) : Nat.card (sec10D c R L) = 81 := by
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => h.commute_c_of_mem_inf hy)
  have hdis : Disjoint (R ⊓ L) (Subgroup.zpowers c) :=
    disjoint_zpowers_of_pow_three (h.pow_three h.mem_A) fun hc => h.c_not_mem_L hc.2
  rw [sec10D, sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdis,
    h.card_inf, Nat.card_zpowers, h.orderOf_c]

theorem Sec10Std.c_mem_D (_h : Sec10Std G A c L a R) : c ∈ sec10D c R L :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers c)

theorem Sec10Std.inf_le_D (_h : Sec10Std G A c L a R) : R ⊓ L ≤ sec10D c R L := le_sup_right

theorem Sec10Std.d_mem_inf (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) : d ∈ R ⊓ L := by
  have hd : d ∈ A ⊓ L := hdL ▸ Subgroup.mem_zpowers d
  exact ⟨h.A_le_R hd.1, hd.2⟩

theorem Sec10Std.d_mem_A (_h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) : d ∈ A :=
  (hdL ▸ Subgroup.mem_zpowers d : d ∈ A ⊓ L).1

theorem Sec10Std.inf_centralizer_a (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hA : A = Subgroup.closure {c, a, d}) :
    R ⊓ L ⊓ Subgroup.centralizer ({a} : Set G) = Subgroup.zpowers d := by
  have hdRL := h.d_mem_inf hdL
  have hdA := h.d_mem_A hdL
  apply le_antisymm
  · intro x hx
    obtain ⟨hxRL, hxa⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxa
    have hx3 : x ^ 3 = 1 := h.isElemAbelian_inf.2 x hxRL
    have hAx : A ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [hA, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with rfl | rfl | rfl
      · exact (h.commute_c_of_mem_inf hxRL).symm
      · exact hxa.symm
      · exact congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨y, hdRL⟩ ⟨x, hxRL⟩)
    have hxA := Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3 hAx
    rw [← hdL]
    exact ⟨hxA, hxRL.2⟩
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hdRL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.comm hdA h.a_mem

end Std

end CFSG.RankThree.PartTwo.Sec10
