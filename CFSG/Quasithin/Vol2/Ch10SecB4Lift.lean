module

public import CFSG.Quasithin.Vol2.Ch10SecBFacts
public import CFSG.Quasithin.Vol2.Ch10SecBCoordL0
public import CFSG.Quasithin.Background.C2PushLift

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

abbrev imgO2 (L X : Subgroup G) : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
  (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

omit [Finite G] in
theorem le_normalizer_of_conj_mem {Q : Type*} [Group Q] {H N : Subgroup Q}
    (h : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set Q) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h g hg n, fun hn => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) _ hn
  simpa [mul_assoc] using this

section Image

variable {L X : Subgroup G}

omit [Finite G] in
theorem mk_mem_imgO2 {x : G} (hxL : x ∈ L) (hx : x ∈ X) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩) ∈ imgO2 L X :=
  ⟨⟨x, hxL⟩, hx, rfl⟩

theorem imgO2_eq_oTwoUpper (hXL : X ≤ L) (hX : X = oTwoUpper X) :
    imgO2 L X = oTwoUpper (imgO2 L X) := by
  have hY : (X.subgroupOf L).map L.subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXL]
  have h1 : (oTwoUpper X).subgroupOf L = oTwoUpper (X.subgroupOf L) := by
    conv_lhs => rw [← hY, oTwoUpper_map]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [imgO2, oTwoUpper_map, ← h1, ← hX]

theorem map_pCoreOf_le (hXL : X ≤ L) :
    ((pCoreOf 2 X).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤
      pCoreOf 2 (imgO2 L X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono fun y hy => CFSG.LieType.BorelTits.pCoreOf_le 2 X hy) ?_ ?_
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨g, hg, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨g * y * g⁻¹, ?_, by simp⟩
    have hy' : (y : G) ∈ pCoreOf 2 X := hy
    have hg' : (g : G) ∈ X := hg
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hg') _).mp hy'
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  · exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
      (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXL)).symm).map
      _

theorem mem_pCoreOf_of_mk (hXL : X ≤ L) {x : G} (hx : x ∈ X)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hXL hx⟩ ∈ pCoreOf 2 (imgO2 L X)) :
    x ∈ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  set N : Subgroup G := X ⊓ ((pCoreOf 2 (imgO2 L X)).comap π).map L.subtype with hNdef
  have hmemN : ∀ y : G, y ∈ N ↔ ∃ hy : y ∈ X, π ⟨y, hXL hy⟩ ∈ pCoreOf 2 (imgO2 L X) := by
    intro y
    constructor
    · rintro ⟨hyX, ⟨z, hz, rfl⟩⟩
      exact ⟨hyX, hz⟩
    · rintro ⟨hyX, hy⟩
      exact ⟨hyX, ⟨⟨y, hXL hyX⟩, hy, rfl⟩⟩
  have hNle : N ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) ?_
    · have key : ∀ g ∈ X, ∀ y ∈ N, g * y * g⁻¹ ∈ N := by
        intro g hg y hy
        obtain ⟨hyX, hy'⟩ := (hmemN y).mp hy
        have hm : g * y * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg)
        refine (hmemN _).mpr ⟨hm, ?_⟩
        have hgN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (imgO2 L X)
          (mk_mem_imgO2 (hXL hg) hg)
        have := (Subgroup.mem_normalizer_iff.mp hgN _).mp hy'
        rw [show (⟨g * y * g⁻¹, hXL hm⟩ : ↥L) = ⟨g, hXL hg⟩ * ⟨y, hXL hyX⟩ * ⟨g, hXL hg⟩⁻¹
          from rfl, map_mul, map_mul, map_inv]
        exact this
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨key g hg y, fun hy => ?_⟩
      have := key g⁻¹ (X.inv_mem hg) _ hy
      simpa [mul_assoc] using this
    · rintro ⟨y, hy⟩
      obtain ⟨hyX, hy'⟩ := (hmemN y).mp hy
      obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (imgO2 L X) ⟨_, hy'⟩
      have ha' : (π ⟨y, hXL hyX⟩) ^ 2 ^ a = 1 := congrArg Subtype.val ha
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha'
      obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨_, ha'⟩
      have hb' : ((⟨y, hXL hyX⟩ : ↥L) ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
      refine ⟨a + b, Subtype.ext ?_⟩
      have := congrArg Subtype.val hb'
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      show y ^ 2 ^ (a + b) = 1
      rw [pow_add, pow_mul, this]
  exact hNle ((hmemN x).mpr ⟨hx, h⟩)

theorem relIndex_imgO2 (hXL : X ≤ L) :
    (pCoreOf 2 (imgO2 L X)).relIndex (imgO2 L X) = (pCoreOf 2 X).relIndex X := by
  set ψ : ↥X →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL) with hψ
  have hrange : ψ.range = imgO2 L X := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact mk_mem_imgO2 (hXL x.2) x.2
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hcomap : (pCoreOf 2 X).subgroupOf X = (pCoreOf 2 (imgO2 L X)).comap ψ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro hx
      exact map_pCoreOf_le hXL ⟨⟨x, hXL x.2⟩, hx, rfl⟩
    · intro hx
      exact mem_pCoreOf_of_mk hXL x.2 hx
  have h := Subgroup.index_comap (H := pCoreOf 2 (imgO2 L X)) ψ
  rw [← hcomap, hrange] at h
  exact h.symm

end Image

omit [Finite G] in
theorem mk_mem_normalizer_imgO2 {L X : Subgroup G} {s : G} (hsL : s ∈ L)
    (hsX : s ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨s, hsL⟩ ∈
      Subgroup.normalizer (imgO2 L X : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  refine le_normalizer_of_conj_mem (H := ((Subgroup.normalizer (X : Set G)).subgroupOf L).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ?_ ⟨⟨s, hsL⟩, hsX, rfl⟩
  rintro _ ⟨g, hg, rfl⟩ _ ⟨y, hy, rfl⟩
  refine ⟨g * y * g⁻¹, ?_, by simp⟩
  have hy' : (y : G) ∈ X := hy
  have hg' : (g : G) ∈ Subgroup.normalizer (X : Set G) := hg
  have := (Subgroup.mem_normalizer_iff.mp hg' _).mp hy'
  exact Subgroup.mem_subgroupOf.mpr (by simpa using this)

theorem exists_pow_four_not_mem (hF : FactL33M11) {H T L X : Subgroup G}
    (hT : IsSylowTwoOf T H) (hL : L ∈ cComp H)
    (htype : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11))
    (hXL : X ≤ L) (hX : X = oTwoUpper X) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hpow : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X) (hrel : (pCoreOf 2 X).relIndex X = 9) :
    ∃ s ∈ T, ∃ x ∈ X, s ^ 4 * x * (s ^ 4)⁻¹ * x⁻¹ ∉ pCoreOf 2 X := by
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    C2Push.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hL) hT
  have hS : IsSylowTwoOf (D1 T L) ⊤ :=
    isSylowTwoOf_map_of_surjective hTLs _ (QuotientGroup.mk'_surjective _)
  have hSY : D1 T L ≤ Subgroup.normalizer (imgO2 L X : Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rintro _ ⟨⟨s, hsL⟩, hsT, rfl⟩
    exact mk_mem_normalizer_imgO2 hsL (hTX (Subgroup.mem_subgroupOf.mp hsT).1)
  have hpow' : ∀ q ∈ imgO2 L X, q ^ 3 ∈ pCoreOf 2 (imgO2 L X) := by
    rintro _ ⟨⟨y, hyL⟩, hyX, rfl⟩
    have hy3 := hpow y hyX
    rw [← map_pow]
    exact map_pCoreOf_le hXL ⟨⟨y ^ 3, L.pow_mem hyL 3⟩, hy3, rfl⟩
  obtain ⟨_, ⟨⟨s, hsL⟩, hsT, rfl⟩, _, ⟨⟨y, hyL⟩, hyX, rfl⟩, hne⟩ := hF _ htype (D1 T L)
    (imgO2 L X) hS (imgO2_eq_oTwoUpper hXL hX) hSY hpow' (by rw [relIndex_imgO2 hXL, hrel])
  refine ⟨s, (Subgroup.mem_subgroupOf.mp hsT).1, y, hyX, fun hmem => hne ?_⟩
  have hm := map_pCoreOf_le hXL
    ⟨⟨_, hXL (CFSG.LieType.BorelTits.pCoreOf_le 2 X hmem)⟩, hmem, rfl⟩
  have e : (⟨s ^ 4 * y * (s ^ 4)⁻¹ * y⁻¹, hXL (CFSG.LieType.BorelTits.pCoreOf_le 2 X hmem)⟩ :
      ↥L) = ⟨s, hsL⟩ ^ 4 * ⟨y, hyL⟩ * (⟨s, hsL⟩ ^ 4)⁻¹ * ⟨y, hyL⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow] at hm
  exact hm

end CFSG.Quasithin.Vol2.Ch10.SecB
