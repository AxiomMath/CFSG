module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.GroupTheory.ABGLocalTools.RelativeStability
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_modO2_modO2Image {H X : Subgroup G} (hXH : X ≤ H) :
    Nonempty (ModO2 (modO2Image H X) ≃* ModO2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set N := CFSG.pCore 2 ↥H with hN
  let ψ : ↥X →* (↥H ⧸ N) := (QuotientGroup.mk' N).comp (Subgroup.inclusion hXH)
  have hrange : ψ.range = modO2Image H X := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let φ : ↥X →* ↥(modO2Image H X) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict
  have hφs : Function.Surjective φ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective
  have hφk : ∀ x : ↥X, φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have h1 : ψ x = 1 := congrArg Subtype.val hx
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, h1⟩
    refine ⟨k, (Subgroup.inclusion_injective hXH) ?_⟩
    have h2 : (Subgroup.inclusion hXH x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [map_pow, h2, map_one]
  have hPn : (CFSG.pCore 2 ↥(modO2Image H X)).Normal := CFSG.pCore_normal
  let ψ' : ↥X →* ModO2 (modO2Image H X) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(modO2Image H X))).comp φ
  have hψ's : Function.Surjective ψ' := (QuotientGroup.mk'_surjective _).comp hφs
  have hker : ψ'.ker = CFSG.pCore 2 ↥X := by
    apply le_antisymm
    · have hp : IsPGroup 2 ψ'.ker := by
        rintro ⟨x, hx⟩
        have h1 : φ x ∈ CFSG.pCore 2 ↥(modO2Image H X) := by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at hx
          exact hx
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image H X))) ⟨_, h1⟩
        have h2 : φ (x ^ 2 ^ k) = 1 := by
          rw [map_pow]
          exact congrArg Subtype.val hk
        obtain ⟨j, hj⟩ := hφk _ h2
        refine ⟨k + j, Subtype.ext ?_⟩
        show x ^ 2 ^ (k + j) = 1
        rw [pow_add, pow_mul, hj]
      exact le_sSup ⟨inferInstance, hp⟩
    · intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact CFSG.ABGLocalTools.map_pCore_le_of_surjective φ hφs ⟨x, hx, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

omit [Finite G] in
theorem nonempty_modO2_conjugate (X : Subgroup G) (g : G) :
    Nonempty (ModO2 (CFSG.conjugate X g) ≃* ModO2 X) := by
  let e : ↥X ≃* ↥(X.map (MulAut.conj g⁻¹).toMonoidHom) :=
    X.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have he := CFSG.pCore_map_iso 2 e
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(CFSG.conjugate X g)) e he).symm⟩

omit [Finite G] in
theorem modO2Image_mono' {H Y Z : Subgroup G} (h : Y ≤ Z) : modO2Image H Y ≤ modO2Image H Z :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem modO2Image_le_normalizer' {H A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    modO2Image H A ≤ Subgroup.normalizer (modO2Image H B : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have h1 : A.subgroupOf H ≤ Subgroup.normalizer ((B.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    fun a ha => Subgroup.le_normalizer_comap H.subtype (hAB ha)
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

omit [Finite G] in
theorem isSylowTwoOf_modO2Image {H S : Subgroup G} (hS : IsSylowTwoOf S H) :
    IsSylowTwoOf (modO2Image H S) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)

theorem modO2Image_pCoreOf_le {H X : Subgroup G} :
    modO2Image H (pCoreOf 2 X) ≤ pCoreOf 2 (modO2Image H X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (modO2Image_mono' (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
    (modO2Image_le_normalizer' (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)) ?_
  exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_of_injective _
    (Subgroup.subtype_injective H)).map _

omit [Finite G] in
theorem commutator_modO2Image_le {H A B Y : Subgroup G} (h : ⁅A, B⁆ ≤ Y) :
    ⁅modO2Image H A, modO2Image H B⁆ ≤ modO2Image H Y := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  have hxy : (⁅(x : G), (y : G)⁆ : G) ∈ Y := h (Subgroup.commutator_mem_commutator hx hy)
  refine Subgroup.mem_map.mpr ⟨⁅x, y⁆, ?_, ?_⟩
  · show ((⁅x, y⁆ : ↥H) : G) ∈ Y
    simpa [commutatorElement_def] using hxy
  · simp [commutatorElement_def]

omit [Finite G] in
theorem isPGroup_of_mem_center {H X : Subgroup G} (hXH : X ≤ H)
    (hs : IsSimpleGroup (ModO2 X)) (hnab : ∃ a b : ModO2 X, a * b ≠ b * a)
    {y : ↥H ⧸ CFSG.pCore 2 ↥H} (hy : y ∈ modO2Image H X)
    (hc : ∀ z ∈ modO2Image H X, y * z = z * y) : ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_modO2_modO2Image hXH
  have hPn : (CFSG.pCore 2 ↥(modO2Image H X)).Normal := CFSG.pCore_normal
  have hcen : e (QuotientGroup.mk' _ ⟨y, hy⟩) ∈ Subgroup.center (ModO2 X) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hc w hw).symm
  have hbot : Subgroup.center (ModO2 X) = ⊥ := by
    have := hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 X)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  rw [hbot, Subgroup.mem_bot, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcen
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image H X))) ⟨_, hcen⟩
  exact ⟨k, congrArg Subtype.val (congrArg Subtype.val hk)⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
