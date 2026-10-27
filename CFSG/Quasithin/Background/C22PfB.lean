module

public import CFSG.Quasithin.Background.C22PfA
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.C2Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace C22Pf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_modO2Image_iff {H A : Subgroup G} {x : ↥H ⧸ CFSG.pCore 2 ↥H} :
    x ∈ modO2Image H A ↔ ∃ a : ↥H, (a : G) ∈ A ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥H) a = x := by
  rw [modO2Image, Subgroup.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, Subgroup.mem_subgroupOf.mp ha, h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, Subgroup.mem_subgroupOf.mpr ha, h⟩⟩

omit [Finite G] in
theorem mk_eq_one_iff {H : Subgroup G} (h : ↥H) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hy
    exact ⟨h, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = h := Subtype.ext hzy
    rwa [this] at hz

omit [Finite G] in
theorem mem_of_mk_mem {H A : Subgroup G} (hQ : pCoreOf 2 H ≤ A) {h : ↥H}
    (hh : QuotientGroup.mk' (CFSG.pCore 2 ↥H) h ∈ modO2Image H A) : (h : G) ∈ A := by
  obtain ⟨a, ha, hae⟩ := mem_modO2Image_iff.mp hh
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (a⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, hae, inv_mul_cancel]
  rw [mk_eq_one_iff] at h1
  have e : (h : G) = (a : G) * ((a⁻¹ * h : ↥H) : G) := by simp
  rw [e]
  exact A.mul_mem ha (hQ h1)

omit [Finite G] in
theorem isPGroup_modO2Image {H A : Subgroup G} (hA : IsPGroup 2 ↥A) :
    IsPGroup 2 ↥(modO2Image H A) := by
  have hsub : IsPGroup 2 ↥(A.subgroupOf H) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hA ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  exact hsub.map _

omit [Finite G] in
theorem mk_mem_normalizer {H A : Subgroup G} {x : ↥H}
    (hx : (x : G) ∈ Subgroup.normalizer (A : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ∈ Subgroup.normalizer
      ((modO2Image H A : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
  constructor
  · intro hy
    obtain ⟨a, ha, hae⟩ := mem_modO2Image_iff.mp hy
    refine mem_modO2Image_iff.mpr ⟨x * a * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hae]⟩
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp ha
  · intro hy
    obtain ⟨a, ha, hae⟩ := mem_modO2Image_iff.mp hy
    refine mem_modO2Image_iff.mpr ⟨x⁻¹ * a * x, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp ha
      simpa using h1
    · rw [map_mul, map_mul, map_inv, hae]
      group

theorem mem_normalizer_of_conj_mem {Γ : Type*} [Group Γ] [Finite Γ] {A : Subgroup Γ} {g : Γ}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set Γ) := by
  let f : A → A := fun a => ⟨g * a * g⁻¹, h a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa [f] using this
  have hsurj := Finite.surjective_of_injective hf
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => h a ha, fun ha => ?_⟩
  obtain ⟨b, hb⟩ := hsurj ⟨_, ha⟩
  have := congrArg Subtype.val hb
  simp only [f, mul_left_inj, mul_right_inj] at this
  exact this ▸ b.2

theorem mem_normalizer_of_mk {H R : Subgroup G} (hRH : R ≤ H) (hQ : pCoreOf 2 H ≤ R) {x : ↥H}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ∈ Subgroup.normalizer
      ((modO2Image H R : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    (x : G) ∈ Subgroup.normalizer (R : Set G) := by
  refine mem_normalizer_of_conj_mem fun r hr => ?_
  have hrH : r ∈ H := hRH hr
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (x * ⟨r, hrH⟩ * x⁻¹) ∈ modO2Image H R := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp (mem_modO2Image_iff.mpr ⟨⟨r, hrH⟩, hr, rfl⟩)
  exact mem_of_mk_mem hQ h1

theorem eq_pCoreOf_normalizer_modO2Image {H R : Subgroup G} (hR : IsTwoRadicalIn H R) :
    modO2Image H R = pCoreOf 2 (Subgroup.normalizer
      ((modO2Image H R : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : pCoreOf 2 H ≤ R := c2_1_pCore_le hR
  have hRH : R ≤ H := hR.1
  set N := Subgroup.normalizer
    ((modO2Image H R : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) with hN
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (isPGroup_modO2Image hR.isPGroup)
  ·
    set P : Subgroup G := ((pCoreOf 2 N).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
      H.subtype with hP
    have hmemP : ∀ h : ↥H, (h : G) ∈ P ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥H) h ∈ pCoreOf 2 N := by
      intro h
      constructor
      · rintro ⟨y, hy, hyh⟩
        have : y = h := Subtype.ext hyh
        rw [← this]
        exact hy
      · intro hh
        exact ⟨h, hh, rfl⟩
    have hPH : P ≤ H := Subgroup.map_subtype_le _
    have hP2 : IsPGroup 2 ↥P := by
      rintro ⟨p, hp⟩
      obtain ⟨y, hy, rfl⟩ := hp
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 N) ⟨_, hy⟩
      have hk' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (y ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      rw [mk_eq_one_iff] at hk'
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hk'⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simpa [pow_add, pow_mul] using this
    have hPN : P ≤ H ⊓ Subgroup.normalizer (R : Set G) := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := hp
      exact ⟨y.2, mem_normalizer_of_mk hRH hQ ((pCoreOf_le 2 N) hy)⟩
    have hnorm : H ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
      intro g hg
      refine mem_normalizer_of_conj_mem fun p hp => ?_
      obtain ⟨y, hy, rfl⟩ := hp
      have hgN : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg.1⟩ ∈ N :=
        mk_mem_normalizer (A := R) hg.2
      refine (hmemP ⟨g * y * g⁻¹, H.mul_mem (H.mul_mem hg.1 y.2) (H.inv_mem hg.1)⟩).mpr ?_
      have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g * y * g⁻¹, H.mul_mem (H.mul_mem hg.1 y.2)
          (H.inv_mem hg.1)⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg.1⟩ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) y * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
              ⟨g, hg.1⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 N hgN) _).mp hy
    have hPR : P ≤ R := by
      rw [hR.2.2]
      exact le_pCoreOf_of_le_normalizer 2 hPN hnorm hP2
    intro z hz
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact mem_modO2Image_iff.mpr ⟨h, hPR ((hmemP h).mpr hz), rfl⟩

theorem mem_normalizer_of_mk_cComp {H L : Subgroup G} (hL : L ∈ cComp H) {x : ↥H}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ∈ Subgroup.normalizer
      ((modO2Image H L : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    (x : G) ∈ Subgroup.normalizer (L : Set G) := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hLx : L.map (MulAut.conj (x : G)).toMonoidHom ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj (x : G)) hL
    have h2 : H.map (MulAut.conj (x : G)).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer x.2)
    rwa [h2] at h1
  have himage : modO2Image H (L.map (MulAut.conj (x : G)).toMonoidHom) = modO2Image H L := by
    ext u
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ u
    constructor
    · intro hu
      obtain ⟨a, ha, hae⟩ := mem_modO2Image_iff.mp hu
      obtain ⟨l, hl, hla⟩ := Subgroup.mem_map.mp ha
      have hla' : (x : G) * l * (x : G)⁻¹ = a := by simpa [MulAut.conj_apply] using hla
      have e : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a = QuotientGroup.mk' (CFSG.pCore 2 ↥H) x *
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨l, hLH hl⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) x)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hla'.symm
      rw [← hae, e]
      exact (Subgroup.mem_normalizer_iff.mp hx _).mp (mem_modO2Image_iff.mpr ⟨_, hl, rfl⟩)
    · intro hu
      have hv := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp hu
      obtain ⟨l, hl, hle⟩ := mem_modO2Image_iff.mp hv
      refine mem_modO2Image_iff.mpr ⟨x * l * x⁻¹, Subgroup.mem_map.mpr ⟨l, hl, by
        simp [MulAut.conj_apply]⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, hle]
      group
  have h3 := modO2Image_injOn H hLx hL himage
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3

theorem a37_modO2 (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y) {H : Subgroup G}
    (hH : IsSQTKIn H) : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H) :=
  hA37 _ (SQTKHyp.of_sqtkGroup ↥H hH)

theorem le_of_le_cComp_of_sqtk (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    {H R L U : Subgroup G} (hH : IsSQTKIn H) (hR : IsTwoRadicalIn H R) (hL : L ∈ cComp H)
    (hUL : U ≤ L) (hU : IsPGroup 2 ↥U)
    (hN : H ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (U : Set G)) : U ≤ R := by
  have hQ : pCoreOf 2 H ≤ R := c2_1_pCore_le hR
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hUH : U ≤ H := hUL.trans hLH
  have hkey := C22Pf.le_of_le_cComp (a37_modO2 hA37 hH) (eq_pCoreOf_normalizer_modO2Image hR)
    (modO2Image_mem_cComp hL) (Subgroup.map_mono (Subgroup.subgroupOf_mono H hUL))
    (isPGroup_modO2Image hU) (by
      rintro x ⟨hxR, hxL⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact mk_mem_normalizer (hN ⟨⟨x.2, mem_normalizer_of_mk hR.1 hQ hxR⟩,
        mem_normalizer_of_mk_cComp hL hxL⟩))
  intro u hu
  exact mem_of_mk_mem hQ (hkey (mem_modO2Image_iff.mpr ⟨⟨u, hUH hu⟩, hu, rfl⟩))

end C22Pf

end CFSG.Quasithin
