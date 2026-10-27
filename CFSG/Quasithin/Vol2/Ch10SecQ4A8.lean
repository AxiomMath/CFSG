module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A7
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G Y : Type} [Group G] [Group Y] {L : Subgroup G} (f : ↥L →* Y)
  (hkQ : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockQ L)
include hkQ

theorem mem_pCore_range_iff (x : ↥L) :
    f.rangeRestrict x ∈ CFSG.pCore 2 ↥f.range ↔ x ∈ CFSG.pCore 2 ↥L := by
  constructor
  · intro hx
    have h1 := mem_blockQ_of_mem_pCore hx
    rw [MonoidHom.coe_rangeRestrict, blockQ_range f hkQ, mem_imgL] at h1
    obtain ⟨x', hx'Q, hx'⟩ := h1
    have h2 : f (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
    have h3 := (blockQ L).mul_mem hx'Q (hkQ _ h2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h3
    exact mem_pCore_of_mem_blockQ h3
  · intro hx
    refine mem_pCore_of_mem_blockQ ?_
    rw [MonoidHom.coe_rangeRestrict, blockQ_range f hkQ, mem_imgL]
    exact ⟨x, mem_blockQ_of_mem_pCore hx, rfl⟩

@[expose] noncomputable def quotHom : ↥L →* ↥f.range ⧸ CFSG.pCore 2 ↥f.range :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥f.range)).comp f.rangeRestrict

omit hkQ in
theorem quotHom_surjective : Function.Surjective (quotHom f) :=
  (QuotientGroup.mk'_surjective _).comp f.rangeRestrict_surjective

theorem ker_quotHom : (quotHom f).ker = CFSG.pCore 2 ↥L := by
  ext x
  rw [MonoidHom.mem_ker, quotHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact mem_pCore_range_iff f hkQ x

@[expose] noncomputable def quotEquivRange :
    ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥f.range ⧸ CFSG.pCore 2 ↥f.range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_quotHom f hkQ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (quotHom_surjective f))

variable [Finite G] (hkU : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockU L → (x : G) = 1)
include hkU

omit hkQ [Finite G] in
theorem eq_of_mem_blockU {x x' : ↥L} (hx : (x : G) ∈ blockU L) (hx' : (x' : G) ∈ blockU L)
    (h : f x = f x') : x = x' := by
  have h1 : f (x'⁻¹ * x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := hkU _ h1 (by simpa using (blockU L).mul_mem ((blockU L).inv_mem hx') hx)
  have h3 : x'⁻¹ * x = 1 := Subtype.ext (by simpa using h2)
  exact (inv_mul_eq_one.mp h3).symm

theorem isShort2_range_irr (hL : IsShort2 L) :
    blockZ f.range < blockU f.range ∧
      ∀ W : Subgroup Y, blockZ f.range ≤ W → W ≤ blockU f.range →
        f.range ≤ Subgroup.normalizer (W : Set Y) → W = blockZ f.range ∨ W = blockU f.range := by
  rw [blockU_range f hkQ, blockZ_range f hkQ hkU]
  have hZU : imgL f (blockZ L) ≤ imgL f (blockU L) := fun y hy => by
    obtain ⟨x, hxZ, rfl⟩ := (mem_imgL f).mp hy
    exact (mem_imgL f).mpr ⟨x, hxZ.1, rfl⟩
  have hUL : blockU L ≤ L := hL.2.2.1.1.trans (inf_le_left.trans
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
  refine ⟨lt_of_le_of_ne hZU fun heq => ?_, fun W hZW hWU hWn => ?_⟩
  · refine hL.2.2.2.2.1.ne (le_antisymm inf_le_left fun u hu => ?_)
    have h1 : f ⟨u, hUL hu⟩ ∈ imgL f (blockZ L) := heq ▸ (mem_imgL f).mpr ⟨_, hu, rfl⟩
    obtain ⟨z, hzZ, hz⟩ := (mem_imgL f).mp h1
    have := congrArg Subtype.val (eq_of_mem_blockU f hkU hzZ.1 hu hz)
    simp only at this
    rw [← this]
    exact hzZ
  · set W₀ : Subgroup G := (W.comap f).map L.subtype ⊓ blockU L with hW₀
    have hmemW₀ : ∀ x : ↥L, (x : G) ∈ blockU L → f x ∈ W → (x : G) ∈ W₀ :=
      fun x hxU hxW => ⟨⟨x, hxW, rfl⟩, hxU⟩
    have hW₀mem : ∀ x : ↥L, (x : G) ∈ W₀ → f x ∈ W := by
      rintro x ⟨⟨x', hx'W, hx'x⟩, -⟩
      rw [Subtype.ext hx'x] at hx'W
      exact hx'W
    have hZW₀ : blockZ L ≤ W₀ := fun z hz =>
      hmemW₀ ⟨z, hUL hz.1⟩ hz.1 (hZW ((mem_imgL f).mpr ⟨_, hz, rfl⟩))
    have hW₀n : L ≤ Subgroup.normalizer (W₀ : Set G) := by
      intro l hl
      have hUn := le_normalizer_blockU L hl
      have hfl : f ⟨l, hl⟩ ∈ f.range := ⟨_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have hgL : g ∈ L := hUL hg.2
        have hgU := (Subgroup.mem_normalizer_iff.mp hUn g).mp hg.2
        refine hmemW₀ (⟨l, hl⟩ * ⟨g, hgL⟩ * ⟨l, hl⟩⁻¹) hgU ?_
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp (hWn hfl) _).mp (hW₀mem ⟨g, hgL⟩ hg)
      · intro hg
        have hgU : g ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hUn g).mpr hg.2
        have hgL : g ∈ L := hUL hgU
        refine hmemW₀ ⟨g, hgL⟩ hgU ?_
        have h1 := hW₀mem (⟨l, hl⟩ * ⟨g, hgL⟩ * ⟨l, hl⟩⁻¹) hg
        rw [map_mul, map_mul, map_inv] at h1
        exact (Subgroup.mem_normalizer_iff.mp (hWn hfl) _).mpr h1
    have hWimg : W = imgL f W₀ := by
      apply le_antisymm
      · intro w hw
        obtain ⟨x, hxU, rfl⟩ := (mem_imgL f).mp (hWU hw)
        exact (mem_imgL f).mpr ⟨x, hmemW₀ x hxU hw, rfl⟩
      · intro y hy
        obtain ⟨x, hxW, rfl⟩ := (mem_imgL f).mp hy
        exact hW₀mem x hxW
    rcases hL.2.2.2.2.2 W₀ hZW₀ inf_le_right hW₀n with h | h
    · exact Or.inl (by rw [hWimg, h])
    · exact Or.inr (by rw [hWimg, h])

theorem isShort2_range (hL : IsShort2 L) (h5 : IsAltType L 5) : IsShort2 f.range := by
  have hQ := blockQ_range f hkQ
  have hU := blockU_range f hkQ
  have hZ := blockZ_range f hkQ hkU
  have hUQ : blockU L ≤ blockQ L := hL.2.2.1.1.trans inf_le_left
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro N _ hN
    have hNc : (N.comap f.rangeRestrict).Normal := Subgroup.Normal.comap inferInstance _
    let ψ : ↥L →* ↥f.range ⧸ N := (QuotientGroup.mk' N).comp f.rangeRestrict
    have hψ : Function.Surjective ψ :=
      (QuotientGroup.mk'_surjective _).comp f.rangeRestrict_surjective
    have hψk : ψ.ker = N.comap f.rangeRestrict := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_comap]
    let e : ↥L ⧸ N.comap f.rangeRestrict ≃* ↥f.range ⧸ N :=
      (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    have h1 := hL.1 (N.comap f.rangeRestrict) (hN.of_equiv e.symm)
    rw [← Subgroup.map_comap_eq_self_of_surjective f.rangeRestrict_surjective N, h1,
      Subgroup.map_top, MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective]
  ·
    rintro y ⟨⟨x, rfl⟩, hyc⟩
    have hxU : (x : G) ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have huL : u ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L (hUQ hu)
      have hfu : f ⟨u, huL⟩ ∈ blockQ f.range := hQ ▸ (mem_imgL f).mpr ⟨_, hUQ hu, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hyc _ hfu
      have h1 : f (⟨u, huL⟩ * x * ⟨u, huL⟩⁻¹ * x⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
        group
      have hUn : L ≤ Subgroup.normalizer (blockU L : Set G) := le_normalizer_blockU L
      have h2 : u * ((x : G) * u⁻¹ * (x : G)⁻¹) ∈ blockU L :=
        (blockU L).mul_mem hu ((Subgroup.mem_normalizer_iff.mp (hUn x.2) _).mp
          ((blockU L).inv_mem hu))
      have h3 := hkU _ h1 (by simpa [mul_assoc] using h2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      have := congrArg (· * ((x : G) * u)) h3
      simp only [one_mul] at this
      rw [← this]
      group
    show f x ∈ blockQ f.range
    rw [hQ]
    exact (mem_imgL f).mpr ⟨x, inf_centralizer_blockU_le hL h5 hxU, rfl⟩
  ·
    rw [hU, hQ]
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨x, hxU, rfl⟩ := (mem_imgL f).mp hy
      refine ⟨(mem_imgL f).mpr ⟨x, hUQ hxU, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro z hz
      obtain ⟨x', hx'Q, rfl⟩ := (mem_imgL f).mp hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hL.2.2.1.1 hxU).2 _ hx'Q)
    · obtain ⟨x, hxU, rfl⟩ := (mem_imgL f).mp hy
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hL.2.2.1.2 _ hxU)
      rw [this, map_one]
  ·
    let e := quotEquivRange f hkQ
    rcases hL.2.2.2.1 with h | h
    · exact Or.inl ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp h)
    · exact Or.inr (by rw [← Nat.card_congr e.toEquiv]; exact h)
  · exact isShort2_range_irr f hkQ hkU hL

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
