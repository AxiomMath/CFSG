module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

private theorem k89j2_barAction_eq_conj_mk {G : Type} [Group G] {L : Subgroup G} {x : G}
    (hxL : x ∈ L) :
    barAction L ⟨x, Subgroup.le_normalizer hxL⟩ =
      MulAut.conj (QuotientGroup.mk ⟨x, hxL⟩) := by
  apply MulEquiv.ext
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [barAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

private theorem k89j2_mem_normalizer_of_conj_le {G : Type} [Group G] {S : Subgroup G} {g : G}
    (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ S) (h2 : ∀ s ∈ S, g⁻¹ * s * g ∈ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact h1 s
  · intro hs
    have h := h2 (g * s * g⁻¹) hs
    simpa [mul_assoc] using h

private theorem k89j2_barAction_conj {G : Type} [Group G]
    {L R K : Subgroup G} (hRLN : R ≤ Subgroup.normalizer (L : Set G))
    (hKN : K ≤ Subgroup.normalizer (R : Set G))
    {x : G} (hxK : x ∈ K) (hxL : x ∈ L) (r : ↥R) :
    barAction L ⟨x, Subgroup.le_normalizer hxL⟩ *
        ((barAction L).comp (Subgroup.inclusion hRLN)) r *
        (barAction L ⟨x, Subgroup.le_normalizer hxL⟩)⁻¹ =
      ((barAction L).comp (Subgroup.inclusion hRLN))
        ⟨x * (r : G) * x⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hKN hxK) (r : G)).mp r.2⟩ := by
  simp only [MonoidHom.comp_apply]
  have hc : Subgroup.inclusion hRLN
      ⟨x * (r : G) * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hKN hxK) (r : G)).mp r.2⟩ =
      (⟨x, Subgroup.le_normalizer hxL⟩ : Subgroup.normalizer (L : Set G)) *
          Subgroup.inclusion hRLN r *
        (⟨x, Subgroup.le_normalizer hxL⟩ : Subgroup.normalizer (L : Set G))⁻¹ := by
    ext
    simp [Subgroup.inclusion, mul_assoc]
  rw [hc, map_mul, map_mul, map_inv]

private theorem k89j2_conj_mem_normalizer_range {G : Type} [Group G]
    {L R K : Subgroup G} (hRLN : R ≤ Subgroup.normalizer (L : Set G))
    (hKN : K ≤ Subgroup.normalizer (R : Set G))
    {x : G} (hxK : x ∈ K) (hxL : x ∈ L) :
    MulAut.conj (QuotientGroup.mk ⟨x, hxL⟩) ∈
      Subgroup.normalizer
        (((barAction L).comp (Subgroup.inclusion hRLN)).range :
          Set (MulAut (Bar2 L))) := by
  have hconj : MulAut.conj (QuotientGroup.mk ⟨x, hxL⟩) =
      barAction L ⟨x, Subgroup.le_normalizer hxL⟩ :=
    (k89j2_barAction_eq_conj_mk hxL).symm
  rw [hconj]
  refine k89j2_mem_normalizer_of_conj_le ?_ ?_
  · intro s hs
    obtain ⟨r, rfl⟩ := hs
    refine ⟨⟨x * (r : G) * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKN hxK) (r : G)).mp r.2⟩, ?_⟩
    exact (k89j2_barAction_conj hRLN hKN hxK hxL r).symm
  · intro s hs
    obtain ⟨r, rfl⟩ := hs
    have hx1K : x⁻¹ ∈ K := K.inv_mem hxK
    have hx1L : x⁻¹ ∈ L := L.inv_mem hxL
    have ha_inv : barAction L ⟨x⁻¹, Subgroup.le_normalizer hx1L⟩ =
        (barAction L ⟨x, Subgroup.le_normalizer hxL⟩)⁻¹ := by
      rw [← map_inv]
      congr 1
    have ha_inv' : barAction L ⟨x, Subgroup.le_normalizer hxL⟩ =
        (barAction L ⟨x⁻¹, Subgroup.le_normalizer hx1L⟩)⁻¹ := by
      rw [ha_inv, inv_inv]
    refine ⟨⟨x⁻¹ * (r : G) * (x⁻¹)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKN hx1K) (r : G)).mp r.2⟩, ?_⟩
    rw [← ha_inv, ha_inv']
    exact (k89j2_barAction_conj hRLN hKN hx1K hx1L r).symm

private theorem k89j2_mem_pCoreOf_commutator_of_barAction_eq_one {G : Type} [Group G]
    {L : Subgroup G} {d k : G} (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hk : k ∈ L)
    (hd : barAction L ⟨d, hdN⟩ = 1) :
    d * k * d⁻¹ * k⁻¹ ∈ pCoreOf 2 L := by
  have hconj : d * k * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hdN k).mp hk
  have hmem : d * k * d⁻¹ * k⁻¹ ∈ L := L.mul_mem hconj (L.inv_mem hk)
  have h1 : (QuotientGroup.mk ⟨d * k * d⁻¹, hconj⟩ : Bar2 L) =
      QuotientGroup.mk ⟨k, hk⟩ := by
    have h := barAction_mk L ⟨d, hdN⟩ ⟨k, hk⟩
    rw [hd] at h
    have h' : ((Subgroup.normalizerMonoidHom L ⟨d, hdN⟩) ⟨k, hk⟩) =
        ⟨d * k * d⁻¹, hconj⟩ := Subtype.ext rfl
    rw [h'] at h
    simpa using h.symm
  have h2 : (QuotientGroup.mk (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥L) : Bar2 L) = 1 := by
    have h3 : (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥L) =
        ⟨d * k * d⁻¹, hconj⟩ * ⟨k, hk⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [h3, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
    simp
  have hmemCore : (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) _).mp h2
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := L)
    ⟨d * k * d⁻¹ * k⁻¹, hmem⟩).mpr hmemCore

theorem s889_j2aut {G : Type} [Group G] [Finite G] (D : Data G)
    (h882 : R882 D) (h885 : R885 D) (hFacts : AllFacts889 D) (hcore : J2AutCore) :
    S889J2Aut D := by
  intro L P ω hω R hRp hRM hKR hO2R r hr l hl
  have hS : Set880 D L P := hω.set880
  have h1 : D.M ≤ Subgroup.normalizer (L : Set G) := r889_normalizes_of_inputs h882 h885 hS
  have hRLN : R ≤ Subgroup.normalizer (L : Set G) := hRM.trans h1
  let ρ : ↥R →* MulAut (Bar2 L) := (barAction L).comp (Subgroup.inclusion hRLN)
  let S : Subgroup (MulAut (Bar2 L)) := ρ.range
  have hS2 : IsPGroup 2 S :=
    hRp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  let Kb : Subgroup (Bar2 L) :=
    (K889 L ω).subgroupOf L |>.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hnorm : ∀ k ∈ Kb, MulAut.conj k ∈ Subgroup.normalizer (S : Set (MulAut (Bar2 L))) := by
    intro kb hkb
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hkb
    have hyK : (y : G) ∈ K889 L ω := Subgroup.mem_subgroupOf.mp hy
    have hyL : (y : G) ∈ L := y.2
    have hxeq : (⟨(y : G), hyL⟩ : ↥L) = y := Subtype.ext rfl
    rw [← hyk, ← hxeq]
    exact k89j2_conj_mem_normalizer_range (L := L) (K := K889 L ω) hRLN hKR hyK hyL
  have hbot : S = ⊥ :=
    hcore (Bar2 L) (h885 L P hS).1 Kb (hFacts L P ω hω).imageAlt6 S hS2 hnorm
  have hρ1 : ρ ⟨r, hr⟩ = 1 := by
    have hmem : ρ ⟨r, hr⟩ ∈ S := MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hbar : barAction L ⟨r, hRLN hr⟩ = 1 := by
    have hmem : barAction L (Subgroup.inclusion hRLN ⟨r, hr⟩) = 1 := hρ1
    simpa [Subgroup.inclusion] using hmem
  exact k89j2_mem_pCoreOf_commutator_of_barAction_eq_one (hRLN hr) hl hbar

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
