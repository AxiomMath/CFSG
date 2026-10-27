module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley

section Defs

@[expose] noncomputable def ggIotaK
    (t : StatedLieTag) (n f : ℕ) (hf : 1 ≤ f) :
    (ggU t n f).K →* ModGL (langTag t) GGL :=
  (ggIota t n f hf).comp (QuotientGroup.mk' (Subgroup.center (ggU t n f).K))

@[expose] noncomputable def ggFixGp (t : StatedLieTag) (f : ℕ) :
    Subgroup (ModGL (langTag t) GGL) :=
  adjointGroup (langTag t) GGL ⊓ (ggPhi t f).eqLocus (MonoidHom.id _)

private theorem ggRatEmb_pow_f_aux {f : ℕ} (hf : 1 ≤ f) (c : GaloisField 2 f) :
    c ^ 2 ^ f = c := by
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite (GaloisField 2 f)
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (Nat.pos_iff_ne_zero.mp hf)
  calc c ^ 2 ^ f = c ^ Fintype.card (GaloisField 2 f) := by
        rw [← hcard, Nat.card_eq_fintype_card]
    _ = c := FiniteField.pow_card c

theorem ggFixGp_eq_fix
    {t : StatedLieTag} {f : ℕ} (D : LangDatum (langTag t) GGL)
    (hΦ : D.Φ = ggPhi t f) : D.fix = ggFixGp t f := by
  rw [LangDatum.fix, hΦ, ggFixGp]

theorem ggRatEmb_range {f : ℕ} (hf : 1 ≤ f) :
    Set.range (ggRatEmb f) = {c : GGL | c ^ 2 ^ f = c} := by
  classical
  let K := GaloisField 2 f
  letI : Algebra K GGL := (ggRatEmb f).toAlgebra
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    change (ggRatEmb f a) ^ 2 ^ f = ggRatEmb f a
    rw [← map_pow, ggRatEmb_pow_f_aux hf a]
  · intro hc
    have hcard : Nat.card K = 2 ^ f :=
      GaloisField.card 2 f (Nat.pos_iff_ne_zero.mp hf)
    have hc' : c ^ Nat.card K = c := by rw [hcard]; exact hc
    obtain ⟨a, ha⟩ :=
      CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K) (L := GGL) hc'
    exact ⟨a, by simpa only [RingHom.algebraMap_toAlgebra] using ha⟩

theorem ggRank_untw
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (n f : ℕ) :
    (ggU t n f).D.rank = (langTag t).rank := by
  rcases ht with rfl | rfl | rfl | rfl <;> rfl

theorem ggPhi_pinnedX_untw
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) (f : ℕ) {γ : Fin (langTag t).rank → ℤ}
    (hγ : IsRoot (langTag t) γ) (c : GGL) :
    ggPhi t f (pinnedX (langTag t) GGL γ c) = pinnedX (langTag t) GGL γ (c ^ 2 ^ f) := by
  rcases ht with rfl | rfl | rfl | rfl
  · change Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.F4 GGL γ c) =
      pinnedX Tag.F4 GGL γ (c ^ 2 ^ f)
    rw [show Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.F4 GGL γ c) =
        pinnedX Tag.F4 GGL γ (ggFrobT f c) from
      Units.ext (entrywise_pinnedX (ggFrobT f) γ c), ggFrobT_apply]
  · change Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E6 GGL γ c) =
      pinnedX Tag.E6 GGL γ (c ^ 2 ^ f)
    rw [show Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E6 GGL γ c) =
        pinnedX Tag.E6 GGL γ (ggFrobT f c) from
      Units.ext (entrywise_pinnedX (ggFrobT f) γ c), ggFrobT_apply]
  · change Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E7 GGL γ c) =
      pinnedX Tag.E7 GGL γ (c ^ 2 ^ f)
    rw [show Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E7 GGL γ c) =
        pinnedX Tag.E7 GGL γ (ggFrobT f c) from
      Units.ext (entrywise_pinnedX (ggFrobT f) γ c), ggFrobT_apply]
  · change Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E8 GGL γ c) =
      pinnedX Tag.E8 GGL γ (c ^ 2 ^ f)
    rw [show Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E8 GGL γ c) =
        pinnedX Tag.E8 GGL γ (ggFrobT f c) from
      Units.ext (entrywise_pinnedX (ggFrobT f) γ c), ggFrobT_apply]

theorem ggPhi_pinnedX_twistedE6
    (f : ℕ) {γ : Fin (langTag .twistedE6).rank → ℤ}
    (hγ : IsRoot (langTag .twistedE6) γ) (c : GGL) :
    ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL γ c) =
      pinnedX (langTag .twistedE6) GGL (permLattice (TwistTag.perm .E6) γ) (c ^ 2 ^ f) := by
  haveI : CharP GGL 2 := inferInstance
  have h2 : (2 : GGL) = 0 := by exact_mod_cast CharP.cast_eq_zero GGL 2
  have h := CFSG.LieType.Chevalley.E6GraphRadical.twistHom_pinnedX_of_two
    (E := GGL) h2 (ggFrobT f) hγ c
  rw [ggFrobT_apply] at h
  exact h

theorem ggFixGp_inf_rootSubgroup_untw
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) {f : ℕ} (hf : 1 ≤ f)
    {γ : Fin (langTag t).rank → ℤ} (hγ : IsRoot (langTag t) γ) :
    ((ggFixGp t f ⊓ CFSG.Blueprint.Chevalley.rootSubgroup (langTag t) GGL γ :
        Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) =
      Set.range (fun c : GaloisField 2 f => pinnedX (langTag t) GGL γ (ggRatEmb f c)) := by
  classical
  ext y
  constructor
  · intro hy
    rw [ggFixGp] at hy
    obtain ⟨hyFix, hyRoot⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨-, hyEq⟩ := Subgroup.mem_inf.1 hyFix
    have hyPhi : ggPhi t f y = y := MonoidHom.mem_eqLocusM.1 hyEq
    obtain ⟨d, hd⟩ := mem_rootSubgroup.1 hyRoot
    have hp : pinnedX (langTag t) GGL γ (d ^ 2 ^ f) = pinnedX (langTag t) GGL γ d := by
      rw [← ggPhi_pinnedX_untw ht f hγ d, hd, hyPhi, ← hd]
    have hd' : d ^ 2 ^ f = d := pinnedX_injective (τ := langTag t) (R := GGL) γ hp
    have hdmem : d ∈ Set.range (ggRatEmb f) := by
      rw [ggRatEmb_range hf]
      exact hd'
    obtain ⟨c, hc⟩ := hdmem
    refine ⟨c, ?_⟩
    change pinnedX (langTag t) GGL γ (ggRatEmb f c) = y
    rw [hc, hd]
  · rintro ⟨c, rfl⟩
    rw [ggFixGp]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨pinnedX_mem_adjointGroup γ _, ?_⟩,
      mem_rootSubgroup.2 ⟨ggRatEmb f c, rfl⟩⟩
    refine MonoidHom.mem_eqLocusM.2 ?_
    rw [ggPhi_pinnedX_untw ht f hγ, ← map_pow (ggRatEmb f) c (2 ^ f),
      ggRatEmb_pow_f_aux hf c]
    rfl

end Defs

end CFSG.StandardType.GGFinModel
