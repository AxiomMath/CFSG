module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapSec
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_secAut_eq_one_iff_mem (U₂ U₁ : Subgroup W)
    (g : ↥(secStabAll U₂ U₁)) :
    secAut U₂ U₁ g = 1 ↔ ∀ u : ↥U₂, (g : MulAut W) u * (u : W)⁻¹ ∈ U₁ := by
  constructor
  · intro h u
    have h1 : secAut U₂ U₁ g (QuotientGroup.mk u) = QuotientGroup.mk u := by rw [h]; rfl
    rw [secAut_mk] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem).mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [resAut, div_eq_mul_inv] using h2
  · intro h
    refine MulEquiv.ext fun v => ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    rw [MulAut.one_apply, secAut_mk]
    exact (QuotientGroup.eq_iff_div_mem).mpr
      (Subgroup.mem_subgroupOf.mpr (by simpa [resAut, div_eq_mul_inv] using h u))

@[expose] noncomputable def w16f_secImgHom (K : Subgroup (MulAut W)) (U U₀ : Subgroup W)
    (hKs : K ≤ secStabAll U U₀) : ↥K →* ↥(secImg K U U₀) where
  toFun a := ⟨secAut U U₀ ⟨a.1, hKs a.2⟩, mem_secImg.mpr ⟨⟨a.1, hKs a.2⟩, a.2, rfl⟩⟩
  map_one' := Subtype.ext (by
    show secAut U U₀ ⟨(1 : MulAut W), hKs (one_mem K)⟩ = 1
    rw [show (⟨(1 : MulAut W), hKs (one_mem K)⟩ : ↥(secStabAll U U₀)) = 1 from rfl,
      map_one])
  map_mul' a b := Subtype.ext (by
    show secAut U U₀ ⟨(a * b).1, hKs (a * b).2⟩ =
      secAut U U₀ ⟨a.1, hKs a.2⟩ * secAut U U₀ ⟨b.1, hKs b.2⟩
    rw [show (⟨(a * b).1, hKs (a * b).2⟩ : ↥(secStabAll U U₀)) =
        (⟨a.1, hKs a.2⟩ * ⟨b.1, hKs b.2⟩ : ↥(secStabAll U U₀)) from rfl, map_mul])

theorem w16f_secImgHom_surjective (K : Subgroup (MulAut W)) (U U₀ : Subgroup W)
    (hKs : K ≤ secStabAll U U₀) : Function.Surjective (w16f_secImgHom K U U₀ hKs) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hgK, hgφ⟩ := mem_secImg.mp hφ
  refine ⟨⟨g.1, hgK⟩, Subtype.ext ?_⟩
  show secAut U U₀ ⟨g.1, hKs hgK⟩ = φ
  rw [show (⟨g.1, hKs hgK⟩ : ↥(secStabAll U U₀)) = g from Subtype.ext rfl, hgφ]

theorem w16f_secImgHom_injective (K : Subgroup (MulAut W)) (U U₀ R : Subgroup W)
    (hKs : K ≤ secStabAll U U₀) (hRst : StableUnder K R) (hRU : R ≤ U)
    (hinf : R ⊓ U₀ = ⊥) (hKf : K ⊓ centSub R = ⊥) :
    Function.Injective (w16f_secImgHom K U U₀ hKs) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hsec : secAut U U₀ ⟨a.1, hKs a.2⟩ = 1 := congrArg Subtype.val ha
  have hmem : ∀ u : ↥U, a.1 (u : W) * (u : W)⁻¹ ∈ U₀ :=
    (w16f_secAut_eq_one_iff_mem U U₀ ⟨a.1, hKs a.2⟩).mp hsec
  have hcent : a.1 ∈ centSub R := by
    rw [mem_centSub]
    intro r hr
    have h1 : a.1 r * r⁻¹ ∈ U₀ := by simpa using hmem ⟨r, hRU hr⟩
    have h2 : a.1 r * r⁻¹ ∈ R := R.mul_mem (hRst a.1 a.2 r hr) (R.inv_mem hr)
    have h3 : a.1 r * r⁻¹ ∈ R ⊓ U₀ := ⟨h2, h1⟩
    rw [hinf] at h3
    exact mul_inv_eq_one.mp (by simpa using h3)
  have hbot : a.1 ∈ K ⊓ centSub R := ⟨a.2, hcent⟩
  rw [hKf] at hbot
  exact Subtype.ext (by simpa using hbot)

@[expose] noncomputable def w16f_secImgEquiv (K : Subgroup (MulAut W)) (U U₀ R : Subgroup W)
    (hKs : K ≤ secStabAll U U₀) (hRst : StableUnder K R) (hRU : R ≤ U)
    (hinf : R ⊓ U₀ = ⊥) (hKf : K ⊓ centSub R = ⊥) : ↥K ≃* ↥(secImg K U U₀) :=
  MulEquiv.ofBijective (w16f_secImgHom K U U₀ hKs)
    ⟨w16f_secImgHom_injective K U U₀ R hKs hRst hRU hinf hKf,
      w16f_secImgHom_surjective K U U₀ hKs⟩

@[expose] noncomputable def w16f_secTEquivHom (R U U₀ : Subgroup W) (hRU : R ≤ U) :
    ↥R →* SecT U U₀ :=
  (QuotientGroup.mk' (U₀.subgroupOf U)).comp (Subgroup.inclusion hRU)

theorem w16f_secTEquivHom_injective (R U U₀ : Subgroup W) (hRU : R ≤ U)
    (hinf : R ⊓ U₀ = ⊥) : Function.Injective (w16f_secTEquivHom R U U₀ hRU) := by
  intro r s hrs
  have h1 : (QuotientGroup.mk (⟨r.1, hRU r.2⟩ : ↥U) : SecT U U₀) =
      QuotientGroup.mk (⟨s.1, hRU s.2⟩ : ↥U) := hrs
  have h2 := (QuotientGroup.eq_iff_div_mem).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  have h3 : r.1 * s.1⁻¹ ∈ R := R.mul_mem r.2 (R.inv_mem s.2)
  have h4 : r.1 * s.1⁻¹ ∈ R ⊓ U₀ := ⟨h3, by simpa [div_eq_mul_inv] using h2⟩
  rw [hinf] at h4
  exact Subtype.ext (mul_inv_eq_one.mp (by simpa using h4))

theorem w16f_secTEquivHom_surjective (R U U₀ : Subgroup W) (hRU : R ≤ U)
    (hsup : R ⊔ U₀ = U) : Function.Surjective (w16f_secTEquivHom R U U₀ hRU) := by
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  have hu : (u : W) ∈ R ⊔ U₀ := by rw [hsup]; exact u.2
  obtain ⟨r, hr, z, hz, hrz⟩ := Subgroup.mem_sup.mp hu
  refine ⟨⟨r, hr⟩, ?_⟩
  change QuotientGroup.mk (⟨r, hRU hr⟩ : ↥U) = QuotientGroup.mk u
  rw [QuotientGroup.eq_iff_div_mem]
  change (r : W) / (u : W) ∈ U₀
  have hz' : (r : W) / (u : W) = z⁻¹ := by
    rw [div_eq_mul_inv, ← hrz, mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hz']
  exact U₀.inv_mem hz

@[expose] noncomputable def w16f_secTEquiv (R U U₀ : Subgroup W) (hRU : R ≤ U)
    (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U) : ↥R ≃* SecT U U₀ :=
  MulEquiv.ofBijective (w16f_secTEquivHom R U U₀ hRU)
    ⟨w16f_secTEquivHom_injective R U U₀ hRU hinf,
      w16f_secTEquivHom_surjective R U U₀ hRU hsup⟩

theorem w16f_secTEquiv_apply (R U U₀ : Subgroup W) (hRU : R ≤ U)
    (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U) (r : ↥R) :
    w16f_secTEquiv R U U₀ hRU hinf hsup r =
      QuotientGroup.mk (⟨r.1, hRU r.2⟩ : ↥U) := rfl

theorem w16f_secTEquiv_secAut (R U U₀ : Subgroup W) (hRU : R ≤ U)
    (hinf : R ⊓ U₀ = ⊥) (hsup : R ⊔ U₀ = U) {a : MulAut W}
    (ha : a ∈ secStabAll U U₀) (haR : ∀ r ∈ R, a r ∈ R) (r : ↥R) :
    w16f_secTEquiv R U U₀ hRU hinf hsup ⟨a r.1, haR r.1 r.2⟩ =
      secAut U U₀ ⟨a, ha⟩ (w16f_secTEquiv R U U₀ hRU hinf hsup r) := by
  rw [w16f_secTEquiv_apply, w16f_secTEquiv_apply, secAut_mk]
  rfl

end CFSG.LocalAnalysis.WeakClosure81
