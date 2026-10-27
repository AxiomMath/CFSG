module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTr
import CFSG.LocalAnalysis.StandardType.GGExcKGSFCore
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

namespace GGSFTr

variable {t : StatedLieTag} {n f p : ℕ} {M : GGKGModel t n f p} {G : Type} [Group G]
  {ψ : (ggU t n f).K →* G} {Bs : Subgroup G} (T : GGSFTr t n f p M ψ Bs)

@[expose] noncomputable def fwd (L : Subgroup G) : Subgroup (GGAutU t n f) :=
  (L.subgroupOf T.N).map T.hom

theorem mem_fwd_iff {L : Subgroup G} (x : T.N) : T.hom x ∈ T.fwd L ↔ (x : G) ∈ L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain rfl : y = x := T.hom_inj hyx
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem fwd_map_psi (X : Subgroup (ggU t n f).K) :
    T.fwd (X.map ψ) = (X.map (ggPsiU t n f)).map (MulAut.conj T.kappa).toMonoidHom := by
  ext a
  constructor
  · rintro ⟨x, ⟨k, hk, hkx⟩, rfl⟩
    have hxe : x = ⟨ψ k, T.psi_le ⟨k, rfl⟩⟩ := Subtype.ext hkx.symm
    refine ⟨ggPsiU t n f k, ⟨k, hk, rfl⟩, ?_⟩
    rw [hxe, T.hom_psi]
    simp [MulAut.conj_apply]
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨ψ k, T.psi_le ⟨k, rfl⟩⟩, ⟨k, hk, rfl⟩, ?_⟩
    rw [T.hom_psi]
    simp [MulAut.conj_apply]

theorem fwd_psi_range : T.fwd ψ.range = (ggPsiU t n f).range := by
  have hN : ((ggPsiU t n f).range).Normal := GGSFCore.normal_range_ggPsiU t n f
  have h := T.fwd_map_psi (⊤ : Subgroup (ggU t n f).K)
  rw [← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map] at h
  rw [h]
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hN.conj_mem x hx T.kappa
  · intro ha
    refine ⟨T.kappa⁻¹ * a * T.kappa, ?_, ?_⟩
    · simpa using hN.conj_mem a ha T.kappa⁻¹
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem exists_fwd_eq {Lb : Subgroup (GGAutU t n f)} (h : Lb ≤ (ggPsiU t n f).range) :
    ∃ L : Subgroup G, L ≤ ψ.range ∧ T.fwd L = Lb := by
  refine ⟨(Lb.comap T.hom).map T.N.subtype, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : T.hom x ∈ T.fwd ψ.range := T.fwd_psi_range ▸ h hx
    exact (T.mem_fwd_iff x).1 hx'
  · ext a
    constructor
    · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
      obtain rfl : y = x := Subtype.ext hyx
      exact hy
    · intro ha
      have ha' : a ∈ T.fwd ψ.range := T.fwd_psi_range ▸ h ha
      obtain ⟨x, -, rfl⟩ := ha'
      exact ⟨x, ⟨x, ha, rfl⟩, rfl⟩

theorem mem_centralizer_fwd_iff {L : Subgroup G} (hL : L ≤ T.N) (x : T.N) :
    (x : G) ∈ Subgroup.centralizer (L : Set G) ↔
      T.hom x ∈ Subgroup.centralizer (T.fwd L : Set (GGAutU t n f)) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hc _ ⟨y, hy, rfl⟩
    have h1 : (y : G) * (x : G) = (x : G) * (y : G) := hc _ hy
    have h2 : y * x = x * y := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  · intro hc g hg
    have hgN : g ∈ T.N := hL hg
    have h1 := hc (T.hom ⟨g, hgN⟩) ⟨⟨g, hgN⟩, hg, rfl⟩
    have h2 : (⟨g, hgN⟩ : T.N) * x = x * ⟨g, hgN⟩ :=
      T.hom_inj (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2

theorem mem_normalizer_fwd_iff {L : Subgroup G} (hL : L ≤ T.N) (x : T.N) :
    (x : G) ∈ Subgroup.normalizer (L : Set G) ↔
      T.hom x ∈ Subgroup.normalizer (T.fwd L : Set (GGAutU t n f)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn a
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : (x : G) * (y : G) * (x : G)⁻¹ ∈ L := (hn _).1 hy
      exact ⟨x * y * x⁻¹, h1, by simp [map_mul, map_inv]⟩
    · rintro ⟨z, hz, hza⟩
      have hz2 : (x : G)⁻¹ * (z : G) * (x : G) ∈ L := by
        refine (hn _).2 ?_
        have : (x : G) * ((x : G)⁻¹ * (z : G) * (x : G)) * (x : G)⁻¹ = z := by group
        rwa [this]
      refine ⟨x⁻¹ * z * x, hz2, ?_⟩
      have : T.hom (x⁻¹ * z * x) = (T.hom x)⁻¹ * T.hom z * T.hom x := by
        simp [map_mul, map_inv]
      rw [this]
      have hza' : T.hom z = T.hom x * a * (T.hom x)⁻¹ := hza
      rw [hza']
      group
  · intro hn g
    constructor
    · intro hg
      have hgN : g ∈ T.N := hL hg
      have h1 := (hn (T.hom ⟨g, hgN⟩)).1 ((T.mem_fwd_iff ⟨g, hgN⟩).2 hg)
      have h2 : T.hom (x * ⟨g, hgN⟩ * x⁻¹) ∈ T.fwd L := by
        simpa [map_mul, map_inv] using h1
      exact (T.mem_fwd_iff _).1 h2
    · intro hg
      have hgN : g ∈ T.N := by
        have h1 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ T.N :=
          T.N.mul_mem (T.N.mul_mem (T.N.inv_mem x.2) (hL hg)) x.2
        simpa [mul_assoc] using h1
      have h2 : T.hom (x * ⟨g, hgN⟩ * x⁻¹) ∈ T.fwd L := (T.mem_fwd_iff _).2 hg
      have h3 : T.hom x * T.hom ⟨g, hgN⟩ * (T.hom x)⁻¹ ∈ T.fwd L := by
        simpa [map_mul, map_inv] using h2
      exact (T.mem_fwd_iff _).1 ((hn _).2 h3)

theorem fwd_inf_centralizer {U : Subgroup G} (hU : U ≤ T.N) :
    T.fwd (ψ.range ⊓ Subgroup.centralizer (U : Set G)) =
      (ggPsiU t n f).range ⊓ Subgroup.centralizer (T.fwd U : Set (GGAutU t n f)) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨T.fwd_psi_range ▸ (T.mem_fwd_iff x).2 hx.1, (T.mem_centralizer_fwd_iff hU x).1 hx.2⟩
  · rintro ⟨ha1, ha2⟩
    have ha' : a ∈ T.fwd ψ.range := T.fwd_psi_range ▸ ha1
    obtain ⟨x, hxψ, rfl⟩ := ha'
    exact ⟨x, ⟨hxψ, (T.mem_centralizer_fwd_iff hU x).2 ha2⟩, rfl⟩

theorem fwd_inf_centralizer_singleton (x : T.N) :
    T.fwd (ψ.range ⊓ Subgroup.centralizer {(x : G)}) =
      (ggPsiU t n f).range ⊓ Subgroup.centralizer {T.hom x} := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨T.fwd_psi_range ▸ (T.mem_fwd_iff y).2 hy.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h1 : (x : G) * (y : G) = (y : G) * (x : G) := Subgroup.mem_centralizer_iff.1 hy.2 _ rfl
    have h2 : x * y = y * x := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  · rintro ⟨ha1, ha2⟩
    have ha' : a ∈ T.fwd ψ.range := T.fwd_psi_range ▸ ha1
    obtain ⟨y, hyψ, rfl⟩ := ha'
    refine ⟨y, ⟨hyψ, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h1 : T.hom x * T.hom y = T.hom y * T.hom x := Subgroup.mem_centralizer_iff.1 ha2 _ rfl
    have h2 : x * y = y * x := T.hom_inj (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2

theorem isComponentOf_fwd_iff {L H : Subgroup G} (hL : L ≤ T.N) (hH : H ≤ T.N) :
    IsComponentOf (T.fwd L) (T.fwd H) ↔ IsComponentOf L H := by
  have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := T.hom) T.hom_inj
    (Q := L.subgroupOf T.N) (K := H.subgroupOf T.N)
  have h2 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (f := T.N.subtype)
    T.N.subtype_injective (Q := L.subgroupOf T.N) (K := H.subgroupOf T.N)
  rw [Subgroup.map_subgroupOf_eq_of_le hL, Subgroup.map_subgroupOf_eq_of_le hH] at h2
  exact h1.trans h2.symm

theorem lieModel_of_fwd {L : Subgroup G} (hL : L ≤ T.N) {k : ℕ}
    (h : LieModel (↥(T.fwd L) ⧸ Subgroup.center ↥(T.fwd L)) .PSL k 2 (2 * f)) :
    LieModel (↥L ⧸ Subgroup.center ↥L) .PSL k 2 (2 * f) := by
  let e1 : ↥L ≃* ↥(L.subgroupOf T.N) := (Subgroup.subgroupOfEquivOfLe hL).symm
  let e2 : ↥(L.subgroupOf T.N) ≃* ↥(T.fwd L) :=
    Subgroup.equivMapOfInjective _ T.hom T.hom_inj
  let e : ↥L ≃* ↥(T.fwd L) := e1.trans e2
  have hc : (Subgroup.center ↥L).map e.toMonoidHom = Subgroup.center ↥(T.fwd L) :=
    Subgroup.map_center_eq e
  exact LieModel.of_mulEquiv (QuotientGroup.congr _ _ e hc).symm h

end GGSFTr

end Universal

end CFSG.StandardType
