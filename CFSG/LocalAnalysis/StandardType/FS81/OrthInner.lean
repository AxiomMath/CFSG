module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthCore
public import CFSG.LocalAnalysis.StandardType.FS81.OrthRowCanonAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem mem_torus_of_commute_rot {l : List (V × V)} (hl : IsFrame Q l)
    (hfull : finrank (ZMod 2) V = 2 * l.length) {c : V ≃ₗ[ZMod 2] V}
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ p ∈ l, Commute c (rot Q p.1 p.2)) : c ∈ torus Q l := by
  obtain ⟨t, ht_mem, ht_eq⟩ := centralizer_torus_le_of_commute_rot hl hc hcomm
  have hfin : finrank (ZMod 2) (Wspan l) = finrank (ZMod 2) V := by
    rw [IsFrame.finrank_Wspan hl, hfull]
  have htop : Wspan l = ⊤ := Submodule.eq_top_of_finrank_eq hfin
  have hct : c = t := by
    apply LinearEquiv.ext
    intro y
    exact ht_eq y (by rw [htop]; exact Submodule.mem_top)
  rw [hct]
  exact ht_mem

theorem exists_inner_of_centralizes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (htype : IsPlusType Q ↔ Even n)
    (hind : OmegaAutIsometric Q) {G : Type} [Group G] {K A : Subgroup G}
    (e : ↥K ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hA : IsMaxElemAb3 K A) {c : G} (hcK : c ∈ Subgroup.normalizer (K : Set G))
    (hcA : ∀ a ∈ A, c * a * c⁻¹ = a) :
    ∃ k ∈ K, ∀ y ∈ K, c * y * c⁻¹ = k * y * k⁻¹ := by
  classical
  have hAK : (A.subgroupOf K).map K.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hElemK : IsElemAbelian 3 (A.subgroupOf K) := hA.2.1.subgroupOf K
  have hMaxK : ∀ F : Subgroup ↥K, IsElemAbelian 3 F → A.subgroupOf K ≤ F →
      F = A.subgroupOf K := by
    intro F hF hAF
    have h1 : F.map K.subtype = A := by
      refine hA.2.2 (F.map K.subtype) ?_ (hF.map K.subtype) ?_
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · calc A = (A.subgroupOf K).map K.subtype := hAK.symm
          _ ≤ F.map K.subtype := Subgroup.map_mono hAF
    calc F = (F.map K.subtype).comap K.subtype :=
          (Subgroup.comap_map_eq_self_of_injective K.subtype_injective F).symm
      _ = A.comap K.subtype := by rw [h1]
      _ = A.subgroupOf K := rfl
  set Ω : Subgroup (V ≃ₗ[ZMod 2] V) :=
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ with hΩ
  let E : Subgroup ↥Ω := (A.subgroupOf K).map e.toMonoidHom
  let E' : Subgroup (V ≃ₗ[ZMod 2] V) := E.map Ω.subtype
  have hE'elem : IsElemAbelian 3 E' := (hElemK.map e.toMonoidHom).map Ω.subtype
  have hE'Ω : E' ≤ Ω := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE'max : ∀ E'' : Subgroup (V ≃ₗ[ZMod 2] V), E'' ≤ Ω → IsElemAbelian 3 E'' → E' ≤ E'' →
      E'' = E' := by
    intro E'' hE''le hE''elem hE'E''
    have hFelem : IsElemAbelian 3 ((E''.comap Ω.subtype).comap e.toMonoidHom) :=
      (hE''elem.comap Ω.subtype_injective).comap e.injective
    have hAF : A.subgroupOf K ≤ (E''.comap Ω.subtype).comap e.toMonoidHom := fun x hx =>
      hE'E'' (Subgroup.mem_map_of_mem Ω.subtype (Subgroup.mem_map_of_mem e.toMonoidHom hx))
    have hF := hMaxK _ hFelem hAF
    refine le_antisymm (fun y hy => ?_) hE'E''
    have hyΩ : y ∈ Ω := hE''le hy
    have hxF : e.symm ⟨y, hyΩ⟩ ∈ (E''.comap Ω.subtype).comap e.toMonoidHom := by
      show Ω.subtype (e.toMonoidHom (e.symm ⟨y, hyΩ⟩)) ∈ E''
      simpa using hy
    rw [hF] at hxF
    exact ⟨⟨y, hyΩ⟩, ⟨e.symm ⟨y, hyΩ⟩, hxF, by simp⟩, rfl⟩
  obtain ⟨l, hl, hlen, hEtorus⟩ :=
    fs81_orth_maxElemAb3_eq_torus hQ hdim htype hE'Ω hE'elem hE'max
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨c, hcK⟩
  have hα₀_val : ∀ x : ↥K, ((α₀ x : ↥K) : G) = c * (x : G) * c⁻¹ := by
    intro x
    simpa [α₀] using Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨c, hcK⟩ x
  let α : MulAut ↥Ω := e.symm.trans (α₀.trans e)
  have hα_apply : ∀ x : ↥K, α (e x) = e (α₀ x) := by
    intro x
    simp [α]
  obtain ⟨h, hhO, hhα⟩ := hind α
  have hfix : ∀ x : ↥K, (x : G) ∈ A →
      h * ((e x : ↥Ω) : V ≃ₗ[ZMod 2] V) * h⁻¹ = ((e x : ↥Ω) : V ≃ₗ[ZMod 2] V) := by
    intro x hx
    have hα₀fix : α₀ x = x := by
      apply Subtype.ext
      rw [hα₀_val, hcA (x : G) hx]
    calc h * ((e x : ↥Ω) : V ≃ₗ[ZMod 2] V) * h⁻¹
        = ((α (e x) : ↥Ω) : V ≃ₗ[ZMod 2] V) := (hhα _).symm
      _ = ((e (α₀ x) : ↥Ω) : V ≃ₗ[ZMod 2] V) := by rw [hα_apply]
      _ = ((e x : ↥Ω) : V ≃ₗ[ZMod 2] V) := by rw [hα₀fix]
  have hfull : finrank (ZMod 2) V = 2 * l.length := by rw [hlen, hdim]
  have hcomm : ∀ p ∈ l, Commute h (rot Q p.1 p.2) := by
    intro p hp
    have hxE' : rot Q p.1 p.2 ∈ E' := by
      rw [hEtorus]
      exact rot_mem_torus hp
    obtain ⟨y, hyE, hyx⟩ := Subgroup.mem_map.mp hxE'
    obtain ⟨z, hzE, hzy⟩ := Subgroup.mem_map.mp hyE
    have hzA : (z : G) ∈ A := Subgroup.mem_subgroupOf.mp hzE
    have hfixz := hfix z hzA
    have hxz : rot Q p.1 p.2 = ((e z : ↥Ω) : V ≃ₗ[ZMod 2] V) := by
      rw [← hyx, ← hzy]
      rfl
    rw [hxz]
    exact mul_inv_eq_iff_eq_mul.mp hfixz
  have htorus : h ∈ torus Q l := mem_torus_of_commute_rot hl hfull hhO hcomm
  have hhΩ : h ∈ Ω := torus_le_commutator hl htorus
  let k : ↥K := e.symm ⟨h, hhΩ⟩
  have hkK : (k : G) ∈ K := k.2
  refine ⟨k, hkK, ?_⟩
  intro y hy
  let x : ↥K := ⟨y, hy⟩
  have hv : ((α₀ x : ↥K) : G) = c * y * c⁻¹ := by
    rw [hα₀_val]
  have hEqK : k * x * k⁻¹ = α₀ x := by
    apply e.injective
    have hek : e k = ⟨h, hhΩ⟩ := by simp [k]
    rw [map_mul, map_mul, map_inv, hek, ← hα_apply x]
    apply Subtype.ext
    show h * ((e x : ↥Ω) : V ≃ₗ[ZMod 2] V) * h⁻¹ =
      ((α (e x) : ↥Ω) : V ≃ₗ[ZMod 2] V)
    exact (hhα (e x)).symm
  rw [← hv, ← hEqK]
  simp [Subgroup.coe_mul, Subgroup.coe_inv, x]

end CFSG.StandardType.FrameRoute.FS81
