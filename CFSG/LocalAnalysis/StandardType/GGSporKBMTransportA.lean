module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportCore
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

variable {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']

private theorem gkA_map_map_symm_self {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X : Subgroup G) : Subgroup.map e.symm.toMonoidHom (Subgroup.map e.toMonoidHom X) = X := by
  rw [Subgroup.map_map]
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  rw [hcomp, Subgroup.map_id]

private theorem gkA_map_centralizer_eq {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (S : Set G) :
    Subgroup.map e.toMonoidHom (Subgroup.centralizer S) =
      Subgroup.centralizer (e '' S) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image S e.toMonoidHom) ?_
  intro y hy
  rw [Subgroup.mem_map]
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  apply e.injective
  rw [map_mul, map_mul, e.apply_symm_apply]
  exact hy (e s) ⟨s, hs, rfl⟩

private theorem gkA_map_centralizer_subgroup {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (Q : Subgroup G) :
    Subgroup.map e.toMonoidHom (Subgroup.centralizer (Q : Set G)) =
      Subgroup.centralizer (Subgroup.map e.toMonoidHom Q : Set G') := by
  rw [gkA_map_centralizer_eq]
  simp only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom]

private noncomputable def gkA_centralizerEquiv (e : K ≃* K') (x : K) :
    ↥(Subgroup.centralizer ({x} : Set K)) ≃* ↥(Subgroup.centralizer ({e x} : Set K')) :=
  (Subgroup.equivMapOfInjective (Subgroup.centralizer ({x} : Set K)) e.toMonoidHom
      (fun _ _ h => e.injective h)).trans
    (MulEquiv.subgroupCongr
      (CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x))

private theorem gkA_centralizerEquiv_coe (e : K ≃* K') (x : K)
    (z : ↥(Subgroup.centralizer ({x} : Set K))) :
    ((gkA_centralizerEquiv e x z : ↥(Subgroup.centralizer ({e x} : Set K'))) : K') = e z.1 := by
  show ((MulEquiv.subgroupCongr
      (CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x))
        ((Subgroup.equivMapOfInjective (Subgroup.centralizer ({x} : Set K)) e.toMonoidHom
          (fun _ _ h => e.injective h)) z) : K') = e z.1
  rw [MulEquiv.subgroupCongr_apply]
  exact Subgroup.coe_equivMapOfInjective_apply _ _ _ z

private theorem gkA_subgroupOf_map_centralizerEquiv (e : K ≃* K') (x : K) {J : Subgroup K}
    (hJ : J ≤ Subgroup.centralizer ({x} : Set K)) :
    Subgroup.map (gkA_centralizerEquiv e x).toMonoidHom
        (J.subgroupOf (Subgroup.centralizer ({x} : Set K))) =
      (Subgroup.map e.toMonoidHom J).subgroupOf
        (Subgroup.centralizer ({e x} : Set K')) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact ⟨y.1, hy, (gkA_centralizerEquiv_coe e x y).symm⟩
  · intro hz
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hz
    obtain ⟨g, hg, hgz⟩ := hz
    have hgX : g ∈ Subgroup.centralizer ({x} : Set K) := hJ hg
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hgX⟩, hg, ?_⟩
    apply Subtype.ext
    change ((gkA_centralizerEquiv e x ⟨g, hgX⟩ :
      ↥(Subgroup.centralizer ({e x} : Set K'))) : K') = (z : K')
    rw [gkA_centralizerEquiv_coe]
    simpa using hgz

private theorem gkA_isComponentOf_map_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {J X : Subgroup G} (h : IsComponentOf J X) :
    IsComponentOf (Subgroup.map e.toMonoidHom J) (Subgroup.map e.toMonoidHom X) :=
  CFSG.Assembly.isComponentOf_iff_open.mpr
    (CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e
      (CFSG.Assembly.isComponentOf_iff_open.mp h))

private theorem gkA_isComponentOf_of_map_mulEquiv {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {J X : Subgroup G}
    (h : IsComponentOf (Subgroup.map e.toMonoidHom J) (Subgroup.map e.toMonoidHom X)) :
    IsComponentOf J X := by
  have h' := gkA_isComponentOf_map_mulEquiv e.symm h
  rwa [gkA_map_map_symm_self e J, gkA_map_map_symm_self e X] at h'

private theorem gkA_largeEvenPComponent_map_centralizer_iff (p : ℕ) (e : K ≃* K') (x : K)
    (C : Subgroup K) :
    LargeEvenPComponent p (Subgroup.centralizer ({e x} : Set K')) (Subgroup.map e C) ↔
      LargeEvenPComponent p (Subgroup.centralizer ({x} : Set K)) C := by
  rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x]
  exact largeEvenPComponent_map_mulEquiv p e (Subgroup.centralizer ({x} : Set K)) C

private theorem gkA_not_largeEvenPComponent_centralizer_of_map (p : ℕ) (e : K ≃* K') (x : K)
    (h : ∀ C' : Subgroup K', ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({e x} : Set K')) C') :
    ∀ C : Subgroup K, ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({x} : Set K)) C := by
  intro C hC
  exact h (Subgroup.map e C) ((gkA_largeEvenPComponent_map_centralizer_iff p e x C).mpr hC)

theorem bmOpCent_map_mulEquiv (p : ℕ) (e : K ≃* K') (x : K) :
    BMOpCent p (e x) = (BMOpCent p x).map e.toMonoidHom := by
  have hcoe : ∀ z : ↥(Subgroup.centralizer ({x} : Set K)),
      ((gkA_centralizerEquiv e x z :
        ↥(Subgroup.centralizer ({e x} : Set K'))) : K') = e z.1 :=
    gkA_centralizerEquiv_coe e x
  have hcomp : MonoidHom.comp (Subgroup.centralizer ({e x} : Set K')).subtype
        (gkA_centralizerEquiv e x).toMonoidHom =
      MonoidHom.comp e.toMonoidHom (Subgroup.centralizer ({x} : Set K)).subtype := by
    ext z
    exact hcoe z
  have hpc : CFSG.pCore p ↥(Subgroup.centralizer ({e x} : Set K')) =
      Subgroup.map (gkA_centralizerEquiv e x).toMonoidHom
        (CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K))) :=
    (CFSG.pCore_map_iso p (gkA_centralizerEquiv e x)).symm
  unfold BMOpCent
  calc Subgroup.map (Subgroup.centralizer ({e x} : Set K')).subtype
        (CFSG.pCore p ↥(Subgroup.centralizer ({e x} : Set K')))
      = Subgroup.map (Subgroup.centralizer ({e x} : Set K')).subtype
          (Subgroup.map (gkA_centralizerEquiv e x).toMonoidHom
            (CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K)))) := by rw [hpc]
    _ = Subgroup.map (MonoidHom.comp (Subgroup.centralizer ({e x} : Set K')).subtype
            (gkA_centralizerEquiv e x).toMonoidHom)
          (CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K))) := by
        rw [Subgroup.map_map]
    _ = Subgroup.map (MonoidHom.comp e.toMonoidHom
            (Subgroup.centralizer ({x} : Set K)).subtype)
          (CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K))) := by rw [hcomp]
    _ = Subgroup.map e.toMonoidHom
          (Subgroup.map (Subgroup.centralizer ({x} : Set K)).subtype
            (CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K)))) := by
        rw [Subgroup.map_map]

theorem bmPPrimeCore_of_mulEquiv (p : ℕ) (e : K ≃* K') (h : BMPPrimeCore p K) :
    BMPPrimeCore p K' := by
  intro x' hx' hno'
  let x : K := e.symm x'
  have hxe : e x = x' := e.apply_symm_apply x'
  have hx : orderOf x = p := by rw [← MulEquiv.orderOf_eq e x, hxe, hx']
  have hno'' : ∀ C' : Subgroup K', ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({e x} : Set K')) C' := by rwa [hxe]
  have hno : ∀ C : Subgroup K, ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({x} : Set K)) C :=
    gkA_not_largeEvenPComponent_centralizer_of_map p e x hno''
  rw [← hxe]
  rw [largeEvenPPrimeCore_map_mulEquiv p (gkA_centralizerEquiv e x), h x hx hno, Subgroup.map_bot]

theorem bmCentreZ_of_mulEquiv (p : ℕ) (e : K ≃* K') (h : BMCentreZ p K) : BMCentreZ p K' := by
  intro x' hx' hno' A' hA' hnorm' hEA'
  let x : K := e.symm x'
  have hxe : e x = x' := e.apply_symm_apply x'
  have hx : orderOf x = p := by rw [← MulEquiv.orderOf_eq e x, hxe, hx']
  have hno'' : ∀ C' : Subgroup K', ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({e x} : Set K')) C' := by rwa [hxe]
  have hno : ∀ C : Subgroup K, ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({x} : Set K)) C :=
    gkA_not_largeEvenPComponent_centralizer_of_map p e x hno''
  have hA'ey : A' ≤ Subgroup.centralizer ({e x} : Set K') := by rwa [hxe]
  have hnorm'ey : ∀ g ∈ Subgroup.centralizer ({e x} : Set K'),
      ∀ a ∈ A', g * a * g⁻¹ ∈ A' := by rwa [hxe]
  let A : Subgroup K := Subgroup.comap e.toMonoidHom A'
  have hAmap : Subgroup.map e.toMonoidHom A = A' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective A'
  have hA : A ≤ Subgroup.centralizer ({x} : Set K) := by
    have h1 : Subgroup.map e.toMonoidHom A ≤ Subgroup.centralizer ({e x} : Set K') := by
      rw [hAmap]
      exact hA'ey
    have h2 : A ≤ Subgroup.comap e.toMonoidHom
        (Subgroup.centralizer ({e x} : Set K')) :=
      (Subgroup.map_le_iff_le_comap (f := e.toMonoidHom)).mp h1
    rwa [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x,
      Subgroup.comap_map_eq_self_of_injective e.injective] at h2
  have hnorm : ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    have hg' : e g ∈ Subgroup.centralizer ({e x} : Set K') := by
      rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have ha' : e a ∈ A' := ha
    have hstep := hnorm'ey (e g) hg' (e a) ha'
    change e (g * a * g⁻¹) ∈ A'
    simpa [map_mul] using hstep
  have hEA : IsElemAbelian p A := CFSG.Open.IsElemAbelian.comap hEA' e.injective
  have hle := h x hx hno A hA hnorm hEA
  have hmap := Subgroup.map_mono (f := e.toMonoidHom) hle
  rw [hAmap, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hxe] at hmap
  exact hmap

theorem bmPCentralF1_of_mulEquiv (p : ℕ) (e : K ≃* K') (h : BMPCentralF1 p K) :
    BMPCentralF1 p K' := by
  intro x' hx' hno'
  let x : K := e.symm x'
  have hxe : e x = x' := e.apply_symm_apply x'
  have hx : orderOf x = p := by rw [← MulEquiv.orderOf_eq e x, hxe, hx']
  have hno'' : ∀ C' : Subgroup K', ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({e x} : Set K')) C' := by rwa [hxe]
  have hno : ∀ C : Subgroup K, ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({x} : Set K)) C :=
    gkA_not_largeEvenPComponent_centralizer_of_map p e x hno''
  obtain ⟨hxQ, hcomm, hcen, hle⟩ := h x hx hno
  have hQ : BMOpCent p x' = Subgroup.map e.toMonoidHom (BMOpCent p x) := by
    have := bmOpCent_map_mulEquiv p e x
    rwa [hxe] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQ, ← hxe]
    exact Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩
  · rw [hQ, ← Subgroup.map_commutator (BMOpCent p x) (BMOpCent p x) e.toMonoidHom,
      hcomm, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hxe]
  · rw [hQ, ← gkA_map_centralizer_subgroup e (BMOpCent p x),
      ← Subgroup.map_inf (BMOpCent p x) (Subgroup.centralizer (BMOpCent p x : Set K))
        e.toMonoidHom e.injective, hcen, MonoidHom.map_zpowers,
      MulEquiv.coe_toMonoidHom, hxe]
  · have hmono := Subgroup.map_mono (f := e.toMonoidHom) hle
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x,
      gkA_map_centralizer_subgroup e (BMOpCent p x), ← hQ, hxe] at hmono
    exact hmono

theorem bmPCentralF4_of_mulEquiv (p : ℕ) (e : K ≃* K') (h : BMPCentralF4 p K) :
    BMPCentralF4 p K' := by
  intro x' hx' hno' N' hN'le hN'normal hN'zp hN'Q
  let x : K := e.symm x'
  have hxe : e x = x' := e.apply_symm_apply x'
  have hx : orderOf x = p := by rw [← MulEquiv.orderOf_eq e x, hxe, hx']
  have hno'' : ∀ C' : Subgroup K', ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({e x} : Set K')) C' := by rwa [hxe]
  have hno : ∀ C : Subgroup K, ¬ LargeEvenPComponent p
      (Subgroup.centralizer ({x} : Set K)) C :=
    gkA_not_largeEvenPComponent_centralizer_of_map p e x hno''
  have hN'leey : N' ≤ Subgroup.centralizer ({e x} : Set K') := by rwa [hxe]
  let N : Subgroup K := Subgroup.comap e.toMonoidHom N'
  have hNmap : Subgroup.map e.toMonoidHom N = N' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N'
  have hNle : N ≤ Subgroup.centralizer ({x} : Set K) := by
    have h1 : Subgroup.map e.toMonoidHom N ≤ Subgroup.centralizer ({e x} : Set K') := by
      rw [hNmap]
      exact hN'leey
    have h2 : N ≤ Subgroup.comap e.toMonoidHom
        (Subgroup.centralizer ({e x} : Set K')) :=
      (Subgroup.map_le_iff_le_comap (f := e.toMonoidHom)).mp h1
    rwa [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x,
      Subgroup.comap_map_eq_self_of_injective e.injective] at h2
  have hNnormal : ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have hg' : e g ∈ Subgroup.centralizer ({x'} : Set K') := by
      rw [← hxe, ← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hn' : e n ∈ N' := hn
    have hstep := hN'normal (e g) hg' (e n) hn'
    change e (g * n * g⁻¹) ∈ N'
    simpa [map_mul] using hstep
  have hNzp : Subgroup.zpowers x ≤ N := by
    intro z hz
    have hz' : e z ∈ Subgroup.zpowers x' := by
      have h1 : e z ∈ Subgroup.zpowers (e.toMonoidHom x) := by
        rw [← MonoidHom.map_zpowers e.toMonoidHom x]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      rwa [MulEquiv.coe_toMonoidHom, hxe] at h1
    have hz'N : e z ∈ N' := hN'zp hz'
    have : e z ∈ Subgroup.map e.toMonoidHom N := by
      rw [hNmap]
      exact hz'N
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp this
  have hQ : BMOpCent p x' = Subgroup.map e.toMonoidHom (BMOpCent p x) := by
    have := bmOpCent_map_mulEquiv p e x
    rwa [hxe] at this
  have hNQ : N ≤ BMOpCent p x := by
    have h1 : Subgroup.map e.toMonoidHom N ≤
        Subgroup.map e.toMonoidHom (BMOpCent p x) := by
      rw [hNmap, ← hQ]
      exact hN'Q
    have h2 : N ≤ Subgroup.comap e.toMonoidHom
        (Subgroup.map e.toMonoidHom (BMOpCent p x)) :=
      (Subgroup.map_le_iff_le_comap (f := e.toMonoidHom)).mp h1
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h2
  rcases h x hx hno N hNle hNnormal hNzp hNQ with hNz | hNQ'
  · left
    rw [← hNmap, hNz, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hxe]
  · right
    rw [← hNmap, hNQ']
    exact hQ.symm

theorem bSevenComp_of_mulEquiv (e : K ≃* K') (h : BSevenComp K) : BSevenComp K' := by
  intro x' hx'
  let x : K := e.symm x'
  have hxe : e x = x' := e.apply_symm_apply x'
  have hx : orderOf x = 7 := by rw [← MulEquiv.orderOf_eq e x, hxe, hx']
  obtain ⟨J, hJ, hJuniv, hJcard, hJcore⟩ := h x hx
  have hX : Subgroup.map e.toMonoidHom (Subgroup.centralizer ({x} : Set K)) =
      Subgroup.centralizer ({e x} : Set K') :=
    CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x
  refine ⟨Subgroup.map e.toMonoidHom J, ?_, ?_, ?_, ?_⟩
  · have hJmap : IsComponentOf (Subgroup.map e.toMonoidHom J)
        (Subgroup.centralizer ({e x} : Set K')) := by
      have := gkA_isComponentOf_map_mulEquiv e hJ
      rwa [hX] at this
    rwa [← hxe]
  · intro J'' hJ''
    let J₁ : Subgroup K := Subgroup.comap e.toMonoidHom J''
    have hJ₁map : Subgroup.map e.toMonoidHom J₁ = J'' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective J''
    have hJ₁ : IsComponentOf J₁ (Subgroup.centralizer ({x} : Set K)) := by
      apply gkA_isComponentOf_of_map_mulEquiv e
      rw [hJ₁map, hX, hxe]
      exact hJ''
    calc J'' = Subgroup.map e.toMonoidHom J₁ := hJ₁map.symm
      _ = Subgroup.map e.toMonoidHom J := by rw [hJuniv J₁ hJ₁]
  · have hmapinf : Subgroup.map e.toMonoidHom
        (J ⊓ Subgroup.centralizer (J : Set K)) =
        Subgroup.map e.toMonoidHom J ⊓
          Subgroup.centralizer (Subgroup.map e.toMonoidHom J : Set K') := by
      rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, gkA_map_centralizer_subgroup e J]
    rw [← hmapinf, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hJcard]
  · have hJleX : J ⊓ Subgroup.centralizer (J : Set K) ≤
        Subgroup.centralizer ({x} : Set K) := le_trans inf_le_left hJ.1
    have hpc := largeEvenPPrimeCore_map_mulEquiv 7 (gkA_centralizerEquiv e x)
    rw [← hxe, hpc, hJcore, gkA_subgroupOf_map_centralizerEquiv e x hJleX]
    rw [← gkA_map_centralizer_subgroup e J,
      ← Subgroup.map_inf J (Subgroup.centralizer (J : Set K)) e.toMonoidHom e.injective]

theorem bSevenCentAbelian_of_mulEquiv (e : K ≃* K') (h : BSevenCentAbelian K) :
    BSevenCentAbelian K' := by
  intro E' hE' hcard' a' ha' b' hb'
  let E : Subgroup K := Subgroup.comap e.toMonoidHom E'
  have hEmap : Subgroup.map e.toMonoidHom E = E' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E'
  have hE : IsElemAbelian 7 E := CFSG.Open.IsElemAbelian.comap hE' e.injective
  have hcard : Nat.card E = 49 := by
    have h1 : Nat.card E = Nat.card E' := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hEmap]
    rw [h1, hcard']
  have haE : e.symm a' ∈ Subgroup.centralizer (E : Set K) := by
    have h1 : a' ∈ Subgroup.map e.toMonoidHom (Subgroup.centralizer (E : Set K)) := by
      rw [gkA_map_centralizer_subgroup e E, hEmap]
      exact ha'
    rw [Subgroup.mem_map_equiv] at h1
    exact h1
  have hbE : e.symm b' ∈ Subgroup.centralizer (E : Set K) := by
    have h1 : b' ∈ Subgroup.map e.toMonoidHom (Subgroup.centralizer (E : Set K)) := by
      rw [gkA_map_centralizer_subgroup e E, hEmap]
      exact hb'
    rw [Subgroup.mem_map_equiv] at h1
    exact h1
  have hh := h E hE hcard (e.symm a') haE (e.symm b') hbE
  have := congrArg e.toMonoidHom hh
  simpa only [map_mul, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using this

theorem bSevenSpread_of_mulEquiv (e : K ≃* K') (h : BSevenSpread K) : BSevenSpread K' := by
  intro E' hE' hcard' hex
  let E : Subgroup K := Subgroup.comap e.toMonoidHom E'
  have hEmap : Subgroup.map e.toMonoidHom E = E' :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective E'
  have hE : IsElemAbelian 7 E := CFSG.Open.IsElemAbelian.comap hE' e.injective
  have hcard : Nat.card E = 49 := by
    have h1 : Nat.card E = Nat.card E' := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hEmap]
    rw [h1, hcard']
  obtain ⟨t', ht'ne, ht'⟩ := hex
  let t : K := e.symm t'
  have htne : t ≠ 1 := by
    intro ht1
    apply ht'ne
    have h1 : e.symm t' = 1 := ht1
    rw [← e.apply_symm_apply t', h1, map_one]
  apply h E hE hcard
  refine ⟨t, htne, ?_⟩
  intro y hy hyne J hJ
  have hJmap : IsComponentOf (Subgroup.map e.toMonoidHom J)
      (Subgroup.centralizer ({e y} : Set K')) := by
    have := gkA_isComponentOf_map_mulEquiv e hJ
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e y] at this
  have heyE : e y ∈ E' := by
    rw [← hEmap]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have heyne : e y ≠ 1 := by
    intro h1
    exact hyne (e.injective (by rw [h1, map_one]))
  have ht'mem := ht' (e y) heyE heyne (Subgroup.map e.toMonoidHom J) hJmap
  have hJmapinf : Subgroup.map e.toMonoidHom (J ⊓ Subgroup.centralizer (J : Set K)) =
      Subgroup.map e.toMonoidHom J ⊓
        Subgroup.centralizer (Subgroup.map e.toMonoidHom J : Set K') := by
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, gkA_map_centralizer_subgroup e J]
  have ht'mem' : t' ∈ Subgroup.map e.toMonoidHom
      (J ⊓ Subgroup.centralizer (J : Set K)) := by
    rw [hJmapinf]
    exact ht'mem
  exact (Subgroup.mem_map_equiv (f := e)
    (K := J ⊓ Subgroup.centralizer (J : Set K))).mp ht'mem'

end CFSG.StandardType.SporadicShape
