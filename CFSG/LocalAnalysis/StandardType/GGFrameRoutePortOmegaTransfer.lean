module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly

open scoped Matrix

theorem Rank3Witness.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {r : ℕ}
    (h : Rank3Witness G r) : Rank3Witness H r := by
  obtain ⟨E, t, hE, hcard, hdisj, hpow, htcent, hEcent⟩ := h
  have hcenter : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
    Subgroup.map_center_eq e
  refine ⟨E.map e.toMonoidHom, e t, hE.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  · calc
      E.map e.toMonoidHom ⊓ Subgroup.center H
          = E.map e.toMonoidHom ⊓ (Subgroup.center G).map e.toMonoidHom := by
              rw [← hcenter]
      _ = (E ⊓ Subgroup.center G).map e.toMonoidHom := by
              rw [Subgroup.map_inf E (Subgroup.center G) e.toMonoidHom e.injective]
      _ = ⊥ := by rw [hdisj, Subgroup.map_bot e.toMonoidHom]
  · obtain ⟨k, hk⟩ := hpow
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · intro ht'
    have htZ : t ∈ Subgroup.center G := by
      have := ht'
      rw [← hcenter] at this
      simpa using (Subgroup.mem_map_equiv.mp this)
    exact htcent htZ
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hycomm : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hEcent hy)
    have hcomm : e (y * t) = e (t * y) := by rw [hycomm]
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hcomm

private theorem omegaTenTransfer_map_mulVec {ι : Type} [Fintype ι] {K L : Type} [Field K] [Field L]
    (σ : K ≃+* L) (A : Matrix ι ι K) (v : ι → K) :
    A.map σ *ᵥ (fun i => σ (v i)) = fun i => σ ((A *ᵥ v) i) := by
  funext i
  exact (RingHom.map_mulVec σ.toRingHom A v i).symm

private theorem omegaTenTransfer_map_largeEvenOrthGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (σ : K ≃+* L) {Q : (ι → K) → K} {Q' : (ι → L) → L}
    (hQ : ∀ v : ι → K, Q' (fun i => σ (v i)) = σ (Q v)) (Φ : GL ι K ≃* GL ι L)
    (hcoe : ∀ g : GL ι K, ((Φ g : GL ι L) : Matrix ι ι L) = (g : Matrix ι ι K).map σ) :
    (LargeEvenOrthGroup Q).map Φ.toMonoidHom = LargeEvenOrthGroup Q' := by
  rw [largeEvenOrthGroup_def, largeEvenOrthGroup_def, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext g
  constructor
  · rintro ⟨g₀, hg₀, rfl⟩
    intro w
    let v : ι → K := fun i => σ.symm (w i)
    have hv : (fun i => σ (v i)) = w := by
      funext i
      exact σ.apply_symm_apply (w i)
    have hstep : ((Φ g₀ : GL ι L) : Matrix ι ι L) *ᵥ w =
        fun i => σ ((((g₀ : GL ι K) : Matrix ι ι K) *ᵥ v) i) := by
      rw [hcoe g₀, ← hv]
      exact omegaTenTransfer_map_mulVec σ ((g₀ : GL ι K) : Matrix ι ι K) v
    calc
      Q' (((Φ g₀ : GL ι L) : Matrix ι ι L) *ᵥ w)
          = Q' (fun i => σ ((((g₀ : GL ι K) : Matrix ι ι K) *ᵥ v) i)) := by rw [hstep]
      _ = σ (Q (((g₀ : GL ι K) : Matrix ι ι K) *ᵥ v)) :=
            hQ (((g₀ : GL ι K) : Matrix ι ι K) *ᵥ v)
      _ = σ (Q v) := by rw [hg₀]
      _ = Q' w := by rw [← hQ v, hv]
  · intro hg
    refine ⟨Φ.symm g, ?_, Φ.apply_symm_apply g⟩
    intro v
    apply σ.injective
    have hmat : ((g : GL ι L) : Matrix ι ι L) =
        (((Φ.symm g : GL ι K)) : Matrix ι ι K).map σ := by
      have h := hcoe (Φ.symm g)
      rwa [Φ.apply_symm_apply] at h
    calc
      σ (Q (((Φ.symm g : GL ι K) : Matrix ι ι K) *ᵥ v))
          = Q' (fun i => σ ((((Φ.symm g : GL ι K) : Matrix ι ι K) *ᵥ v) i)) :=
              (hQ (((Φ.symm g : GL ι K) : Matrix ι ι K) *ᵥ v)).symm
      _ = Q' (((g : GL ι L) : Matrix ι ι L) *ᵥ (fun i => σ (v i))) := by
            congr 1
            rw [hmat]
            exact (omegaTenTransfer_map_mulVec σ ((Φ.symm g : GL ι K) : Matrix ι ι K) v).symm
      _ = Q' (fun i => σ (v i)) := hg _
      _ = σ (Q v) := hQ v

theorem nonempty_mulEquiv_largeEvenOmega_of_ringEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {K L : Type} [Field K] [Field L] (σ : K ≃+* L) {Q : (ι → K) → K} {Q' : (ι → L) → L}
    (hQ : ∀ v : ι → K, Q' (fun i => σ (v i)) = σ (Q v)) :
    Nonempty (↥(LargeEvenOmega Q) ≃* ↥(LargeEvenOmega Q')) := by
  let Φ : GL ι K ≃* GL ι L := Units.mapEquiv (RingEquiv.toMulEquiv σ.mapMatrix)
  have hcoe : ∀ g : GL ι K,
      ((Φ g : GL ι L) : Matrix ι ι L) = (g : Matrix ι ι K).map σ := by
    intro g
    simp [Φ]
  have homega : (LargeEvenOmega Q).map Φ.toMonoidHom = LargeEvenOmega Q' := by
    rw [largeEvenOmega_def, largeEvenOmega_def, Subgroup.map_commutator,
      omegaTenTransfer_map_largeEvenOrthGroup σ hQ Φ hcoe]
  exact ⟨(Subgroup.equivMapOfInjective (LargeEvenOmega Q) Φ.toMonoidHom Φ.injective).trans
    (MulEquiv.subgroupCongr homega)⟩

end CFSG.StandardType.FrameRoute

end
