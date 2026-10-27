module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts15b
public import CFSG.Quasithin.Vol2.KGNatSp4N13

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.Open (pCoreOf)

namespace KA

theorem mem_pCoreOf_iff' {G : Type*} [Group G] (X : Subgroup G) (x : ↥X) :
    (x : G) ∈ pCoreOf 2 X ↔ x ∈ CFSG.pCore 2 ↥X := by
  exact Subgroup.mem_map_iff_mem X.subtype_injective

variable {W : Type*} [CommGroup W]

theorem mapsTo_of_conj {H : Subgroup (MulAut W)} {Z U : Subgroup W}
    (hfix : Ch11.SecA.RadicalFixes H Z U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z) {ρ : MulAut W}
    (hρZ : ∀ z ∈ Z, ρ z ∈ Z)
    (hρR : ∀ r ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U)),
      ρ⁻¹ * r * ρ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U))) :
    ∀ u ∈ U, ρ u ∈ U := by
  intro u hu
  refine hfix _ fun x hx => ?_
  obtain ⟨x', -, hx'⟩ := hρR _ ((mem_pCoreOf_iff' _ x).mpr hx)
  have h2 := hpt _ x'.2 u hu
  have hx'' : (x' : MulAut W) = ρ⁻¹ * x * ρ := hx'
  rw [hx''] at h2
  have h3 := hρZ _ h2
  simpa only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self] using h3

theorem mem_stabW_of_conj [Finite W] {H : Subgroup (MulAut W)} {Z U : Subgroup W}
    (hfix : Ch11.SecA.RadicalFixes H Z U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z) {τ : MulAut W}
    (hτZ : τ ∈ Ch11.SecA.stabW Z)
    (hτR : ∀ r ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U)),
      τ * r * τ⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U))) :
    τ ∈ Ch11.SecA.stabW U := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hτR' := inv_conj_mem_of_conj_mem hτR
  have h1 := mapsTo_of_conj hfix hpt (fun z hz => (Ch11.SecA.mem_stabW.mp hτZ z).mp hz) hτR'
  have h2 := mapsTo_of_conj hfix hpt
    (fun z hz => (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW Z).inv_mem hτZ) z).mp hz)
    (by simpa only [inv_inv] using hτR)
  refine Ch11.SecA.mem_stabW.mpr fun w => ⟨h1 w, fun hw => ?_⟩
  have := h2 _ hw
  rwa [MulAut.inv_apply_self] at this

variable {K : Type} [Field K] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem eq_of_forall_f_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {a b : MulAut W}
    (ha : a ∈ H) (hb : b ∈ H) (h : ∀ w, f (a w) = f (b w)) : a = b := by
  obtain ⟨α, hα⟩ : ∃ α : ↥(StatedSp 2 K), π α = ⟨a, ha⟩ := hf.onto ⟨a, ha⟩
  obtain ⟨β, hβ⟩ : ∃ β : ↥(StatedSp 2 K), π β = ⟨b, hb⟩ := hf.onto ⟨b, hb⟩
  have hαβ : α = β := by
    apply mat_injective
    refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← hf.act4, ← hf.act4, hα, hβ]
    exact h w
  have h1 := congrArg Subtype.val hα
  have h2 := congrArg Subtype.val hβ
  rw [hαβ] at h1
  exact h1.symm.trans h2

@[expose] noncomputable def gconjMap (g : StatedSp 2 K)
    (T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)) :
    (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K) :=
  ((Matrix.mulVecLin (mat 2 K g⁻¹)).toAddMonoidHom.comp T).comp
    (Matrix.mulVecLin (mat 2 K g)).toAddMonoidHom

theorem gconjMap_apply (g : StatedSp 2 K) (T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (x : Fin 2 ⊕ Fin 2 → K) : gconjMap g T x = mat 2 K g⁻¹ *ᵥ T (mat 2 K g *ᵥ x) := rfl

theorem gconjMap_iterate (g : StatedSp 2 K) (T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (m : ℕ) (x : Fin 2 ⊕ Fin 2 → K) :
    (⇑(gconjMap g T))^[m] x = mat 2 K g⁻¹ *ᵥ (⇑T)^[m] (mat 2 K g *ᵥ x) := by
  induction m generalizing x with
  | zero => rw [Function.iterate_zero, id, Function.iterate_zero, id, mat_inv_mulVec]
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, gconjMap_apply,
      mat_mulVec_inv]

end KA

end CFSG.Quasithin.Vol2.KGNat
