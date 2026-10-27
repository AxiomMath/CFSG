module

public import CFSG.Quasithin.Vol2.E2NineTI2bDefs
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

namespace TI2b

variable {G G' : Type} [Group G] [Group G']

theorem pCoreOf_map_of_injective {f : G →* G'} (hf : Function.Injective f) (Y : Subgroup G) :
    pCoreOf 2 (Y.map f) = (pCoreOf 2 Y).map f := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Y.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem solvRad_map_of_injective {f : G →* G'} (hf : Function.Injective f) (Y : Subgroup G) :
    (CFSG.solvableRadical ↥(Y.map f)).map (Y.map f).subtype =
      ((CFSG.solvableRadical ↥Y).map Y.subtype).map f := by
  rw [← E1.solvableRadical_map_mulEquiv (Y.equivMapOfInjective f hf), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem dich_map_of_injective {f : G →* G'} (hf : Function.Injective f) {R Y : Subgroup G} :
    Dich (R.map f) (Y.map f) ↔ Dich R Y := by
  unfold Dich
  rw [pCoreOf_map_of_injective hf, solvRad_map_of_injective hf,
    ← Subgroup.map_inf _ _ _ hf]
  constructor
  · rintro (h | h)
    · exact Or.inl ((Subgroup.map_le_map_iff_of_injective hf).mp h)
    · exact Or.inr ((Subgroup.map_eq_bot_iff_of_injective _ hf).mp h)
  · rintro (h | h)
    · exact Or.inl (Subgroup.map_mono h)
    · exact Or.inr (by rw [h, Subgroup.map_bot])

theorem dich_conj {x : G} {R Y : Subgroup G} : Dich (conjSub x R) (conjSub x Y) ↔ Dich R Y :=
  dich_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective

theorem dich_of_embedding {f : G →* G'} (hf : Function.Injective f) {R' Y' : Subgroup G}
    {R Y : Subgroup G'} (hR : R'.map f = R) (hY : Y'.map f = Y) (h : Dich R' Y') : Dich R Y := by
  rw [← hR, ← hY]
  exact (dich_map_of_injective hf).mpr h

theorem starDich_of_swap {K Ts R₀ : Subgroup G} (hKn : K.Normal) (hR₀K : R₀ ≤ K) {t : G}
    (ht : t ∈ Ts) (𝓡 : Set (Subgroup G))
    (hcov : ∀ x : G, conjSub x R₀ ≤ Ts → conjSub x R₀ ∈ 𝓡 ∨ conjSub t (conjSub x R₀) ∈ 𝓡)
    (hD : ∀ R ∈ 𝓡, R ≤ Ts → R ≤ K → ∀ Y : Subgroup G, Y ≤ K →
      Ts ⊓ K ⊓ Subgroup.centralizer (R : Set G) ≤ Y → Dich R Y) :
    StarDich K Ts R₀ := by
  intro x hxT Y hYK hCY
  have hRK : conjSub x R₀ ≤ K := fun a ha => by
    have h1 := hR₀K (mem_conjSub.mp ha)
    have h2 := hKn.conj_mem _ h1 x
    simpa [mul_assoc] using h2
  rcases hcov x hxT with hR | hR
  · exact hD _ hR hxT hRK Y hYK hCY
  ·
    set R := conjSub x R₀ with hRdef
    have hTt : ∀ a ∈ Ts, t * a * t⁻¹ ∈ Ts := fun a ha =>
      Ts.mul_mem (Ts.mul_mem ht ha) (Ts.inv_mem ht)
    have hTt' : ∀ a ∈ Ts, t⁻¹ * a * t ∈ Ts := fun a ha =>
      Ts.mul_mem (Ts.mul_mem (Ts.inv_mem ht) ha) ht
    have hKt : ∀ a ∈ K, t * a * t⁻¹ ∈ K := fun a ha => hKn.conj_mem a ha t
    have hKt' : ∀ a ∈ K, t⁻¹ * a * t ∈ K := fun a ha => by
      simpa using hKn.conj_mem a ha t⁻¹
    have hR'T : conjSub t R ≤ Ts := fun a ha => by
      have h1 := hxT (mem_conjSub.mp ha)
      simpa [mul_assoc] using hTt _ h1
    have hR'K : conjSub t R ≤ K := fun a ha => by
      have h1 := hRK (mem_conjSub.mp ha)
      simpa [mul_assoc] using hKt _ h1
    have hY'K : conjSub t Y ≤ K := fun a ha => by
      have h1 := hYK (mem_conjSub.mp ha)
      simpa [mul_assoc] using hKt _ h1
    have hC' : Ts ⊓ K ⊓ Subgroup.centralizer (conjSub t R : Set G) ≤ conjSub t Y := by
      intro z hz
      obtain ⟨⟨hzT, hzK⟩, hzC⟩ := hz
      rw [mem_conjSub]
      refine hCY ⟨⟨hTt' z hzT, hKt' z hzK⟩, ?_⟩
      show t⁻¹ * z * t ∈ Subgroup.centralizer (R : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : t * h * t⁻¹ ∈ conjSub t R := by
        rw [mem_conjSub]
        simpa [mul_assoc] using hh
      have h2 := (Subgroup.mem_centralizer_iff.mp hzC) _ hh'
      have h3 := congrArg (fun w => t⁻¹ * w * t) h2
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] at h3 ⊢
      simpa [mul_assoc] using h3
    have hd := hD _ hR hR'T hR'K (conjSub t Y) hY'K hC'
    have key : ∀ X : Subgroup G, conjSub t⁻¹ (conjSub t X) = X := fun X => by
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    have := dich_conj (x := t⁻¹) (R := conjSub t R) (Y := conjSub t Y)
    rw [key, key] at this
    exact this.mpr hd

end TI2b

end E2

end CFSG.Quasithin
