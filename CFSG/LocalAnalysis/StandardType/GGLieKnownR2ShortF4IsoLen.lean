module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
open scoped commutatorElement

private def isoLen_f4Highest : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private def f4LongOrbit : Finset (Fin (Tag.rank .F4) → ℤ) :=
  [![2, 3, 4, 2], ![1, 3, 4, 2], ![1, 2, 4, 2], ![1, 2, 2, 2], ![1, 2, 2, 0], ![1, 1, 2, 2],
   ![1, 1, 2, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 1, 2, 2], ![0, 1, 2, 0], ![0, 1, 0, 0],
   ![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, -2, 0], ![-1, -1, -2, -2], ![-1, -2, -2, -2],
   ![-1, -2, -2, 0], ![-1, -2, -4, -2], ![-1, -3, -4, -2], ![-2, -3, -4, -2], ![0, -1, -2, -2],
   ![0, -1, -2, 0], ![0, -1, 0, 0]].toFinset

private abbrev f4Datum0 : UniversalRootDatum (Multiplicative (ZMod 2)) where
  rank := Tag.rank .F4
  cartan := Tag.cartan .F4
  isFiniteType := CFSG.LieType.Chevalley.isFiniteType_cartan .F4
  divisible := ∅
  rootGroup := fun _ => ⊥

private theorem isoLen_f4_height_le_rootFinset :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) ≤ 11 := by decide +kernel

private theorem f4_height_eleven_eq_highest :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) = 11 → v = isoLen_f4Highest := by decide +kernel

private theorem f4_highest_mem_rootFinset :
    isoLen_f4Highest ∈ rootFinset Tag.F4 := by decide +kernel

private theorem f4_highest_sum : (∑ i : Fin (Tag.rank .F4), isoLen_f4Highest i) = 11 := by
  decide +kernel

private theorem f4_orbit_closed :
    ∀ v ∈ f4LongOrbit, ∀ i : Fin (Tag.rank .F4), reflect .F4 i v ∈ f4LongOrbit := by
  decide +kernel

private theorem f4_highest_mem_orbit : isoLen_f4Highest ∈ f4LongOrbit := by decide +kernel

private theorem f4_single_mem_orbit_le_one :
    ∀ i : Fin (Tag.rank .F4),
      (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ f4LongOrbit → i.val ≤ 1 := by
  decide +kernel

private theorem f4Highest_mem_roots0 :
    isoLen_f4Highest ∈ f4Datum0.roots :=
  (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).1
    (mem_rootFinset.1 f4_highest_mem_rootFinset)

private theorem f4_height_le0 :
    ∀ δ ∈ f4Datum0.roots, (∑ i, δ i) ≤ ∑ i, isoLen_f4Highest i := by
  intro δ hδ
  have hδ' : IsRoot .F4 δ :=
    (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).2 hδ
  have hle : (∑ i, δ i) ≤ 11 := isoLen_f4_height_le_rootFinset δ (mem_rootFinset.2 hδ')
  have hsum : (∑ i : Fin (Tag.rank .F4), isoLen_f4Highest i) = 11 := f4_highest_sum
  omega

private noncomputable def isoLen_f4WordE1 : (coxeterMatrix f4Datum0.isFiniteType).Group :=
  (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩

private noncomputable def isoLen_f4WordE0 : (coxeterMatrix f4Datum0.isFiniteType).Group :=
  (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩

private theorem isoLen_f4_word_e1 :
    weylAction f4Datum0.isFiniteType isoLen_f4WordE1 isoLen_f4Highest =
      Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [isoLen_f4WordE1, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem isoLen_f4_word_e0 :
    weylAction f4Datum0.isFiniteType isoLen_f4WordE0 isoLen_f4Highest =
      Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [isoLen_f4WordE0, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem isoLen_f4_longRoot_e1 :
    GGLongRoot f4Datum0 (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1) :=
  ⟨isoLen_f4WordE1, isoLen_f4Highest, f4Highest_mem_roots0, f4_height_le0, isoLen_f4_word_e1.symm⟩

private theorem isoLen_f4_longRoot_e0 :
    GGLongRoot f4Datum0 (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1) :=
  ⟨isoLen_f4WordE0, isoLen_f4Highest, f4Highest_mem_roots0, f4_height_le0, isoLen_f4_word_e0.symm⟩

private theorem f4_eq_highest_of_isMaxHeight0
    {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ f4Datum0.roots)
    (hmax : ∀ δ ∈ f4Datum0.roots, (∑ i, δ i) ≤ ∑ i, γ i) : γ = isoLen_f4Highest := by
  have hθ : isoLen_f4Highest ∈ f4Datum0.roots := f4Highest_mem_roots0
  have h1 : (∑ i, isoLen_f4Highest i) ≤ ∑ i, γ i := hmax isoLen_f4Highest hθ
  have hγ' : IsRoot .F4 γ :=
    (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).2 hγ
  have h2 : (∑ i, γ i) ≤ 11 := isoLen_f4_height_le_rootFinset γ (mem_rootFinset.2 hγ')
  have hsum : (∑ i, γ i) = 11 := by
    have := f4_highest_sum
    omega
  exact f4_height_eleven_eq_highest γ (mem_rootFinset.2 hγ') hsum

private theorem f4_weylAction_mem_orbit (w : GGWeyl f4Datum0) :
    weylAction f4Datum0.isFiniteType w isoLen_f4Highest ∈ f4LongOrbit := by
  obtain ⟨ω, rfl⟩ := (coxeterMatrix f4Datum0.isFiniteType).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil => simpa [CoxeterSystem.wordProd_nil] using f4_highest_mem_orbit
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple, reflection_apply]
    exact f4_orbit_closed _ ih i

private theorem f4_ggLongRoot_single_iff_aux
    (i : Fin (Tag.rank .F4)) :
    GGLongRoot f4Datum0 (Pi.single i 1) ↔ i.val ≤ 1 := by
  constructor
  · intro hlong
    by_contra hle
    have hle' : 1 < i.val := Nat.lt_of_not_le hle
    obtain ⟨w, γ₀, hγ₀, hmax, heq⟩ := hlong
    have hγ₀eq : γ₀ = isoLen_f4Highest := f4_eq_highest_of_isMaxHeight0 hγ₀ hmax
    subst hγ₀eq
    have horbit : weylAction f4Datum0.isFiniteType w isoLen_f4Highest ∈ f4LongOrbit :=
      f4_weylAction_mem_orbit w
    rw [← heq] at horbit
    exact absurd (f4_single_mem_orbit_le_one i horbit) (by omega)
  · intro hi
    have h0 : i.val = 0 ∨ i.val = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hi
    rcases h0 with h | h
    · have hi0 : i = (⟨0, by decide⟩ : Fin (Tag.rank .F4)) := Fin.ext h
      rw [hi0]
      exact isoLen_f4_longRoot_e0
    · have hi1 : i = (⟨1, by decide⟩ : Fin (Tag.rank .F4)) := Fin.ext h
      rw [hi1]
      exact isoLen_f4_longRoot_e1

theorem ggLongRoot_weylAction_iff {U : Type} [Group U] (Δ : UniversalRootDatum U) (w : GGWeyl Δ)
    (γ : Fin Δ.rank → ℤ) :
    GGLongRoot Δ (weylAction Δ.isFiniteType w γ) ↔ GGLongRoot Δ γ := by
  constructor
  · rintro ⟨w', γ₀, hγ₀, hmax, hγw⟩
    refine ⟨w⁻¹ * w', γ₀, hγ₀, hmax, ?_⟩
    rw [weylAction_mul_apply, ← hγw, weylAction_inv_apply_apply]
  · rintro ⟨w', γ₀, hγ₀, hmax, hγw⟩
    exact ⟨w * w', γ₀, hγ₀, hmax, by rw [weylAction_mul_apply, hγw]⟩

theorem f4_ggLongRoot_single_iff
    (K : Type) [Field K] (i : Fin (f4Datum K).rank) :
    GGLongRoot (f4Datum K) (Pi.single i 1) ↔ i.val ≤ 1 := by
  change GGLongRoot f4Datum0 (Pi.single i 1) ↔ i.val ≤ 1
  exact f4_ggLongRoot_single_iff_aux i

end CFSG.StandardType.LieKnownR2.Short
