module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

@[expose] def twE6Alpha : Fin (Tag.rank .F4) → ℤ := ![1, 2, 3, 2]

private def teConj_f4Highest : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private def teConj_f4LongOrbit : Finset (Fin (Tag.rank .F4) → ℤ) :=
  [![2, 3, 4, 2], ![1, 3, 4, 2], ![1, 2, 4, 2], ![1, 2, 2, 2], ![1, 2, 2, 0], ![1, 1, 2, 2],
   ![1, 1, 2, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 1, 2, 2], ![0, 1, 2, 0], ![0, 1, 0, 0],
   ![-1, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, -2, 0], ![-1, -1, -2, -2], ![-1, -2, -2, -2],
   ![-1, -2, -2, 0], ![-1, -2, -4, -2], ![-1, -3, -4, -2], ![-2, -3, -4, -2], ![0, -1, -2, -2],
   ![0, -1, -2, 0], ![0, -1, 0, 0]].toFinset

private abbrev teConj_f4Datum0 : UniversalRootDatum (Multiplicative (ZMod 2)) where
  rank := Tag.rank .F4
  cartan := Tag.cartan .F4
  isFiniteType := CFSG.LieType.Chevalley.isFiniteType_cartan .F4
  divisible := ∅
  rootGroup := fun _ => ⊥

private theorem teConj_f4_height_le_rootFinset :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) ≤ 11 := by decide +kernel

private theorem teConj_f4_height_eleven_eq_highest :
    ∀ v ∈ rootFinset Tag.F4, (∑ i, v i) = 11 → v = teConj_f4Highest := by decide +kernel

private theorem teConj_f4_highest_mem_rootFinset :
    teConj_f4Highest ∈ rootFinset Tag.F4 := by decide +kernel

private theorem teConj_f4_highest_sum :
    (∑ i : Fin (Tag.rank .F4), teConj_f4Highest i) = 11 := by decide +kernel

private theorem teConj_f4_orbit_closed :
    ∀ v ∈ teConj_f4LongOrbit, ∀ i : Fin (Tag.rank .F4),
      reflect .F4 i v ∈ teConj_f4LongOrbit := by decide +kernel

private theorem teConj_f4_highest_mem_orbit : teConj_f4Highest ∈ teConj_f4LongOrbit := by
  decide +kernel

private theorem teConj_f4_alpha_not_mem_orbit : twE6Alpha ∉ teConj_f4LongOrbit := by
  decide +kernel

private theorem teConj_f4_single_mem_orbit_le_one :
    ∀ i : Fin (Tag.rank .F4),
      (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ teConj_f4LongOrbit → i.val ≤ 1 := by
  decide +kernel

private theorem teConj_f4Highest_mem_roots0 :
    teConj_f4Highest ∈ teConj_f4Datum0.roots :=
  (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).1
    (mem_rootFinset.1 teConj_f4_highest_mem_rootFinset)

private theorem teConj_f4_height_le0 :
    ∀ δ ∈ teConj_f4Datum0.roots, (∑ i, δ i) ≤ ∑ i, teConj_f4Highest i := by
  intro δ hδ
  have hδ' : IsRoot .F4 δ :=
    (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).2 hδ
  have hle : (∑ i, δ i) ≤ 11 :=
    teConj_f4_height_le_rootFinset δ (mem_rootFinset.2 hδ')
  have hsum : (∑ i : Fin (Tag.rank .F4), teConj_f4Highest i) = 11 := teConj_f4_highest_sum
  omega

private noncomputable def teConj_f4WordE1 : GGWeyl teConj_f4Datum0 :=
  (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩

private noncomputable def teConj_f4WordE0 : GGWeyl teConj_f4Datum0 :=
  (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩

private theorem teConj_f4_word_e1 :
    weylAction teConj_f4Datum0.isFiniteType teConj_f4WordE1 teConj_f4Highest =
      Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [teConj_f4WordE1, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem teConj_f4_word_e0 :
    weylAction teConj_f4Datum0.isFiniteType teConj_f4WordE0 teConj_f4Highest =
      Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [teConj_f4WordE0, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem teConj_f4_longRoot_e1 :
    GGLongRoot teConj_f4Datum0 (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .F4)) 1) :=
  ⟨teConj_f4WordE1, teConj_f4Highest, teConj_f4Highest_mem_roots0, teConj_f4_height_le0,
    teConj_f4_word_e1.symm⟩

private theorem teConj_f4_longRoot_e0 :
    GGLongRoot teConj_f4Datum0 (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .F4)) 1) :=
  ⟨teConj_f4WordE0, teConj_f4Highest, teConj_f4Highest_mem_roots0, teConj_f4_height_le0,
    teConj_f4_word_e0.symm⟩

private theorem teConj_f4_eq_highest_of_isMaxHeight0
    {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ teConj_f4Datum0.roots)
    (hmax : ∀ δ ∈ teConj_f4Datum0.roots, (∑ i, δ i) ≤ ∑ i, γ i) : γ = teConj_f4Highest := by
  have hθ : teConj_f4Highest ∈ teConj_f4Datum0.roots := teConj_f4Highest_mem_roots0
  have h1 : (∑ i, teConj_f4Highest i) ≤ ∑ i, γ i := hmax teConj_f4Highest hθ
  have hγ' : IsRoot .F4 γ :=
    (CFSG.LieType.Chevalley.isRoot_iff_mem_roots (τ := .F4)).2 hγ
  have h2 : (∑ i, γ i) ≤ 11 := teConj_f4_height_le_rootFinset γ (mem_rootFinset.2 hγ')
  have hsum : (∑ i, γ i) = 11 := by
    have := teConj_f4_highest_sum
    omega
  exact teConj_f4_height_eleven_eq_highest γ (mem_rootFinset.2 hγ') hsum

private theorem teConj_f4_weylAction_mem_orbit (w : GGWeyl teConj_f4Datum0) :
    weylAction teConj_f4Datum0.isFiniteType w teConj_f4Highest ∈ teConj_f4LongOrbit := by
  obtain ⟨ω, rfl⟩ :=
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil => simpa [CoxeterSystem.wordProd_nil] using teConj_f4_highest_mem_orbit
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple, reflection_apply]
    exact teConj_f4_orbit_closed _ ih i

private theorem teConj_f4_ggLongRoot_single_iff_aux
    (i : Fin (Tag.rank .F4)) :
    GGLongRoot teConj_f4Datum0 (Pi.single i 1) ↔ i.val ≤ 1 := by
  constructor
  · intro hlong
    by_contra hle
    have hle' : 1 < i.val := Nat.lt_of_not_le hle
    obtain ⟨w, γ₀, hγ₀, hmax, heq⟩ := hlong
    have hγ₀eq : γ₀ = teConj_f4Highest := teConj_f4_eq_highest_of_isMaxHeight0 hγ₀ hmax
    subst hγ₀eq
    have horbit : weylAction teConj_f4Datum0.isFiniteType w teConj_f4Highest ∈
        teConj_f4LongOrbit := teConj_f4_weylAction_mem_orbit w
    rw [← heq] at horbit
    exact absurd (teConj_f4_single_mem_orbit_le_one i horbit) (by omega)
  · intro hi
    have h0 : i.val = 0 ∨ i.val = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hi
    rcases h0 with h | h
    · have hi0 : i = (⟨0, by decide⟩ : Fin (Tag.rank .F4)) := Fin.ext h
      rw [hi0]
      exact teConj_f4_longRoot_e0
    · have hi1 : i = (⟨1, by decide⟩ : Fin (Tag.rank .F4)) := Fin.ext h
      rw [hi1]
      exact teConj_f4_longRoot_e1

private noncomputable def teConj_f4Word2 : GGWeyl teConj_f4Datum0 :=
  (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩

private noncomputable def teConj_f4Word3 : GGWeyl teConj_f4Datum0 :=
  (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨0, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨1, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨2, by decide⟩ *
    (coxeterMatrix teConj_f4Datum0.isFiniteType).toCoxeterSystem.simple ⟨3, by decide⟩

private theorem teConj_f4_word2_apply :
    weylAction teConj_f4Datum0.isFiniteType teConj_f4Word2 twE6Alpha =
      Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [teConj_f4Word2, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem teConj_f4_word3_apply :
    weylAction teConj_f4Datum0.isFiniteType teConj_f4Word3 twE6Alpha =
      Pi.single (⟨3, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
  simp only [teConj_f4Word3, weylAction_mul_apply, weylAction_simple, reflection_apply]
  decide +kernel

private theorem teConj_f4_short_single (i : Fin (Tag.rank .F4)) (hi : 2 ≤ i.val) :
    ∃ u : GGWeyl teConj_f4Datum0,
      Pi.single i 1 = weylAction teConj_f4Datum0.isFiniteType u twE6Alpha := by
  fin_cases i
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact ⟨teConj_f4Word2, teConj_f4_word2_apply.symm⟩
  · exact ⟨teConj_f4Word3, teConj_f4_word3_apply.symm⟩

private theorem teConj_f4_ggLongRoot_weylAction_iff (w : GGWeyl teConj_f4Datum0)
    (γ : Fin (Tag.rank .F4) → ℤ) :
    GGLongRoot teConj_f4Datum0 (weylAction teConj_f4Datum0.isFiniteType w γ) ↔
      GGLongRoot teConj_f4Datum0 γ := by
  constructor
  · rintro ⟨w', γ₀, hγ₀, hmax, hγw⟩
    refine ⟨w⁻¹ * w', γ₀, hγ₀, hmax, ?_⟩
    rw [weylAction_mul_apply, ← hγw, weylAction_inv_apply_apply]
  · rintro ⟨w', γ₀, hγ₀, hmax, hγw⟩
    exact ⟨w * w', γ₀, hγ₀, hmax, by rw [weylAction_mul_apply, hγw]⟩

theorem exists_conj_ggRootSub_of_weylAction
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {r β : Fin D.rank → ℤ} (hr : r ∈ D.roots) (w : GGWeyl D)
    (hβ : β = weylAction D.isFiniteType w r) (u : K) :
    ∃ g : K, ggRootSub D (MonoidHom.id K) β u = (D.rootGroup r).map (MulAut.conj g).toMonoidHom ∧
      ggRootSub D (MonoidHom.id K) (-β) u =
        (D.rootGroup (-r)).map (MulAut.conj g).toMonoidHom := by
  set m : K := nrep hct w with hm
  have ham : ActsAs D m w := by rw [hm]; exact actsAs_nrep hct w
  have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      (MulAut.conj (u * m)).toMonoidHom := by
    ext x
    change u * (m * x * m⁻¹) * u⁻¹ = (u * m) * x * (u * m)⁻¹
    group
  have hβmap : D.rootGroup β = (D.rootGroup r).map (MulAut.conj m).toMonoidHom := by
    rw [hβ, ← ham r hr]
  have hnegmem : -r ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hr
  have hneg : -β = weylAction D.isFiniteType w (-r) := by rw [map_neg, ← hβ]
  have hnegmap : D.rootGroup (-β) = (D.rootGroup (-r)).map (MulAut.conj m).toMonoidHom := by
    rw [hneg, ← ham (-r) hnegmem]
  refine ⟨u * m, ?_, ?_⟩
  · calc ggRootSub D (MonoidHom.id K) β u
        = ((D.rootGroup β).map (MulAut.conj u).toMonoidHom).map (MonoidHom.id K) := rfl
      _ = (D.rootGroup β).map (MulAut.conj u).toMonoidHom := Subgroup.map_id _
      _ = ((D.rootGroup r).map (MulAut.conj m).toMonoidHom).map
            (MulAut.conj u).toMonoidHom := by rw [hβmap]
      _ = (D.rootGroup r).map ((MulAut.conj u).toMonoidHom.comp
            (MulAut.conj m).toMonoidHom) := by rw [Subgroup.map_map]
      _ = (D.rootGroup r).map (MulAut.conj (u * m)).toMonoidHom := by rw [hcomp]
  · calc ggRootSub D (MonoidHom.id K) (-β) u
        = ((D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map (MonoidHom.id K) := rfl
      _ = (D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom := Subgroup.map_id _
      _ = ((D.rootGroup (-r)).map (MulAut.conj m).toMonoidHom).map
            (MulAut.conj u).toMonoidHom := by rw [hnegmap]
      _ = (D.rootGroup (-r)).map ((MulAut.conj u).toMonoidHom.comp
            (MulAut.conj m).toMonoidHom) := by rw [Subgroup.map_map]
      _ = (D.rootGroup (-r)).map (MulAut.conj (u * m)).toMonoidHom := by rw [hcomp]

theorem twE6_alpha_mem_roots
    {k : Type} [Field k] (θ : k →+* k) : twE6Alpha ∈ (twistedDatum k θ).roots := by
  rw [twistedDatum_roots]
  exact mem_rootFinset.1 (by decide +kernel)

theorem twE6_alpha_not_long
    {k : Type} [Field k] (θ : k →+* k) : ¬ GGLongRoot (twistedDatum k θ) twE6Alpha := by
  change ¬ GGLongRoot teConj_f4Datum0 twE6Alpha
  rintro ⟨w, γ₀, hγ₀, hmax, heq⟩
  have hγ₀eq : γ₀ = teConj_f4Highest :=
    teConj_f4_eq_highest_of_isMaxHeight0 hγ₀ hmax
  subst hγ₀eq
  have horbit : weylAction teConj_f4Datum0.isFiniteType w teConj_f4Highest ∈
      teConj_f4LongOrbit := teConj_f4_weylAction_mem_orbit w
  rw [← heq] at horbit
  exact teConj_f4_alpha_not_mem_orbit horbit

theorem twE6_exists_weyl_of_not_long
    {k : Type} [Field k] (θ : k →+* k) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : β ∈ (twistedDatum k θ).roots) (hs : ¬ GGLongRoot (twistedDatum k θ) β) :
    ∃ w : GGWeyl (twistedDatum k θ),
      β = weylAction (twistedDatum k θ).isFiniteType w twE6Alpha := by
  change β ∈ teConj_f4Datum0.roots at hβ
  change ¬ GGLongRoot teConj_f4Datum0 β at hs
  change ∃ w : GGWeyl teConj_f4Datum0,
    β = weylAction teConj_f4Datum0.isFiniteType w twE6Alpha
  simp only [CFSG.LieType.RootSystem.roots, Set.mem_union, Set.mem_setOf_eq] at hβ
  obtain ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩ := hβ
  · have hlong_i : ¬ GGLongRoot teConj_f4Datum0 (Pi.single i 1) := fun h =>
      hs ((teConj_f4_ggLongRoot_weylAction_iff w (Pi.single i 1)).2 h)
    have hi2 : 2 ≤ i.val := by
      by_contra h
      have h1 : i.val ≤ 1 := by omega
      exact hlong_i ((teConj_f4_ggLongRoot_single_iff_aux i).2 h1)
    obtain ⟨u, hu⟩ := teConj_f4_short_single i hi2
    refine ⟨w * u, ?_⟩
    rw [weylAction_mul_apply, hu]
  · exact absurd hi (Set.notMem_empty i)

end CFSG.StandardType.LieKnownR2.Short
