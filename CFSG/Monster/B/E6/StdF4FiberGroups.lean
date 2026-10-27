module

public import CFSG.Monster.B.E6.StdF4FiberRoots
public import CFSG.Monster.B.E6.StdF4Opposite

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical Matrix
open scoped Pointwise

theorem fibRoots_perm
    (d : Fin 5) :
    ∀ α ∈ fibRoots d, permLattice TwistTag.E6.perm α ∈ fibRoots d := by
  rintro α ⟨hα, hh, h1, h2⟩
  obtain ⟨e1, e2⟩ := fib_perm_check d α (mem_rootList hα)
  exact ⟨hα.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hh,
    lt_of_lt_of_eq h1 e1.symm, le_of_le_of_eq h2 e2.symm⟩

theorem fibForm_add_smul (d : Fin 5) (a b : ℕ) (α β : Fin TwistTag.E6.tag.rank → ℤ) :
    fibForm d (a • α + b • β) = a * fibForm d α + b * fibForm d β := by
  rw [fibForm, fibForm, fibForm, add_dotProduct, smul_dotProduct, smul_dotProduct, nsmul_eq_mul,
    nsmul_eq_mul]

theorem height_add_smul {τ : Tag} (a b : ℕ) (α β : Fin τ.rank → ℤ) :
    height (a • α + b • β) = a * height α + b * height β := by
  simp only [height, Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

theorem fibRoots_closed (d : Fin 5) : ∀ α ∈ fibRoots d, ∀ β ∈ fibRoots d, ∀ a b : ℕ,
    1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ fibRoots d := by
  rintro α ⟨-, hα1, hα2, hα3⟩ β ⟨-, hβ1, hβ2, hβ3⟩ a b ha hb hr
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [height_add_smul]
    positivity
  · change 0 < a • α (i6 1) + b • β (i6 1)
    simp only [nsmul_eq_mul]
    positivity
  · rw [fibForm_add_smul]
    positivity

theorem mem_fibOrbits
    {d : Fin 5} {O : Finset (Fin TwistTag.E6.tag.rank → ℤ)} :
    O ∈ fibOrbits d ↔ O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ fibRoots d := by
  rw [fibOrbits, Finset.mem_filter, mem_posOrbits]
  constructor
  · rintro ⟨⟨hO, hpos⟩, hc⟩
    exact ⟨hO, fun α hα => ⟨(hpos hα).1, (hpos hα).2, (hc α hα).1, (hc α hα).2⟩⟩
  · rintro ⟨hO, hsub⟩
    exact ⟨⟨hO, fun α hα => ⟨(hsub hα).1, (hsub hα).2.1⟩⟩,
      fun α hα => ⟨(hsub hα).2.2.1, (hsub hα).2.2.2⟩⟩

@[expose] def fibV
    (d : Fin 5) : Subgroup (ModGL Tag.E6 K) :=
  rootSpan TwistTag.E6.tag K (fibRoots d) ⊓ twistedFixedGroup TwistTag.E6 K barHom

@[expose] def fibOrbitEnum (d : Fin 5) (j : Fin (fibOrbits d).card) :
    Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  ((fibOrbits d).equivFin.symm j : Finset (Fin TwistTag.E6.tag.rank → ℤ))

theorem fibOrbitEnum_injective (d : Fin 5) : Function.Injective (fibOrbitEnum d) :=
  fun _ _ h => (fibOrbits d).equivFin.symm.injective (Subtype.ext h)

theorem range_fibOrbitEnum
    (d : Fin 5) : Set.range (fibOrbitEnum d) =
    {O | O ∈ TwistTag.E6.diagramRootOrbits ∧
      (O : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ fibRoots d} := by
  ext O
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨j, rfl⟩
    exact mem_fibOrbits.mp ((fibOrbits d).equivFin.symm j).2
  · refine ⟨(fibOrbits d).equivFin ⟨O, mem_fibOrbits.mpr h⟩, ?_⟩
    rw [fibOrbitEnum, Equiv.symm_apply_apply]

theorem card_fibV
    (d : Fin 5) : Nat.card (fibV d) = 2 ^ fibExp d := by
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => ⟨hα.1, hα.2.1⟩) (fibRoots_perm d) (fibRoots_closed d) (fibOrbitEnum d)
    (fibOrbitEnum_injective d) (range_fibOrbitEnum d)
  have hmem : ∀ j, fibOrbitEnum d j ∈ TwistTag.E6.diagramRootOrbits := fun j =>
    (mem_fibOrbits.mp ((fibOrbits d).equivFin.symm j).2).1
  calc Nat.card (fibV d)
      = Nat.card (Set.univ : Set ((j : Fin (fibOrbits d).card) →
          ↥(rootSpan TwistTag.E6.tag K (fibOrbitEnum d j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom))) := (Nat.card_congr hbij.equiv).symm
    _ = ∏ j, Nat.card ↥(rootSpan TwistTag.E6.tag K
          (fibOrbitEnum d j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
            twistedFixedGroup TwistTag.E6 K barHom) := by
        rw [Nat.card_univ, Nat.card_pi]
    _ = ∏ j, (if (fibOrbitEnum d j).card = 1 then 2 else 4) :=
        Finset.prod_congr rfl fun j _ => card_rootSpan_orbit (hmem j)
    _ = ∏ O ∈ fibOrbits d, (if O.card = 1 then 2 else 4) := by
        rw [← Finset.prod_coe_sort (fibOrbits d)]
        exact Fintype.prod_equiv (fibOrbits d).equivFin.symm _ _ fun j => rfl
    _ = 2 ^ fibExp d := prod_fibOrbits d

theorem fibRoots_subset_radical (d : Fin 5) :
    fibRoots d ⊆ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ) := by
  rintro α ⟨hα, hh, h1, -⟩
  refine ⟨⟨hα, hh⟩, fun h => ?_⟩
  have h0 := h.1.2 (i6 1) (by rw [nativeUnion_firstJ]; exact fun h => ne_one_of_mem_setA h rfl)
  exact absurd h0 (ne_of_gt h1)

theorem fibV_le_stdRadical
    (d : Fin 5) : fibV d ≤ stdRadical firstJ := by
  refine inf_le_inf ?_ le_rfl
  exact iSup₂_le fun α hα => le_iSup₂_of_le α (fibRoots_subset_radical d hα) le_rfl

theorem stdRadical_le_nativeParabolic'
    (I : Set (Fin 4)) :
    stdRadical firstJ ≤ nativeParabolic I :=
  (stdRadical_le_stdBorel firstJ).trans (stdBorel_le_nativeParabolic I)

theorem leviParabolic_le_normalizer
    {I : Set (Fin 4)} (hI : I ⊆ firstJ) :
    leviParabolic firstJ I ≤ Subgroup.normalizer (stdRadical firstJ : Set (ModGL Tag.E6 K)) := by
  intro l hl
  have hlP : l ∈ nativeParabolic firstJ := stdLevi_le_nativeParabolic two_mem_firstJ
    (leviParabolic_le_stdLevi two_mem_firstJ hI hl)
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hN := (stdRadical_normal firstJ).conj_mem
  constructor
  · intro hu
    have := hN ⟨u, stdRadical_le_nativeParabolic firstJ hu⟩ hu ⟨l, hlP⟩
    exact this
  · intro hu
    have h := hN ⟨l * u * l⁻¹, stdRadical_le_nativeParabolic firstJ hu⟩ hu ⟨l⁻¹, inv_mem hlP⟩
    convert Subgroup.mem_subgroupOf.mp h using 1
    simp [mul_assoc]

theorem nativeParabolic_eq_sup
    (I : Set (Fin 4)) :
    nativeParabolic I = stdRadical firstJ ⊔ leviParabolic firstJ I := by
  refine le_antisymm ((Subgroup.closure_le _).2 (Set.union_subset (fun b hb => ?_) ?_))
    (sup_le (stdRadical_le_nativeParabolic' I) (leviParabolic_le_nativeParabolic firstJ I))
  · obtain ⟨⟨q, c⟩, ⟨hq, hc, rfl⟩, -⟩ := existsUnique_stdRadical_mul_stdBorel firstJ hb
    exact mul_mem (Subgroup.mem_sup_left hq)
      (Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl hc)))
  · rintro _ ⟨i, hi, rfl⟩
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩))

theorem coe_nativeParabolic_eq_mul
    {I : Set (Fin 4)} (hI : I ⊆ firstJ) :
    (nativeParabolic I : Set (ModGL Tag.E6 K)) =
      (stdRadical firstJ : Set (ModGL Tag.E6 K)) *
        (leviParabolic firstJ I : Set (ModGL Tag.E6 K)) := by
  rw [nativeParabolic_eq_sup I]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ (leviParabolic_le_normalizer hI)

theorem stdRadical_inf_leviParabolic
    {I : Set (Fin 4)} (hI : I ⊆ firstJ) :
    stdRadical firstJ ⊓ leviParabolic firstJ I = ⊥ :=
  eq_bot_iff.2 fun _ hg =>
    (stdRadical_inf_stdLevi firstJ).le ⟨hg.1, leviParabolic_le_stdLevi two_mem_firstJ hI hg.2⟩

theorem card_nativeParabolic_eq
    {I : Set (Fin 4)} (hI : I ⊆ firstJ) :
    Nat.card (nativeParabolic I) =
      Nat.card (stdRadical firstJ) * Nat.card (leviParabolic firstJ I) := by
  have hdisj := stdRadical_inf_leviParabolic hI
  let f : stdRadical firstJ × leviParabolic firstJ I → nativeParabolic I := fun p =>
    ⟨p.1 * p.2, mul_mem (stdRadical_le_nativeParabolic' I p.1.2)
      (leviParabolic_le_nativeParabolic firstJ I p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p p' h => ?_, fun g => ?_⟩
    · have e : (p.1 : ModGL Tag.E6 K) * p.2 = p'.1 * p'.2 := congrArg Subtype.val h
      have hm : (p'.1 : ModGL Tag.E6 K)⁻¹ * p.1 = p'.2 * (p.2 : ModGL Tag.E6 K)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
      have h1 : (p'.1 : ModGL Tag.E6 K)⁻¹ * p.1 ∈ stdRadical firstJ ⊓ leviParabolic firstJ I :=
        Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem p'.1.2) p.1.2, hm ▸ mul_mem p'.2.2 (inv_mem p.2.2)⟩
      rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h1
      have h2 : (p.2 : ModGL Tag.E6 K) = p'.2 := by
        rw [h1] at e
        exact mul_left_cancel e
      exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2)
    · have hg : (g : ModGL Tag.E6 K) ∈ (nativeParabolic I : Set (ModGL Tag.E6 K)) := g.2
      rw [coe_nativeParabolic_eq_mul hI] at hg
      obtain ⟨q, hq, l, hl, e⟩ := hg
      exact ⟨(⟨q, hq⟩, ⟨l, hl⟩), Subtype.ext e⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem card_parabolicG
    (I : Set (Fin 4)) :
    Nat.card (parabolicG I) = Nat.card stdBorelG *
      ∑ᶠ w ∈ (ncs.parabolic I : Set NW), weylWeight ncs E6Folded.letterWeight w := by
  have hset : ((parabolicG I : Subgroup stdGroup) : Set stdGroup) =
      QuotientGroup.mk ⁻¹' residue ncs stdDistance I c₀ := by
    ext p
    rw [SetLike.mem_coe, Set.mem_preimage, mem_residue_mk_iff, inv_one, one_mul]
  rw [← ncard_residue_eq_finsum hδ hpanel I c₀,
    ← Nat.card_coe_set_eq (residue ncs stdDistance I c₀),
    ← QuotientGroup.card_preimage_mk, ← hset]
  rfl

theorem card_nativeParabolic
    (I : Set (Fin 4)) :
    Nat.card (nativeParabolic I) = 3 * 2 ^ 36 *
      ∑ᶠ w ∈ (ncs.parabolic I : Set NW), weylWeight ncs E6Folded.letterWeight w := by
  rw [← card_stdBorelG, ← card_parabolicG]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (nativeParabolic_le_stdGroup I)).toEquiv).symm

end CFSG.Monster.B.E6.StdF4
