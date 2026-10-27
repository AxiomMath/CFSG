module

public import CFSG.Monster.B.E6.StdF4FiberCount
public import CFSG.Monster.B.E6.StdF4WeylPair

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Monster.B.Classical Matrix

abbrev fibT
    (d : Fin 5) : stdGroup := tW (ncs.wordProd (fibWord d))

abbrev fibYE (d : Fin 5) : Fin Tag.E6.rank → ℤ := fibY d

theorem isRoot_fibYE
    (d : Fin 5) : IsRoot Tag.E6 (fibYE d) := isRoot_fibYL d

theorem coe_fibT
    (d : Fin 5) : (fibT d : ModGL Tag.E6 K) = pinnedX Tag.E6 K (fibYE d) 1 := by
  rw [coe_tW, wsmul_fibWord]
  rfl

theorem betaGL_fibT
    (d : Fin 5) : betaGL (fibT d : ModGL Tag.E6 K) = fibT d := by
  rw [coe_fibT]
  exact Units.ext (by rw [betaGL_apply, entrywise_pinnedX, map_one])

theorem apply_fibT
    (b : betaGroup) (d : Fin 5) : (b : MulAut stdGroup) (fibT d) = fibT d := by
  rcases mem_betaGroup_iff.mp b.2 with h | h <;> rw [h]
  · rfl
  · exact Subtype.ext ((coe_betaG_apply _).trans (betaGL_fibT d))

theorem commute_pinnedX_fibT
    (d : Fin 5) {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h0 : 0 ≤ α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ fibYE d)) (c : K) :
    pinnedX Tag.E6 K α c * (fibT d : ModGL Tag.E6 K) = fibT d * pinnedX Tag.E6 K α c := by
  rw [coe_fibT]
  by_cases he : α = fibYE d
  · subst he
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · exact (pinnedX_commute_of_rootForm_nonneg (Or.inr (Or.inl rfl)) hα (isRoot_fibYE d) he h0
      c 1).eq

theorem rootSpan_le_centralizer_fibT
    (d : Fin 5) {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 ≤ fibForm d α) :
    rootSpan TwistTag.E6.tag K S ≤ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} :=
  iSup₂_le fun α hα x hx => by
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact Subgroup.mem_centralizer_singleton_iff.2 (commute_pinnedX_fibT d (hS α hα).1
      (hS α hα).2 c)

theorem fibV_le_centralizer
    (d : Fin 5) :
    fibV d ≤ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} :=
  inf_le_left.trans (rootSpan_le_centralizer_fibT d fun _ hα => ⟨hα.1, hα.2.2.2⟩)

theorem stdLeviUnipotent_le_centralizer
    (d : Fin 5) :
    stdLeviUnipotent firstJ ≤ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} := by
  refine inf_le_left.trans (rootSpan_le_centralizer_fibT d fun α hα => ⟨hα.2.1, ?_⟩)
  have h1 : α (i6 1) = 0 := hα.1.2 (i6 1) (by
    rw [nativeUnion_firstJ]
    exact fun h => ne_one_of_mem_setA h rfl)
  exact fib_levi_check d α (mem_rootList hα.2.1) hα.2.2 h1

theorem commute_torusElt_fibT
    (d : Fin 5) {i : Fin Tag.E6.rank}
    (hi : ∑ j, Tag.E6.cartan i j * fibYE d j = 0) (s : Kˣ) :
    torusElt Tag.E6 K i s * (fibT d : ModGL Tag.E6 K) = fibT d * torusElt Tag.E6 K i s := by
  have h := root_torus_conjugation (R := K) i (isRoot_fibYE d) s 1
  rw [hi, zpow_zero, Units.val_one, one_mul] at h
  rw [coe_fibT, ← mul_inv_eq_iff_eq_mul, h]

theorem fixedTorusGen_mem_centralizer_fibT
    (d : Fin 5) :
    fixedTorusGen ∈ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, fixedTorusGen, mul_assoc,
    commute_torusElt_fibT d (fib_torus_check d).2, ← mul_assoc,
    commute_torusElt_fibT d (fib_torus_check d).1, mul_assoc]

theorem stdTorus_le_centralizer_fibT
    (d : Fin 5) :
    stdTorus ≤ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} := by
  rw [← stdTorus0_eq_stdTorus, stdTorus0_eq_zpowers]
  exact Subgroup.zpowers_le.mpr (fixedTorusGen_mem_centralizer_fibT d)

theorem stdLeviBorel_le_centralizer_fibT
    (d : Fin 5) :
    stdLeviBorel firstJ ≤ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} :=
  sup_le (stdTorus_le_centralizer_fibT d) (stdLeviUnipotent_le_centralizer d)

theorem nativeRep_mem_centralizer_fibT
    {d : Fin 5} {i : Fin 4} (hi : i ∈ fibIF d) :
    nativeRep i ∈ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} := by
  have hfix : nativeRefl i • fibYE d = fibYE d := by
    have h := wsmul_simple i (fibY d)
    rw [fib_refl_check d i hi] at h
    unfold wsmul at h
    rw [nativeCoxeterSystem_simple, coe_nativeSimple_eq_nativeRefl] at h
    exact h
  have h := canonicalRep_mul_pinnedX_mul_inv_of_two two_eq_zero_K (nativeRefl i)
    (isRoot_fibYE d) (1 : K)
  rw [hfix] at h
  rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul, coe_fibT]
  exact h

theorem fibLevi_le_centralizer
    (d : Fin 5) :
    fibLevi d ≤ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} := by
  refine (Subgroup.closure_le _).2 (Set.union_subset (fun b hb => ?_) ?_)
  · exact stdLeviBorel_le_centralizer_fibT d hb
  · rintro _ ⟨i, hi, rfl⟩
    exact nativeRep_mem_centralizer_fibT (Finset.mem_coe.1 hi)

theorem apply_mem_of_betaGL_mem
    {H : Subgroup (ModGL Tag.E6 K)}
    (hH : ∀ g ∈ H, betaGL g ∈ H) (b : betaGroup) {x : stdGroup}
    (hx : (x : ModGL Tag.E6 K) ∈ H) :
    (((b : MulAut stdGroup) x : stdGroup) : ModGL Tag.E6 K) ∈ H := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [h]
    exact hx
  · rw [h, coe_betaG_apply]
    exact hH _ hx

@[expose] def betaStar
    (H : Subgroup (ModGL Tag.E6 K)) (hH : ∀ g ∈ H, betaGL g ∈ H) :
    Subgroup GStar where
  carrier := {γ | (γ.left : ModGL Tag.E6 K) ∈ H}
  mul_mem' {γ γ'} hγ hγ' := by
    change (((γ * γ').left : stdGroup) : ModGL Tag.E6 K) ∈ H
    rw [SemidirectProduct.mul_left, Subgroup.coe_mul]
    exact mul_mem hγ (apply_mem_of_betaGL_mem hH γ.right hγ')
  one_mem' := one_mem H
  inv_mem' {γ} hγ := by
    change (((γ⁻¹).left : stdGroup) : ModGL Tag.E6 K) ∈ H
    rw [SemidirectProduct.inv_left]
    have h1 : ((γ.left⁻¹ : stdGroup) : ModGL Tag.E6 K) ∈ H := by
      rw [Subgroup.coe_inv]
      exact inv_mem hγ
    exact apply_mem_of_betaGL_mem hH γ.right⁻¹ h1

theorem mem_betaStar
    {H : Subgroup (ModGL Tag.E6 K)} {hH : ∀ g ∈ H, betaGL g ∈ H} {γ : GStar} :
    γ ∈ betaStar H hH ↔ (γ.left : ModGL Tag.E6 K) ∈ H :=
  Iff.rfl

theorem card_betaStar
    {H : Subgroup (ModGL Tag.E6 K)} (hH : ∀ g ∈ H, betaGL g ∈ H)
    (hG : H ≤ stdGroup) : Nat.card (betaStar H hH) = Nat.card H * 2 := by
  let e : betaStar H hH ≃ H × betaGroup :=
    { toFun := fun γ => (⟨γ.1.left, γ.2⟩, γ.1.right)
      invFun := fun p => ⟨⟨⟨p.1, hG p.1.2⟩, p.2⟩, p.1.2⟩
      left_inv := fun γ => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_betaGroup]

theorem betaGL_mem_leviParabolic
    {I : Set (Fin 4)} {g : ModGL Tag.E6 K}
    (hg : g ∈ leviParabolic firstJ I) : betaGL g ∈ leviParabolic firstJ I := by
  have hle : leviParabolic firstJ I ≤ (leviParabolic firstJ I).comap betaGL := by
    refine (Subgroup.closure_le _).2 (Set.union_subset (fun b hb => ?_) ?_)
    · exact Subgroup.subset_closure (Or.inl (betaGL_mem_stdLeviBorel hb))
    · rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, betaGL_nativeRep]
      exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
  exact hle hg

abbrev fibLStar
    (d : Fin 5) : Subgroup GStar :=
  betaStar (fibLevi d) fun _ => betaGL_mem_leviParabolic

@[expose] def radStar :
    Subgroup GStar :=
  ((stdRadical firstJ).subgroupOf stdGroup).map SemidirectProduct.inl

@[expose] def fibVStar
    (d : Fin 5) : Subgroup GStar :=
  ((fibV d).subgroupOf stdGroup).map SemidirectProduct.inl

theorem mem_map_inl_iff
    {H : Subgroup stdGroup} {γ : GStar} :
    γ ∈ H.map (SemidirectProduct.inl : stdGroup →* GStar) ↔ γ.left ∈ H ∧ γ.right = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, h1⟩
    exact ⟨γ.left, hx, SemidirectProduct.ext rfl h1.symm⟩

theorem mem_radStar
    {γ : GStar} :
    γ ∈ radStar ↔ (γ.left : ModGL Tag.E6 K) ∈ stdRadical firstJ ∧ γ.right = 1 :=
  mem_map_inl_iff

theorem mem_fibVStar
    {d : Fin 5} {γ : GStar} :
    γ ∈ fibVStar d ↔ (γ.left : ModGL Tag.E6 K) ∈ fibV d ∧ γ.right = 1 :=
  mem_map_inl_iff

theorem card_map_inl
    (H : Subgroup stdGroup) :
    Nat.card (H.map (SemidirectProduct.inl : stdGroup →* GStar)) = Nat.card H :=
  (Nat.card_congr (H.equivMapOfInjective _ SemidirectProduct.inl_injective).toEquiv).symm

theorem card_subgroupOf_stdGroup
    {H : Subgroup (ModGL Tag.E6 K)} (hG : H ≤ stdGroup) :
    Nat.card (H.subgroupOf stdGroup) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG).toEquiv

theorem fibV_le_stdGroup
    (d : Fin 5) : fibV d ≤ stdGroup :=
  (fibV_le_stdRadical d).trans ((stdRadical_le_stdBorel firstJ).trans stdBorel_le_stdGroup)

theorem stdRadical_le_stdGroup' :
    stdRadical firstJ ≤ stdGroup :=
  (stdRadical_le_stdBorel firstJ).trans stdBorel_le_stdGroup

theorem fibLevi_le_stdGroup
    (d : Fin 5) : fibLevi d ≤ stdGroup :=
  (leviParabolic_le_nativeParabolic firstJ _).trans (nativeParabolic_le_stdGroup _)

theorem card_radStar :
    Nat.card radStar = 2 ^ 21 := by
  rw [radStar, card_map_inl, card_subgroupOf_stdGroup stdRadical_le_stdGroup',
    card_stdRadical_firstJ]

theorem card_fibVStar
    (d : Fin 5) : Nat.card (fibVStar d) = 2 ^ fibExp d := by
  rw [fibVStar, card_map_inl, card_subgroupOf_stdGroup (fibV_le_stdGroup d), card_fibV]

theorem card_fibLStar
    (d : Fin 5) : Nat.card (fibLStar d) = fibLeviCard d * 2 := by
  rw [card_betaStar _ (fibLevi_le_stdGroup d), card_fibLevi]

theorem parStar_eq_betaStar :
    parStar firstJ =
    betaStar (nativeParabolic firstJ) fun _ => betaGL_mem_nativeParabolic :=
  SetLike.ext fun _ => Iff.rfl

theorem card_parStar :
    Nat.card (parStar firstJ) = 3 * 2 ^ 36 * 93555 * 2 := by
  rw [parStar_eq_betaStar, card_betaStar _ (nativeParabolic_le_stdGroup _),
    card_nativeParabolic_firstJ]

theorem conj_inl_fibT
    (γ : GStar) (d : Fin 5) :
    γ * SemidirectProduct.inl (fibT d) * γ⁻¹ =
      SemidirectProduct.inl (γ.left * fibT d * γ.left⁻¹) := by
  rw [conj_inl, apply_fibT]

theorem mem_centralizer_inl_fibT_iff
    {γ : GStar} {d : Fin 5} :
    γ ∈ Subgroup.centralizer {SemidirectProduct.inl (fibT d)} ↔
      (γ.left : ModGL Tag.E6 K) ∈ Subgroup.centralizer {(fibT d : ModGL Tag.E6 K)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul, conj_inl_fibT,
    SemidirectProduct.inl_injective.eq_iff, Subgroup.mem_centralizer_singleton_iff,
    ← mul_inv_eq_iff_eq_mul, ← Subtype.coe_inj]
  rfl

theorem fibVStar_le
    (d : Fin 5) :
    fibVStar d ≤ parStar firstJ ⊓ Subgroup.centralizer {SemidirectProduct.inl (fibT d)} := by
  intro γ hγ
  obtain ⟨hv, -⟩ := mem_fibVStar.1 hγ
  exact ⟨stdRadical_le_nativeParabolic' firstJ (fibV_le_stdRadical d hv),
    mem_centralizer_inl_fibT_iff.2 (fibV_le_centralizer d hv)⟩

theorem fibLStar_le
    (d : Fin 5) :
    fibLStar d ≤ parStar firstJ ⊓ Subgroup.centralizer {SemidirectProduct.inl (fibT d)} := by
  intro γ hγ
  exact ⟨(leviParabolic_le_nativeParabolic firstJ _).trans
      (nativeParabolic_mono (fibIF_subset d)) hγ,
    mem_centralizer_inl_fibT_iff.2 (fibLevi_le_centralizer d hγ)⟩

end CFSG.Monster.B.E6.StdF4
