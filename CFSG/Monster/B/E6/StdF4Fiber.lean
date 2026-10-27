module

public import CFSG.Monster.B.E6.StdF4FiberCore
public import CFSG.Monster.B.E6.StdF4FiberSets

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar parLeft thetaFirst)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical Matrix Module

theorem fibV_eq_inf_stdGroup
    (d : Fin 5) :
    fibV d = rootSpan TwistTag.E6.tag K (fibRoots d) ⊓ stdGroup :=
  le_antisymm (le_inf inf_le_left (fibV_le_stdGroup d))
    (inf_le_inf_left _ (graphFixedRootGroup_le _ _ _))

theorem fibOrbit_eq
    (d : Fin 5) :
    fibOrbit d = SemidirectProduct.inl '' levPoints (repLevel d) := by
  rw [fibOrbit, conjOrbit_parStar_tW, level_fibWord]

theorem exists_mem_fibOrbit
    {x : stdGroup} (hx : x ∈ rootClass) :
    ∃ d : Fin 5, SemidirectProduct.inl x ∈ fibOrbit d := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff _).1 hx
  obtain ⟨d, hd⟩ := exists_repLevel g
  exact ⟨d, by rw [fibOrbit_eq, ← hd]; exact ⟨_, rootMap_mem_levPoints g, rfl⟩⟩

theorem exists_eq_conj_of_mem_fibOrbit
    {d : Fin 5} {x : GStar} (hx : x ∈ fibOrbit d) :
    ∃ u ∈ radStar, ∃ l ∈ leviStar,
      x = u * l * SemidirectProduct.inl (fibT d) * (u * l)⁻¹ := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  obtain ⟨u, hu, l, hl, e⟩ := exists_mul_of_mem_parStar ⟨γ, hγ⟩
  exact ⟨u, hu, l, hl, by rw [← e]⟩

theorem fibLStar_of_JJ
    {d : Fin 5} (hd : d = 0 ∨ d = 4) : fibLStar d = leviStar :=
  SetLike.ext fun γ => by rw [mem_betaStar, mem_leviStar, fibLevi_of_JJ hd]

theorem standard_first_parabolic_root_orbit_radical_fibers :
    Nat.card (stdRadical firstJ) = 2 ^ 21 ∧
    CFSG.pCore 2 (parStar firstJ) = radStar.subgroupOf (parStar firstJ) ∧
    (∀ γ : GStar, γ ∈ radStar ↔ (γ.left : ModGL Tag.E6 K) ∈ stdRadical firstJ ∧ γ.right = 1) ∧
    (∀ γ : GStar, γ ∈ leviStar ↔ (γ.left : ModGL Tag.E6 K) ∈ stdLevi firstJ) ∧
    fibY = ![![1, 2, 2, 3, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 0, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0],
      ![-1, -2, -2, -3, -2, -1]] ∧
    fibIF = ![{1, 2, 3}, {2, 3}, {1, 2}, {2, 3}, {1, 2, 3}] ∧
    (∀ x ∈ rootClass, ∃ d : Fin 5, SemidirectProduct.inl x ∈ fibOrbit d) ∧
    (∀ d : Fin 5,
      (fibT d : ModGL Tag.E6 K) = pinnedX Tag.E6 K (fibYE d) 1 ∧
      fibOrbit d = conjOrbit (parStar firstJ) (SemidirectProduct.inl (fibT d)) ∧
      fibOrbit d = SemidirectProduct.inl '' levPoints (repLevel d) ∧
      repLevel d = ![2, 1, 0, -1, -2] d ∧
      (fibOrbit d).ncard = ![1, 1782, 44352, 1824768, 2097152] d ∧
      (∀ x ∈ fibOrbit d, (conjOrbit radStar x).ncard = ![1, 2, 64, 2048, 2097152] d) ∧
      fibRoots d = {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ 0 < α (i6 1) ∧
        0 ≤ α ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ fibYL d)} ∧
      fibV d = rootSpan TwistTag.E6.tag K (fibRoots d) ⊓ stdGroup ∧
      (∀ γ : GStar, γ ∈ fibVStar d ↔ (γ.left : ModGL Tag.E6 K) ∈ fibV d ∧ γ.right = 1) ∧
      (∀ γ : GStar, γ ∈ fibLStar d ↔
        (γ.left : ModGL Tag.E6 K) ∈ leviParabolic firstJ (fibIF d : Set (Fin 4))) ∧
      leviParabolic firstJ (fibIF d : Set (Fin 4)) = Subgroup.closure
        ((stdLeviBorel firstJ : Set (ModGL Tag.E6 K)) ∪ nativeRep '' (fibIF d : Set (Fin 4))) ∧
      parStar firstJ ⊓ Subgroup.centralizer {SemidirectProduct.inl (fibT d)} =
        fibVStar d ⊔ fibLStar d ∧
      fibVStar d ⊓ fibLStar d = ⊥ ∧
      parStar firstJ ⊓ Subgroup.centralizer {SemidirectProduct.inl (fibT d)} ≤
        Subgroup.normalizer (fibVStar d : Set GStar) ∧
      (∀ γ : GStar, γ ∈ inlLevi d ↔
        (γ.left : ModGL Tag.E6 K) ∈ leviParabolic firstJ (fibIF d : Set (Fin 4)) ∧
          γ.right = 1) ∧
      (∀ γ : GStar, γ ∈ betaSub ↔ γ.left = 1) ∧
      fibLStar d = inlLevi d ⊔ betaSub ∧ inlLevi d ⊓ betaSub = ⊥ ∧
      fibLStar d ≤ Subgroup.normalizer (inlLevi d : Set GStar) ∧
      Nat.card (fibV d) = 2 ^ ![21, 20, 15, 10, 0] d ∧
      (∀ x ∈ fibOrbit d, ∃ u ∈ radStar, ∃ l ∈ leviStar,
        x = u * l * SemidirectProduct.inl (fibT d) * (u * l)⁻¹) ∧
      (∀ u ∈ radStar, ∀ (l : GStar) (hl : l ∈ leviStar),
        fibCoset d (u * l * SemidirectProduct.inl (fibT d) * (u * l)⁻¹) =
          QuotientGroup.mk (⟨l, hl⟩ : leviStar)) ∧
      (∀ x ∈ fibOrbit d, ∀ y ∈ fibOrbit d,
        fibCoset d x = fibCoset d y ↔ y ∈ conjOrbit radStar x)) ∧
    (∀ d : Fin 5, d = 0 ∨ d = 4 → fibLStar d = leviStar ∧
      ∀ x ∈ fibOrbit d, ∀ y ∈ fibOrbit d, y ∈ conjOrbit radStar x) ∧
    (∀ (k : Fin 3) (S : Submodule K (Fin 6 → K)), S ∈ isoSubs k ↔
      finrank K S = k + 1 ∧ ∀ v ∈ S, ∀ w ∈ S, herm6 v w = 0) ∧
    (isoSubs 2).ncard = 891 ∧ (isoSubs 0).ncard = 693 ∧
    fibKd 1 = 2 ∧ fibKd 2 = 0 ∧ fibKd 3 = 2 ∧
    (∀ d : Fin 5, d = 1 ∨ d = 2 ∨ d = 3 →
      fibSub d '' fibOrbit d = isoSubs (fibKd d) ∧
      (∀ x ∈ fibOrbit d, ∀ y ∈ fibOrbit d, fibSub d x = fibSub d y ↔ y ∈ conjOrbit radStar x) ∧
      (∀ γ : parStar firstJ,
        fibSub d ((γ : GStar) * SemidirectProduct.inl (fibT d) * (γ : GStar)⁻¹) =
          (residueFlag (QuotientGroup.mk (parLeft γ))).sub (fibKd d)) ∧
      (∀ γ γ' : parStar firstJ,
        fibSub d ((γ' : GStar) * ((γ : GStar) * SemidirectProduct.inl (fibT d) *
          (γ : GStar)⁻¹) * (γ' : GStar)⁻¹) =
          (thetaFirst γ' • residueFlag (QuotientGroup.mk (parLeft γ))).sub (fibKd d))) := by
  refine ⟨card_stdRadical_firstJ, pCore_parStar, fun _ => mem_radStar, fun _ => mem_leviStar,
    rfl, rfl, fun x hx => exists_mem_fibOrbit hx, fun d => ?_, fun d hd =>
      ⟨fibLStar_of_JJ hd, fun x hx y hy => mem_conjOrbit_radStar_of_JJ hd hx hy⟩,
    fun _ _ => Iff.rfl, ncard_isoSubs_two, ncard_isoSubs_zero, rfl, rfl, rfl,
    fun d hd => ⟨image_fibSub hd, fun x hx y hy => fibSub_eq_iff hd hx hy,
      fun γ => fibSub_conj hd γ, fun γ γ' => fibSub_conj_conj hd γ γ'⟩⟩
  refine ⟨coe_fibT d, rfl, fibOrbit_eq d, ?_, ?_, fun x hx => ?_, rfl, fibV_eq_inf_stdGroup d,
    fun _ => mem_fibVStar, fun _ => mem_betaStar, rfl, fibCent_eq_sup d, fibVStar_inf_fibLStar d,
    fibCent_le_normalizer d, fun _ => mem_inlLevi, fun _ => mem_betaSub, fibLStar_eq_sup d,
    inlLevi_inf_betaSub d, fibLStar_le_normalizer d, ?_,
    fun x hx => exists_eq_conj_of_mem_fibOrbit hx, fun u hu l hl => fibCoset_mul d hu hl,
    fun x hx y hy => fibCoset_eq_iff hx hy⟩
  · fin_cases d <;> rfl
  · rw [ncard_fibOrbit]
    fin_cases d <;> rfl
  · rw [ncard_conjOrbit_radStar hx]
    fin_cases d <;> rfl
  · rw [card_fibV]
    fin_cases d <;> rfl

end CFSG.Monster.B.E6.StdF4
