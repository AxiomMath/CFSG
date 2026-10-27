module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBRepAbstract
public import CFSG.LocalAnalysis.StandardType.GGTableBMarkedTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBPositionToralExc
public import CFSG.LocalAnalysis.StandardType.GGStdPosE6ThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RecipeExcLang TableBExc

private theorem inndiagConj_rootDiagUnit
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ) :
    inndiagConj .E6 K ⟨rootDiagUnit .E6 a, rootDiagUnit_mem_inndiagGroup a⟩ =
      rootDiagAutHom .E6 K a := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_inndiagConj]
  rfl

private theorem conj_rootDiagUnit_eq_rootDiagAutHom
    {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (ha : rootDiagUnit .E6 a ∈ adjointGroup .E6 K) :
    MulAut.conj (⟨rootDiagUnit .E6 a, ha⟩ : adjointGroup .E6 K) =
      rootDiagAutHom .E6 K a := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rfl

private theorem conj_mem_diag_of_mem_torusPow
    {K : Type} [Field K] {p : ℕ} {v : adjointGroup .E6 K}
    (hv : v ∈ TableBExc.torusPow .E6 K p) :
    MulAut.conj v ∈ (rootDiagAutHom .E6 K).range := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_torusPow.mp hv).1
  have hmem : rootDiagUnit .E6 a ∈ adjointGroup .E6 K :=
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
      (by rw [← ha]; exact (mem_torusPow.mp hv).1)
  have hv' : v = ⟨rootDiagUnit .E6 a, hmem⟩ := Subtype.ext ha
  rw [hv']
  exact ⟨a, (conj_rootDiagUnit_eq_rootDiagAutHom a hmem).symm⟩

private theorem inndiagConj_eq_conj_mul_diag
    {K : Type} [Field K] [Finite K] (w : inndiagGroup .E6 K) :
    ∃ ρ : adjointGroup .E6 K, ∃ δ ∈ (rootDiagAutHom .E6 K).range,
      inndiagConj .E6 K w = MulAut.conj ρ * δ := by
  obtain ⟨b, j, hj, hwv⟩ := w.2
  have hw : w = ⟨rootDiagUnit .E6 b, rootDiagUnit_mem_inndiagGroup b⟩ *
      ⟨j, adjointGroup_le_inndiagGroup hj⟩ := by
    apply Subtype.ext
    simpa using hwv
  have hmem : inndiagConj .E6 K ⟨j, adjointGroup_le_inndiagGroup hj⟩ =
      MulAut.conj (⟨j, hj⟩ : adjointGroup .E6 K) :=
    inndiagConj_of_mem (g := ⟨j, hj⟩)
  rw [hw, map_mul, inndiagConj_rootDiagUnit, hmem]
  refine ⟨rootDiagAutHom .E6 K b ⟨j, hj⟩, rootDiagAutHom .E6 K b, ⟨b, rfl⟩, ?_⟩
  have hconj : rootDiagAutHom .E6 K b * MulAut.conj (⟨j, hj⟩ : adjointGroup .E6 K) =
      MulAut.conj (rootDiagAutHom .E6 K b ⟨j, hj⟩) * rootDiagAutHom .E6 K b := by
    have h1 : rootDiagAutHom .E6 K b * MulAut.conj (⟨j, hj⟩ : adjointGroup .E6 K) *
        (rootDiagAutHom .E6 K b)⁻¹ =
        MulAut.conj (rootDiagAutHom .E6 K b ⟨j, hj⟩) := by
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    calc rootDiagAutHom .E6 K b * MulAut.conj (⟨j, hj⟩ : adjointGroup .E6 K)
        = rootDiagAutHom .E6 K b * MulAut.conj (⟨j, hj⟩ : adjointGroup .E6 K) *
            (rootDiagAutHom .E6 K b)⁻¹ * rootDiagAutHom .E6 K b := by group
      _ = MulAut.conj (rootDiagAutHom .E6 K b ⟨j, hj⟩) * rootDiagAutHom .E6 K b := by rw [h1]
  exact hconj

private theorem range_inndiagConj_le_inndiagAut
    {K : Type} [Field K] [Finite K] :
    Set.range (inndiagConj .E6 K) ⊆ LayerSixE.inndiagAut .E6 K := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨b, j, hj, hwv⟩ := w.2
  have hw : w = ⟨rootDiagUnit .E6 b, rootDiagUnit_mem_inndiagGroup b⟩ *
      ⟨j, adjointGroup_le_inndiagGroup hj⟩ := by
    apply Subtype.ext
    simpa using hwv
  have hmem : inndiagConj .E6 K ⟨j, adjointGroup_le_inndiagGroup hj⟩ =
      MulAut.conj (⟨j, hj⟩ : adjointGroup .E6 K) :=
    inndiagConj_of_mem (g := ⟨j, hj⟩)
  rw [hw, map_mul, inndiagConj_rootDiagUnit, hmem]
  exact (LayerSixE.inndiagAut .E6 K).mul_mem
    (Subgroup.mem_sup_right ⟨b, rfl⟩) (Subgroup.mem_sup_left ⟨⟨j, hj⟩, rfl⟩)

private theorem absorption_adjoint
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTableBAbsorptionAt p (Set.range (inndiagConj .E6 K)) := by
  intro M _ _ L' E θ hE hpos i hi
  have hD : ∀ x ∈ (rootDiagAutHom .E6 K).range, ∀ y ∈ (rootDiagAutHom .E6 K).range,
      x * y = y * x := by
    intro x hx y hy
    have h := OutdiagE6.diag_conj_eq hx hy
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h]
  have hI : ∀ i ∈ Set.range (inndiagConj .E6 K), ∃ ρ : adjointGroup .E6 K,
      ∃ δ ∈ (rootDiagAutHom .E6 K).range, i = MulAut.conj ρ * δ := by
    rintro i ⟨w, rfl⟩
    exact inndiagConj_eq_conj_mul_diag w
  have hgoal : ∀ c : MulAut (adjointGroup .E6 K),
      c ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range →
      (∀ s ∈ Set.range (fun e : E => ggLAut L' θ ⟨e, hE e.2⟩),
        c * s * c⁻¹ ∈ (rootDiagAutHom .E6 K).range) →
      ∃ ρ : adjointGroup .E6 K, ∃ t : MulAut (adjointGroup .E6 K),
        i = MulAut.conj ρ * t ∧ ∀ e : E, Commute t (ggLAut L' θ ⟨e, hE e.2⟩) := by
    intro c hc hS
    obtain ⟨ρ, t, hρt, htC⟩ := ggTableB_absorption_of_conj_diag (rootDiagAutHom .E6 K).range
      hD hI (Set.range fun e : E => ggLAut L' θ ⟨e, hE e.2⟩) c hc hS i hi
    exact ⟨ρ, t, hρt, fun e => htC _ (Set.mem_range_self e)⟩
  by_cases hp3 : p = 3
  · have h3 : 3 ∣ Nat.card K - 1 := by rw [← hp3]; exact hpq
    have hĒ𝒟 : ggLAutImage L' θ E ≤ LayerSixE.inndiagAut .E6 K := by
      rintro a ⟨x, hx, rfl⟩
      have hx' : x = (⟨(x.1 : M), hE (Subgroup.mem_subgroupOf.mp hx)⟩ :
          Subgroup.normalizer (L' : Set M)) := by
        apply Subtype.ext
        rfl
      rw [hx']
      exact range_inndiagConj_le_inndiagAut
        (hpos.2.2.2.1 ⟨(x.1 : M), Subgroup.mem_subgroupOf.mp hx⟩)
    have hEA : IsElemAbelian p E := hpos.2.1
    have hĒp : IsElemAbelian p (ggLAutImage L' θ E) := by
      have h := isElemAbelian_range (fun a b => Subtype.ext (Subtype.ext
          (IsElemAbelian.comm hEA (Subgroup.mem_subgroupOf.mp a.2)
            (Subgroup.mem_subgroupOf.mp b.2))))
        (fun a => Subtype.ext (Subtype.ext (hEA.2 _ (Subgroup.mem_subgroupOf.mp a.2))))
        ((ggLAut L' θ).comp (E.subgroupOf (Subgroup.normalizer (L' : Set M))).subtype)
      simpa only [ggLAutImage, MonoidHom.range_comp, Subgroup.range_subtype] using h
    have hĒ : IsElemAbelian 3 (ggLAutImage L' θ E) := by
      rw [hp3] at hĒp
      exact hĒp
    have hL : GGTorusLift p 5 (adjointGroup .E6 K) := by
      rw [hp3]
      exact TableBExc.ggTorusLift_adjoint_E6_three h3
    have hĒ5 : 3 ^ 5 ≤ Nat.card (ggLAutImage L' θ E) := by
      have h := pow_le_card_ggLAutImage hpos hp hL
      rwa [hp3] at h
    obtain ⟨g, hg⟩ := exists_inner_conj_mem_diag_e6 h3 hĒ𝒟 hĒ hĒ5
    exact hgoal (MulAut.conj g) ⟨g, rfl⟩ (fun s hs => by
      obtain ⟨e, rfl⟩ := hs
      exact hg _ ⟨⟨e, hE e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩)
  · obtain ⟨g, hg⟩ := exists_position_conj_torusPow_E6 hp hp2 hp3 hpq hpos
    exact hgoal (MulAut.conj g) ⟨g, rfl⟩ (fun s hs => by
      obtain ⟨e, rfl⟩ := hs
      obtain ⟨v, hv, hveq⟩ := hg e
      dsimp only
      rw [hveq]
      have h1 : MulAut.conj g * MulAut.conj (g⁻¹ * v * g) * (MulAut.conj g)⁻¹ =
          MulAut.conj v := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rw [h1]
      exact conj_mem_diag_of_mem_torusPow hv)

private theorem absorption_markID
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTableBAbsorptionAt p (markIDImage (IsRoot .E6) K (adjointGroup .E6 K)) := by
  refine ggTableBAbsorptionAt_of_mulEquiv
    (centerQuotEquivOfBot
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := K)))
    (fun φ hφ => by
      obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hφ
      exact ⟨w, hw.symm⟩) (absorption_adjoint hp hp2 hpq)

private def AbsorptionChevOn (K : Type) [Field K]
    (S : (Fin Tag.E6.rank → ℤ) → Prop) (p : ℕ) : Prop :=
  GGTableBAbsorptionAt p (markIDImage S K (MarkChev.chevH Tag.E6.cartan S K false))

private theorem AbsorptionChevOn.of_eq {K : Type} [Field K]
    {S S' : (Fin Tag.E6.rank → ℤ) → Prop} {p : ℕ} (hS : S = S')
    (h : AbsorptionChevOn K S p) : AbsorptionChevOn K S' p := hS ▸ h

private theorem absorption_chevOn_isRoot
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    AbsorptionChevOn K (IsRoot .E6) p := by
  unfold AbsorptionChevOn
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot .E6) K),
      H = adjointGroup .E6 K → GGTableBAbsorptionAt p (markIDImage (IsRoot .E6) K H) from
    key _ (chevH_false_eq_adjointGroup K .E6)
  intro H hH
  subst hH
  exact absorption_markID hp hp2 hpq

private theorem absorption_chevOn_largeEven
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    AbsorptionChevOn K (LargeEvenIsRoot Tag.E6.cartan) p :=
  (absorption_chevOn_isRoot hp hp2 hpq).of_eq (largeEvenIsRoot_eq_isRoot .E6).symm

private theorem absorption_chev
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTableBAbsorptionAt p
      (LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) := by
  have h := absorption_chevOn_largeEven (K := K) hp hp2 hpq
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.E6.cartan K),
      H = MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false →
      GGTableBAbsorptionAt p (LargeEvenChevIDImage Tag.E6.cartan K H) from
    key _ (largeEvenChevH_eq Tag.E6.cartan K false)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

theorem absorption_E6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBE6Row p lab) :
    LargeEvenLabelAll lab fun _ _ I _ => GGTableBAbsorptionAt p I := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨-, hd⟩ := hrow
    have h1 : 2 ∣ 2 ^ lab.n := dvd_pow_self 2 (by have := hlab.1; omega)
    have h2 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    omega
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hdvd⟩ := hrow
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeChevalley_and (P := fun R _ I _ => GGTableBAbsorptionAt p I)
    (fun K _ _ hK => by
      have hchar : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hdvd
      exact absorption_chev (K := K) hp hp2 hpq) hQ

end CFSG.StandardType
