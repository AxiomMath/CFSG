module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBRepAbstract
public import CFSG.LocalAnalysis.StandardType.GGTableBMarkedTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBTorusFix
public import CFSG.LocalAnalysis.StandardType.GGStdPosE6ThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.StandardType.RecipeExcLang CFSG.StandardType.NoOffE6Three
open CFSG.StandardType.LayerSixE CFSG.StandardType.TableBExc
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem entrywise_conj_rootDiagAutHom {K : Type} [Field K]
    (σ : K ≃+* K) (b : Fin Tag.E6.rank → Kˣ) :
    entrywiseAdjointAut Tag.E6 σ * rootDiagAutHom Tag.E6 K b *
        (entrywiseAdjointAut Tag.E6 σ)⁻¹ =
      rootDiagAutHom Tag.E6 K (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) := by
  have h_inv : (entrywiseAdjointAut Tag.E6 σ)⁻¹ = entrywiseAdjointAut Tag.E6 σ.symm := by
    show (entrywiseAdjointAutHom (τ := Tag.E6) (K := K) σ)⁻¹ =
      entrywiseAdjointAutHom (τ := Tag.E6) (K := K) σ.symm
    rw [← map_inv]
    rfl
  refine MulEquiv.ext fun g => Subtype.ext ?_
  calc ((entrywiseAdjointAut Tag.E6 σ * rootDiagAutHom Tag.E6 K b *
        (entrywiseAdjointAut Tag.E6 σ)⁻¹) g : ModGL Tag.E6 K)
      = (entrywiseAdjointAut Tag.E6 σ
          ((rootDiagAutHom Tag.E6 K b) ((entrywiseAdjointAut Tag.E6 σ)⁻¹ g)) :
            ModGL Tag.E6 K) := by
          rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = (Units.map (entrywiseHom σ.toRingHom))
          (((rootDiagAutHom Tag.E6 K b) ((entrywiseAdjointAut Tag.E6 σ)⁻¹ g)) :
            ModGL Tag.E6 K) := by
          rw [coe_entrywiseAdjointAut]
    _ = (Units.map (entrywiseHom σ.toRingHom))
          (rootDiagUnit Tag.E6 b * (((entrywiseAdjointAut Tag.E6 σ)⁻¹ g) : ModGL Tag.E6 K) *
            (rootDiagUnit Tag.E6 b)⁻¹) := by
          change (Units.map (entrywiseHom σ.toRingHom))
              (↑(((rootDiagAut Tag.E6 K b) ((entrywiseAdjointAut Tag.E6 σ)⁻¹ g)) :
                ModGL Tag.E6 K)) =
            (Units.map (entrywiseHom σ.toRingHom))
              (rootDiagUnit Tag.E6 b * (((entrywiseAdjointAut Tag.E6 σ)⁻¹ g) : ModGL Tag.E6 K) *
                (rootDiagUnit Tag.E6 b)⁻¹)
          rw [coe_rootDiagAut]
    _ = rootDiagUnit Tag.E6 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) *
          (g : ModGL Tag.E6 K) *
          (rootDiagUnit Tag.E6 (fun i => Units.map σ.toRingHom.toMonoidHom (b i)))⁻¹ := by
          rw [h_inv, coe_entrywiseAdjointAut, map_mul, map_mul, map_inv,
            units_map_entrywiseHom_rootDiagUnit_ringEquiv]
          rw [show (Units.map (entrywiseHom σ.toRingHom))
              ((Units.map (entrywiseHom σ.symm.toRingHom)) (g : ModGL Tag.E6 K)) =
              (g : ModGL Tag.E6 K) from by
            rw [← exactEntrywiseAut_apply (τ := Tag.E6) σ.symm (g : ModGL Tag.E6 K),
              ← exactEntrywiseAut_apply (τ := Tag.E6) σ
                (exactEntrywiseAut Tag.E6 σ.symm (g : ModGL Tag.E6 K))]
            exact MulEquiv.apply_symm_apply (exactEntrywiseAut Tag.E6 σ)
              (g : ModGL Tag.E6 K)]
    _ = ((rootDiagAutHom Tag.E6 K (fun i => Units.map σ.toRingHom.toMonoidHom (b i))) g :
            ModGL Tag.E6 K) := (coe_rootDiagAut _ g).symm

private theorem entrywiseAdjointAut_pow_fixes {K : Type} [Field K]
    {σ : K ≃+* K} {c : ℕ}
    (hσ : (entrywiseAdjointAut Tag.E6 σ) ^ 3 ^ c = 1) (x : K) :
    (σ ^ 3 ^ c) x = x := by
  have hpow : entrywiseAdjointAut Tag.E6 (σ ^ 3 ^ c) = 1 := by
    show entrywiseAdjointAutHom (τ := Tag.E6) (K := K) (σ ^ 3 ^ c) = 1
    rw [map_pow]
    exact hσ
  have i : Fin Tag.E6.rank := ⟨0, by decide⟩
  have hx := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) =>
    ((φ ⟨xUnit Tag.E6 K i x, xUnit_mem_adjointGroup i x⟩ : adjointGroup Tag.E6 K) :
      ModGL Tag.E6 K)) hpow
  rw [coe_entrywiseAdjointAut, units_map_entrywiseHom_xUnit, MulAut.one_apply] at hx
  exact xOp_injective i (congrArg Units.val hx)

private theorem entrywiseAdjointAut_commute_diag3 {K : Type} [Field K]
    {σ : K ≃+* K} {c : ℕ}
    (hσ : (entrywiseAdjointAut Tag.E6 σ) ^ 3 ^ c = 1)
    {ζ : Kˣ} (_hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (x : Fin Tag.E6.rank → ZMod 3) :
    entrywiseAdjointAut Tag.E6 σ * diag3 ζ hζ (Multiplicative.ofAdd x) =
      diag3 ζ hζ (Multiplicative.ofAdd x) * entrywiseAdjointAut Tag.E6 σ := by
  have hζK : (ζ : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hζ
  have hζ1K : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  set b := zetaHom ζ hζ (Multiplicative.ofAdd x) with hb
  have hb3 : ∀ i, (b i : K) ^ 3 = 1 := by
    intro i
    have h3 : b ^ 3 = 1 := by
      rw [hb, ← map_pow, pow_three_eq_one, map_one]
    have h3i : b i ^ 3 = 1 := by
      have := congrFun h3 i
      rwa [Pi.pow_apply, Pi.one_apply] at this
    rw [← Units.val_pow_eq_pow_val, h3i, Units.val_one]
  have hfix : ∀ i, σ (b i : K) = (b i : K) := fun i =>
    ringAut_apply_eq_of_pow_fixes Nat.prime_three hζ1K hζK
      (entrywiseAdjointAut_pow_fixes hσ ζ) (hb3 i)
  have hconj := entrywise_conj_rootDiagAutHom (K := K) σ b
  have hconj' : entrywiseAdjointAut Tag.E6 σ * rootDiagAutHom Tag.E6 K b *
      (entrywiseAdjointAut Tag.E6 σ)⁻¹ = rootDiagAutHom Tag.E6 K b := by
    rw [hconj]
    congr 1
    funext i
    exact Units.ext (hfix i)
  change entrywiseAdjointAut Tag.E6 σ * rootDiagAutHom Tag.E6 K b =
    rootDiagAutHom Tag.E6 K b * entrywiseAdjointAut Tag.E6 σ
  calc entrywiseAdjointAut Tag.E6 σ * rootDiagAutHom Tag.E6 K b =
        (entrywiseAdjointAut Tag.E6 σ * rootDiagAutHom Tag.E6 K b *
          (entrywiseAdjointAut Tag.E6 σ)⁻¹) * entrywiseAdjointAut Tag.E6 σ := by group
    _ = rootDiagAutHom Tag.E6 K b * entrywiseAdjointAut Tag.E6 σ := by rw [hconj']

private theorem inndiagConj_mem_inndiagAut {K : Type} [Field K] [Finite K]
    (w : inndiagGroup Tag.E6 K) :
    inndiagConj Tag.E6 K w ∈ LayerSixE.inndiagAut Tag.E6 K := by
  obtain ⟨b, j, hj, hw⟩ := mem_inndiagGroup.mp w.2
  have hw' : w = ⟨rootDiagUnit Tag.E6 b, rootDiagUnit_mem_inndiagGroup b⟩ *
      ⟨j, adjointGroup_le_inndiagGroup hj⟩ := Subtype.ext hw
  rw [hw', map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  · rw [show inndiagConj Tag.E6 K ⟨rootDiagUnit Tag.E6 b, _⟩ =
        rootDiagAutHom Tag.E6 K b from rfl]
    exact Subgroup.mem_sup_right ⟨b, rfl⟩
  · rw [inndiagConj_of_mem ⟨j, hj⟩]
    exact Subgroup.mem_sup_left ⟨⟨j, hj⟩, rfl⟩

private theorem modelRep_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) {σ : K ≃+* K} {c : ℕ}
    (hσ : (entrywiseAdjointAut Tag.E6 σ) ^ 3 ^ c = 1) :
    GGTableBFieldRepresentativeAt 3 (Set.range (inndiagConj Tag.E6 K))
      (entrywiseAdjointAut Tag.E6 σ) := by
  intro M _ _ L' E θ hE hpos
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) h3
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζ1u : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  have hζ1 : (ζ : K) ≠ 1 := fun h => hζ1u (Units.ext h)
  have hζK : (ζ : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hζ
  have hEab : CFSG.Open.IsElemAbelian 3 (E.subgroupOf (Subgroup.normalizer (L' : Set M))) := by
    refine ⟨IsMulCommutative.mk (Std.Commutative.mk
        (fun a b => Subtype.ext (Subtype.ext ?_))),
      fun x hx => Subtype.ext ?_⟩
    · have h := hpos.2.1.1.is_comm.comm
          ⟨a.1.1, Subgroup.mem_subgroupOf.mp a.2⟩
          ⟨b.1.1, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa only [Subgroup.coe_mul] using congrArg (fun z : ↥E => (z : M)) h
    · have h := hpos.2.1.2 x.1 (Subgroup.mem_subgroupOf.mp hx)
      simpa using h
  have hĒ : CFSG.Open.IsElemAbelian 3 (ggLAutImage L' θ E) := by
    refine ⟨IsMulCommutative.mk (Std.Commutative.mk (fun a b => ?_)),
      fun x hx => ?_⟩
    · obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hbeq⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← haeq, ← hbeq]
      have hcomm := congrArg (fun z : ↥(E.subgroupOf (Subgroup.normalizer (L' : Set M))) =>
        ggLAut L' θ z) (hEab.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      simpa only [Subgroup.coe_mul, map_mul] using hcomm
    · obtain ⟨x', hx', hxeq⟩ := Subgroup.mem_map.mp hx
      rw [← hxeq, ← map_pow, hEab.2 x' hx', map_one]
  have hĒD : ggLAutImage L' θ E ≤ LayerSixE.inndiagAut Tag.E6 K := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, hw⟩ := hpos.2.2.2.1 ⟨e.1, Subgroup.mem_subgroupOf.mp he⟩
    rw [← hw]
    exact inndiagConj_mem_inndiagAut w
  have h5 : 3 ^ 5 ≤ Nat.card (ggLAutImage L' θ E) :=
    pow_le_card_ggLAutImage hpos Nat.prime_three (TableBExc.ggTorusLift_adjoint_E6_three h3)
  obtain ⟨g, hg⟩ := exists_inner_conj_mem_diag_e6 h3 hĒD hĒ h5
  let S : Set (MulAut (adjointGroup Tag.E6 K)) :=
    Set.range fun e : E => ggLAut L' θ ⟨e, hE e.2⟩
  have hrepr := ggTableB_representative_of_conj_fixed (R := adjointGroup Tag.E6 K)
    (I := Set.range (inndiagConj Tag.E6 K))
    (fun ρ => ⟨⟨ρ, adjointGroup_le_inndiagGroup ρ.2⟩, inndiagConj_of_mem ρ⟩)
    (entrywiseAdjointAut Tag.E6 σ) S (MulAut.conj g) ⟨g, rfl⟩ ?_
  · obtain ⟨u, huI, hucomm⟩ := hrepr
    exact ⟨u, huI, fun e => hucomm _ ⟨e, rfl⟩⟩
  · rintro s ⟨e, rfl⟩
    have hmem : ggLAut L' θ ⟨e, hE e.2⟩ ∈ ggLAutImage L' θ E :=
      Subgroup.mem_map.mpr ⟨⟨e, hE e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩
    have hs3 : (ggLAut L' θ ⟨e, hE e.2⟩) ^ 3 = 1 := hĒ.2 _ hmem
    have hd := hg _ hmem
    have hd3 : (MulAut.conj g * ggLAut L' θ ⟨e, hE e.2⟩ * (MulAut.conj g)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hs3, mul_one, mul_inv_cancel]
    obtain ⟨x, hx⟩ := OutdiagE6.exists_diag3_of_mem_diag hζo hζ hd hd3
    rw [hx]
    exact entrywiseAdjointAut_commute_diag3 hσ hζo hζ hζ1u x

private def ChevRepOn (K : Type) [Field K] (S : (Fin Tag.E6.rank → ℤ) → Prop) : Prop :=
  ∀ f : MulAut (LargeEvenCenterQuot (MarkChev.chevH Tag.E6.cartan S K false)),
    GGTableBFieldSylowMark 3
      (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH Tag.E6.cartan S K false)) f →
    GGTableBFieldRepresentativeAt 3
      (markIDImage S K (MarkChev.chevH Tag.E6.cartan S K false)) f

private theorem ChevRepOn.of_eq {K : Type} [Field K] {S S' : (Fin Tag.E6.rank → ℤ) → Prop}
    (hS : S = S') (h : ChevRepOn K S) : ChevRepOn K S' := hS ▸ h

private theorem chevRepOn_isRoot {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) : ChevRepOn K (IsRoot Tag.E6) := by
  unfold ChevRepOn
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K),
      H = adjointGroup Tag.E6 K →
      (∀ f : MulAut (LargeEvenCenterQuot H),
        GGTableBFieldSylowMark 3 (RecipeFieldExcInn.markFieldImage (IsRoot Tag.E6) K H) f →
        GGTableBFieldRepresentativeAt 3 (markIDImage (IsRoot Tag.E6) K H) f) from
    key _ (chevH_false_eq_adjointGroup K Tag.E6)
  intro H hH
  subst hH
  intro f hf
  obtain ⟨σ, hσ⟩ := exists_eq_entrywise_of_mem_closure_markField hf.1
  obtain ⟨c, hc⟩ := hf.2.1
  have hσpow : (entrywiseAdjointAut Tag.E6 σ) ^ 3 ^ c = 1 := by
    rw [← hσ, ← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  have hI : ∀ φ ∈ markIDImage (IsRoot Tag.E6) K (adjointGroup Tag.E6 K),
      MulAut.congr (centerQuotEquivOfBot center_adjointGroup_eq_bot) φ ∈
        Set.range (inndiagConj Tag.E6 K) := by
    intro φ hφ
    obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hφ
    exact ⟨w, hw.symm⟩
  have hI' : ∀ φ' ∈ Set.range (inndiagConj Tag.E6 K),
      (MulAut.congr (centerQuotEquivOfBot center_adjointGroup_eq_bot)).symm φ' ∈
        markIDImage (IsRoot Tag.E6) K (adjointGroup Tag.E6 K) := by
    rintro φ' ⟨w, rfl⟩
    exact inndiagConj_mem_markID w
  refine ggTableBFieldRepresentativeAt_of_mulEquiv
    (centerQuotEquivOfBot center_adjointGroup_eq_bot) hI hI' ?_
  rw [show MulAut.congr (centerQuotEquivOfBot center_adjointGroup_eq_bot) f =
      entrywiseAdjointAut Tag.E6 σ from hσ]
  exact modelRep_E6 h3 hσpow

private theorem chevRep_E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    ∀ f : MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)),
      GGTableBFieldSylowMark 3 (LargeEvenChevFieldImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false)) f →
      GGTableBFieldRepresentativeAt 3 (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false)) f := by
  have h := (chevRepOn_isRoot (K := K) h3).of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL (LargeEvenCartanE 6) K),
      H = MarkChev.chevH (LargeEvenCartanE 6) (LargeEvenIsRoot (LargeEvenCartanE 6)) K false →
      (∀ f : MulAut (LargeEvenCenterQuot H),
        GGTableBFieldSylowMark 3 (LargeEvenChevFieldImage (LargeEvenCartanE 6) K H) f →
        GGTableBFieldRepresentativeAt 3 (LargeEvenChevIDImage (LargeEvenCartanE 6) K H) f) from
    key _ (largeEvenChevH_eq (LargeEvenCartanE 6) K false)
  intro H hH
  subst hH
  rw [RecipeExcLang.largeEvenChevIDImage_eq]
  exact h

theorem fieldRepresentative_E6_three
    {p : ℕ} {lab : LargeEvenLabel} (hrow : GGL48TBE6Row p lab ∧ p = 3) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f := by
  rcases hrow with ⟨⟨rowtag, rowdvd⟩, hp3⟩
  obtain ⟨t, l, n⟩ := lab
  dsimp only at rowtag
  subst rowtag
  subst hp3
  intro Q hQ
  refine recipeChevalley_and (P := fun R _ I F =>
      ∀ f : MulAut R, GGTableBFieldSylowMark 3 F f → GGTableBFieldRepresentativeAt 3 I f) ?_ hQ
  intro K _ _ hK
  have h3K : 3 ∣ Nat.card K - 1 := by rw [hK]; exact rowdvd
  have : CharP K 2 := charP_two_of_card hK
  exact chevRep_E6 h3K

end CFSG.StandardType
