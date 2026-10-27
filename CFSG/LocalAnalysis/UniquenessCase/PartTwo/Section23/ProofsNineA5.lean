module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineNotSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineASem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdj
public import CFSG.LocalAnalysis.UniquenessCase.UC1K41
public import CFSG.GroupTheory.PerfectTwoQuotient
public import CFSG.Quasithin.SteinbergBMSimpleCoreQuotientKernel

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev SU44K {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    Subgroup G :=
  Hinf (D.M ⊓ c.L)

private noncomputable abbrev SU44N {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (d : S23_9_A0Data D Ch c) : Subgroup G :=
  barPreimage D.M d.rep.ker

private noncomputable abbrev SU44Y {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (Kstar : Subgroup ↥(c.H hV)) (N : Subgroup G) :
    Subgroup ↥(c.H hV) :=
  (Kstar.comap (c.phiL hV) ⊓ N.subgroupOf c.L).map (c.phiL hV)

namespace Ctx23L

theorem exists_lift_elemAbelian {D : Data G} {Ch : Choice2011 G} {p : ℕ} [Fact p.Prime]
    (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hker : ¬ p ∣ Nat.card (c.phiL hV).ker)
    {E : Subgroup ↥(c.H hV)} (hE : IsElemAbelian p E) :
    ∃ El : Subgroup ↥c.L, IsElemAbelian p El ∧ El ≤ E.comap (c.phiL hV) ∧
      El.map (c.phiL hV) = E ∧ El ⊓ (c.phiL hV).ker = ⊥ := by
  obtain ⟨A, hAp, hAle, hAmap, hAdisj⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker (p := p)
      (c.phiL hV) (c.phiL_surjective hV) hker hE.isPGroup
  have hinj : ∀ x y : A, c.phiL hV (x : c.L) = c.phiL hV (y : c.L) → x = y := by
    intro x y hxy
    have hmem : (x : c.L) * (y : c.L)⁻¹ ∈ A ⊓ (c.phiL hV).ker := by
      refine ⟨A.mul_mem x.2 (A.inv_mem y.2), ?_⟩
      change c.phiL hV ((x : c.L) * (y : c.L)⁻¹) = 1
      rw [map_mul, map_inv]
      simpa using congrArg (fun z => z * (c.phiL hV (y : c.L))⁻¹) hxy
    rw [hAdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp hmem)
  have hcomm : IsMulCommutative A := IsMulCommutative.of_comm fun (x y : A) => by
    have hxE : c.phiL hV (x : c.L) ∈ E := by
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem _ x.2
    have hyE : c.phiL hV (y : c.L) ∈ E := by
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem _ y.2
    letI : IsMulCommutative E := hE.1
    refine hinj (x * y) (y * x) ?_
    change c.phiL hV ((x : c.L) * (y : c.L)) = c.phiL hV ((y : c.L) * (x : c.L))
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' ⟨c.phiL hV (x : c.L), hxE⟩
      ⟨c.phiL hV (y : c.L), hyE⟩)
  have hexp : ∀ x ∈ A, x ^ p = 1 := by
    intro x hx
    have hxA : (⟨x ^ p, A.pow_mem hx p⟩ : A) = 1 := by
      refine hinj ⟨x ^ p, A.pow_mem hx p⟩ 1 ?_
      change c.phiL hV (x ^ p) = c.phiL hV 1
      rw [map_pow, map_one]
      have hxE : c.phiL hV x ∈ E := by
        rw [← hAmap]
        exact Subgroup.mem_map_of_mem _ hx
      exact hE.2 (c.phiL hV x) hxE
    simpa using congrArg Subtype.val hxA
  exact ⟨A, ⟨hcomm, hexp⟩, hAle, hAmap, hAdisj⟩

theorem exists_SU44Estar {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hSU44 : S23_9_SU44 D Ch c hV) (hKSU : KSU44) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    let ℓ : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
    let Pℓ : Subgroup ↥(c.H hV) :=
      MulAction.stabilizer ↥(c.H hV) ((ℓ : Subgroup (c.W hV)) : Set (c.W hV))
    let Kstar : Subgroup ↥(c.H hV) := Hinf Pℓ
    ∃ E : Subgroup ↥(c.H hV), IsElemAbelian 3 E ∧ Nat.card ↥E = 9 ∧ E ≤ Pℓ ∧
      E ⊓ (fixingSubgroupOf ↥(c.H hV) (c.W hV) ((ℓ : Subgroup (c.W hV)) : Set (c.W hV))) =
        E ⊓ Kstar ∧
      Nat.card ↥(E ⊓ Kstar) = 3 ∧
      (∃ k ∈ Kstar, ∃ e ∈ E ⊓ Kstar, e * k ≠ k * e) ∧
      ∃ w0 : ↥(c.H hV), w0 ∉ Pℓ ∧ ∀ e ∈ E, w0 * e * w0⁻¹ = e⁻¹ := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let ℓ : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
  let Pℓ : Subgroup ↥(c.H hV) :=
    MulAction.stabilizer ↥(c.H hV) ((ℓ : Subgroup (c.W hV)) : Set (c.W hV))
  let Kstar : Subgroup ↥(c.H hV) := Hinf Pℓ
  obtain ⟨E, hE, hcard, hEnorm, hEfix, hintcard, hnoncentral, w0, hw0, hinv⟩ :=
    hKSU (c.W hV) (c.H hV) hSU44.1 hSU44.2.1 (c.sylowStar hV)
  refine ⟨E, hE, hcard, ?_, ?_, ?_, ?_, w0, ?_, hinv⟩
  · have h := CFSG.GroupTheory.le_stabilizer_fixedPointSubgroup_of_le_normalizer
      (X := ↥(c.H hV)) (M := c.W hV) (S := c.sylowStar hV) (K := E) hEnorm
    exact h
  · simpa only [Pℓ, Kstar, ℓ] using hEfix
  · simpa only [Pℓ, Kstar, ℓ] using hintcard
  · simpa only [Pℓ, Kstar, ℓ] using hnoncentral
  · simpa only [Pℓ, ℓ] using hw0

private theorem exists_SU44Lift_Etil {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (h1930 : H1930 D)
    (hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {E : Subgroup ↥(c.H hV)} (hE : IsElemAbelian 3 E) (hcard : Nat.card ↥E = 9)
    {Pℓ : Subgroup ↥(c.H hV)} (hP : E ≤ Pℓ)
    (hmapPℓ : ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = Pℓ)
    (hker_not : ¬ 3 ∣ Nat.card (c.phiL hV).ker) :
    ∃ (El : Subgroup ↥c.L) (Etil : Subgroup G), IsElemAbelian 3 El ∧
      El ≤ E.comap (c.phiL hV) ∧ El.map (c.phiL hV) = E ∧
      El ⊓ (c.phiL hV).ker = ⊥ ∧
      IsElemAbelian 3 Etil ∧ Nat.card ↥Etil = 9 ∧ Etil ≤ D.M ∧ Etil ≤ c.L ∧
      Etil.subgroupOf c.L = El ∧
      (Etil.subgroupOf c.L).map (c.phiL hV) = E ∧
      (Etil.subgroupOf c.L) ⊓ (c.phiL hV).ker = ⊥ := by
  obtain ⟨El, hEl_el, hEl_le, hEl_map, hEl_ker⟩ :=
    c.exists_lift_elemAbelian hV hker_not (E := E) hE
  have hO2_le : (c.phiL hV).ker ≤ (D.M ⊓ c.L).subgroupOf c.L := by
    rw [hker_eq]
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, x.2⟩
    exact s23_9_O2L_of (D := D) (Ch := Ch) h1930 c (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hElM : El ≤ (D.M ⊓ c.L).subgroupOf c.L := by
    refine hEl_le.trans ?_
    calc E.comap (c.phiL hV) ≤ Pℓ.comap (c.phiL hV) := Subgroup.comap_mono hP
      _ = (((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV)).comap (c.phiL hV) := by
          rw [hmapPℓ]
      _ = (D.M ⊓ c.L).subgroupOf c.L ⊔ (c.phiL hV).ker := Subgroup.comap_map_eq _ _
      _ ≤ (D.M ⊓ c.L).subgroupOf c.L := sup_le le_rfl hO2_le
  let Etil : Subgroup G := El.map c.L.subtype
  have hEtilM : Etil ≤ D.M := by
    have h1 := (Subgroup.map_subtype_le_map_subtype).mpr hElM
    have h2 : ((D.M ⊓ c.L).subgroupOf c.L).map c.L.subtype = D.M ⊓ c.L :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_right
    rw [h2] at h1
    exact h1.trans inf_le_left
  have hEtilL : Etil ≤ c.L := Subgroup.map_subtype_le El
  have hEtil_el : IsElemAbelian 3 Etil := hEl_el.map c.L.subtype
  have hEl_card : Nat.card ↥El = 9 := by
    have h := CFSG.card_map_eq_card_of_inf_ker_eq_bot (f := c.phiL hV) (J := El) hEl_ker
    rw [hEl_map] at h
    exact h.symm.trans hcard
  have hEtil_card : Nat.card ↥Etil = 9 := by
    rw [show Etil = El.map c.L.subtype from rfl,
      Subgroup.card_map_of_injective c.L.subtype_injective]
    exact hEl_card
  have hEtil_sub : Etil.subgroupOf c.L = El := by
    apply Subgroup.map_injective c.L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le El)]
  refine ⟨El, Etil, hEl_el, hEl_le, hEl_map, hEl_ker, hEtil_el, hEtil_card, hEtilM,
    hEtilL, hEtil_sub, ?_, ?_⟩
  · rw [hEtil_sub]; exact hEl_map
  · rw [hEtil_sub]; exact hEl_ker

private theorem SU44_w_lift_decomp {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {E : Subgroup ↥(c.H hV)} {El : Subgroup ↥c.L}
    (hE : IsElemAbelian 3 E) (hEl_el : IsElemAbelian 3 El)
    (hEl_le : El ≤ E.comap (c.phiL hV)) (hEl_map : El.map (c.phiL hV) = E)
    (hEl_ker : El ⊓ (c.phiL hV).ker = ⊥)
    (hker_not : ¬ 3 ∣ Nat.card (c.phiL hV).ker)
    {w0 : ↥(c.H hV)} (hw0inv : ∀ e ∈ E, w0 * e * w0⁻¹ = e⁻¹) :
    ∃ (n m : ↥c.L), m ∈ Subgroup.normalizer (El : Set ↥c.L) ∧
      c.phiL hV m = (c.phiL hV n)⁻¹ * w0 ∧
      (∀ y ∈ E, (c.phiL hV n)⁻¹ * y * c.phiL hV n = y) := by
  have hw0_norm : w0 ∈ Subgroup.normalizer (E : Set ↥(c.H hV)) :=
    CFSG.GroupTheory.mem_normalizer_of_conj_eq_inv hw0inv
  obtain ⟨g, hg⟩ := c.phiL_surjective hV w0
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 El (E.comap (c.phiL hV)) :=
    CFSG.GroupTheory.isSylowOf_comap_of_map_eq_of_coprime_ker (p := 3) (c.phiL hV)
      (c.phiL_surjective hV) hker_not hEl_le hEl_map hEl_ker hEl_el.isPGroup
  obtain ⟨n, hnE, m, hm_norm, hg_eq⟩ :=
    CFSG.GroupTheory.exists_mul_mem_comap_and_normalizer (p := 3) (c.phiL hV) hEl_le hAsyl
      (by rw [hg]; exact hw0_norm)
  have hphi_m : c.phiL hV m = (c.phiL hV n)⁻¹ * w0 := by
    have h1 : w0 = c.phiL hV n * c.phiL hV m := by
      calc w0 = c.phiL hV g := hg.symm
        _ = c.phiL hV (n * m) := by rw [hg_eq]
        _ = c.phiL hV n * c.phiL hV m := map_mul _ _ _
    calc c.phiL hV m = (c.phiL hV n)⁻¹ * (c.phiL hV n * c.phiL hV m) := by group
      _ = (c.phiL hV n)⁻¹ * w0 := by rw [← h1]
  have hcomm_n (y : ↥(c.H hV)) (hy : y ∈ E) : (c.phiL hV n)⁻¹ * y * c.phiL hV n = y := by
    letI : IsMulCommutative ↥E := hE.1
    have hc : c.phiL hV n * y = y * c.phiL hV n :=
      congrArg Subtype.val (mul_comm' (⟨c.phiL hV n, hnE⟩ : E) ⟨y, hy⟩)
    calc (c.phiL hV n)⁻¹ * y * c.phiL hV n = (c.phiL hV n)⁻¹ * (y * c.phiL hV n) := by group
      _ = (c.phiL hV n)⁻¹ * (c.phiL hV n * y) := by rw [← hc]
      _ = y := by group
  exact ⟨n, m, hm_norm, hphi_m, hcomm_n⟩

private theorem SU44_w_inv_of_decomp {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {E : Subgroup ↥(c.H hV)} {El : Subgroup ↥c.L}
    (hEl_map : El.map (c.phiL hV) = E) (hEl_ker : El ⊓ (c.phiL hV).ker = ⊥)
    {w0 : ↥(c.H hV)} (hw0inv : ∀ e ∈ E, w0 * e * w0⁻¹ = e⁻¹)
    {n m : ↥c.L} (hm_norm : m ∈ Subgroup.normalizer (El : Set ↥c.L))
    (hphi_m : c.phiL hV m = (c.phiL hV n)⁻¹ * w0)
    (hcomm_n : ∀ y ∈ E, (c.phiL hV n)⁻¹ * y * c.phiL hV n = y) :
    ∃ w : ↥c.L, (∀ x ∈ El, w * x * w⁻¹ = x⁻¹) ∧
      (∀ x ∈ El.map c.L.subtype, (w : G) * x * (w : G)⁻¹ = x⁻¹) := by
  have hw_invL : ∀ x ∈ El, m * x * m⁻¹ = x⁻¹ := by
    intro x hx
    have hmx : m * x * m⁻¹ ∈ El := (Subgroup.mem_normalizer_iff.mp hm_norm x).mp hx
    have hinj : ∀ y ∈ El, ∀ z ∈ El, c.phiL hV y = c.phiL hV z → y = z := by
      intro y hy z hz hyz
      have hmem : y * z⁻¹ ∈ El ⊓ (c.phiL hV).ker := by
        refine ⟨El.mul_mem hy (El.inv_mem hz), ?_⟩
        show c.phiL hV (y * z⁻¹) = 1
        rw [map_mul, map_inv, hyz]
        simp
      rw [hEl_ker, Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp hmem
    refine hinj _ hmx _ (El.inv_mem hx) ?_
    have hxE : c.phiL hV x ∈ E := by
      rw [← hEl_map]
      exact Subgroup.mem_map_of_mem _ hx
    calc c.phiL hV (m * x * m⁻¹)
        = c.phiL hV m * c.phiL hV x * (c.phiL hV m)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = ((c.phiL hV n)⁻¹ * w0) * c.phiL hV x * ((c.phiL hV n)⁻¹ * w0)⁻¹ := by
          rw [hphi_m]
      _ = (c.phiL hV n)⁻¹ * (w0 * c.phiL hV x * w0⁻¹) * c.phiL hV n := by group
      _ = (c.phiL hV n)⁻¹ * (c.phiL hV x)⁻¹ * c.phiL hV n := by rw [hw0inv _ hxE]
      _ = c.phiL hV (x⁻¹) := by
          rw [map_inv, hcomm_n _ (E.inv_mem hxE)]
  refine ⟨m, hw_invL, ?_⟩
  intro x hx
  obtain ⟨xL, hxL, rfl⟩ := Subgroup.mem_map.mp hx
  simpa using congrArg (fun z : ↥c.L => (z : G)) (hw_invL xL hxL)

private theorem exists_SU44Lift_w {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {E : Subgroup ↥(c.H hV)} {El : Subgroup ↥c.L}
    (hE : IsElemAbelian 3 E) (hEl_el : IsElemAbelian 3 El)
    (hEl_le : El ≤ E.comap (c.phiL hV)) (hEl_map : El.map (c.phiL hV) = E)
    (hEl_ker : El ⊓ (c.phiL hV).ker = ⊥)
    (hker_not : ¬ 3 ∣ Nat.card (c.phiL hV).ker)
    {w0 : ↥(c.H hV)} (hw0inv : ∀ e ∈ E, w0 * e * w0⁻¹ = e⁻¹) :
    ∃ w : ↥c.L, (∀ x ∈ El, w * x * w⁻¹ = x⁻¹) ∧
      (∀ x ∈ El.map c.L.subtype, (w : G) * x * (w : G)⁻¹ = x⁻¹) := by
  obtain ⟨n, m, hm_norm, hphi_m, hcomm_n⟩ :=
    SU44_w_lift_decomp c hV hE hEl_el hEl_le hEl_map hEl_ker hker_not hw0inv
  exact SU44_w_inv_of_decomp c hV hEl_map hEl_ker hw0inv hm_norm hphi_m hcomm_n

theorem exists_SU44Lift {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (hSU44 : S23_9_SU44 D Ch c hV) (hKSU : KSU44)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hSC : KSchurC1) (hK : KOrdNatural) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    let ℓ : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
    let Pℓ : Subgroup ↥(c.H hV) :=
      MulAction.stabilizer ↥(c.H hV) ((ℓ : Subgroup (c.W hV)) : Set (c.W hV))
    let Kstar : Subgroup ↥(c.H hV) := Hinf Pℓ
    ∃ E : Subgroup ↥(c.H hV), ∃ Etil : Subgroup G, ∃ w : ↥c.L,
      IsElemAbelian 3 E ∧ Nat.card ↥E = 9 ∧ E ≤ Pℓ ∧
      E ⊓ (fixingSubgroupOf ↥(c.H hV) (c.W hV) ((ℓ : Subgroup (c.W hV)) : Set (c.W hV))) =
        E ⊓ Kstar ∧
      Nat.card ↥(E ⊓ Kstar) = 3 ∧
      (∃ k ∈ Kstar, ∃ e ∈ E ⊓ Kstar, e * k ≠ k * e) ∧
      Etil ≤ D.M ∧ Etil ≤ c.L ∧ IsElemAbelian 3 Etil ∧ Nat.card ↥Etil = 9 ∧
      (Etil.subgroupOf c.L).map (c.phiL hV) = E ∧
      ((Etil.subgroupOf c.L) ⊓ (c.phiL hV).ker = ⊥) ∧
      (∀ x ∈ (Etil.subgroupOf c.L), w * x * w⁻¹ = x⁻¹) ∧
      (∀ x ∈ Etil, (w : G) * x * (w : G)⁻¹ = x⁻¹) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let ℓ : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
  let Pℓ : Subgroup ↥(c.H hV) :=
    MulAction.stabilizer ↥(c.H hV) ((ℓ : Subgroup (c.W hV)) : Set (c.W hV))
  let Kstar : Subgroup ↥(c.H hV) := Hinf Pℓ
  obtain ⟨E, hE, hcard, hP, hint_eq, hint_card, hnoncentral, w0, hw0, hw0inv⟩ :=
    c.exists_SU44Estar hV hSU44 hKSU
  have hℓ : ℓ = c.Ztil hV := by
    simpa only [ℓ] using c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  have hmapPℓ : ((D.M ⊓ c.L).subgroupOf c.L).map (c.phiL hV) = Pℓ := by
    simpa only [Pℓ, hℓ] using c.map_inf_eq_stabilizer_Ztil hV h4 h1930
  have hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L :=
    c.phiL_ker_eq_pCore_of_kSchurC1 hV hK hnat hSC
      (Or.inr (Or.inl ⟨2, le_rfl, hSU44.1⟩))
  have hker_not : ¬ 3 ∣ Nat.card (c.phiL hV).ker := by
    rw [hker_eq]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  obtain ⟨El, Etil, hEl_el, hEl_le, hEl_map, hEl_ker, hEtil_el, hEtil_card, hEtilM,
    hEtilL, hEtil_sub, hEtil_map, hEtil_ker⟩ :=
    c.exists_SU44Lift_Etil hV h1930 hker_eq hE hcard hP hmapPℓ hker_not
  obtain ⟨w, hw_invL, hw_inv⟩ :=
    c.exists_SU44Lift_w hV hE hEl_el hEl_le hEl_map hEl_ker hker_not hw0inv
  have hEtil_eq : Etil = El.map c.L.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEtilL, hEtil_sub]
  refine ⟨E, Etil, w, hE, hcard, hP, hint_eq, hint_card, hnoncentral, hEtilM, hEtilL,
    hEtil_el, hEtil_card, hEtil_map, hEtil_ker, ?_, ?_⟩
  · rwa [hEtil_sub]
  · rwa [hEtil_eq]

theorem semireg_hyp_of_inverted {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h1930 : H1930 D) {e : G} (he : e ∈ D.M)
    (heZ : e ∉ Subgroup.centralizer (D.Z : Set G))
    {i : G} (hinv : ∀ a ∈ Subgroup.zpowers e, i * a * i⁻¹ = a⁻¹) :
    ∀ (q : ℕ), q.Prime → q ≠ 2 → ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup q ↥X →
      X ≤ D.M ⊓ Subgroup.centralizer ({e} : Set G) →
        X ∉ uniqueSet D.M ∧ q ∉ D.sig := by
  intro q hq hq2 X hXne hXp hXle
  haveI : Fact q.Prime := ⟨hq⟩
  have hXM : X ≤ D.M := hXle.trans inf_le_left
  have hXe : X ≤ Subgroup.centralizer ({e} : Set G) := hXle.trans inf_le_right
  have hnotinv : ¬ InvertedIn D.M (Subgroup.zpowers e) :=
    s23_9_NoInv_of h4 h1930 c e he heZ
  have hXcent : X ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hXe hx)
    exact (hcomm.zpow_right n).eq.symm
  have hXnotU : X ∉ uniqueSet D.M := by
    intro hXU
    exact hnotinv (invertedInOfUnique_holds G D.M (Subgroup.zpowers e) X q i
      D.maxLocal hq hXne hXp hXcent hXU hinv)
  refine ⟨hXnotU, ?_⟩
  intro hqsig
  refine hXnotU ⟨hXM, fun g hXg => ?_⟩
  by_contra hgne
  have hMs : Subgroup.normalizer (D.M : Set G) = D.M :=
    UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal
  have hgM : g ∉ D.M := by
    intro hgM'
    have hgN : g ∈ Subgroup.normalizer (D.M : Set G) := by rw [hMs]; exact hgM'
    exact hgne (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN)
  have hqdvdX : q ∣ Nat.card X := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      have h1 : 1 < Nat.card X := (Subgroup.one_lt_card_iff_ne_bot (H := X)).2 hXne
      omega
    rw [hn]
    exact dvd_pow_self q hn0
  have hspq : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M := by
    rw [h6 h1930 c] at hqsig
    exact hsp q hqsig
  have hle : X ≤ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := le_inf hXM hXg
  exact hspq.2.2 g hgM (hqdvdX.trans (Subgroup.card_dvd_of_le hle))

theorem fixV_eq_bot_of_inverted {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (d : S23_9_A0Data D Ch c) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hSem : S23_9_Semireg D Ch) (h1930 : H1930 D) {e : G} (he : e ∈ D.M)
    (heZ : e ∉ Subgroup.centralizer (D.Z : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (her : orderOf e = r) {i : G}
    (hinv : ∀ a ∈ Subgroup.zpowers e, i * a * i⁻¹ = a⁻¹) :
    d.fixV (barImage D.M (Subgroup.zpowers e)) = ⊥ := by
  exact (S23_9_A0Data.fixV_zpowers_eq_bot_of_semireg_hyp d h1930 hSem he hr hr2 her
    (semireg_hyp_of_inverted (c := c) h4 h6 hsp h1930 he heZ hinv d.q d.hq d.hq2)).1

theorem SU44_fixV_eq_bot {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (d : S23_9_A0Data D Ch c) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hSem : S23_9_Semireg D Ch) (h1930 : H1930 D)
    {Etil : Subgroup G} (hEtilM : Etil ≤ D.M) (hEtil_el : IsElemAbelian 3 Etil)
    (hEtil_card : Nat.card ↥Etil = 9) {w : G}
    (hw_inv : ∀ x ∈ Etil, w * x * w⁻¹ = x⁻¹) {e : G} (he : e ∈ Etil)
    (heZ : e ∉ Subgroup.centralizer (D.Z : Set G)) :
    d.fixV (barImage D.M (Subgroup.zpowers e)) = ⊥ := by
  have he1 : e ≠ 1 := fun h1 => heZ (h1 ▸ Subgroup.one_mem _)
  have hdvd : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one (hEtil_el.2 e he)
  have her : orderOf e = 3 := by
    have hne : orderOf e ≠ 1 := fun h1 => he1 (orderOf_eq_one_iff.mp h1)
    exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  exact Ctx23L.fixV_eq_bot_of_inverted d h4 h6 hsp hSem h1930 (hEtilM he) heZ
    Nat.prime_three (by norm_num) her
    (fun a ha => hw_inv a (Subgroup.zpowers_le.mpr he ha))

private theorem card_barImage_eq_card_of_isPGroup_three {M P : Subgroup G}
    (hP : P ≤ M) (hP3 : IsPGroup 3 P) :
    Nat.card (barImage M P) = Nat.card ↥P := by
  have hdisj : (P.subgroupOf M) ⊓ (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact disjoint_iff.mp
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) (P.subgroupOf M) (CFSG.pCore 2 ↥M)
        (hP3.comap_subtype) (CFSG.pCore_isPGroup (p := 2) (G := ↥M)))
  have h := CFSG.card_map_eq_card_of_inf_ker_eq_bot (f := QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    (J := P.subgroupOf M) hdisj
  rw [show barImage M P = (P.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) from rfl]
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv

private theorem SU44_D0bar_mem_hyperplanes {D : Data G}
    {Etil D0 : Subgroup G} (hEtilM : Etil ≤ D.M) (hEtil_el : IsElemAbelian 3 Etil)
    (hEtil_card : Nat.card ↥Etil = 9)
    (hD0_eq : D0 = Etil ⊓ Subgroup.centralizer (D.Z : Set G))
    (hD0_card : Nat.card ↥D0 = 3) :
    barImage D.M D0 ∈ InS3.hyperplanes 3 (barImage D.M Etil) ∧
      barImage D.M Etil ≠ ⊥ ∧ Nat.card ↥(barImage D.M Etil) = 9 := by
  have hD0_le_Etil : D0 ≤ Etil := by
    rw [hD0_eq]
    exact inf_le_left
  have hD0M : D0 ≤ D.M := hD0_le_Etil.trans hEtilM
  have hA_card : Nat.card ↥(barImage D.M Etil) = 9 := by
    rw [card_barImage_eq_card_of_isPGroup_three hEtilM hEtil_el.isPGroup, hEtil_card]
  have hD0bar_card : Nat.card ↥(barImage D.M D0) = 3 := by
    rw [card_barImage_eq_card_of_isPGroup_three hD0M
      ((hEtil_el.mono hD0_le_Etil).isPGroup), hD0_card]
  have hD0bar_le_A : barImage D.M D0 ≤ barImage D.M Etil := by
    refine Subgroup.map_mono ?_
    intro x hx
    exact hD0_le_Etil (Subgroup.mem_subgroupOf.mp hx)
  refine ⟨⟨hD0bar_le_A, ?_⟩, ?_, hA_card⟩
  · have h := Subgroup.relIndex_mul_card (H := barImage D.M D0) (K := barImage D.M Etil)
    rw [inf_of_le_left hD0bar_le_A, hD0bar_card, hA_card] at h
    omega
  · intro h
    have : Nat.card ↥(barImage D.M Etil) = 1 := by rw [h, Subgroup.card_bot]
    omega

private theorem SU44_hyperplane_card {D : Data G} {Etil D0 : Subgroup G}
    (hEtilM : Etil ≤ D.M) (hEtil_el : IsElemAbelian 3 Etil)
    (hEtil_card : Nat.card ↥Etil = 9)
    (hD0_eq : D0 = Etil ⊓ Subgroup.centralizer (D.Z : Set G))
    (hD0_card : Nat.card ↥D0 = 3)
    {A : Subgroup (Bar2 D.M)} (hA : A = barImage D.M Etil)
    {B : Subgroup (Bar2 D.M)} (hB : B ∈ InS3.hyperplanes 3 A) :
    D0 ≤ Etil ∧ Nat.card ↥A = 9 ∧ Nat.card ↥(barImage D.M D0) = 3 ∧ Nat.card ↥B = 3 := by
  have hD0_le_Etil : D0 ≤ Etil := by
    rw [hD0_eq]
    exact inf_le_left
  have hA_card : Nat.card ↥A = 9 := by
    rw [hA, card_barImage_eq_card_of_isPGroup_three hEtilM hEtil_el.isPGroup, hEtil_card]
  have hD0bar_card : Nat.card ↥(barImage D.M D0) = 3 := by
    rw [card_barImage_eq_card_of_isPGroup_three (hD0_le_Etil.trans hEtilM)
      ((hEtil_el.mono hD0_le_Etil).isPGroup), hD0_card]
  have hBcard : Nat.card ↥B = 3 := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A)
    rw [inf_of_le_left hB.1, hB.2, hA_card] at h
    omega
  exact ⟨hD0_le_Etil, hA_card, hD0bar_card, hBcard⟩

private theorem SU44_exists_mem_Etil_not_D0 {D : Data G}
    {Etil D0 : Subgroup G} (hEtilM : Etil ≤ D.M) (hEtil_el : IsElemAbelian 3 Etil)
    (hEtil_card : Nat.card ↥Etil = 9)
    (hD0_eq : D0 = Etil ⊓ Subgroup.centralizer (D.Z : Set G))
    (hD0_card : Nat.card ↥D0 = 3)
    {A : Subgroup (Bar2 D.M)} (hA : A = barImage D.M Etil)
    {B : Subgroup (Bar2 D.M)} (hB : B ∈ InS3.hyperplanes 3 A)
    (hBne : B ≠ barImage D.M D0) :
    ∃ e ∈ Etil, e ∉ D0 ∧ barImage D.M (Subgroup.zpowers e) = B := by
  obtain ⟨hD0_le_Etil, hA_card, hD0bar_card, hBcard⟩ :=
    SU44_hyperplane_card hEtilM hEtil_el hEtil_card hD0_eq hD0_card hA hB
  have hBnt : Nontrivial ↥B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hBcard]; norm_num)
  obtain ⟨a, haB, ha1⟩ := Subgroup.exists_ne_one_of_nontrivial B
  let aA : ↥A := ⟨a, hB.1 haB⟩
  have haA : (aA : Bar2 D.M) ∈ barImage D.M Etil := by
    rw [← hA]
    exact aA.2
  obtain ⟨y, hySub, hyπ⟩ := Subgroup.mem_map.mp haA
  have heEtil : (y : G) ∈ Etil := Subgroup.mem_subgroupOf.mp hySub
  let e : G := y
  have heM : e ∈ D.M := hEtilM heEtil
  have haordB : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard B haB
      rwa [hBcard] at this
    have hne : orderOf a ≠ 1 := fun h1 => ha1 (orderOf_eq_one_iff.mp h1)
    exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  have haord : orderOf ((aA : ↥A) : Bar2 D.M) = 3 := by
    change orderOf a = 3
    exact haordB
  have hB_eq : B = Subgroup.zpowers ((aA : ↥A) : Bar2 D.M) := by
    have hle : Subgroup.zpowers ((aA : ↥A) : Bar2 D.M) ≤ B :=
      Subgroup.zpowers_le.mpr (show a ∈ B from haB)
    have hcard : Nat.card ↥(Subgroup.zpowers ((aA : ↥A) : Bar2 D.M)) = 3 := by
      rw [Nat.card_zpowers, haord]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hBcard])).symm
  have hbar : barImage D.M (Subgroup.zpowers e) = B := by
    have hsub : (Subgroup.zpowers e).subgroupOf D.M =
        Subgroup.zpowers (⟨e, heM⟩ : ↥D.M) := by
      apply Subgroup.map_injective D.M.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.zpowers_le.mpr heM),
        MonoidHom.map_zpowers]
      rfl
    rw [hB_eq, barImage, hsub, MonoidHom.map_zpowers, hyπ]
  have heD0 : e ∉ D0 := by
    intro he0
    have haD0 : ((aA : ↥A) : Bar2 D.M) ∈ barImage D.M D0 := by
      rw [← hyπ]
      exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr he0, rfl⟩
    have hle : B ≤ barImage D.M D0 := by
      rw [hB_eq]
      exact Subgroup.zpowers_le.mpr haD0
    exact hBne (Subgroup.eq_of_le_of_card_ge hle (by rw [hBcard, hD0bar_card]))
  exact ⟨e, heEtil, heD0, hbar⟩

theorem SU44_D0bar_le_ker {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (d : S23_9_A0Data D Ch c) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hSem : S23_9_Semireg D Ch) (h1930 : H1930 D) (hq3 : d.q ≠ 3)
    {Etil D0 : Subgroup G} (hEtilM : Etil ≤ D.M) (hEtil_el : IsElemAbelian 3 Etil)
    (hEtil_card : Nat.card ↥Etil = 9) (hD0_eq : D0 = Etil ⊓ Subgroup.centralizer (D.Z : Set G))
    (hD0_card : Nat.card ↥D0 = 3)
    (hfix : ∀ e ∈ Etil, e ∉ D0 →
      d.fixV (barImage D.M (Subgroup.zpowers e)) = ⊥) :
    barImage D.M D0 ≤ d.rep.ker := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  let A : Subgroup (Bar2 D.M) := barImage D.M Etil
  obtain ⟨hD0bar_mem, hA_ne, -⟩ :=
    SU44_D0bar_mem_hyperplanes hEtilM hEtil_el hEtil_card hD0_eq hD0_card
  have hA_el : IsElemAbelian 3 A :=
    (hEtil_el.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
  have hsup : (⨆ B : ↥(InS3.hyperplanes 3 A), d.fixV B.1) = ⊤ := by
    simpa only [S23_9_A0Data.fixV] using
      InS3.iSup_fixV_hyperplanes_eq_top d.rep d.hq Nat.prime_three (Ne.symm hq3) hA_el hA_ne
  have hzero : ∀ B ∈ InS3.hyperplanes 3 A, B ≠ barImage D.M D0 → d.fixV B = ⊥ := by
    intro B hB hBne
    obtain ⟨e, heEtil, heD0, hbar⟩ :=
      SU44_exists_mem_Etil_not_D0 hEtilM hEtil_el hEtil_card hD0_eq hD0_card
        (A := A) rfl hB hBne
    rw [← hbar]
    exact hfix e heEtil heD0
  have hle : (⨆ B : ↥(InS3.hyperplanes 3 A), d.fixV B.1) ≤ d.fixV (barImage D.M D0) := by
    refine iSup_le fun B => ?_
    by_cases hB : B.1 = barImage D.M D0
    · rw [hB]
    · rw [hzero B.1 B.2 hB]
      exact bot_le
  have hge : d.fixV (barImage D.M D0) ≤
      (⨆ B : ↥(InS3.hyperplanes 3 A), d.fixV B.1) :=
    le_iSup (fun B : ↥(InS3.hyperplanes 3 A) => d.fixV B.1) ⟨barImage D.M D0, hD0bar_mem⟩
  have htop : d.fixV (barImage D.M D0) = ⊤ := by
    have h1 : (⊤ : Submodule (ZMod d.q) (Additive (↥d.E ⧸ frattini ↥d.E))) ≤
        d.fixV (barImage D.M D0) := hsup ▸ hle
    exact le_antisymm (hge.trans_eq hsup) h1
  exact (CFSG.GroupTheory.fixV_eq_top_iff_le_ker d.rep (barImage D.M D0)).mp htop

private theorem map_subgroupOf_inf_centralizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (E : Subgroup G) :
    ((E ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map (c.phiL hV) =
      (E.subgroupOf c.L).map (c.phiL hV) ⊓ c.CH hV := by
  rw [c.inf_map_phiL_CH hV (E.subgroupOf c.L)]
  congr 1

private theorem SU44_Y_normal {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (hV : IsElemAbelian 2 c.V) {Kstar : Subgroup ↥(c.H hV)} {N : Subgroup G}
    (hKstarMap : ((SU44K c).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hNnormM : D.M ≤ Subgroup.normalizer (N : Set G))
    (hker_le : (c.phiL hV).ker ≤ (D.M ⊓ c.L).subgroupOf c.L) :
    ((SU44Y c hV Kstar N).subgroupOf Kstar).Normal := by
  classical
  let BL : Subgroup ↥c.L := Kstar.comap (c.phiL hV)
  let AL : Subgroup ↥c.L := BL ⊓ N.subgroupOf c.L
  have hBLmap : BL.map (c.phiL hV) = Kstar :=
    Subgroup.map_comap_eq_self_of_surjective (c.phiL_surjective hV) Kstar
  have hBLleM : BL ≤ (D.M ⊓ c.L).subgroupOf c.L := by
    have hEq : BL = (SU44K c).subgroupOf c.L ⊔ (c.phiL hV).ker := by
      change Kstar.comap (c.phiL hV) = _
      rw [← hKstarMap, Subgroup.comap_map_eq]
    rw [hEq]
    exact sup_le (Subgroup.subgroupOf_mono c.L (uc22p21c_Hinf_le (D.M ⊓ c.L))) hker_le
  have hALnorm : ∀ l ∈ BL, ∀ a ∈ AL, l * a * l⁻¹ ∈ AL := by
    intro l hl a ha
    refine Subgroup.mem_inf.mpr ⟨BL.mul_mem (BL.mul_mem hl ha.1) (BL.inv_mem hl), ?_⟩
    rw [Subgroup.mem_subgroupOf]
    have hlM : (l : G) ∈ D.M := (Subgroup.mem_subgroupOf.mp (hBLleM hl)).1
    have haN : (a : G) ∈ N := Subgroup.mem_subgroupOf.mp ha.2
    rw [show ((l * a * l⁻¹ : ↥c.L) : G) = (l : G) * (a : G) * (l : G)⁻¹ from rfl]
    exact (Subgroup.mem_normalizer_iff.mp (hNnormM hlM) (a : G)).mp haN
  have hYle : AL.map (c.phiL hV) ≤ Kstar := by
    rw [← hBLmap]
    exact Subgroup.map_mono inf_le_left
  refine ⟨fun y hy k => ?_⟩
  obtain ⟨a, haA, hya⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
  have hk : (k : ↥(c.H hV)) ∈ BL.map (c.phiL hV) := by
    rw [hBLmap]
    exact k.2
  obtain ⟨l, hlB, hlk⟩ := Subgroup.mem_map.mp hk
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hconj : l * a * l⁻¹ ∈ AL := hALnorm l hlB a haA
  have hkey : (k * y * k⁻¹ : ↥Kstar) = ⟨c.phiL hV (l * a * l⁻¹),
      hYle (Subgroup.mem_map_of_mem _ hconj)⟩ := by
    apply Subtype.ext
    change (k : ↥(c.H hV)) * (y : ↥(c.H hV)) * (k : ↥(c.H hV))⁻¹ =
      c.phiL hV (l * a * l⁻¹)
    rw [map_mul, map_mul, map_inv, ← hya, ← hlk]
  rw [hkey]
  exact Subgroup.mem_map_of_mem _ hconj

private theorem SU44_Y_sup_pCore {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (hV : IsElemAbelian 2 c.V) {Kstar : Subgroup ↥(c.H hV)} {N : Subgroup G} {D0 : Subgroup G}
    (hD0card : Nat.card ↥((D0.subgroupOf c.L).map (c.phiL hV)) = 3)
    (hD0leBL : D0.subgroupOf c.L ≤ Kstar.comap (c.phiL hV))
    (hD0N : D0 ≤ N)
    (hYnorm : ((SU44Y c hV Kstar N).subgroupOf Kstar).Normal)
    (hsimple : IsSimpleGroup (Bar2 Kstar)) :
    (SU44Y c hV Kstar N).subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar = ⊤ := by
  classical
  let BL : Subgroup ↥c.L := Kstar.comap (c.phiL hV)
  let AL : Subgroup ↥c.L := BL ⊓ N.subgroupOf c.L
  let Y : Subgroup ↥(c.H hV) := AL.map (c.phiL hV)
  change Y.subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar = ⊤
  have hBLmap : BL.map (c.phiL hV) = Kstar :=
    Subgroup.map_comap_eq_self_of_surjective (c.phiL_surjective hV) Kstar
  have hYle : Y ≤ Kstar := by
    rw [show Y = AL.map (c.phiL hV) from rfl, ← hBLmap]
    exact Subgroup.map_mono inf_le_left
  have hD0leAL : D0.subgroupOf c.L ≤ AL :=
    le_inf hD0leBL (Subgroup.subgroupOf_mono c.L hD0N)
  have hnt : Nontrivial ↥((D0.subgroupOf c.L).map (c.phiL hV)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hD0card]; norm_num)
  haveI := hnt
  obtain ⟨x, hxmem, hx1⟩ :=
    Subgroup.exists_ne_one_of_nontrivial ((D0.subgroupOf c.L).map (c.phiL hV))
  have hxY : x ∈ Y := Subgroup.map_mono hD0leAL hxmem
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard ((D0.subgroupOf c.L).map (c.phiL hV)) hxmem
      rwa [hD0card] at this
    have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  have hxO2 : (⟨x, hYle hxY⟩ : ↥Kstar) ∉ CFSG.pCore 2 ↥Kstar := by
    intro hxK
    let xK : ↥Kstar := ⟨x, hYle hxY⟩
    have hxKmem : xK ∈ CFSG.pCore 2 ↥Kstar := hxK
    have hxKord : orderOf xK = 3 := by
      rw [← Subgroup.orderOf_coe xK]
      exact hxord
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Kstar)).exists_card_eq
    have hdvd : orderOf xK ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_dvd_natCard _ hxKmem
    rw [hxKord] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  haveI : (Y.subgroupOf Kstar).Normal := hYnorm
  have hsup : Y.subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar = ⊤ := by
    by_contra hne
    have hNtop : (Y.subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar).Normal := inferInstance
    have heq := CFSG.Quasithin.SteinbergBM.eq_pCore_of_normal_of_isSimpleGroup
      (L := ↥Kstar) (p := 2) (N := Y.subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar)
      hNtop le_sup_right hne
    have hYpcore : Y.subgroupOf Kstar ≤ CFSG.pCore 2 ↥Kstar := by
      rw [← heq]
      exact le_sup_left
    exact hxO2 (hYpcore (Subgroup.mem_subgroupOf.mpr hxY))
  exact hsup

private theorem SU44_Y_eq_top {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (hV : IsElemAbelian 2 c.V) {Kstar : Subgroup ↥(c.H hV)} {N : Subgroup G}
    (hKstarMap : ((SU44K c).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hYnorm : ((SU44Y c hV Kstar N).subgroupOf Kstar).Normal)
    (hsup : (SU44Y c hV Kstar N).subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar = ⊤) :
    (SU44Y c hV Kstar N).subgroupOf Kstar = ⊤ := by
  classical
  let BL : Subgroup ↥c.L := Kstar.comap (c.phiL hV)
  let AL : Subgroup ↥c.L := BL ⊓ N.subgroupOf c.L
  let Y : Subgroup ↥(c.H hV) := AL.map (c.phiL hV)
  change Y.subgroupOf Kstar = ⊤
  have hKleL : SU44K c ≤ c.L := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  have hKperf : ⁅SU44K c, SU44K c⁆ = SU44K c := uc22p21c_Hinf_perfect _
  have hKstarPerf : Group.IsPerfect ↥Kstar := by
    have hsubperf : ⁅(SU44K c).subgroupOf c.L, (SU44K c).subgroupOf c.L⁆ =
        (SU44K c).subgroupOf c.L := by
      rw [CFSG.GroupTheory.commutator_subgroupOf_eq hKleL hKleL, hKperf]
    have hmapperf : ⁅Kstar, Kstar⁆ = Kstar := by
      rw [← hKstarMap, ← Subgroup.map_commutator, hsubperf]
    exact Subgroup.isPerfect_iff.mpr hmapperf
  haveI : (Y.subgroupOf Kstar).Normal := hYnorm
  have htopPerf : (⁅(⊤ : Subgroup ↥Kstar), (⊤ : Subgroup ↥Kstar)⁆ :
      Subgroup ↥Kstar) = ⊤ := by
    haveI : Group.IsPerfect ↥Kstar := hKstarPerf
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hYtop : Y.subgroupOf Kstar = ⊤ := by
    have hle : (⊤ : Subgroup ↥Kstar) ≤ Y.subgroupOf Kstar :=
      CFSG.GroupTheory.le_of_commutator_eq_self_of_le_sup_of_isPGroup
        (X := ↥Kstar) (K := ⊤) (N := Y.subgroupOf Kstar)
        (P := CFSG.pCore 2 ↥Kstar)
        (CFSG.pCore_isPGroup (p := 2) (G := ↥Kstar)) htopPerf
        (by rw [show Y.subgroupOf Kstar ⊔ CFSG.pCore 2 ↥Kstar = ⊤ from hsup])
    exact le_antisymm le_top hle
  exact hYtop

private theorem SU44_K_le_sup_pCore {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (hV : IsElemAbelian 2 c.V) (d : S23_9_A0Data D Ch c) (h1930 : H1930 D)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {Kstar : Subgroup ↥(c.H hV)}
    (hKstarMap : ((SU44K c).subgroupOf c.L).map (c.phiL hV) = Kstar)
    (hYtop : (SU44Y c hV Kstar (SU44N c d)).subgroupOf Kstar = ⊤) :
    SU44K c ≤ SU44N c d ⊔ CFSG.Open.pCoreOf 2 c.L := by
  classical
  have hKleL : SU44K c ≤ c.L := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right
  have hKstar_le_Y : Kstar ≤ SU44Y c hV Kstar (SU44N c d) :=
    Subgroup.subgroupOf_eq_top.mp hYtop
  intro x hx
  let xL : ↥c.L := ⟨x, hKleL hx⟩
  have hφK : c.phiL hV xL ∈ Kstar := by
    rw [← hKstarMap]
    exact Subgroup.mem_map.mpr ⟨xL, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨a, haA, haφ⟩ := Subgroup.mem_map.mp (hKstar_le_Y hφK)
  have haN : (a : G) ∈ SU44N c d := Subgroup.mem_subgroupOf.mp haA.2
  have hkerx : a⁻¹ * xL ∈ (c.phiL hV).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, haφ]
    simp
  have hxP : (a : G)⁻¹ * x ∈ CFSG.Open.pCoreOf 2 c.L :=
    Subgroup.mem_map.mpr ⟨a⁻¹ * xL, by rw [← hker]; exact hkerx, rfl⟩
  rw [show x = (a : G) * ((a : G)⁻¹ * x) from by group]
  exact (SU44N c d ⊔ CFSG.Open.pCoreOf 2 c.L).mul_mem
    (Subgroup.mem_sup_left haN) (Subgroup.mem_sup_right hxP)

private theorem SU44_K_le_barPreimage {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (d : S23_9_A0Data D Ch c) (h1930 : H1930 D)
    (hKN : SU44K c ≤ SU44N c d ⊔ CFSG.Open.pCoreOf 2 c.L) :
    SU44K c ≤ SU44N c d := by
  classical
  let K : Subgroup G := SU44K c
  let N : Subgroup G := SU44N c d
  change K ≤ N
  have hKleM : K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hKperf : ⁅K, K⁆ = K := by
    simpa only [K, SU44K] using uc22p21c_Hinf_perfect (D.M ⊓ c.L)
  have hNleM : N ≤ D.M := uc22p21c_barPreimage_le D.M d.rep.ker
  have hNnormM : D.M ≤ Subgroup.normalizer (N : Set G) := by
    haveI : d.rep.ker.Normal := MonoidHom.normal_ker d.rep
    exact uc22p22u_barPreimage_normalizes (D := d.rep.ker)
  haveI : (N.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleM).2 hNnormM
  have hKbar_le : K.subgroupOf D.M ≤ (N.subgroupOf D.M) ⊔
      ((CFSG.Open.pCoreOf 2 c.L).subgroupOf D.M) := by
    rw [← Subgroup.subgroupOf_sup hNleM (s23_9_O2L_of (D := D) (Ch := Ch) h1930 c)]
    exact Subgroup.subgroupOf_mono D.M hKN
  have hperf_bar : ⁅K.subgroupOf D.M, K.subgroupOf D.M⁆ = K.subgroupOf D.M := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hKleM hKleM, hKperf]
  have hPK : IsPGroup 2 ((CFSG.Open.pCoreOf 2 c.L).subgroupOf D.M) :=
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype).comap_subtype
  have hKleNbar : K.subgroupOf D.M ≤ N.subgroupOf D.M :=
    CFSG.GroupTheory.le_of_commutator_eq_self_of_le_sup_of_isPGroup hPK hperf_bar hKbar_le
  intro x hx
  have hxM : ((⟨x, hKleM hx⟩ : ↥D.M) : G) ∈ K := hx
  exact Subgroup.mem_subgroupOf.mp (hKleNbar (Subgroup.mem_subgroupOf.mpr hxM))

private theorem SU44_barImage_le_ker {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (d : S23_9_A0Data D Ch c) (hKleN : SU44K c ≤ SU44N c d) :
    barImage D.M (SU44K c) ≤ d.rep.ker := by
  have hNker : (SU44N c d).subgroupOf D.M =
      (d.rep.ker).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) := by
    ext x
    constructor
    · intro hx
      have hx' : (x : G) ∈ SU44N c d := Subgroup.mem_subgroupOf.mp hx
      exact (uc22p21c_mem_barPreimage.mp hx').2
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (uc22p21c_mem_barPreimage.mpr ⟨x.2, hx⟩)
  rw [show barImage D.M (SU44K c) =
      ((SU44K c).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) from rfl,
    Subgroup.map_le_iff_le_comap]
  intro u hu
  exact hNker ▸ Subgroup.subgroupOf_mono D.M hKleN hu

theorem SU44_K_le_ker {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (hV : IsElemAbelian 2 c.V) (d : S23_9_A0Data D Ch c) (h1930 : H1930 D)
    (hker : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L)
    {Kstar : Subgroup ↥(c.H hV)}
    (hKstarMap : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar)
    {D0 : Subgroup G} (hD0M : D0 ≤ D.M) (hD0L : D0 ≤ c.L)
    (hD0bar : barImage D.M D0 ≤ d.rep.ker)
    (hD0le : (D0.subgroupOf c.L).map (c.phiL hV) ≤ Kstar)
    (hD0card : Nat.card ↥((D0.subgroupOf c.L).map (c.phiL hV)) = 3)
    (hsimple : IsSimpleGroup (Bar2 Kstar)) :
    barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker := by
  classical
  have hker_le : (c.phiL hV).ker ≤ (D.M ⊓ c.L).subgroupOf c.L := by
    rw [hker]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ⟨s23_9_O2L_of (D := D) (Ch := Ch) h1930 c (Subgroup.mem_map_of_mem c.L.subtype hx),
        x.2⟩
  have hNnormM : D.M ≤ Subgroup.normalizer (SU44N c d : Set G) := by
    haveI : d.rep.ker.Normal := MonoidHom.normal_ker d.rep
    exact uc22p22u_barPreimage_normalizes (D := d.rep.ker)
  have hD0N : D0 ≤ SU44N c d := by
    intro x hx
    refine uc22p21c_mem_barPreimage.2 ⟨hD0M hx, ?_⟩
    exact hD0bar (Subgroup.mem_map.mpr
      ⟨⟨x, hD0M hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have hD0leBL : D0.subgroupOf c.L ≤ Kstar.comap (c.phiL hV) :=
    Subgroup.map_le_iff_le_comap.mp hD0le
  have hYnorm := SU44_Y_normal (c := c) hV hKstarMap hNnormM hker_le
  have hYsup := SU44_Y_sup_pCore (c := c) hV hD0card hD0leBL hD0N hYnorm hsimple
  have hYtop := SU44_Y_eq_top (c := c) hV hKstarMap hYnorm hYsup
  exact SU44_barImage_le_ker (c := c) d
    (SU44_K_le_barPreimage (c := c) d h1930
      (SU44_K_le_sup_pCore (c := c) hV d h1930 hker hKstarMap hYtop))

end Ctx23L

private theorem s23_9_A5_D0_basic {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    {hV : IsElemAbelian 2 c.V}
    {Kstar : Subgroup ↥(c.H hV)} {Etil : Subgroup G} {E : Subgroup ↥(c.H hV)}
    (hEtilM : Etil ≤ D.M) (hEtilL : Etil ≤ c.L)
    (hEtil_map : (Etil.subgroupOf c.L).map (c.phiL hV) = E)
    (hEtil_ker : (Etil.subgroupOf c.L) ⊓ (c.phiL hV).ker = ⊥)
    (hEfixCH : E ⊓ c.CH hV = E ⊓ Kstar)
    (hEfixcard : Nat.card ↥(E ⊓ Kstar) = 3) :
    ∃ D0 : Subgroup G, D0 = Etil ⊓ Subgroup.centralizer (D.Z : Set G) ∧ D0 ≤ D.M ∧
      D0 ≤ c.L ∧ (D0.subgroupOf c.L).map (c.phiL hV) ≤ Kstar ∧
      Nat.card ↥((D0.subgroupOf c.L).map (c.phiL hV)) = 3 ∧ Nat.card ↥D0 = 3 := by
  have hD0M : Etil ⊓ Subgroup.centralizer (D.Z : Set G) ≤ D.M :=
    inf_le_left.trans hEtilM
  have hD0L : Etil ⊓ Subgroup.centralizer (D.Z : Set G) ≤ c.L :=
    inf_le_left.trans hEtilL
  have hD0map : ((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map
      (c.phiL hV) = E ⊓ Kstar := by
    rw [Ctx23L.map_subgroupOf_inf_centralizer c hV Etil, hEtil_map, hEfixCH]
  have hD0card : Nat.card ↥(((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map
      (c.phiL hV)) = 3 := by
    rw [hD0map]; exact hEfixcard
  have hD0le : ((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map
      (c.phiL hV) ≤ Kstar := by
    rw [hD0map]; exact inf_le_right
  have hD0disj : ((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) ⊓
      (c.phiL hV).ker = ⊥ := by
    refine le_antisymm ?_ bot_le
    have hle : ((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) ≤
        Etil.subgroupOf c.L := Subgroup.subgroupOf_mono c.L inf_le_left
    calc ((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) ⊓ (c.phiL hV).ker
        ≤ (Etil.subgroupOf c.L) ⊓ (c.phiL hV).ker := inf_le_inf_right _ hle
      _ = ⊥ := hEtil_ker
  have hD0cardD : Nat.card ↥(Etil ⊓ Subgroup.centralizer (D.Z : Set G)) = 3 := by
    have h1 : Nat.card ↥(((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L).map
          (c.phiL hV)) =
        Nat.card ↥((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) :=
      CFSG.card_map_eq_card_of_inf_ker_eq_bot (f := c.phiL hV)
        (J := (Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) hD0disj
    rw [hD0card] at h1
    calc Nat.card ↥(Etil ⊓ Subgroup.centralizer (D.Z : Set G)) =
          Nat.card ↥((Etil ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.L) :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD0L).symm.toEquiv
      _ = 3 := h1.symm
  exact ⟨_, rfl, hD0M, hD0L, hD0le, hD0card, hD0cardD⟩

private theorem s23_9_A5_D0_bar {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    {hV : IsElemAbelian 2 c.V} {d : S23_9_A0Data D Ch c}
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hSemi : S23_9_Semireg D Ch) (hq3 : d.q ≠ 3)
    {D0 Etil : Subgroup G} {w : ↥c.L}
    (hD0_eq : D0 = Etil ⊓ Subgroup.centralizer (D.Z : Set G))
    (hD0cardD : Nat.card ↥D0 = 3)
    (hEtilM : Etil ≤ D.M) (hEtil_el : IsElemAbelian 3 Etil)
    (hEtil_card : Nat.card ↥Etil = 9)
    (hw_inv : ∀ x ∈ Etil, (w : G) * x * (w : G)⁻¹ = x⁻¹) :
    barImage D.M D0 ≤ d.rep.ker := by
  have hfix : ∀ e ∈ Etil, e ∉ D0 →
      d.fixV (barImage D.M (Subgroup.zpowers e)) = ⊥ := by
    intro e heE heD0
    refine Ctx23L.SU44_fixV_eq_bot d h4 h6 hsp hSemi h1930 hEtilM hEtil_el hEtil_card
      hw_inv heE ?_
    intro heZ
    exact heD0 (hD0_eq ▸ Subgroup.mem_inf.mpr ⟨heE, heZ⟩)
  exact Ctx23L.SU44_D0bar_le_ker d h4 h6 hsp hSemi h1930 hq3 hEtilM hEtil_el hEtil_card
    hD0_eq hD0cardD hfix

private theorem s23_9_A5_setup {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (h52 : S23_5_2 D Ch) (h6 : S23_6 D Ch) (hPS : S23_9_PointStab D Ch)
    (hSemi : S23_9_Semireg D Ch) (hKSU : KSU44) (hA : KTab23a) (hD : KTab23d)
    (hK : KOrdNatural) (hSC : KSchurC1)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h1930 : H1930 D) (d : S23_9_A0Data D Ch c) (hSU44 : S23_9_SU44 D Ch c hV)
    (hq3 : d.q ≠ 3) (hnot : ¬ barImage D.M (Hinf (D.M ⊓ c.L)) ≤ d.rep.ker) :
    ∃ (Kstar : Subgroup ↥(c.H hV)) (Etil : Subgroup G) (w : ↥c.L) (E : Subgroup ↥(c.H hV)),
      ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar ∧
      (c.phiL hV).ker = CFSG.pCore 2 ↥c.L ∧
      3 ≤ CFSG.Open.pRank 2 D.Z ∧ CFSG.Open.pRank 2 D.Z = 4 ∧
      Etil ≤ D.M ∧ Etil ≤ c.L ∧ IsElemAbelian 3 Etil ∧ Nat.card ↥Etil = 9 ∧
      (Etil.subgroupOf c.L).map (c.phiL hV) = E ∧
      (Etil.subgroupOf c.L) ⊓ (c.phiL hV).ker = ⊥ ∧
      (∀ x ∈ Etil, (w : G) * x * (w : G)⁻¹ = x⁻¹) ∧
      E ⊓ c.CH hV = E ⊓ Kstar ∧ Nat.card ↥(E ⊓ Kstar) = 3 ∧ IsL2 (Bar2 Kstar) 2 := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  rcases Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c with ⟨hVn, hnat⟩
  have hKne := c.Hinf_inf_L_ne_bot_of_not_barImage_le_rep_ker hV d hnot
  have hcn : c.n = CFSG.Open.pRank 2 D.Z := c.n_eq_pRank_of_pointStab h52 hPS h1930 hKne
  have hpr : CFSG.Open.pRank 2 D.Z = 4 := by rw [← hcn]; exact hSU44.2.2
  have hn : 3 ≤ CFSG.Open.pRank 2 D.Z := by omega
  have hker_eq : (c.phiL hV).ker = CFSG.pCore 2 ↥c.L :=
    c.phiL_ker_eq_pCore_of_kSchurC1 hV hK hnat hSC
      (Or.inr (Or.inl ⟨2, le_rfl, hSU44.1⟩))
  set Kstar : Subgroup ↥(c.H hV) := Hinf (MulAction.stabilizer ↥(c.H hV)
    ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) : Set (c.W hV)))
    with hKstar_def
  obtain ⟨E, Etil, w, hE, hEcard, hEP, hEfix, hEfixcard, hEnc, hEtilM, hEtilL,
    hEtil_el, hEtil_card, hEtil_map, hEtil_ker, hw_invL, hw_inv⟩ :=
    c.exists_SU44Lift hV hSU44 hKSU hA h4 h1930 hnat hSC hK
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  have hKstarMap : ((Hinf (D.M ⊓ c.L)).subgroupOf c.L).map (c.phiL hV) = Kstar := by
    have h := c.map_Hinf_inf_eq hV h4 h1930
    have hKstarZ : Kstar = Hinf (MulAction.stabilizer ↥(c.H hV)
        ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
      rw [hKstar_def, hℓ]
    rw [h, hKstarZ]
  have hCH : c.CH hV = fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
        Set (c.W hV)) := by
    show fixingSubgroupOf ↥(c.H hV) (c.W hV)
      ((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV)) = _
    rw [hℓ]
  have hEfixCH : E ⊓ c.CH hV = E ⊓ Kstar := by
    rw [hCH]
    exact hEfix
  have hL2 : IsL2 (Bar2 Kstar) 2 := by
    obtain ⟨a, ha, hLa⟩ := (hD (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
      (c.commutator_H_eq hV) hn (c.sylowStar hV)).2.2.2.2.2.1
      ⟨2, hpr, hSU44.1, hSU44.2.1⟩
    rw [show a = 2 from by omega] at hLa
    rwa [hKstar_def]
  exact ⟨Kstar, Etil, w, E, hKstarMap, hker_eq, hn, hpr, hEtilM, hEtilL, hEtil_el,
    hEtil_card, hEtil_map, hEtil_ker, hw_inv, hEfixCH, hEfixcard, hL2⟩

theorem s23_9_A5_of (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (h52 : S23_5_2 D Ch) (h6 : S23_6 D Ch) (hPS : S23_9_PointStab D Ch)
    (hSemi : S23_9_Semireg D Ch) (hKSU : KSU44) (hA : KTab23a) (hD : KTab23d)
    (hK : KOrdNatural) (hSC : KSchurC1)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) :
    S23_9_A5 D Ch := by
  intro h1930 c hV d hSU44 _ _ hq3 hnot
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  obtain ⟨Kstar, Etil, w, E, hKstarMap, hker_eq, hn, hpr, hEtilM, hEtilL, hEtil_el,
    hEtil_card, hEtil_map, hEtil_ker, hw_inv, hEfixCH, hEfixcard, hL2⟩ :=
    s23_9_A5_setup c hV h2 h3 h4 h52 h6 hPS hSemi hKSU hA hD hK hSC hsp h1930 d hSU44
      hq3 hnot
  obtain ⟨D0, hD0_eq, hD0M, hD0L, hD0le, hD0card, hD0cardD⟩ :=
    s23_9_A5_D0_basic hEtilM hEtilL hEtil_map hEtil_ker hEfixCH hEfixcard
  have hD0bar := s23_9_A5_D0_bar (hV := hV) h1930 h4 h6 hsp hSemi hq3 hD0_eq hD0cardD
    hEtilM hEtil_el hEtil_card hw_inv
  have hsimple : IsSimpleGroup (Bar2 Kstar) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  exact hnot (Ctx23L.SU44_K_le_ker hV d h1930 hker_eq hKstarMap hD0M hD0L hD0bar hD0le
    hD0card hsimple)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
