module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormalR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {X : Type} [Group X] [Finite X]

private def inComps (N : Subgroup X) : Subgroup X :=
  sSup {K : Subgroup X | CFSG.IsComponent K ∧ K ≤ N}

private def outComps (N : Subgroup X) : Subgroup X :=
  sSup {K : Subgroup X | CFSG.IsComponent K ∧ ¬ K ≤ N}

private theorem inComps_eq (N : Subgroup X) :
    inComps N = sSup {K : Subgroup X | CFSG.IsComponent K ∧ K ≤ N} := rfl

private theorem outComps_eq (N : Subgroup X) :
    outComps N = sSup {K : Subgroup X | CFSG.IsComponent K ∧ ¬ K ≤ N} := rfl

private theorem inComps_le (N : Subgroup X) : inComps N ≤ N := by
  rw [inComps_eq N]
  exact sSup_le fun _ hK => hK.2

private theorem outComps_le_layer (N : Subgroup X) : outComps N ≤ CFSG.layer X := by
  rw [outComps_eq N]
  exact sSup_le fun K hK => CFSG.LocalCores.component_le_layer hK.1

private theorem outComps_centralizes {N : Subgroup X} (hN : N.Normal) :
    outComps N ≤ Subgroup.centralizer (N : Set X) := by
  rw [outComps_eq N]
  refine sSup_le fun K hK => ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK.1 hN with hle | hcomm
  · exact absurd hle hK.2
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

private theorem inComps_le_centralizer_outComps {N : Subgroup X} (hN : N.Normal) :
    inComps N ≤ Subgroup.centralizer (outComps N : Set X) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (outComps_centralizes hN hy) z (inComps_le N hz)).symm

private theorem layer_eq_inComps_sup_outComps (N : Subgroup X) :
    CFSG.layer X = inComps N ⊔ outComps N := by
  rw [CFSG.layer.eq_sSup, inComps_eq N, outComps_eq N, ← sSup_union]
  congr 1
  ext K
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hK
    by_cases h : K ≤ N
    · exact Or.inl ⟨hK, h⟩
    · exact Or.inr ⟨hK, h⟩
  · rintro (⟨hK, _⟩ | ⟨hK, _⟩) <;> exact hK

private theorem exists_mul_of_mem_sup_of_le_centralizer {H K : Subgroup X}
    (h : H ≤ Subgroup.centralizer (K : Set X)) {x : X} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hle : H ≤ Subgroup.normalizer (K : Set X) :=
    h.trans (Subgroup.centralizer_le_normalizer (K : Set X))
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right H K hle
  have hx' : x ∈ (H : Set X) * (K : Set X) := by
    rw [← hcoe]
    exact hx
  rcases Set.mem_mul.mp hx' with ⟨h, hh, k, hk, hk'⟩
  exact ⟨h, hh, k, hk, hk'.symm⟩

theorem s15_Three_layer_normal_eq {N : Subgroup X} (hN : N.Normal) :
    (CFSG.layer ↥N).map N.subtype = sSup {K : Subgroup X | CFSG.IsComponent K ∧ K ≤ N} := by
  change (CFSG.layer ↥N).map N.subtype = inComps N
  refine le_antisymm ?_ ?_
  · rw [CFSG.layer.eq_sSup ↥N, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨CFSG.RankThree.PartTwo.Sec3.isComponent_map_of_normal hN hC,
      Subgroup.map_subtype_le C⟩
  · refine sSup_le fun K hK => ?_
    have hcomp : CFSG.IsComponent (K.subgroupOf N) :=
      CFSG.LocalCores.component_overgroup hK.1 hK.2
    have hle := Subgroup.map_mono (f := N.subtype) (CFSG.LocalCores.component_le_layer hcomp)
    simpa only [Subgroup.map_subgroupOf_eq_of_le hK.2] using hle

theorem s15_Three_center_layer_le_fitting :
    ∀ z ∈ CFSG.layer X, (∀ y ∈ CFSG.layer X, z * y = y * z) → z ∈ CFSG.fittingSubgroup X := by
  intro z hz hzc
  have hzM : z ∈ (Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype := by
    rw [CFSG.LocalCores.mem_map_center_iff (CFSG.layer X)]
    exact ⟨hz, Subgroup.mem_centralizer_iff.mpr fun y hy => (hzc y hy).symm⟩
  have hchar : ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype).Characteristic := by
    haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
    haveI : (Subgroup.center (CFSG.layer X)).Characteristic := inferInstance
    infer_instance
  have hnil : Group.IsNilpotent ((Subgroup.center (CFSG.layer X)).map
      (CFSG.layer X).subtype) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (Subgroup.center (CFSG.layer X))
        (CFSG.layer X).subtype Subtype.val_injective)
  haveI : ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype).Characteristic := hchar
  exact (CFSG.LocalCores.fitting_characteristic (G := X)).2.2 _ inferInstance hnil hzM

theorem s15_Three_decomp {N : Subgroup X} (hN : N.Normal)
    (hF : CFSG.fittingSubgroup X ⊔ CFSG.layer X = ⊤) :
    ∀ a : X, ∃ f ∈ CFSG.fittingSubgroup X,
      ∃ e₁ ∈ sSup {K : Subgroup X | CFSG.IsComponent K ∧ K ≤ N},
      ∃ e₂ ∈ sSup {K : Subgroup X | CFSG.IsComponent K ∧ ¬ K ≤ N}, a = f * e₁ * e₂ := by
  intro a
  change ∃ f ∈ CFSG.fittingSubgroup X, ∃ e₁ ∈ inComps N,
    ∃ e₂ ∈ outComps N, a = f * e₁ * e₂
  have hsplitF : CFSG.fittingSubgroup X ≤
      Subgroup.centralizer ((inComps N ⊔ outComps N : Subgroup X) : Set X) := by
    rw [← layer_eq_inComps_sup_outComps N]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := X))
  have hsplitE : inComps N ≤ Subgroup.centralizer (outComps N : Set X) :=
    inComps_le_centralizer_outComps hN
  have ha : a ∈ CFSG.fittingSubgroup X ⊔ (inComps N ⊔ outComps N) := by
    rw [← layer_eq_inComps_sup_outComps N, hF]
    exact Subgroup.mem_top a
  obtain ⟨f, hf, e, he, hae⟩ := exists_mul_of_mem_sup_of_le_centralizer hsplitF ha
  obtain ⟨e₁, he₁, e₂, he₂, hee⟩ := exists_mul_of_mem_sup_of_le_centralizer hsplitE he
  exact ⟨f, hf, e₁, he₁, e₂, he₂, by rw [hae, hee, mul_assoc]⟩

private theorem fitting_le_centralizer_layer :
    CFSG.fittingSubgroup X ≤ Subgroup.centralizer (CFSG.layer X : Set X) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.LocalCores.fitting_layer_commute (G := X))

private theorem commute_fitting_mul_comps_of_mem {N : Subgroup X} (hN : N.Normal)
    {f e₂ n : X} (hf : f ∈ CFSG.fittingSubgroup X) (he₂ : e₂ ∈ outComps N)
    (hnN : n ∈ N) (hnL : n ∈ CFSG.layer X) :
    (f * e₂) * n = n * (f * e₂) := by
  have hfn : f * n = n * f :=
    (Subgroup.mem_centralizer_iff.mp (fitting_le_centralizer_layer hf) n hnL).symm
  have he₂n : e₂ * n = n * e₂ :=
    (Subgroup.mem_centralizer_iff.mp (outComps_centralizes hN he₂) n hnN).symm
  calc (f * e₂) * n = f * (e₂ * n) := mul_assoc f e₂ n
    _ = f * (n * e₂) := by rw [he₂n]
    _ = (f * n) * e₂ := (mul_assoc f n e₂).symm
    _ = (n * f) * e₂ := by rw [hfn]
    _ = n * (f * e₂) := mul_assoc n f e₂

private theorem outComps_centralizes_outComps_of_mem {N : Subgroup X} (hN : N.Normal)
    {f e₂ x : X} (hf : f ∈ CFSG.fittingSubgroup X) (he₂ : e₂ ∈ outComps N)
    (hx : x = f * e₂) (hxN : x ∈ N) :
    e₂ ∈ Subgroup.centralizer (outComps N : Set X) := by
  have he₂eq : e₂ = f⁻¹ * x := by
    rw [hx]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyL : y ∈ CFSG.layer X := outComps_le_layer N hy
  have hfy : f * y = y * f :=
    (Subgroup.mem_centralizer_iff.mp (fitting_le_centralizer_layer hf) y hyL).symm
  have hfiy : f⁻¹ * y = y * f⁻¹ := Commute.inv_left hfy
  have hyx : y * x = x * y :=
    (Subgroup.mem_centralizer_iff.mp (outComps_centralizes hN hy) x hxN).symm
  calc y * e₂ = y * (f⁻¹ * x) := by rw [he₂eq]
    _ = (y * f⁻¹) * x := (mul_assoc y f⁻¹ x).symm
    _ = (f⁻¹ * y) * x := by rw [hfiy]
    _ = f⁻¹ * (y * x) := mul_assoc f⁻¹ y x
    _ = f⁻¹ * (x * y) := by rw [hyx]
    _ = (f⁻¹ * x) * y := (mul_assoc f⁻¹ x y).symm
    _ = e₂ * y := by rw [← he₂eq]

private theorem mem_centralizer_layer_of_centralizes_parts {N : Subgroup X} (hN : N.Normal)
    {z : X} (hz1 : z ∈ Subgroup.centralizer (inComps N : Set X))
    (hz2 : z ∈ Subgroup.centralizer (outComps N : Set X)) :
    z ∈ Subgroup.centralizer (CFSG.layer X : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [layer_eq_inComps_sup_outComps N] at hy
  obtain ⟨y₁, hy₁, y₂, hy₂, hyy⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (inComps_le_centralizer_outComps hN) hy
  calc y * z = (y₁ * y₂) * z := by rw [hyy]
    _ = y₁ * (y₂ * z) := mul_assoc y₁ y₂ z
    _ = y₁ * (z * y₂) := by rw [Subgroup.mem_centralizer_iff.mp hz2 y₂ hy₂]
    _ = (y₁ * z) * y₂ := (mul_assoc y₁ z y₂).symm
    _ = (z * y₁) * y₂ := by rw [Subgroup.mem_centralizer_iff.mp hz1 y₁ hy₁]
    _ = z * (y₁ * y₂) := mul_assoc z y₁ y₂
    _ = z * y := by rw [hyy]

end Abstract

section Generic

variable {Γ : Type} [Group Γ] [Finite Γ]

private theorem map_subtype_top_eq (H : Subgroup Γ) :
    (⊤ : Subgroup ↥H).map H.subtype = H := by
  refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩

private theorem s15_layer_map_le_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) : (CFSG.layer G).map e.toMonoidHom ≤ CFSG.layer H := by
  rw [CFSG.layer.eq_sSup G, Subgroup.map_le_iff_le_comap]
  exact sSup_le fun C hC =>
    Subgroup.map_le_iff_le_comap.mp
      (CFSG.LocalCores.component_le_layer (CFSG.LocalCores.isComponent_map_mulEquiv e hC))

private theorem s15_fitting_map_le_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) : (CFSG.fittingSubgroup G).map e.toMonoidHom ≤ CFSG.fittingSubgroup H := by
  haveI : Group.IsNilpotent (CFSG.fittingSubgroup G) :=
    (CFSG.LocalCores.fitting_nilpotent (G := G)).1
  refine (CFSG.LocalCores.fitting_characteristic (G := H)).2.2 _ ?_ ?_
  · exact (inferInstance : (CFSG.fittingSubgroup G).Normal).map e.toMonoidHom e.surjective
  · exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (CFSG.fittingSubgroup G) e.toMonoidHom e.injective)

private theorem s15_genFittingFStar_map_le_of_mulEquiv {G H : Type*} [Group G] [Group H]
    [Finite G] (e : G ≃* H) :
    (CFSG.Open.genFittingFStar G).map e.toMonoidHom ≤ CFSG.Open.genFittingFStar H := by
  rw [CFSG.Adapters.genFittingFStar_eq_foundations G,
    CFSG.Adapters.genFittingFStar_eq_foundations H, CFSG.generalizedFitting.eq_sup G,
    CFSG.generalizedFitting.eq_sup H, Subgroup.map_sup]
  exact sup_le ((s15_fitting_map_le_of_mulEquiv e).trans le_sup_left)
    ((s15_layer_map_le_of_mulEquiv e).trans le_sup_right)

private theorem s15_fitting_sup_layer_of_fstar {A : Subgroup Γ} (hF : Fstar A = A) :
    CFSG.fittingSubgroup ↥A ⊔ CFSG.layer ↥A = ⊤ := by
  apply Subgroup.map_injective A.subtype_injective
  rw [map_subtype_top_eq A, ← CFSG.generalizedFitting.eq_sup A,
    ← CFSG.Adapters.genFittingFStar_eq_foundations A]
  exact hF

theorem s15_Three_fstar_of_normal {A B : Subgroup Γ} (hBA : B ≤ A)
    (hn : (B.subgroupOf A).Normal) (hF : Fstar A = A) : Fstar B = B := by
  let N : Subgroup ↥A := B.subgroupOf A
  haveI hNn : N.Normal := hn
  have hFA : CFSG.fittingSubgroup ↥A ⊔ CFSG.layer ↥A = ⊤ :=
    s15_fitting_sup_layer_of_fstar hF
  have hFN : CFSG.Open.genFittingFStar ↥N = ⊤ := by
    rw [CFSG.Adapters.genFittingFStar_eq_foundations ↥N, CFSG.generalizedFitting.eq_sup ↥N]
    refine eq_top_iff.mpr fun n _ => ?_
    obtain ⟨f, hf, e₁, he₁, e₂, he₂, hae⟩ := s15_Three_decomp hNn hFA (N.subtype n)
    change e₁ ∈ inComps N at he₁
    change e₂ ∈ outComps N at he₂
    have h12 : e₁ * e₂ = e₂ * e₁ := by
      have hcent : e₁ ∈ Subgroup.centralizer (outComps N : Set ↥A) :=
        inComps_le_centralizer_outComps hNn he₁
      exact (Subgroup.mem_centralizer_iff.mp hcent e₂ he₂).symm
    let x : ↥A := f * e₂
    have hxeq : N.subtype n = x * e₁ := by
      rw [hae]
      show f * e₁ * e₂ = (f * e₂) * e₁
      calc f * e₁ * e₂ = f * (e₁ * e₂) := mul_assoc f e₁ e₂
        _ = f * (e₂ * e₁) := by rw [h12]
        _ = (f * e₂) * e₁ := (mul_assoc f e₂ e₁).symm
    have hxN : x ∈ N := by
      have h1 : x = N.subtype n * e₁⁻¹ := by
        rw [hxeq]
        group
      rw [h1]
      exact N.mul_mem (show N.subtype n ∈ N from n.2)
        (N.inv_mem (show e₁ ∈ N from inComps_le N he₁))
    have he₂F : e₂ ∈ CFSG.fittingSubgroup ↥A := by
      have hzout : e₂ ∈ Subgroup.centralizer (outComps N : Set ↥A) :=
        outComps_centralizes_outComps_of_mem hNn hf he₂ rfl hxN
      have hzin : e₂ ∈ Subgroup.centralizer (inComps N : Set ↥A) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact Subgroup.mem_centralizer_iff.mp (outComps_centralizes hNn he₂) y
          (inComps_le N hy)
      have hz := mem_centralizer_layer_of_centralizes_parts hNn hzin hzout
      exact s15_Three_center_layer_le_fitting e₂ (outComps_le_layer N he₂)
        (fun y hy => (Subgroup.mem_centralizer_iff.mp hz y hy).symm)
    have hxF : x ∈ CFSG.fittingSubgroup ↥A := by
      change f * e₂ ∈ CFSG.fittingSubgroup ↥A
      exact (CFSG.fittingSubgroup ↥A).mul_mem hf he₂F
    have hxmap : x ∈ (CFSG.fittingSubgroup ↥N).map N.subtype := by
      rw [CFSG.LocalCores.fitting_normal_intersection N]
      exact ⟨hxN, hxF⟩
    obtain ⟨xf, hxfF, hxfval⟩ := Subgroup.mem_map.mp hxmap
    have he₁' : e₁ ∈ (CFSG.layer ↥N).map N.subtype := by
      rw [s15_Three_layer_normal_eq hNn]
      exact he₁
    obtain ⟨ef, hef, hefval⟩ := Subgroup.mem_map.mp he₁'
    have hn_eq : n = xf * ef := by
      apply N.subtype_injective
      rw [map_mul, hxfval, hefval]
      exact hxeq
    rw [hn_eq]
    exact Subgroup.mul_mem_sup hxfF hef
  have htopN : (⊤ : Subgroup ↥N).map
      (Subgroup.subgroupOfEquivOfLe hBA).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (Subgroup.subgroupOfEquivOfLe hBA).surjective
  have hGB : CFSG.Open.genFittingFStar ↥B = ⊤ := by
    have h1 : (CFSG.Open.genFittingFStar ↥N).map
        (Subgroup.subgroupOfEquivOfLe hBA).toMonoidHom = ⊤ := by
      rw [hFN, htopN]
    exact top_le_iff.mp (h1 ▸ s15_genFittingFStar_map_le_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hBA))
  change (CFSG.Open.genFittingFStar ↥B).map B.subtype = B
  rw [hGB]
  exact map_subtype_top_eq B

theorem s15_Three_eq_cent_mul_layer {A B : Subgroup Γ} (hBA : B ≤ A)
    (hn : (B.subgroupOf A).Normal) (hF : Fstar A = A) :
    ∀ a ∈ A, ∃ c ∈ A, ∃ e ∈ (CFSG.layer ↥B).map B.subtype,
      (∀ x ∈ (CFSG.layer ↥B).map B.subtype, c * x = x * c) ∧ a = c * e := by
  let N : Subgroup ↥A := B.subgroupOf A
  haveI hNn : N.Normal := hn
  have hFA : CFSG.fittingSubgroup ↥A ⊔ CFSG.layer ↥A = ⊤ :=
    s15_fitting_sup_layer_of_fstar hF
  intro a ha
  obtain ⟨f, hf, e₁, he₁, e₂, he₂, hae⟩ := s15_Three_decomp hNn hFA ⟨a, ha⟩
  change e₁ ∈ inComps N at he₁
  change e₂ ∈ outComps N at he₂
  have h12 : e₁ * e₂ = e₂ * e₁ := by
    have hcent : e₁ ∈ Subgroup.centralizer (outComps N : Set ↥A) :=
      inComps_le_centralizer_outComps hNn he₁
    exact (Subgroup.mem_centralizer_iff.mp hcent e₂ he₂).symm
  have he₁' : e₁ ∈ (CFSG.layer ↥N).map N.subtype := by
    rw [s15_Three_layer_normal_eq hNn]
    exact he₁
  obtain ⟨ef, hef, hefval⟩ := Subgroup.mem_map.mp he₁'
  let φ : ↥N ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBA
  have he_mem : A.subtype e₁ ∈ (CFSG.layer ↥B).map B.subtype := by
    refine Subgroup.mem_map.mpr ⟨φ ef, ?_, ?_⟩
    · exact s15_layer_map_le_of_mulEquiv φ (Subgroup.mem_map.mpr ⟨ef, hef, rfl⟩)
    · rw [← hefval]
      rfl
  have hc : A.subtype (f * e₂) ∈
      Subgroup.centralizer ((CFSG.layer ↥B).map B.subtype : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    let w : ↥N := φ.symm z
    have hw : w ∈ CFSG.layer ↥N :=
      s15_layer_map_le_of_mulEquiv φ.symm (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
    have hwN : N.subtype w ∈ N := w.2
    have hwL : N.subtype w ∈ CFSG.layer ↥A :=
      CFSG.RankThree.PartTwo.Sec3.layer_map_le_of_normal hNn
        (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
    have hcomm : (f * e₂) * (N.subtype w) = (N.subtype w) * (f * e₂) :=
      commute_fitting_mul_comps_of_mem hNn hf he₂ hwN hwL
    have hzφ : B.subtype z = A.subtype (N.subtype w) := by
      rw [show z = φ w from (φ.apply_symm_apply z).symm]
      rfl
    rw [hzφ]
    simp only [← map_mul]
    rw [hcomm]
  refine ⟨A.subtype (f * e₂), (f * e₂).2, A.subtype e₁, he_mem, ?_, ?_⟩
  · exact fun x hx => (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  · have hae' : a = A.subtype (f * e₁ * e₂) := by
      rw [← hae]
      rfl
    rw [hae']
    have hfac : f * e₁ * e₂ = (f * e₂) * e₁ := by
      calc f * e₁ * e₂ = f * (e₁ * e₂) := mul_assoc f e₁ e₂
        _ = f * (e₂ * e₁) := by rw [h12]
        _ = (f * e₂) * e₁ := (mul_assoc f e₂ e₁).symm
    rw [hfac, map_mul]

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
