module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBar
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBarDown
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T A L K : Subgroup G} {i : ℕ}
  {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}

section SitHelpers

private theorem wc813psit_barSub_mono {X Y : Subgroup G} (hXY : X ≤ Y) :
    barSub H φ X ≤ barSub H φ Y := by
  change (X.subgroupOf H).map φ ≤ (Y.subgroupOf H).map φ
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hXY)

private theorem wc813psit_barSub_inf_of_le (hφ : IsBarMap H (cGrp H T) φ) {X Y : Subgroup G}
    (hCY : cGrp H T ≤ Y) : barSub H φ X ⊓ barSub H φ Y = barSub H φ (X ⊓ Y) := by
  refine le_antisymm ?_ (le_inf
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left))
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_right)))
  intro x hx
  obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, haX, haφ⟩ := mem_barSub.mp hxX
  obtain ⟨b, hbY, hbφ⟩ := mem_barSub.mp hxY
  have hker : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, haφ, hbφ, mul_inv_cancel]
  have hmemC : ((a * b⁻¹ : ↥H) : G) ∈ cGrp H T := (hφ.ker_iff (a * b⁻¹)).mp hker
  have hmemY : ((a * b⁻¹ : ↥H) : G) ∈ Y := hCY hmemC
  have haY : (a : G) ∈ Y := by
    have h2 : ((a * b⁻¹ : ↥H) : G) * (b : G) = (a : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← h2]
    exact Y.mul_mem hmemY hbY
  exact mem_barSub.mpr ⟨a, Subgroup.mem_inf.mpr ⟨haX, haY⟩, haφ⟩

private theorem wc813psit_relIndex_barSub (hφ : IsBarMap H (cGrp H T) φ)
    (hCH : cGrp H T ≤ H) {X Y : Subgroup G} (hXY : X ≤ Y) (hYH : Y ≤ H)
    (hCY : cGrp H T ≤ Y) :
    (barSub H φ X).relIndex (barSub H φ Y) = (X ⊔ cGrp H T).relIndex Y := by
  have hXH : X ≤ H := hXY.trans hYH
  have hker : φ.ker = (cGrp H T).subgroupOf H := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  change (((X.subgroupOf H).map φ).relIndex ((Y.subgroupOf H).map φ)) =
    (X ⊔ cGrp H T).relIndex Y
  rw [Subgroup.relIndex_map_map, hker, ← Subgroup.subgroupOf_sup hXH hCH,
    sup_eq_left.mpr (Subgroup.subgroupOf_mono H hCY), Subgroup.relIndex_subgroupOf hYH]

private theorem wc813psit_shape_barSub (hφ : IsBarMap H (cGrp H T) φ) (hLH : L ≤ H)
    (hCL : cGrp H T ≤ L) {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape L (cGrp H T : Set G) P) :
    HasQuotShape (barSub H φ L) ((⊥ : Subgroup Q) : Set Q) P := by
  have hker : barSub H φ (cGrp H T) = ⊥ := by
    rw [← barPre_bot hφ inf_le_left, barSub_barPre hφ]
  have h1 := hasQuotShape_barSub (C := cGrp H T) hφ (le_refl _) hCL hLH h
  rwa [hker] at h1

private theorem wc813psit_conjClosure_le_barSub (hφ : IsBarMap H (cGrp H T) φ) (hLH : L ≤ H) :
    conjClosure (barSub H φ L) ⊤ ≤ barSub H φ (conjClosure L H) := by
  refine conjClosure_le fun q _ x hx => ?_
  obtain ⟨g, rfl⟩ := hφ.surjective q
  obtain ⟨z, hzL, rfl⟩ := mem_barSub.mp hx
  exact mem_barSub.mpr ⟨g * z * g⁻¹, mem_conjClosure g.2 hzL, by
    rw [map_mul, map_mul, map_inv]⟩

end SitHelpers

theorem Sit813.isComponentOf_barSub (h : Sit813 V H T i A L K)
    (hφ : IsBarMap H (cGrp H T) φ) : IsComponentOf (barSub H φ L) ⊤ := by
  have hker : barSub H φ (cGrp H T) = ⊥ := by
    rw [← barPre_bot hφ inf_le_left, barSub_barPre hφ]
  have hcomp := isComponentModN_barSub (C := cGrp H T) (N := cGrp H T) hφ
    (le_refl _) h.concl813.comp
  rw [hker] at hcomp
  obtain ⟨-, -, -, hsub, hshape⟩ := hcomp
  obtain ⟨X, hX, ψ, hψ, hkerψ, hqs⟩ := hshape
  letI : Group X := hX
  have hinj : Function.Injective ψ := by
    intro a b hab
    have h1 : ψ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab]; group
    have h2 : ((a * b⁻¹ : ↥(barSub H φ L)) : Q) ∈ (⊥ : Subgroup Q) := (hkerψ _).mp h1
    have h3 : ((a * b⁻¹ : ↥(barSub H φ L)) : Q) = 1 := Subgroup.mem_bot.mp h2
    have h4 : a * b⁻¹ = 1 := Subtype.ext h3
    exact mul_inv_eq_one.mp h4
  refine ⟨le_top, hsub, ?_⟩
  have hqs' : Open.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open X).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mpr hqs)
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩) hqs'

theorem Sit813.caseAB_barSub (h : Sit813 V H T i A L K) (hφ : IsBarMap H (cGrp H T) φ)
    (hAB : Case813AB (cGrp H T) L K) :
    Case813AB (⊥ : Subgroup Q) (barSub H φ L) (barSub H φ K) := by
  have hker : barSub H φ (cGrp H T) = ⊥ := by
    rw [← barPre_bot hφ inf_le_left, barSub_barPre hφ]
  have hLH : L ≤ H := h.concl813.comp.2.2.1
  have hCL : cGrp H T ≤ L := h.concl813.ge_C.trans h.concl813.sub_L
  rcases hAB with hL2 | ⟨hr, P, hP, hKeq⟩
  · exact Or.inl (wc813psit_shape_barSub hφ hLH hCL hL2)
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hr with h3 | h4 | h5
      · exact Or.inl (wc813psit_shape_barSub hφ hLH hCL h3)
      · exact Or.inr (Or.inl (wc813psit_shape_barSub hφ hLH hCL h4))
      · exact Or.inr (Or.inr (wc813psit_shape_barSub hφ hLH hCL h5))
    · refine ⟨barSub H φ P, ?_, ?_⟩
      · have h1 := isMaxParabolicMod_barSub (C := cGrp H T) (N := cGrp H T) hφ
          (le_refl _) hLH hP
        rwa [hker] at h1
      · have hCP : cGrp H T ≤ P := hP.1
        have hPH : P ≤ H := hP.2.1.le.trans hLH
        have hodd := oddResMod_barPre hφ inf_le_left (barSub H φ P)
        rw [barPre_barSub hφ hCP hPH] at hodd
        calc barSub H φ K = barSub H φ (oddResMod (cGrp H T) P) := by rw [hKeq]
          _ = barSub H φ (barPre H φ (oddResMod (⊥ : Subgroup Q) (barSub H φ P))) := by
                rw [hodd]
          _ = oddResMod (⊥ : Subgroup Q) (barSub H φ P) := barSub_barPre hφ _

theorem Sit813.caseUC_barSub (h : Sit813 V H T i A L K) (hφ : IsBarMap H (cGrp H T) φ)
    (hUC : Case813UC (cGrp H T) H T A L) :
    Case813UC (⊥ : Subgroup Q) ⊤ (barSub H φ T) (barSub H φ A) (barSub H φ L) := by
  have hLH : L ≤ H := h.concl813.comp.2.2.1
  have hCL : cGrp H T ≤ L := h.concl813.ge_C.trans h.concl813.sub_L
  rcases hUC with hU3 | ⟨hr, hcent⟩
  · exact Or.inl (wc813psit_shape_barSub hφ hLH hCL hU3)
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hr with h3 | h4 | h5
      · exact Or.inl (wc813psit_shape_barSub hφ hLH hCL h3)
      · exact Or.inr (Or.inl (wc813psit_shape_barSub hφ hLH hCL h4))
      · exact Or.inr (Or.inr (wc813psit_shape_barSub hφ hLH hCL h5))
    · intro a ha t ht
      obtain ⟨a', ha'A, ha'φ⟩ := mem_barSub.mp ha
      obtain ⟨htT, htC⟩ := Subgroup.mem_inf.mp ht
      obtain ⟨t₀, ht₀T, ht₀φ⟩ := mem_barSub.mp htT
      have hclift : t ∈ barSub H φ (conjClosure L H) :=
        wc813psit_conjClosure_le_barSub hφ hLH htC
      obtain ⟨y, hyC, hyφ⟩ := mem_barSub.mp hclift
      have hker : φ (t₀ * y⁻¹) = 1 := by
        rw [map_mul, map_inv, ht₀φ, hyφ]
        group
      have hmemC : ((t₀ * y⁻¹ : ↥H) : G) ∈ cGrp H T := (hφ.ker_iff (t₀ * y⁻¹)).mp hker
      have ht₀C : (t₀ : G) ∈ conjClosure L H := by
        have h1 : ((t₀ * y⁻¹ : ↥H) : G) ∈ conjClosure L H :=
          le_conjClosure L H (hCL hmemC)
        have heq : (t₀ : G) = ((t₀ * y⁻¹ : ↥H) : G) * (y : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [heq]
        exact (conjClosure L H).mul_mem h1 hyC
      have hcent₀ : (a' : G) * (t₀ : G) * (a' : G)⁻¹ * (t₀ : G)⁻¹ ∈ cGrp H T :=
        hcent (a' : G) ha'A (t₀ : G) ⟨ht₀T, ht₀C⟩
      have htriv : φ (a' * y * a'⁻¹ * y⁻¹) = 1 := by
        have h1 : φ (a' * y * a'⁻¹ * y⁻¹) = φ (a' * t₀ * a'⁻¹ * t₀⁻¹) := by
          simp only [map_mul, map_inv]
          rw [hyφ, ht₀φ]
        rw [h1]
        refine (hφ.ker_iff (a' * t₀ * a'⁻¹ * t₀⁻¹)).mpr ?_
        rw [show ((a' * t₀ * a'⁻¹ * t₀⁻¹ : ↥H) : G) =
            (a' : G) * (t₀ : G) * (a' : G)⁻¹ * (t₀ : G)⁻¹ from by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]]
        exact hcent₀
      rw [← ha'φ, ← hyφ, Subgroup.mem_bot]
      rw [show φ a' * φ y * (φ a')⁻¹ * (φ y)⁻¹ = φ (a' * y * a'⁻¹ * y⁻¹) from by
        simp only [map_mul, map_inv]]
      exact htriv

theorem Sit813.isSylowIn_barSub (h : Sit813 V H T i A L K) (hφ : IsBarMap H (cGrp H T) φ) :
    IsSylowIn 2 (barSub H φ T ⊓ barSub H φ K) (barSub H φ K) := by
  have hKH : K ≤ H := h.concl813.sub_L.trans h.concl813.comp.2.2.1
  have hCK : cGrp H T ≤ K := h.concl813.ge_C
  have hCH : cGrp H T ≤ H := hCK.trans hKH
  have hSyl : IsSylowIn 2 (T ⊓ K) K := h.concl813.t_sylow
  rw [wc813psit_barSub_inf_of_le (X := T) (Y := K) hφ hCK]
  refine ⟨wc813psit_barSub_mono inf_le_right, ?_, ?_⟩
  · have hp : IsPGroup 2 ((T ⊓ K).subgroupOf H) :=
      hSyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hKH)).symm
    exact hp.map φ
  · rw [wc813psit_relIndex_barSub hφ hCH inf_le_right hKH hCK]
    intro h2
    have hdvd : ((T ⊓ K) ⊔ cGrp H T).relIndex K ∣ (T ⊓ K).relIndex K :=
      ⟨(T ⊓ K).relIndex ((T ⊓ K) ⊔ cGrp H T), by
        rw [mul_comm]
        exact (Subgroup.relIndex_mul_relIndex (H := T ⊓ K)
          (K := (T ⊓ K) ⊔ cGrp H T) (L := K) le_sup_left
          (sup_le inf_le_right hCK)).symm⟩
    exact hSyl.not_dvd_relIndex (h2.trans hdvd)

end CFSG.LocalAnalysis.WeakClosure81

end
