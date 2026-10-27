module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

theorem exists_monoidHom_of_index_two_extension
    {G H : Type*} [Group G] [Group H]
    (hGidx : (commutator G).index = 2)
    (ψ : commutator G ≃* commutator H)
    {d : G} {r : H} (hd2 : d * d = 1) (hr2 : r * r = 1)
    (hd : d ∉ commutator G) (hr : r ∉ commutator H)
    (hconj : ∀ x : commutator G,
      (ψ ⟨d * (x : G) * d⁻¹, by
        haveI : (commutator G).Normal := inferInstance
        exact (inferInstance : (commutator G).Normal).conj_mem (x : G) x.2 d⟩ : H) =
        r * (ψ x : H) * r⁻¹) :
    ∃ φ : G →* H, (∀ x : commutator G, φ x = ψ x) ∧ φ d = r ∧ Function.Injective φ := by
  classical
  have hdinv : d⁻¹ ∉ commutator G := fun h => hd (by simpa using (commutator G).inv_mem h)
  let mem : ∀ g : G, g ∉ commutator G → g * d⁻¹ ∈ commutator G := fun g hg =>
    (Subgroup.mul_mem_iff_of_index_two hGidx).mpr (iff_of_false hg hdinv)
  let Ψ : commutator G →* H := (Subgroup.subtype (commutator H)).comp ψ.toMonoidHom
  have hΨ : ∀ x : commutator G, Ψ x = (ψ x : H) := fun x => rfl
  have hΨinj : Function.Injective Ψ := fun a b h => ψ.injective (Subtype.ext h)
  let f : G → H := fun g =>
    if hg : g ∈ commutator G then Ψ ⟨g, hg⟩ else Ψ ⟨g * d⁻¹, mem g hg⟩ * r
  have hf_pos : ∀ g (hg : g ∈ commutator G), f g = Ψ ⟨g, hg⟩ := by
    intro g hg; simp only [f, dif_pos hg]
  have hf_neg : ∀ g (hg : g ∉ commutator G), f g = Ψ ⟨g * d⁻¹, mem g hg⟩ * r := by
    intro g hg; simp only [f, dif_neg hg]
  have hrψ : ∀ x : commutator G, r * Ψ x = (Ψ ⟨d * (x : G) * d⁻¹, by
        haveI : (commutator G).Normal := inferInstance
        exact (inferInstance : (commutator G).Normal).conj_mem (x : G) x.2 d⟩ : H) * r := by
    intro x
    have h2 : Ψ ⟨d * (x : G) * d⁻¹, _⟩ = r * Ψ x * r⁻¹ := hconj x
    rw [h2]
    group
  have hd_eq : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hmul : ∀ a b : G, f (a * b) = f a * f b := by
    intro a b
    by_cases ha : a ∈ commutator G
    · by_cases hb : b ∈ commutator G
      · have hab : a * b ∈ commutator G := (commutator G).mul_mem ha hb
        rw [hf_pos _ ha, hf_pos _ hb, hf_pos _ hab, ← map_mul Ψ]
        rw [hΨinj.eq_iff]
        exact Subtype.ext rfl
      · have hab : a * b ∉ commutator G := fun h =>
          hb (by simpa using (commutator G).mul_mem ((commutator G).inv_mem ha) h)
        rw [hf_pos _ ha, hf_neg _ hb, hf_neg _ hab, ← mul_assoc, ← map_mul Ψ,
          mul_right_cancel_iff]
        rw [hΨinj.eq_iff]
        refine Subtype.ext ?_
        show (a * b) * d⁻¹ = a * (b * d⁻¹)
        group
    · by_cases hb : b ∈ commutator G
      · have hab : a * b ∉ commutator G := fun h =>
          ha (by simpa using (commutator G).mul_mem h ((commutator G).inv_mem hb))
        rw [hf_neg _ ha, hf_pos _ hb, hf_neg _ hab]
        have h1 : (Ψ ⟨a * d⁻¹, mem a ha⟩ * r) * Ψ ⟨b, hb⟩
            = Ψ ⟨a * d⁻¹, mem a ha⟩ * (r * Ψ ⟨b, hb⟩) := by group
        rw [h1, hrψ ⟨b, hb⟩, ← mul_assoc, ← map_mul Ψ, mul_right_cancel_iff]
        rw [hΨinj.eq_iff]
        refine Subtype.ext ?_
        show (a * b) * d⁻¹ = (a * d⁻¹) * (d * b * d⁻¹)
        group
      · have hab : a * b ∈ commutator G :=
          (Subgroup.mul_mem_iff_of_index_two hGidx).mpr (iff_of_false ha hb)
        rw [hf_neg _ ha, hf_neg _ hb, hf_pos _ hab]
        have h1 : (Ψ ⟨a * d⁻¹, mem a ha⟩ * r) * (Ψ ⟨b * d⁻¹, mem b hb⟩ * r)
            = Ψ ⟨a * d⁻¹, mem a ha⟩ * (r * Ψ ⟨b * d⁻¹, mem b hb⟩) * r := by group
        rw [h1, hrψ ⟨b * d⁻¹, mem b hb⟩]
        have h2 : Ψ ⟨a * d⁻¹, mem a ha⟩ * (Ψ ⟨d * ((⟨b * d⁻¹, mem b hb⟩ : commutator G) : G) * d⁻¹,
              by
                haveI : (commutator G).Normal := inferInstance
                exact (inferInstance : (commutator G).Normal).conj_mem
                  ((⟨b * d⁻¹, mem b hb⟩ : commutator G) : G)
                  (⟨b * d⁻¹, mem b hb⟩ : commutator G).2 d⟩ * r) * r
            = (Ψ ⟨a * d⁻¹, mem a ha⟩ * Ψ ⟨d * ((⟨b * d⁻¹, mem b hb⟩ : commutator G) : G) * d⁻¹,
                by
                  haveI : (commutator G).Normal := inferInstance
                  exact (inferInstance : (commutator G).Normal).conj_mem
                    ((⟨b * d⁻¹, mem b hb⟩ : commutator G) : G)
                    (⟨b * d⁻¹, mem b hb⟩ : commutator G).2 d⟩) * (r * r) := by group
        rw [h2, hr2, mul_one, ← map_mul Ψ]
        rw [hΨinj.eq_iff]
        refine Subtype.ext ?_
        show (a * b : G) = (a * d⁻¹) * (d * (b * d⁻¹) * d⁻¹)
        rw [hd_eq, show (a * d) * (d * (b * d) * d) = a * (d * d) * b * (d * d) by group,
          hd2]
        group
  have hker : ∀ g : G, f g = 1 → g = 1 := by
    intro g hg
    by_cases h : g ∈ commutator G
    · rw [hf_pos _ h] at hg
      have h1 : (⟨g, h⟩ : commutator G) = 1 := by
        apply ψ.injective
        rw [map_one]
        exact Subtype.ext hg
      exact Subtype.ext_iff.mp h1
    · rw [hf_neg _ h] at hg
      have h2 : Ψ ⟨g * d⁻¹, mem g h⟩ = r := by
        have h3 := congrArg (· * r⁻¹) hg
        simpa [mul_assoc, hr2, inv_eq_of_mul_eq_one_right hr2] using h3
      have h4 : (ψ ⟨g * d⁻¹, mem g h⟩ : H) = r := by rw [← hΨ]; exact h2
      exact absurd (h4 ▸ (ψ ⟨g * d⁻¹, mem g h⟩).2) hr
  let φ : G →* H := MonoidHom.mk' f hmul
  have hφ : ∀ g, φ g = f g := fun g => rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x
    rw [hφ, hf_pos _ x.2]
    rfl
  · have h1 : Ψ ⟨d * d⁻¹, mem d hd⟩ = 1 := by
      have h2 : (⟨d * d⁻¹, mem d hd⟩ : commutator G) = 1 := Subtype.ext (mul_inv_cancel d)
      rw [h2, map_one]
    rw [hφ, hf_neg _ hd, h1, one_mul]
  · intro a b hab
    rw [← mul_inv_eq_one]
    apply hker
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    rwa [← hφ]

end CFSG.OddTranspositions.PartThree

namespace CFSG.OddTranspositions.PartThree

theorem monoidHom_eq_of_center_diff_mem {A B : Type*} [Group A] [Group B]
    (hperf : commutator A = ⊤) {f₁ f₂ : A →* B}
    (hZ : ∀ x : A, f₁ x * (f₂ x)⁻¹ ∈ Subgroup.center B) : f₁ = f₂ := by
  classical
  let g : A → Subgroup.center B := fun x => ⟨f₁ x * (f₂ x)⁻¹, hZ x⟩
  have hz : ∀ z : A, f₁ z = (g z : B) * f₂ z := by
    intro z
    show f₁ z = f₁ z * (f₂ z)⁻¹ * f₂ z
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hmul : ∀ x y : A, g (x * y) = g x * g y := by
    intro x y
    have hxy : f₁ (x * y) = ((g x : B) * (g y : B)) * f₂ (x * y) := by
      calc f₁ (x * y) = f₁ x * f₁ y := map_mul _ _ _
        _ = ((g x : B) * f₂ x) * ((g y : B) * f₂ y) := by rw [hz, hz]
        _ = ((g x : B) * (g y : B)) * (f₂ x * f₂ y) := by
              have hc' : Commute (f₂ x) (g y : B) := Subgroup.mem_center_iff.mp (g y).2 (f₂ x)
              rw [show (g x : B) * f₂ x * ((g y : B) * f₂ y)
                  = (g x : B) * (f₂ x * (g y : B)) * f₂ y by group]
              rw [hc'.eq]
              group
        _ = ((g x : B) * (g y : B)) * f₂ (x * y) := by rw [map_mul]
    apply Subtype.ext
    simpa using mul_right_cancel ((hz (x * y)).symm.trans hxy)
  let h : A →* Subgroup.center B := MonoidHom.mk' g hmul
  have hker : h.ker = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Abelianization.commutator_subset_ker h
  have h1 : h = 1 := MonoidHom.ext fun x => by
    have hx : x ∈ h.ker := by rw [hker]; exact Subgroup.mem_top x
    rwa [MonoidHom.mem_ker] at hx
  ext x
  have hx : (f₁ x * (f₂ x)⁻¹ : B) = 1 := by
    have hφx : h x = 1 := by rw [h1]; rfl
    change ((g x : Subgroup.center B) : B) = 1
    rw [show g x = h x from rfl, hφx]
    rfl
  exact mul_inv_eq_one.mp hx

end CFSG.OddTranspositions.PartThree

