module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixU
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
import CFSG.Quasithin.EmptyFaithful.S152VR1

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q] [Finite Q]

theorem Datum.mem_centralizer_of_chart {p : ℕ} {B Bs X Z : Subgroup G}
    {f : ↥(Subgroup.normalizer (X : Set G)) →* Q}
    (hD : Datum p (Subgroup.normalizer (X : Set G)) f X Bs Z) (hX : Group.IsPerfect ↥X)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* Q}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p (img _ f B) (img _ f Bs) K 1 n ψ)
    (hrange : ψ.range = img _ f X) (hd : GGActsDiagonally (p := 2) (f := 1) ψ (img _ f Bs))
    (hfull : Nat.card ↥(img _ f Bs) =
      3 ^ (n - 1) * Nat.card ↥(img _ f Bs ⊓ Subgroup.centralizer (img _ f X : Set Q)))
    {t : G} (htC : t ∈ Subgroup.centralizer (Bs : Set G))
    (htN : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.centralizer (X : Set G) := by
  have hCq : f ⟨t, htN⟩ ∈ Subgroup.centralizer (img _ f Bs : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨b, hb, rfl⟩ := mem_img.1 hq
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 htC) _ hb)
  have hNq : f ⟨t, htN⟩ ∈ Subgroup.normalizer (img _ f X : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      obtain ⟨u, hu, rfl⟩ := mem_img.1 hq
      refine mem_img.2 ⟨⟨t, htN⟩ * u * ⟨t, htN⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.1 htN _).1 hu
    · intro hq
      obtain ⟨u, hu, hut⟩ := mem_img.1 hq
      refine mem_img.2 ⟨⟨t, htN⟩⁻¹ * u * ⟨t, htN⟩, ?_, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem htN) _).1 hu
        simpa using h'
      · rw [map_mul, map_mul, map_inv, hut]
        group
  have h2q : (f ⟨t, htN⟩) ^ 2 = 1 := by
    have h1 : (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simpa using ht2)
    rw [← map_pow, h1, map_one]
  have hcent := QTwo.qtwoDL1_invFix_unit hK h hrange hd hfull hCq hNq h2q
  have hcomm : ∀ x ∈ X, t * x * t⁻¹ * x⁻¹ ∈ Z := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (X : Set G) := hD.LN hx
    have hmem : t * x * t⁻¹ * x⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      mul_mem (mul_mem (mul_mem htN hxN) (inv_mem htN)) (inv_mem hxN)
    apply (hD.mem_ker_iff ⟨t * x * t⁻¹ * x⁻¹, hmem⟩).1
    rw [MonoidHom.mem_ker]
    have e : (⟨t * x * t⁻¹ * x⁻¹, hmem⟩ : ↥(Subgroup.normalizer (X : Set G))) =
        ⟨t, htN⟩ * ⟨x, hxN⟩ * ⟨t, htN⟩⁻¹ * ⟨x, hxN⟩⁻¹ := rfl
    have hc := (Subgroup.mem_centralizer_iff.1 hcent) (f ⟨x, hxN⟩)
      (mem_img.2 ⟨⟨x, hxN⟩, hx, rfl⟩)
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have hα := CFSG.Quasithin.S152V.mulAut_eq_one_of_central hX
    (X.normalizerMonoidHom ⟨t, htN⟩) fun x => by
      have hc := hcomm x x.2
      have hcx := hD.Zcent _ hc x x.2
      have hmem : (x : G)⁻¹ * (t * x * t⁻¹) ∈ Z := by
        have e : (x : G)⁻¹ * (t * x * t⁻¹) = t * x * t⁻¹ * (x : G)⁻¹ :=
          calc (x : G)⁻¹ * (t * x * t⁻¹) = (x : G)⁻¹ * ((t * x * t⁻¹ * (x : G)⁻¹) * x) := by
                group
            _ = (x : G)⁻¹ * (x * (t * x * t⁻¹ * (x : G)⁻¹)) := by rw [hcx]
            _ = t * x * t⁻¹ * (x : G)⁻¹ := by group
        rw [e]
        exact hc
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hD.Zcent _ hmem l l.2)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : t * x * t⁻¹ = x :=
    congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : G)) hα
  exact (mul_inv_eq_iff_eq_mul.1 hx').symm

end NsQuot

namespace QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {B Bs X : Subgroup G} {z : Additive ↥Bs ≃+ DVec 6}

theorem GGQTwoDNbrSixFrame.mem_centralizer (Φ : GGQTwoDNbrSixFrame B Bs X z)
    {t : G} (htC : t ∈ Subgroup.centralizer (Bs : Set G))
    (htN : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.centralizer (X : Set G) := by
  refine Φ.datum.mem_centralizer_of_chart Φ.perfect Φ.card_K Φ.hyp Φ.range Φ.diag ?_ htC htN ht2
  rw [Φ.datum.card_img le_rfl, card_bs_of_module z, Φ.datum.cent Φ.perfect le_rfl, Φ.cent]
  norm_num

end QTwo

end CFSG.StandardType

end
