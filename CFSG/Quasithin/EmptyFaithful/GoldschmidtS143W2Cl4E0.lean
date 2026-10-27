module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompX
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Cl4Odd
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {L : Subgroup G}

theorem card_outer_u33 {K : Type} [Group K]
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 3 1) :
    Nat.card (Outer K) = 2 := by
  obtain ⟨-, -, h3, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound K 3 3 1 hmod
  rw [h3]
  norm_num

theorem x_mem_comp (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x))
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1) : x ∈ L := by
  have hLN := normalizer_of_component h hf hL
  exact mem_of_orderOf_three hL.1 hLN (pCoreOf_isPGroup 2 (Gw d x))
    (inf_centralizer_eq_pCoreOf h hf hL hLN).le (card_outer_u33 hmod) h.x_mem_Gw h.hx3

theorem E0_le_comp (h : Ctx T M g A t d x) (hf : LocalFacts T d x)
    (hL : IsComponentIn L (Gw d x))
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1) :
    rOf T M ⊓ Gw d x ≤ L := by
  have hLN := normalizer_of_component h hf hL
  have hxL : x ∈ L := x_mem_comp h hf hL hmod
  set E : Subgroup G := rOf T M ⊓ Gw d x with hE
  obtain ⟨eZ⟩ := h.hR
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b =>
    eZ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hcommG : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxN := x_mem_normalizer_E0 h
  have hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun e he => (Subgroup.mem_normalizer_iff.mp hxN e).mp he
  let φ : ↥E → ↥E := fun e =>
    ⟨x * (e : G) * x⁻¹ * (e : G)⁻¹, E.mul_mem (hxE e e.2) (E.inv_mem e.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : x * (a : G) * x⁻¹ * (a : G)⁻¹ = x * (b : G) * x⁻¹ * (b : G)⁻¹ :=
      congrArg Subtype.val hab
    set u : G := x * (a : G) * x⁻¹ * (a : G)⁻¹ with hu
    have huE : u ∈ E := (φ a).2
    have hxa : x * (a : G) * x⁻¹ = u * a := by rw [hu]; group
    have hxb : x * (b : G) * x⁻¹ = u * b := by
      have : x * (b : G) * x⁻¹ = (x * (b : G) * x⁻¹ * (b : G)⁻¹) * b := by group
      rw [this, ← h1]
    have hab' : (a : G) * (b : G)⁻¹ ∈ E := E.mul_mem a.2 (E.inv_mem b.2)
    have hc : x * ((a : G) * (b : G)⁻¹) * x⁻¹ = (a : G) * (b : G)⁻¹ := by
      calc x * ((a : G) * (b : G)⁻¹) * x⁻¹
          = (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹)⁻¹ := by group
        _ = u * ((a : G) * (b : G)⁻¹) * u⁻¹ := by rw [hxa, hxb]; group
        _ = (a : G) * (b : G)⁻¹ := by rw [hcommG u huE _ hab']; group
    have h0 := E0_fpf h hab' hc
    exact Subtype.ext (mul_inv_eq_one.mp h0)
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro e he
  obtain ⟨e', he'⟩ := hsurj ⟨e, he⟩
  have h2 : (e : G) = x * (e' : G) * x⁻¹ * (e' : G)⁻¹ := (congrArg Subtype.val he').symm
  have h3 : (e' : G) * x⁻¹ * (e' : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hLN e'.2.2) x⁻¹).mp (L.inv_mem hxL)
  rw [h2, show x * (e' : G) * x⁻¹ * (e' : G)⁻¹ = x * ((e' : G) * x⁻¹ * (e' : G)⁻¹) by group]
  exact L.mul_mem hxL h3

theorem z_mem_E0 (h : Ctx T M g A t d x) : d * d ∈ rOf T M ⊓ Gw d x := by
  have hzV : d * d ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M h.z_mem
  have hzA : d * d ∈ A := by
    rw [h.c18.b.v_eq_inf] at hzV
    exact hzV.1
  exact ⟨h.c18.b.A_le hzA, h.z_mem_Gw⟩

end InspW2

end S143

end CFSG.Quasithin
