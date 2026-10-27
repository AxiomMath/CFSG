module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelectedBase
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Quotient36 CFSG.Assembly
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_centralizer_of_scalar {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {L D R : Subgroup G} (hLD : L ≤ Subgroup.normalizer (D : Set G)) (hDq : IsPGroup q D)
    (hRL : R ≤ L) (hR2 : IsPGroup 2 R) (hRf : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hRext : IsExtraspecialPGroup 2 ↥R) (hRcard : Nat.card R = 2 ^ (1 + 2 * 2))
    (hDfr : (inSubgroup frattini D).relIndex D = q ^ 4) {b : G} (hbL : b ∈ L)
    (hbR : b ∈ Subgroup.centralizer (R : Set G)) {s : G} (hsL : s ∈ L)
    (hs : ¬ q ∣ orderOf (s * b * s⁻¹ * b⁻¹)) :
    s * b * s⁻¹ * b⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q ↥D) := ⟨hDq⟩
  have : Subgroup.Normalizes L D := ⟨hLD⟩
  let ρ : Representation (ZMod q) ↥L (Additive (↥D ⧸ frattini ↥D)) :=
    frattiniRep (E := ↥L) (X := ↥D) q
  let ρR : Representation (ZMod q) ↥R (Additive (↥D ⧸ frattini ↥D)) :=
    ρ.comp (Subgroup.inclusion hRL)
  have hsmul : ∀ (g : ↥L) (x : ↥D), ((g • x : ↥D) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
    fun g x => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe L D g x
  have hord2 : ∀ r : ↥R, ¬ q ∣ orderOf r := by
    intro r hdvd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) r
    have h2 : q ∣ 2 ^ k := hk ▸ hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  have hinj : Function.Injective ρR := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hr' : ρ (Subgroup.inclusion hRL r) = 1 := hr
    have htriv : ∀ x : ↥D, ((((Subgroup.inclusion hRL r : ↥L) • x : ↥D)) : ↥D ⧸ frattini ↥D) =
        (x : ↥D ⧸ frattini ↥D) := by
      intro x
      have h1 := frattiniRep_apply_mk (E := ↥L) (X := ↥D) q (Subgroup.inclusion hRL r) x
      have h2 : ρ (Subgroup.inclusion hRL r) (Additive.ofMul (x : ↥D ⧸ frattini ↥D)) =
          Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hr']; rfl
      exact Additive.ofMul.injective (h1.symm.trans h2)
    have hnot : ¬ q ∣ orderOf (Subgroup.inclusion hRL r) := by
      rw [orderOf_injective (Subgroup.inclusion hRL) (Subgroup.inclusion_injective hRL) r]
      exact hord2 r
    have hfix := smul_eq_of_smul_mk_eq hDq (Subgroup.inclusion hRL r) hnot htriv
    have hmem : (r : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨r.2, ?_⟩
      show (r : G) ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg (fun y : ↥D => (y : G)) (hfix ⟨d, hd⟩)
      simp only [hsmul] at h1
      have h2 : (r : G) * d = d * r := by
        calc (r : G) * d = ((r : G) * d * (r : G)⁻¹) * r := by group
          _ = d * r := by rw [Subgroup.coe_inclusion] at h1; rw [h1]
      exact h2.symm
    rw [hRf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcardV : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
    rw [← hDfr, Lifting36.relIndex_frattini_eq_card_quotient]
    rfl
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 2 ^ 2 := by
    have h1 : Nat.card (Additive (↥D ⧸ frattini ↥D)) =
        q ^ Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
    rw [hcardV] at h1
    have := Nat.pow_right_injective hq.two_le h1
    omega
  have : FiniteDimensional (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  obtain ⟨z, hz⟩ := Lifting36.exists_center_eq_zpowers hRext
  have hK : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨-, -, hcent, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.minimal_extraspecial_module_scalar_centralizer.{
      0, 0, 0, 0} hRext hRcard hz hK hdim ρR hinj
  let bE : ↥L := ⟨b, hbL⟩
  have hu : ρ.asGroupHom bE ∈ Subgroup.centralizer (Set.range ρR.asGroupHom) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    have hcomm : Subgroup.inclusion hRL r * bE = bE * Subgroup.inclusion hRL r := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hbR (r : G) r.2
      simpa using this
    change ρ.asGroupHom (Subgroup.inclusion hRL r) * ρ.asGroupHom bE =
      ρ.asGroupHom bE * ρ.asGroupHom (Subgroup.inclusion hRL r)
    rw [← map_mul, ← map_mul, hcomm]
  rw [hcent] at hu
  obtain ⟨c, hc⟩ := hu
  have hρb : ρ.asGroupHom bE = Units.map (algebraMap (ZMod q)
      (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))).toMonoidHom c := hc.symm
  let sE : ↥L := ⟨s, hsL⟩
  set g : ↥L := sE * bE * sE⁻¹ * bE⁻¹ with hg
  have hscalar_comm : ∀ u : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ,
      u * ρ.asGroupHom bE = ρ.asGroupHom bE * u := by
    intro u
    rw [hρb]
    apply Units.ext
    apply LinearMap.ext
    intro v
    simp
  have hρg : ρ.asGroupHom g = 1 := by
    rw [hg, map_mul, map_mul, map_mul, map_inv, map_inv, hscalar_comm (ρ.asGroupHom sE)]
    group
  have htriv : ∀ x : ↥D, ((g • x : ↥D) : ↥D ⧸ frattini ↥D) = (x : ↥D ⧸ frattini ↥D) := by
    intro x
    have h1 := frattiniRep_apply_mk (E := ↥L) (X := ↥D) q g x
    have h2 : ρ g (Additive.ofMul (x : ↥D ⧸ frattini ↥D)) =
        Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by
      have hgg : ((ρ.asGroupHom g : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
          Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D))) = ρ g :=
        Representation.asGroupHom_apply ρ g
      rw [← hgg, hρg]
      rfl
    exact Additive.ofMul.injective (h1.symm.trans h2)
  have hgo : ¬ q ∣ orderOf g := by
    rw [← Subgroup.orderOf_coe]
    exact hs
  have hfix := smul_eq_of_smul_mk_eq hDq g hgo htriv
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 := congrArg (fun y : ↥D => (y : G)) (hfix ⟨d, hd⟩)
  simp only [hsmul] at h1
  have h1' : (g : G) * d * (g : G)⁻¹ = d := h1
  have hgG : (g : G) = s * b * s⁻¹ * b⁻¹ := rfl
  rw [hgG] at h1'
  calc d * (s * b * s⁻¹ * b⁻¹) = (s * b * s⁻¹ * b⁻¹ * d * (s * b * s⁻¹ * b⁻¹)⁻¹) *
        (s * b * s⁻¹ * b⁻¹) := by rw [h1']
    _ = s * b * s⁻¹ * b⁻¹ * d := by group

end CFSG.RankThree.PartTwo.Sec3
