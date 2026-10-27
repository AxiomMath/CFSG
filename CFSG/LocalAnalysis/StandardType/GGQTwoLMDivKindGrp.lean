module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.StandardType.QTwo

variable {G : Type} [Group G]

private theorem qTwoLMDivKindGrp_comm_eq_one {L : Subgroup G} {L0 : Type} [Group L0]
    (c : ↥L →* L0) (hperf : commutator ↥L = ⊤) (hc_ker : c.ker ≤ Subgroup.center ↥L) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l : ↥L, c ⟨b * l * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb l).mp l.2⟩ = c l)
    (l : G) (hl : l ∈ L) : b * l * b⁻¹ * l⁻¹ = 1 := by
  have hmem : ∀ l : ↥L, b * (l : G) * b⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp hb (l : G)).mp l.2
  let φ : ↥L → ↥L := fun l => ⟨b * (l : G) * b⁻¹, hmem l⟩ * l⁻¹
  have hφc : ∀ l : ↥L, c (φ l) = 1 := by
    intro l
    have hh : c ⟨b * (l : G) * b⁻¹, hmem l⟩ = c l := h l
    show c (⟨b * (l : G) * b⁻¹, hmem l⟩ * l⁻¹) = 1
    rw [map_mul, map_inv, hh]
    group
  have hφz : ∀ l : ↥L, φ l ∈ Subgroup.center ↥L := fun l =>
    hc_ker (MonoidHom.mem_ker.mpr (hφc l))
  let f : ↥L →* Subgroup.center ↥L :=
    { toFun := fun l => ⟨φ l, hφz l⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show ((φ 1 : ↥L) : G) = 1
        simp [φ]
      map_mul' := fun l l' => by
        apply Subtype.ext
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hφz l') ((l : ↥L)⁻¹)
        have hc' : ((l : G))⁻¹ * (b * (l' : G) * b⁻¹ * (l' : G)⁻¹) =
            (b * (l' : G) * b⁻¹ * (l' : G)⁻¹) * ((l : G))⁻¹ := by
          have hcc := congrArg Subtype.val hc
          simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv] at hcc
          simpa using hcc
        show ((φ (l * l') : ↥L) : G) =
          ((φ l : ↥L) : G) * ((φ l' : ↥L) : G)
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv]
        calc b * ((l : G) * (l' : G)) * b⁻¹ * ((l : G) * (l' : G))⁻¹
            = (b * (l : G) * b⁻¹) *
                ((b * (l' : G) * b⁻¹ * (l' : G)⁻¹) * (l : G)⁻¹) := by group
          _ = (b * (l : G) * b⁻¹) *
                ((l : G)⁻¹ * (b * (l' : G) * b⁻¹ * (l' : G)⁻¹)) := by rw [← hc']
          _ = (b * (l : G) * b⁻¹ * (l : G)⁻¹) *
                (b * (l' : G) * b⁻¹ * (l' : G)⁻¹) := by group }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff]
    have h1 := Abelianization.commutator_subset_ker f
    rwa [hperf] at h1
  have hfl : f ⟨l, hl⟩ = 1 := by
    have hmemker : (⟨l, hl⟩ : ↥L) ∈ f.ker := by
      rw [hker]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.mp hmemker
  have hφ1 : ((φ ⟨l, hl⟩ : ↥L) : G) = 1 := by
    have h1 := congrArg (fun x : Subgroup.center ↥L => ((x : ↥L) : G)) hfl
    simpa [f] using h1
  simpa [φ] using hφ1

theorem qTwoLMDivKind_mem_centralizer_of_map_conj {L : Subgroup G} {L0 : Type} [Group L0]
    (c : ↥L →* L0) (hperf : commutator ↥L = ⊤) (hc_ker : c.ker ≤ Subgroup.center ↥L) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l : ↥L, c ⟨b * l * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb l).mp l.2⟩ = c l) :
    b ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hconj : b * l * b⁻¹ = l :=
    mul_inv_eq_one.mp (qTwoLMDivKindGrp_comm_eq_one c hperf hc_ker hb h l hl)
  calc l * b = b * l * b⁻¹ * b := by rw [hconj]
    _ = b * l := by group

theorem qTwoLMDivKind_exists_lift_cube {L L0 : Type} [Group L] [Group L0] (c : L →* L0)
    (hc_surj : Function.Surjective c) (hc_two : IsPGroup 2 c.ker) {v : L0} (hv : v ^ 3 = 1) :
    ∃ t : L, t ^ 3 = 1 ∧ c t = v := by
  obtain ⟨t₀, rfl⟩ := hc_surj v
  have hk : t₀ ^ 3 ∈ c.ker := by
    rw [MonoidHom.mem_ker, map_pow, hv]
  obtain ⟨a, ha⟩ := hc_two.exists_pow_pow_eq_one ⟨t₀ ^ 3, hk⟩
  have ha' : t₀ ^ (3 * 2 ^ a) = 1 := by
    have h1 := congrArg Subtype.val ha
    simpa [Subgroup.coe_pow, pow_mul] using h1
  have h4 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  refine ⟨t₀ ^ (4 ^ a), ?_, ?_⟩
  · rw [← pow_mul,
      show 4 ^ a * 3 = (3 * 2 ^ a) * 2 ^ a by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
        ring,
      pow_mul, ha', one_pow]
  · rw [map_pow, pow_eq_pow_mod (4 ^ a) hv, h4, pow_one]

end CFSG.StandardType.QTwo

end
