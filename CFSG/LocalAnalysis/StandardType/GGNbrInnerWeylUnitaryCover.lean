module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LieType.Steinberg.CentralExt.UnitaryTwoMultiplier

public section

namespace CFSG.StandardType.LineU

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.CentralExt
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem exists_hom_of_sections {S Q L' : Type} [Group S] [Finite S] [Group Q] [Group L']
    [Finite L'] (proj : S →* Q) (ψ : L' →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L')
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : S →* E, ∀ g, π (s g) = g) :
    ∃ φ : S →* L', ∀ s, ψ (φ s) = proj s := by
  classical
  let E : Subgroup (S × L') :=
    (proj.comp (MonoidHom.fst S L')).eqLocus (ψ.comp (MonoidHom.snd S L'))
  let π : E →* S := (MonoidHom.fst S L').comp E.subtype
  have hmem : ∀ e : E, proj (e : S × L').1 = ψ (e : S × L').2 := fun e => e.2
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨l, hl⟩ := hψ (proj s)
    exact ⟨⟨(s, l), hl.symm⟩, rfl⟩
  have hcen : π.ker ≤ Subgroup.center E := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro e'
    have h1 : (e : S × L').1 = 1 := he
    have h2 : (e : S × L').2 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hmem e, h1, map_one]
    have hc := Subgroup.mem_center_iff.mp (hker h2) (e' : S × L').2
    apply Subtype.ext
    apply Prod.ext
    · show (e' : S × L').1 * (e : S × L').1 = (e : S × L').1 * (e' : S × L').1
      rw [h1, one_mul, mul_one]
    · exact hc
  obtain ⟨σ, hσ⟩ := hsec E π hπ hcen
  refine ⟨(MonoidHom.snd S L').comp (E.subtype.comp σ), fun s => ?_⟩
  have h1 : ((σ s : E) : S × L').1 = s := hσ s
  show ψ ((σ s : E) : S × L').2 = proj s
  rw [← hmem (σ s), h1]

theorem surjective_of_cover {S Q L' : Type} [Group S] [Group Q] [Group L'] (proj : S →* Q)
    (hproj : Function.Surjective proj) (ψ : L' →* Q) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (φ : S →* L') (hφ : ∀ s, ψ (φ s) = proj s) :
    Function.Surjective φ := by
  have hcomm : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ φ.range := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs⟩ := hproj (ψ x)
    obtain ⟨s', hs'⟩ := hproj (ψ y)
    have hz : x * (φ s)⁻¹ ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hs, mul_inv_cancel]
    have hz' : y * (φ s')⁻¹ ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hs', mul_inv_cancel]
    have hx : x = (x * (φ s)⁻¹) * φ s := by group
    have hy : y = (y * (φ s')⁻¹) * φ s' := by group
    rw [hx, hy, comm_mul_central hz hz']
    exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
  have htop : (⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ : Subgroup L') = ⊤ := hperf
  rw [htop] at hcomm
  intro l
  obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
  exact ⟨s, hs⟩

section Sections


theorem statedSU_exists_section_unitary {n d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hd6 : (d, n) ≠ (6, 1))
    {E : Type} [Group E] [Finite E] {π : E →* StatedSU d (2 ^ n) K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedSU d (2 ^ n) K →* E, ∀ g, π (s g) = g := by
  rcases Nat.even_or_odd d with he | ho
  · by_cases hn2 : 2 ≤ n
    · have hq : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
        (F := K) (p := 2) (f := n) hK he (by omega) hq hπ hcen
    · obtain rfl : n = 1 := by omega
      obtain ⟨r, hr⟩ := he
      have hd6' : d ≠ 6 := fun h => hd6 (by rw [h])
      have hr4 : 4 ≤ r := by omega
      obtain rfl : d = 2 * r := by omega
      have hZc : ((StatedScalars (Fin (2 * r)) K).subgroupOf (StatedSU (2 * r) (2 ^ 1) K)) ≤
          Subgroup.center (StatedSU (2 * r) (2 ^ 1) K) := fun z hz => by
        have hz' : (z : GL (Fin (2 * r)) K) ∈ Subgroup.center (GL (Fin (2 * r)) K) := by
          have h1 := Subgroup.mem_subgroupOf.1 hz
          rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
        exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)
      have : Group.IsPerfect (StatedSU (2 * r) (2 ^ 1) K) :=
        CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU (F := K) (p := 2) (f := 1)
          hK (by omega)
      open CFSG.LocalAnalysis.ComponentInitial in
      exact CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
        (θ := QuotientGroup.mk' ((StatedScalars (Fin (2 * r)) K).subgroupOf
          (StatedSU (2 * r) (2 ^ 1) K))) (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']; exact hZc)
        (fun P _ _ _ η hη hC h2 =>
          (even_even_dimensional_unitary_prime_field_central_two_cover_trivial
            η hη hC h2 hr4
            (CFSG.LieType.Steinberg.CentralExt.SUClosed.lieModel_psu_two hK
              (by omega))).1)
        (fun E _ _ π hπ hcen hc =>
          CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
            (F := K) (p := 2) (f := 1) hK ⟨r, two_mul r⟩ (by omega) E π hπ hcen hc)
        E π hπ hcen
  · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (F := K) (p := 2) (f := n) hK hn (by omega) (Nat.not_even_iff_odd.mpr ho)
      (fun h => by
        have := congrArg Prod.fst h
        simp only at this
        omega) hπ hcen

theorem unitaryCoverAt {n d : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hd : 5 ≤ d) (hd6 : (d, n) ≠ (6, 1)) : UnitaryCoverAt n d K := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 : Nat.card K = 1 := by simpa using hK
      have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
      exact absurd (Subsingleton.elim (1 : K) 0) one_ne_zero
    · exact h
  have : CharP K 2 := (CFSG.StandardType.TableBU.unitaryFieldData_of_card hK hn).charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq32 : (d, 2 ^ n) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hperf : Group.IsPerfect (StatedSU d (2 ^ n) K) := by
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU (F := K) (p := 2)
        (f := n) hK (by omega)
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd (F := K) (p := 2)
        (f := n) hK (by omega) hq32
  refine ⟨hperf.commutator_eq_top, ?_⟩
  intro L' _ _ ψ hψ hker hperf'
  exact exists_hom_of_sections (LargeEvenProjMk (unitarySU 2 n K d)) ψ hψ hker
    (fun E _ _ π hπ hcen => statedSU_exists_section_unitary hK hn hd hd6 hπ hcen)

theorem unitaryUniversalCover : UnitaryUniversalCover := fun _ _ _ _ _ hK hd hd6 =>
  unitaryCoverAt hK hd hd6

end Sections

end CFSG.StandardType.LineU

end
