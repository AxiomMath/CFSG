module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUDvd
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed

public section

namespace CFSG.StandardType.LineU

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly

@[expose] def pullbackSub {n d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (ψ : L' →* LargeEvenProj (unitarySU 2 n K d)) :
    Subgroup (↥(unitarySU 2 n K d) × L') where
  carrier := {x | LargeEvenProjMk (unitarySU 2 n K d) x.1 = ψ x.2}
  mul_mem' := fun {a b} ha hb => by
    have ha' : LargeEvenProjMk (unitarySU 2 n K d) a.1 = ψ a.2 := ha
    have hb' : LargeEvenProjMk (unitarySU 2 n K d) b.1 = ψ b.2 := hb
    change LargeEvenProjMk (unitarySU 2 n K d) (a.1 * b.1) = ψ (a.2 * b.2)
    rw [map_mul, map_mul, ha', hb']
  one_mem' := by
    change LargeEvenProjMk (unitarySU 2 n K d) 1 = ψ 1
    rw [map_one, map_one]
  inv_mem' := fun {a} ha => by
    have ha' : LargeEvenProjMk (unitarySU 2 n K d) a.1 = ψ a.2 := ha
    change LargeEvenProjMk (unitarySU 2 n K d) a.1⁻¹ = ψ a.2⁻¹
    rw [map_inv, map_inv, ha']

theorem unitaryCoverAt_of_section {n d : ℕ} {K : Type} [Field K] [Finite K]
    (hperf : commutator (unitarySU 2 n K d) = ⊤)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(unitarySU 2 n K d)),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : ↥(unitarySU 2 n K d) →* E, ∀ g, π (s g) = g) :
    UnitaryCoverAt n d K := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin d) K) :=
    Finite.of_injective (fun u : Matrix.GeneralLinearGroup (Fin d) K =>
      (u : Matrix (Fin d) (Fin d) K)) fun _ _ h => Units.ext h
  unfold UnitaryCoverAt
  refine ⟨hperf, ?_⟩
  intro L' _ _ ψ hψ hker _
  let p₁ : ↥(pullbackSub ψ) →* ↥(unitarySU 2 n K d) :=
    (MonoidHom.fst (↥(unitarySU 2 n K d)) L').comp (pullbackSub ψ).subtype
  have hp₁ : Function.Surjective p₁ := by
    intro s
    obtain ⟨l, hl⟩ := hψ (LargeEvenProjMk (unitarySU 2 n K d) s)
    exact ⟨⟨(s, l), hl.symm⟩, rfl⟩
  have hp₁c : p₁.ker ≤ Subgroup.center ↥(pullbackSub ψ) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : ↥(unitarySU 2 n K d) × L').1 = 1 := hx
    have h3 : LargeEvenProjMk (unitarySU 2 n K d) (x : ↥(unitarySU 2 n K d) × L').1 =
        ψ (x : ↥(unitarySU 2 n K d) × L').2 := x.2
    have h4 : (x : ↥(unitarySU 2 n K d) × L').2 ∈ Subgroup.center L' := by
      refine hker ?_
      rw [MonoidHom.mem_ker, ← h3, h1, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · show (y : ↥(unitarySU 2 n K d) × L').1 * (x : ↥(unitarySU 2 n K d) × L').1 =
        (x : ↥(unitarySU 2 n K d) × L').1 * (y : ↥(unitarySU 2 n K d) × L').1
      rw [h1, mul_one, one_mul]
    · exact Subgroup.mem_center_iff.mp h4 (y : ↥(unitarySU 2 n K d) × L').2
  obtain ⟨s, hs⟩ := hsec (pullbackSub ψ) p₁ hp₁ hp₁c
  refine ⟨(MonoidHom.snd (↥(unitarySU 2 n K d)) L').comp ((pullbackSub ψ).subtype.comp s),
    fun g => ?_⟩
  have h1 : ((s g : ↥(pullbackSub ψ)) : ↥(unitarySU 2 n K d) × L').1 = g := hs g
  have h2 : LargeEvenProjMk (unitarySU 2 n K d)
      ((s g : ↥(pullbackSub ψ)) : ↥(unitarySU 2 n K d) × L').1 =
      ψ ((s g : ↥(pullbackSub ψ)) : ↥(unitarySU 2 n K d) × L').2 := (s g).2
  rw [h1] at h2
  exact h2.symm

@[expose] def UnitaryCoverTwoEven : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 4 → Even d → 8 ≤ d →
    UnitaryCoverAt 1 d K

section Certificates


theorem unitaryUniversalCover_of_twoEven (h : UnitaryCoverTwoEven) : UnitaryUniversalCover := by
  unfold UnitaryUniversalCover
  intro n d K _ _ hK hd hdn
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      simp only [pow_zero, one_pow] at hK
      omega
    · omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    CFSG.StandardType.TableBU.unitaryFieldData_of_card hK hn
  haveI : CharP K 2 := hU.charP
  rcases Nat.even_or_odd d with he | ho
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    ·
      obtain rfl : n = 1 := by omega
      have hK4 : Nat.card K = 4 := hK.trans (by norm_num)
      obtain ⟨k, rfl⟩ := he
      have hne : k + k ≠ 6 := fun h6 => hdn (by rw [h6])
      exact h (k + k) K hK4 ⟨k, rfl⟩ (by omega)
    ·
      have hq : 4 ≤ 2 ^ n :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hd4 : 4 ≤ d := by omega
      have hperf : commutator (unitarySU 2 n K d) = ⊤ := by
        haveI := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hK hd4
        exact Group.IsPerfect.commutator_eq_top
      refine unitaryCoverAt_of_section hperf ?_
      intro E _ _ π hπ hcen
      exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central
        hK he hd4 hq hπ hcen
  ·
    have hd3 : 3 ≤ d := by omega
    have hq : (d, 2 ^ n) ≠ (3, 2) := by
      intro heq
      have := congrArg Prod.fst heq
      simp only at this
      omega
    have hodd : ¬ Even d := Nat.not_even_iff_odd.2 ho
    have hperf : commutator (unitarySU 2 n K d) = ⊤ := by
      haveI := CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hK hd3 hq
      exact Group.IsPerfect.commutator_eq_top
    refine unitaryCoverAt_of_section hperf ?_
    intro E _ _ π hπ hcen
    exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      hK hn hd3 hodd hq hπ hcen

theorem ggLNoInvariantLineInputOn_unitDvd_of_twoEven (h : UnitaryCoverTwoEven) :
    GGLNoInvariantLineInputOn GGUnitDvdLabelNo63 :=
  ggLNoInvariantLineInputOn_unitDvd (unitaryUniversalCover_of_twoEven h)

end Certificates

end CFSG.StandardType.LineU
