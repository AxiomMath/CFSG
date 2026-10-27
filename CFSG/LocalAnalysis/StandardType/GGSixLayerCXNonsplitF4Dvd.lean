module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Four
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Six
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcLabel
public import CFSG.LieType.SeitzGeneration.ExcPlaneF4Rest
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

namespace F4Nonsplit

theorem not_isComponentOf_of_conj_centralizer_cyclic {G : Type*} [Group G] {a g : G}
    {T : Subgroup G} (hT : IsCyclic T) (hc : Subgroup.centralizer {g * a * g⁻¹} = T)
    {X : Subgroup G} : ¬ IsComponentOf X (Subgroup.centralizer {a}) := by
  refine not_isComponentOf_of_commute fun b hb c hc' => ?_
  have hmem : ∀ d ∈ Subgroup.centralizer {a}, g * d * g⁻¹ ∈ T := fun d hd => by
    rw [← hc, Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hd
    calc g * d * g⁻¹ * (g * a * g⁻¹) = g * (d * a) * g⁻¹ := by group
      _ = g * (a * d) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * (g * d * g⁻¹) := by group
  have := hT
  have h1 : (⟨_, hmem b hb⟩ : T) * ⟨_, hmem c hc'⟩ = ⟨_, hmem c hc'⟩ * ⟨_, hmem b hb⟩ :=
    (IsCyclic.isMulCommutative (α := T)).is_comm.comm _ _
  have h2 : g * b * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * b * g⁻¹) :=
    congrArg Subtype.val h1
  calc b * c = g⁻¹ * ((g * b * g⁻¹) * (g * c * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * c * g⁻¹) * (g * b * g⁻¹)) * g := by rw [h2]
    _ = c * b := by group

theorem not_dvd_card_of_ne_two {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  obtain ⟨f, -, hK⟩ := exists_card_eq_two_pow K
  rw [hK]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

end F4Nonsplit

section Holds


theorem ggF4NonsplitDvdInput_holds : GGF4NonsplitDvdInput := by
  intro K _ _ _ p hp hp2 hq1 hq2 hdvd a ha X hX
  have hp3 : 3 < p := by
    have h3 := ExcNonsplit.ne_three_of_not_dvd_card hq1 hq2
    have := hp.two_le
    omega
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one ha) with h1 | hap
  ·
    rw [orderOf_eq_one_iff] at h1
    subst h1
    have htop : Subgroup.centralizer ({1} : Set ↥(adjointGroup .F4 K)) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (one_mem _))
    rw [htop] at hX
    have hQ : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(adjointGroup .F4 K)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K)
    have hc : ⁅(⊤ : Subgroup ↥(adjointGroup .F4 K)), ⊤⁆ = ⊤ :=
      CFSG.RankThree.Chevalley.commutator_eq_self_of_isPerfect hQ.1
    have hQ' : CFSG.IsQuasisimple ↥(⁅(⊤ : Subgroup ↥(adjointGroup .F4 K)), ⊤⁆ :
        Subgroup ↥(adjointGroup .F4 K)) := by
      rw [hc]
      exact hQ
    rw [F4Nonsplit.eq_commutator_of_isComponentOf hQ' hX, hc, Subgroup.card_top]
    exact hdvd
  ·
    have hpK := F4Nonsplit.not_dvd_card_of_ne_two (K := K) hp hp2
    have hq1' : 1 ≤ Nat.card K := Nat.card_pos
    have hqq : Nat.card K ≤ Nat.card K ^ 2 := by nlinarith
    obtain ⟨m, hm, hpm⟩ := CFSG.LieType.SeitzGeneration.exists_dvd_phi_of_dvd_card_F4 hp hpK hdvd
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      apply hq1
      have e : (exhaustionPhi 1).eval (Nat.card K : ℤ) = ((Nat.card K - 1 : ℕ) : ℤ) := by
        simp [exhaustionPhi, Nat.cast_sub hq1']
      rw [e] at hpm
      exact Int.natCast_dvd_natCast.1 hpm
    · exfalso
      apply hq2
      have e : (exhaustionPhi 2).eval (Nat.card K : ℤ) = ((Nat.card K + 1 : ℕ) : ℤ) := by
        simp [exhaustionPhi]
      rw [e] at hpm
      exact Int.natCast_dvd_natCast.1 hpm
    · have e : (exhaustionPhi 3).eval (Nat.card K : ℤ) =
          ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) := by
        simp [exhaustionPhi]
      rw [e] at hpm
      exact F4Nonsplit.dvd_card_of_isComponentOf_phiThree hp hp3
        (Int.natCast_dvd_natCast.1 hpm) hap hX
    · have e : (exhaustionPhi 4).eval (Nat.card K : ℤ) = ((Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by
        simp [exhaustionPhi]
      rw [e] at hpm
      exact F4Nonsplit.dvd_card_of_isComponentOf_phiFour hp hp3
        (Int.natCast_dvd_natCast.1 hpm) hap hX
    · have e : (exhaustionPhi 6).eval (Nat.card K : ℤ) =
          ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) := by
        simp [exhaustionPhi, Nat.cast_sub hqq]
      rw [e] at hpm
      exact F4Nonsplit.dvd_card_of_isComponentOf_phiSix hp hp3
        (Int.natCast_dvd_natCast.1 hpm) hap hX
    · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
        CFSG.RankThree.PartOne.KE.F4_eight_cyclic_sylow
          CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers_F4 K hp hp3 hpm
      obtain ⟨g, -, hg⟩ := hcent a hap
      exact absurd hX (F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg)
    · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
        CFSG.RankThree.PartOne.KE.F4_twelve_cyclic_sylow
          CFSG.RankThree.PartOne.KE.cyclic_torus_prime_centralizers_F4 K hp hp3 hpm
      obtain ⟨g, -, hg⟩ := hcent a hap
      exact absurd hX (F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg)

end Holds

end CFSG.StandardType
