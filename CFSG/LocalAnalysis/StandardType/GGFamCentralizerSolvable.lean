module

public import CFSG.LocalAnalysis.StandardType.GGFamAssembly
public import CFSG.LocalAnalysis.StandardType.GGFamF4Assembly
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTrivial
public import CFSG.LocalAnalysis.StandardType.GGFamF4Trivial
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGLangFamily
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG7
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient
public import CFSG.GroupTheory.QuasisimplePSolvable
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LangRat
open scoped commutatorElement

theorem isSolvable_familyToral
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hp : p.Prime) (hpodd : Odd p)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1)
    (hpq : p ∣ S.D.q ^ 2 - 1)
    (hNPC : CFSG.HasNormalPComplement p
      ↥⁅S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)),
        S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))⁆) :
    Group.IsSolvable ↥(S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) := by
  classical
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    norm_num at hpodd
  letI : Finite S.D.model := S.finite
  let H : Subgroup (ModGL τ L) :=
    S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))
  let χ : Multiplicative (Fin τ.rank → ℤ) →* (ι → Lˣ) :=
    Pi.monoidHom fun u => rootCharHom (a u)
  let Oidx := Set.range (rationalRootsM S.ρ χ)
  let A : Oidx → Subgroup (ModGL τ L) := fun O => rootSpan τ L O.1
  let R : Oidx → Subgroup (ModGL τ L) := fun O => ⁅A O ⊓ S.Γ, A O ⊓ S.Γ⁆
  have hHmodel : H ≤ S.D.model :=
    (inf_le_left : H ≤ S.Γ).trans (Subgroup.commutator_le_self S.D.model)
  haveI : Finite ↥H :=
    Finite.of_injective (Subgroup.inclusion hHmodel) (Subgroup.inclusion_injective _)
  have hRleH : ∀ O, R O ≤ H := by
    intro O
    obtain ⟨_, i, rfl⟩ := O
    have hcent : A ⟨rationalRootsM S.ρ χ i, ⟨i, rfl⟩⟩ ≤
        Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have hsub : rationalRootsM S.ρ χ i ⊆ rootCharKernel (a u) := by
        intro γ hγ
        obtain ⟨hroot, hχ⟩ := (mem_kernelRoots_famChar a).1
          (famComp_rationalRootsM_subset_kernelRoots
            (fun gamma hgamma => rho_mem_kernelRoots_famChar S a hT hgamma) i hγ)
        exact ⟨hroot, hχ u⟩
      exact Subgroup.mem_centralizer_iff.1
        (CFSG.LieType.Chevalley.rootSpan_le_centralizer (a u) hsub hx) _ rfl
    have hRleA : R ⟨rationalRootsM S.ρ χ i, ⟨i, rfl⟩⟩ ≤
        A ⟨rationalRootsM S.ρ χ i, ⟨i, rfl⟩⟩ ⊓ S.Γ :=
      Subgroup.commutator_le_self
        (A ⟨rationalRootsM S.ρ χ i, ⟨i, rfl⟩⟩ ⊓ S.Γ)
    exact le_inf (hRleA.trans inf_le_right) (hRleA.trans (inf_le_left.trans hcent))
  have hcommR : ∀ O O', O ≠ O' → R O ≤ Subgroup.centralizer (R O' : Set (ModGL τ L)) := by
    intro O O' hne x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_rootSpan_inf_Γ_of_ne S hT hne x
      (Subgroup.commutator_le_self (A O ⊓ S.Γ) hx) y
      (Subgroup.commutator_le_self (A O' ⊓ S.Γ) hy)).eq.symm
  have hperfect_le : ∀ P : Subgroup (ModGL τ L), P ≤ H → ⁅P, P⁆ = P → P ≤ ⨆ O, R O := by
    intro P hP hperf
    exact perfect_le_iSup_commutator_rationalSpanM S hp a hT hap
      (by simpa [H] using hP) hperf
  by_cases h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1
  ·
    have hpos : ∀ i : KernelComponent χ, 0 < componentOrbitLength S.ρ (componentRoots χ i) := by
      intro i
      exact componentOrbitLength_pos S (fun γ hγ => by
        obtain ⟨h, -⟩ := hγ
        exact h.1)
    have hFieldData : ∀ (i : KernelComponent χ),
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) →
        CFSG.StandardType.GGCompFieldData S.D.q (rationalComponentM S.ρ S.Γ χ i) := by
      intro i hqi
      let s := componentOrbitLength S.ρ (componentRoots χ i)
      have hs : 0 < s := hpos i
      rcases hτ with rfl | rfl | rfl | rfl
      · rcases langFamRatCompFieldF4_holds S hp hp2 hT hap h1 i hqi with hAt | ⟨hq2, -, hcard, -⟩
        · exact Or.inl ⟨s, Nat.succ_le_of_lt hs, hAt⟩
        · exact Or.inr ⟨hq2, Or.inl hcard⟩
      · exact Or.inl ⟨s, Nat.succ_le_of_lt hs,
          (langFamRatCompFieldLenSL_of_lanes langFamRatFieldSL_typeA langFamRatFieldSL_inner
              langFamRatFieldSL_outerD_high langFamRatFieldSL_outerD_four langFamRatFieldSL_outerE .E6 L p₀ S (Or.inl rfl) p hp hp2 ι a hT hap h1
            i hqi).toAt⟩
      · exact Or.inl ⟨s, Nat.succ_le_of_lt hs,
          (langFamRatCompFieldLenSL_of_lanes langFamRatFieldSL_typeA langFamRatFieldSL_inner
              langFamRatFieldSL_outerD_high langFamRatFieldSL_outerD_four langFamRatFieldSL_outerE .E7 L p₀ S (Or.inr (Or.inl rfl)) p hp hp2 ι a hT hap h1
            i hqi).toAt⟩
      · exact Or.inl ⟨s, Nat.succ_le_of_lt hs,
          (langFamRatCompFieldLenSL_of_lanes langFamRatFieldSL_typeA langFamRatFieldSL_inner
              langFamRatFieldSL_outerD_high langFamRatFieldSL_outerD_four langFamRatFieldSL_outerE .E8 L p₀ S (Or.inr (Or.inr rfl)) p hp hp2 ι a hT hap h1
            i hqi).toAt⟩
    have hTameR : ∀ O, CFSG.IsQuasisimple (R O) ∨ Group.IsSolvable ↥(R O) := by
      intro O
      obtain ⟨_, i, rfl⟩ := O
      have htame : CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) ∨
          Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ χ i) := by
        rcases hτ with rfl | rfl | rfl | rfl
        · exact langFamTame_F4 S hp hp2 hT hap h1 i
        · exact langFamTame_of_prime (Or.inl rfl) S hp hp2 hT hap h1 i
        · exact langFamTame_of_prime (Or.inr (Or.inl rfl)) S hp hp2 hT hap h1 i
        · exact langFamTame_of_prime (Or.inr (Or.inr rfl)) S hp hp2 hT hap h1 i
      change CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) ∨
        Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ χ i)
      exact htame
    have hRsolv : ∀ O, Group.IsSolvable ↥(R O) := by
      intro O
      rcases hTameR O with hq | hs
      · exfalso
        have hperfR : ⁅R O, R O⁆ = R O :=
          CFSG.HardMathSupport.Timmesfeld.LangTorus.commutator_self_eq_of_commutator_top
            hq.1.commutator_eq_top
        have hRH : R O ≤ H := hRleH O
        have hRcomm : R O ≤ ⁅H, H⁆ := by
          calc R O = ⁅R O, R O⁆ := hperfR.symm
            _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hRH hRH
        have hNPC_R : CFSG.HasNormalPComplement p ↥(R O) :=
          CFSG.hasNormalPComplement_of_le p hRcomm hNPC
        haveI : Group.IsPerfect ↥(R O) := Subgroup.isPerfect_iff.mpr hperfR
        have hRmodel : R O ≤ S.D.model :=
          (hRH.trans inf_le_left).trans (Subgroup.commutator_le_self S.D.model)
        haveI : Finite ↥(R O) :=
          Finite.of_injective (Subgroup.inclusion hRmodel) (Subgroup.inclusion_injective _)
        haveI : Fact p.Prime := ⟨hp⟩
        have hcop : Nat.Coprime p (Nat.card ↥(R O)) :=
          CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect hNPC_R
        have hpR : p ∣ Nat.card ↥(R O) := by
          obtain ⟨_, i, rfl⟩ := O
          have hqRi : CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) := by
            change CFSG.IsQuasisimple (R ⟨rationalRootsM S.ρ χ i, ⟨i, rfl⟩⟩)
            exact hq
          change p ∣ Nat.card ↥(rationalComponentM S.ρ S.Γ χ i)
          exact CFSG.StandardType.ggCompFieldData_dvd (hFieldData i hqRi) hp hpq
        exact (hp.coprime_iff_not_dvd.mp hcop) hpR
      · exact hs
    have hsolvSup : Group.IsSolvable ↥(⨆ O, R O) := by
      haveI : Finite (kernelRoots χ) :=
        ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
      haveI : Finite (KernelComponent χ) := inferInstance
      haveI : Finite Oidx := (Set.finite_range _).to_subtype
      haveI : Fintype Oidx := Fintype.ofFinite Oidx
      exact CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isSolvable_iSup_of_commute
        R hRsolv hcommR
    let P0 : Subgroup ↥H := CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥H)
    let P : Subgroup (ModGL τ L) := P0.map H.subtype
    have hP_le_H : P ≤ H := by
      rintro x hx
      change x ∈ P0.map H.subtype at hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have hP_perf : ⁅P, P⁆ = P := by
      have h0 : ⁅P0, P0⁆ = P0 :=
        CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup ↥H)
      have h := congrArg (Subgroup.map H.subtype) h0
      rw [Subgroup.map_commutator] at h
      simpa [P] using h
    have hP_sup : P ≤ ⨆ O, R O := hperfect_le P hP_le_H hP_perf
    have hP_bot : P = ⊥ := by
      haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP_perf
      exact CFSG.Walter.eq_bot_of_isPerfect_of_le_isSolvable hP_sup hsolvSup
    have hP0_bot : P0 = ⊥ := by
      have hmap : P0.map H.subtype = ⊥ := by simpa [P] using hP_bot
      exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hmap
    have hsolvTop : Group.IsSolvable ↥(⊤ : Subgroup ↥H) :=
      (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot (⊤ : Subgroup ↥H)).mpr hP0_bot
    exact Group.isSolvable_of_surjective (f := Subgroup.topEquiv.toMonoidHom)
      (MulEquiv.surjective _)
  ·
    push Not at h1
    have hcent_top : Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨u, rfl⟩
      simp [h1 u]
    have hH : H = S.Γ := by
      simp [H, hcent_top]
    have hqΓ : CFSG.Open.IsQuasisimple ↥S.Γ := by
      rcases hτ with rfl | rfl | rfl | rfl
      ·
        obtain ⟨Fr, hFr, hΦ⟩ := S.exists_frobenius_of_steinberg (by decide) (by decide)
        obtain ⟨K, hKf, hKfin, hKa, e, -, -⟩ := S.descends_of_exact (Or.inr rfl) ⟨Fr, hFr, hΦ⟩
          (fun K _ _ => CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_F4_eq_top K)
        let : Field K := hKf
        let : Finite K := hKfin
        let : Algebra K L := hKa
        exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm
          (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
            (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (K := K)))
      · obtain ⟨-, -, -, -, hq, -⟩ := famTrivial_Γ_data (Or.inl rfl) S
        exact hq
      · obtain ⟨-, -, -, -, hq, -⟩ := famTrivial_Γ_data (Or.inr (Or.inl rfl)) S
        exact hq
      · obtain ⟨-, -, -, -, hq, -⟩ := famTrivial_Γ_data (Or.inr (Or.inr rfl)) S
        exact hq
    have hperfΓ : ⁅S.Γ, S.Γ⁆ = S.Γ :=
      CFSG.HardMathSupport.Timmesfeld.LangTorus.commutator_self_eq_of_commutator_top hqΓ.1
    have hcompΓ : CFSG.Open.IsComponentOf S.Γ H := by
      rw [hH]
      exact ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hqΓ⟩
    have hFieldData : CFSG.StandardType.GGCompFieldData S.D.q S.Γ := by
      rcases hτ with rfl | rfl | rfl | rfl
      · obtain ⟨i, -, hfield⟩ := langFamilyCompFieldF4_trivial S a h1 S.Γ hcompΓ
        rcases hfield with hAt | ⟨hq2, -, hcard, -⟩
        · exact Or.inl ⟨componentOrbitLength S.ρ (componentRoots χ i),
            Nat.succ_le_of_lt (componentOrbitLength_pos S (fun γ hγ => by
              obtain ⟨h, -⟩ := hγ
              exact h.1)), hAt⟩
        · exact Or.inr ⟨hq2, Or.inl hcard⟩
      · exact Or.inl ⟨1, by norm_num,
          by simpa using (famTrivial_ggCompFieldAtSL_Γ (Or.inl rfl) S).toAt⟩
      · exact Or.inl ⟨1, by norm_num,
          by simpa using (famTrivial_ggCompFieldAtSL_Γ (Or.inr (Or.inl rfl)) S).toAt⟩
      · exact Or.inl ⟨1, by norm_num,
          by simpa using (famTrivial_ggCompFieldAtSL_Γ (Or.inr (Or.inr rfl)) S).toAt⟩
    have hpΓ : p ∣ Nat.card ↥S.Γ :=
      CFSG.StandardType.ggCompFieldData_dvd hFieldData hp hpq
    have hNPCΓ : CFSG.HasNormalPComplement p ↥S.Γ := by
      have h' := hNPC
      change CFSG.HasNormalPComplement p ↥⁅H, H⁆ at h'
      rw [hH, hperfΓ] at h'
      exact h'
    haveI : Finite ↥S.Γ :=
      Finite.of_injective (Subgroup.inclusion (Subgroup.commutator_le_self S.D.model))
        (Subgroup.inclusion_injective _)
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Group.IsPerfect ↥S.Γ := Subgroup.isPerfect_iff.mpr hperfΓ
    have hcop : Nat.Coprime p (Nat.card ↥S.Γ) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect hNPCΓ
    exfalso
    exact (hp.coprime_iff_not_dvd.mp hcop) hpΓ

end CFSG.StandardType.TableCRes
