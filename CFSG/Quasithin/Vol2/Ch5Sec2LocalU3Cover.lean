module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Lie
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import CFSG.LieType.Steinberg.CentralExt.SUOddCover
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord2
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem factU3Cover_holds :
    FactU3Cover := by
  intro X _ _ k hk hX hm
  have : Group.IsPerfect X := hX.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = (2 ^ k) ^ 2 ∧
        Nonempty (X ⧸ Subgroup.center X ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 (2 ^ k) F)) := by
    rcases hm with ⟨-, -, F, hF1, hF2, hF, he⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact ⟨F, hF1, hF2, hF, he⟩
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := CFSG.SectionRank.charP_two_of_card (f := k * 2) (by rw [hF, pow_mul])
  set Z := Subgroup.center X with hZdef
  set π : X →* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 (2 ^ k) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' Z) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : ∀ x, π x = 1 ↔ x ∈ Z := fun x => by
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set O := CFSG.LieType.Steinberg.oddPart Z le_rfl with hO
  have hOZ : O ≤ π.ker := fun x hx => (hπk x).mpr hx.1
  set η : X ⧸ O →* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 (2 ^ k) F) :=
    QuotientGroup.lift O π hOZ with hη
  have hηmk : ∀ x, η (QuotientGroup.mk x) = π x := fun x => rfl
  have hηs : Function.Surjective η := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hηk : ∀ x : X, (QuotientGroup.mk x : X ⧸ O) ∈ η.ker ↔ x ∈ Z := fun x => by
    rw [MonoidHom.mem_ker, hηmk, hπk]
  have hηc : η.ker ≤ Subgroup.center (X ⧸ O) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxZ := (hηk x).mp hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hxZ w]
  have hη2 : IsPGroup 2 η.ker := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : X ⧸ O)
    have hxZ : x ∈ Z := (hηk x).mp (hx ▸ y.2)
    obtain ⟨a, ha⟩ := CFSG.LieType.Steinberg.exists_pow_two_pow_mem_oddPart (le_refl Z) hxZ
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hx, ← QuotientGroup.mk_pow, Subgroup.coe_one,
      QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (X ⧸ O) := by
    refine ⟨?_⟩
    have h1 := Group.IsPerfect.commutator_eq_top (G := X)
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ commutator X := by rw [h1]; exact Subgroup.mem_top x
    have h3 : (⊤ : Subgroup X).map (QuotientGroup.mk' O) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)
    have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hx
    rw [commutator_def, Subgroup.map_commutator, h3, ← commutator_def] at h2
    exact h2
  have hη1 := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_two_cover_trivial hF
    (by omega) (n := 3) le_rfl (by decide) (fun _ => hk) (X ⧸ O) η hηs hηc hη2
  have hZO : ∀ z ∈ Z, Odd (orderOf z) := by
    intro z hz
    have h1 : (QuotientGroup.mk z : X ⧸ O) ∈ η.ker := (hηk z).mpr hz
    rw [hη1, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact h1.2
  have hodd : Odd (Nat.card Z) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card Z := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have h3 := hZO z z.2
    rw [Subgroup.orderOf_coe, hz] at h3
    exact absurd h3 (by decide)
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (ρ : E →* Assembly.LowTwoRank.StatedSU 3 (2 ^ k) F),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center E → Odd (Nat.card ρ.ker) →
      ∃ s : Assembly.LowTwoRank.StatedSU 3 (2 ^ k) F →* E, ∀ g, ρ (s g) = g :=
    fun E _ _ ρ hρ hC hρo => by
    obtain ⟨s, hs, -⟩ :=
      CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting hF hk hρ hC
        hρo
    exact ⟨s, hs⟩
  obtain ⟨φ, hφ, -, hmap⟩ := Ch1.exists_cover_map_of_odd_splitting hodd e hsplit
  have hD3 : Nat.card ((Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
      (Assembly.LowTwoRank.StatedSU 3 (2 ^ k) F)) ∣ 3 :=
    Ch1.card_scalars_dvd_three (p := 2) (f := k) (Or.inr ⟨hF, rfl⟩)
  have hZ3 : Nat.card Z ∣ 3 := by
    rw [hZdef, ← hmap]
    exact (Subgroup.card_map_dvd _ _).trans hD3
  rcases (Nat.dvd_prime Nat.prime_three).mp hZ3 with h1 | h3
  ·
    have hZb : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z h1
    have hinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [← hZb]
      exact (hπk x).mp hx
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by omega, F, inferInstance, inferInstance, hF,
      ⟨MulEquiv.ofBijective π ⟨hinj, hπs⟩⟩⟩)))
  ·
    obtain ⟨-, ⟨iso⟩⟩ := Ch1.triple_cover_unitary h3 (p := 2) (f := k) hF e hsplit
    exact Or.inr (Or.inr (Or.inl ⟨k, by omega, F, inferInstance, inferInstance, hF, ⟨iso⟩⟩))

end CFSG.Quasithin.H13
