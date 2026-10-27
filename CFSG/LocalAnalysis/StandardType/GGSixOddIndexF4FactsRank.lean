module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Facts
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Fixed
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.K128.D4Arith
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Abstract

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem ggF4_eq_three_or_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  omega

omit [Finite X] in
theorem ggF4_isPGroup_of_pow_eq_one {p : ℕ} (hp : p.Prime) {A : Subgroup X}
    (hA : ∀ a ∈ A, a ^ p = 1) : IsPGroup p A := by
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hA g.1 g.2))
  rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
  · exact ⟨0, by rw [h2]; simp⟩
  · exact ⟨1, by rw [h2]; simp⟩

theorem ggF4_card_le_sq_of_exponent {p e : ℕ} (hp : p.Prime)
    (H : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ e)))) (hH : ∀ h ∈ H, h ^ p = 1) :
    Nat.card H ≤ p ^ 2 := by
  classical
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  let _ : Fintype (Multiplicative (ZMod (p ^ e))) := Fintype.ofFinite _
  have hcyc : Nat.card {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1} ≤ p := by
    have := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (p ^ e))) hp.pos
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  let ι : H → (Fin 2 → {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) := fun h i =>
    ⟨(h : Fin 2 → Multiplicative (ZMod (p ^ e))) i, by simpa using congrFun (hH h h.2) i⟩
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hxy i))
  calc Nat.card H ≤ Nat.card (Fin 2 → {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) :=
        Nat.card_le_card_of_injective ι hι
    _ = (Nat.card {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) ^ 2 := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hcyc 2

theorem ggF4_card_le_sq_of_sylowShape {p e : ℕ} (hp : p.Prime)
    (hs : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e X) (A : Subgroup X)
    (hA : ∀ a ∈ A, a ^ p = 1) : Nat.card A ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hAS⟩ := (ggF4_isPGroup_of_pow_eq_one hp hA).exists_le_sylow
  obtain ⟨φ⟩ := hs (S : Subgroup X) S.isPGroup' S.not_dvd_index
  have hcard : Nat.card ((A.subgroupOf S).map φ.toMonoidHom) = Nat.card A := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv
  rw [← hcard]
  refine ggF4_card_le_sq_of_exponent hp _ ?_
  rintro _ ⟨a, ha, rfl⟩
  have hap : a ^ p = 1 := Subtype.ext (by simpa using hA a (Subgroup.mem_subgroupOf.1 ha))
  rw [← map_pow, hap, map_one]

theorem ggF4_card_le_of_pRank_le_one {p : ℕ} (hp : p.Prime) (h : CFSG.pRank p X ≤ 1)
    (A : Subgroup X) (hA : ∀ a ∈ A, a ^ p = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (ggF4_isPGroup_of_pow_eq_one hp hA)
  have hel : CFSG.IsElementaryAbelian p A :=
    { is_comm := ⟨fun a b => Subtype.ext (hAc a.1 a.2 b.1 b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun g =>
        Subtype.ext (by simpa using hA g.1 g.2)) }
  have hmem : j ∈ {r : ℕ | ∃ B : Subgroup X, CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ r} :=
    ⟨A, hel, hj⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ B : Subgroup X, CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ r} := by
    refine ⟨Nat.card X, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : Nat.card B ≤ Nat.card X := Nat.card_le_card_of_injective _ B.subtype_injective
    rw [hB] at h1
    exact (Nat.lt_pow_self hp.one_lt).le.trans h1
  have hj1 : j ≤ 1 := (le_csSup hbdd hmem).trans h
  rw [hj]
  calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
    _ = p := pow_one p

theorem ggF4_card_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card X)
    (A : Subgroup X) (hA : ∀ a ∈ A, a ^ p = 1) : Nat.card A = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (ggF4_isPGroup_of_pow_eq_one hp hA)
  have hdvd : Nat.card A ∣ Nat.card X := Subgroup.card_subgroup_dvd_card A
  rw [hj] at hdvd
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj, hj0, pow_zero]
  · exact absurd ((dvd_pow_self p hj0.ne').trans hdvd) h

theorem ggF4_card_le_of_map {U G W : Type*} [Group U] [Group G] [Group W] {p N : ℕ}
    {χ : U →* G} (hχ : Function.Injective χ) {R : Subgroup U} {Y : Subgroup G}
    (hRY : R.map χ = Y) (ε : R ≃* W)
    (hW : ∀ A : Subgroup W, (∀ a ∈ A, a ^ p = 1) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      Nat.card A ≤ N)
    {E : Subgroup G} (hEY : E ≤ Y) (hE : IsElemAbelian p E) : Nat.card E ≤ N := by
  have hER := ggF4_comap_le_of_le_map hχ hRY hEY
  have hErange : E ≤ χ.range := hEY.trans (hRY ▸ Subgroup.map_le_range χ R)
  have hcard : Nat.card (((E.comap χ).subgroupOf R).map ε.toMonoidHom) = Nat.card E := by
    rw [Subgroup.card_map_of_injective ε.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv,
      ← Subgroup.card_map_of_injective hχ, Subgroup.map_comap_eq_self hErange]
  rw [← hcard]
  refine hW _ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : χ (x : U) ∈ E := hx
    have h1 : (x : U) ^ p = 1 := hχ (by rw [map_pow, hE.2 _ hx', map_one])
    have h2 : x ^ p = 1 := Subtype.ext (by simpa using h1)
    rw [← map_pow, h2, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hx' : χ (x : U) ∈ E := hx
    have hy' : χ (y : U) ∈ E := hy
    have hxy : χ (x : U) * χ (y : U) = χ (y : U) * χ (x : U) :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
    have h1 : (x : U) * y = y * x := hχ (by rw [map_mul, map_mul]; exact hxy)
    have h2 : x * y = y * x := Subtype.ext h1
    rw [← map_mul, h2, map_mul]

end Abstract

section ReeRank

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K128 CFSG.RankThree.LargeReeOrder in
theorem ggF4_ree_card_le_sq {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (A : Subgroup (ReeTag.F4.reeGamma K a)) (hA : ∀ x ∈ A, x ^ p = 1)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ p ^ 2 := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hp2 : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  by_cases hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a)
  · rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp (by omega)
      hdvd with h | h | h | h | h
    · exact ggF4_card_le_sq_of_sylowShape hp (sylowShape_ree_phi1 hK hp hp5 h) A hA
    · exact ggF4_card_le_sq_of_sylowShape hp (sylowShape_ree_phi2 hK hp hp5 h) A hA
    · exact ggF4_card_le_sq_of_sylowShape hp (sylowShape_ree_phi4 hK hp hp5 h) A hA
    · exact (ggF4_card_le_of_pRank_le_one hp (pRank_le_one_ree_phi6 hK hp hp5 h) A hA hAc).trans
        hp2
    · exact (ggF4_card_le_of_pRank_le_one hp (pRank_le_one_ree_phi12 hK hp hp5 h) A hA hAc).trans
        hp2
  · rw [ggF4_card_eq_one_of_not_dvd hp hdvd A hA]
    exact Nat.one_le_pow _ _ hp.pos

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne.BRANCH in
theorem ggF4_ree_card_le_of_exponent_three {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (A : Subgroup (ReeTag.F4.reeGamma K a)) (hA : ∀ x ∈ A, x ^ 3 = 1) :
    Nat.card A ≤ 3 ^ 3 := by
  classical
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have horder := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1
  have hmod3 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rcases CFSG.RankThree.PartOne.BRANCH.two_pow_mod_three (2 * a + 1) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by simp)
    · exact h
  have hQ2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb := card_le_of_sector_three D (odd_mPhi2' a) (torusParam_phi2 D.isFrob)
    (fun i hi => not_nine_dvd_ree_twisted hQ2 hmod3 (by
      rw [mPhi2] at hi
      rw [horder] at hi
      rw [mul_comm] at hi
      exact hi)) hA
  exact hb.trans_eq (by norm_num)

end ReeRank

section Rank

theorem ggF4_graphField_card_le {p N : ℕ}
    (hW : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (m : ℕ),
      Nat.card K = 2 ^ (2 * m + 1) → ∀ A : Subgroup (ReeTag.F4.reeGamma K m),
        (∀ a ∈ A, a ^ p = 1) → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ N)
    {G : Type} [Group G] [Finite G] {n f : ℕ} {ψ : (ggU .F4 n f).K →* G} {G₀ : Subgroup G}
    (hcfg : GGF4Config n f ψ G₀) (hf : Odd f) {s : G}
    (hs : s ∈ Subgroup.normalizer (G₀ : Set G)) (hsG : s ∉ G₀) (hs2 : orderOf s = 2)
    {E : Subgroup G} (hEY : E ≤ G₀ ⊓ Subgroup.centralizer {s}) (hE : IsElemAbelian p E) :
    Nat.card E ≤ N := by
  obtain ⟨-, -, hrange, hker, -, -, hC⟩ := hcfg
  subst hrange
  obtain ⟨m, rfl⟩ := hf
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 _ (by omega)
  have : CharP (GaloisField 2 (2 * m + 1)) ReeTag.F4.prime :=
    (inferInstance : CharP (GaloisField 2 (2 * m + 1)) 2)
  have hψ := ggF4_injective_of_center_eq_bot center_adjointGroup_eq_bot hker
  obtain ⟨χ, hχ, hmap⟩ :=
    ggF4_exists_ree_embedding (K := GaloisField 2 (2 * m + 1)) hK hψ hC hs hsG hs2
  exact ggF4_card_le_of_map hχ hmap (ReeTag.reeFixedEquivReeGamma _ m)
    (hW (GaloisField 2 (2 * m + 1)) m hK) hEY hE

theorem ggF4_graphField_rank_le_sq_of_five_le :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
      GGF4Config n f ψ G₀ → Odd f → ∀ p : ℕ, p.Prime → 5 ≤ p →
      ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ → orderOf s = 2 →
        ∀ E : Subgroup G, E ≤ G₀ ⊓ Subgroup.centralizer {s} → IsElemAbelian p E →
          Nat.card E ≤ p ^ 2 := by
  intro G _ _ n f ψ G₀ hcfg hf p hp hp5 s hs hsG hs2 E hEY hE
  exact ggF4_graphField_card_le
    (fun K _ _ _ m hK A hA hAc => ggF4_ree_card_le_sq hK hp hp5 A hA hAc) hcfg hf hs hsG hs2 hEY hE

theorem ggF4_graphField_rank_le_cube :
    ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
      GGF4Config n f ψ G₀ → Odd f → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ → orderOf s = 2 →
        ∀ E : Subgroup G, E ≤ G₀ ⊓ Subgroup.centralizer {s} → IsElemAbelian p E →
          Nat.card E ≤ p ^ 3 := by
  intro G _ _ n f ψ G₀ hcfg hf p hp hp2 s hs hsG hs2 E hEY hE
  rcases ggF4_eq_three_or_five_le hp hp2 with rfl | hp5
  · exact ggF4_graphField_card_le
      (fun K _ _ _ m hK A hA _ => ggF4_ree_card_le_of_exponent_three hK A hA)
      hcfg hf hs hsG hs2 hEY hE
  · exact (ggF4_graphField_rank_le_sq_of_five_le G n f ψ G₀ hcfg hf p hp hp5 s hs hsG hs2 E hEY
      hE).trans (Nat.pow_le_pow_right hp.pos (by norm_num))

end Rank

end CFSG.StandardType
