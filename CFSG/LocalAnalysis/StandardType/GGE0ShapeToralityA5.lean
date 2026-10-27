module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeRealConj
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeWeylGoodDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeBruhat
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.HardMathSupport.Timmesfeld.Torality.ToralPairOne
public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Open

private theorem step_eq_frobTwistGL_aux
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (D : LangDatum τ L) {f : ℕ} {P : ModGL τ L}
    (hΦ : ∀ g, D.Φ g = P * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * P⁻¹) :
    D.step = frobTwistGL τ L 2 f (D.n * P) := by
  apply MonoidHom.ext
  intro g
  rw [frobTwistGL_apply]
  change D.n * D.Φ g * D.n⁻¹ =
    (D.n * P) * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * (D.n * P)⁻¹
  rw [hΦ g]
  group

private theorem mapsTo_familyKernel_aux
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) (ha : ∀ i, rootDiagUnit τ (a i) ∈ D.torus) :
    Set.MapsTo ρ (familyKernel a) (familyKernel a) := by
  intro γ hγ
  refine ⟨(hρ.isRoot_iff γ).2 hγ.1, fun i => ?_⟩
  rw [hρ.rootChar_eq (a i) (ha i) γ hγ.1, hγ.2 i, one_pow]

private theorem n_mul_P_mem_normalizer_aux
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L) {P : ModGL τ L}
    (hP : P = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ), P = diagramAt τ L t h) :
    D.n * P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  obtain ⟨w, hn⟩ := D.n_weyl
  refine mul_mem ?_ ?_
  · rw [hn]
    exact canonicalRep_mem_normalizer (R := L) w
  · rcases hP with rfl | ⟨t, ht, rfl⟩
    · exact Subgroup.one_mem _
    · subst ht
      exact diagramMap_mem_normalizer t

private theorem famKernel_step_mem_torusGroup_aux
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} {D : LangDatum τ L}
    {Q : ModGL τ L} (hstep : D.step = frobTwistGL τ L 2 f Q)
    (hQ : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L))) :
    (torusGroup τ L).map D.step ≤ torusGroup τ L := by
  haveI : PerfectRing L 2 := IsAlgClosed.perfectRing L 2
  rw [hstep, map_frobTwistGL_torusGroup 2 f hQ]

private theorem famKernel_step_mem_rootSpan_aux
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a)) :
    (rootSpan τ L (familyKernel a)).map D.step ≤ rootSpan τ L (familyKernel a) := by
  have hmap : (rootSpan τ L (familyKernel a)).map D.step =
      rootSpan τ L (ρ '' familyKernel a) := by
    simp only [rootSpan, Subgroup.map_iSup]
    rw [iSup_image]
    exact iSup_congr fun γ => iSup_congr fun hγ => hρ.map_rootSubgroup γ hγ.1
  rw [hmap]
  exact rootSpan_mono hρΨ.image_subset

private theorem step_mem_familyGroup_aux
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    {f : ℕ} {P : ModGL τ L} (hstepEq : D.step = frobTwistGL τ L 2 f (D.n * P))
    (hQ : D.n * P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)))
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a))
    {g : ModGL τ L} (hg : g ∈ familyGroup (K := L) a) :
    D.step g ∈ familyGroup (K := L) a := by
  have htorus := famKernel_step_mem_torusGroup_aux hstepEq hQ
  have hrootspan := famKernel_step_mem_rootSpan_aux hρ hρΨ
  have hle : (familyGroup (K := L) a).map D.step ≤ familyGroup (K := L) a := by
    rw [familyGroup, Subgroup.map_sup]
    exact sup_le (htorus.trans le_sup_left) (hrootspan.trans le_sup_right)
  exact hle (Subgroup.mem_map_of_mem _ hg)

private theorem step_mem_adjointGroup_aux
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) : D.step g ∈ adjointGroup τ L := by
  have hmap : (rootSpan τ L {α | IsRoot τ α}).map D.step ≤ rootSpan τ L {α | IsRoot τ α} := by
    refine Subgroup.map_le_iff_le_comap.2 ?_
    refine iSup₂_le fun γ hγ => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : D.step x ∈ (rootSubgroup τ L γ).map D.step := ⟨x, hx, rfl⟩
    rw [hρ.map_rootSubgroup γ hγ] at h1
    exact Subgroup.mem_iSup_of_mem (ρ γ)
      (Subgroup.mem_iSup_of_mem ((hρ.isRoot_iff γ).2 hγ) h1)
  rw [adjointGroup_eq_rootSpan]
  exact hmap ⟨g, by rwa [adjointGroup_eq_rootSpan] at hg, rfl⟩

private theorem exists_q_eq_two_pow_aux
    {K : Type} [Field K] [CharP K 2]
    (S : LangSetup .E6 (AlgebraicClosure K) 5) :
    ∃ f : ℕ, 1 ≤ f ∧ S.D.q = 2 ^ f := by
  obtain ⟨p, f, hp, hf, hqeq⟩ := (isPrimePow_nat_iff _).mp S.hqpow.1
  have hp2 : p = 2 := by
    have h0 : ((p : ℕ) : AlgebraicClosure K) = 0 := by
      have h := S.hqpow.2
      rw [← hqeq, Nat.cast_pow] at h
      exact (pow_eq_zero_iff (by omega)).1 h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h0)).symm
  subst hp2
  exact ⟨f, by omega, hqeq.symm⟩

private theorem lang_solution_in_familyGroup_aux
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (D : LangDatum .E6 L) {f : ℕ} (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ : FrobRootMap D ρ) {ι : Type}
    {a : ι → Fin Tag.E6.rank → Lˣ}
    (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a)) :
    ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a, z⁻¹ * D.step z = c := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  have hΦ' : ∀ y, D.Φ y =
      P * Units.map (entrywiseHom (iterateFrobenius L 2 f)) y * P⁻¹ := by
    intro y
    rw [hΦ y, hFr_eq]
  have hstepEq : D.step = frobTwistGL .E6 L 2 f (D.n * P) := step_eq_frobTwistGL_aux D hΦ'
  have hQ := n_mul_P_mem_normalizer_aux D hP
  have hst : ∀ y ∈ familyGroup (K := L) a,
      frobTwistGL .E6 L 2 f (D.n * P) y ∈ familyGroup (K := L) a := by
    intro y hy
    rw [← hstepEq]
    exact step_mem_familyGroup_aux D hstepEq hQ hρ hρΨ hy
  intro c hc
  obtain ⟨z, hz, hzc⟩ := lang_familyGroup_of_mapsTo (ℓ := 2) a f hf (D.n * P) hst c hc
  refine ⟨z, hz, ?_⟩
  rw [hstepEq, frobTwistGL_apply]
  exact hzc

theorem toral_conj_in_model
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hWG : WeylGoodRankFive (AlgebraicClosure K))
    (S : LangSetup .E6 (AlgebraicClosure K) 5)
    (hT3 : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
        rootDiagUnit .E6 a ∈ S.D.torus)
    {A : Subgroup (ModGL .E6 (AlgebraicClosure K))} (hA : A ≤ S.D.model)
    (hAel : IsElemAbelian 3 A) (h5 : 3 ^ 5 ≤ Nat.card A) :
    ∃ h ∈ S.D.model, A.map (MulAut.conj h).toMonoidHom ≤ S.D.torus := by
  classical
  let L := AlgebraicClosure K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAadj : A ≤ adjointGroup .E6 L := hA.trans inf_le_left
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hAel hx hy
  have hAexp : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => hAel.2 x hx
  have hKnot3 : ¬ 3 ∣ Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    intro h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    exact absurd h32 (by norm_num)
  obtain ⟨g, hgG, hgA⟩ :=
    ExcFramesHalf.bigElemAbelianToralBar_E6_three K hKnot3 A hAadj hAcomm hAexp h5
  have hcoord : ∀ x : A, ∃ a : Fin Tag.E6.rank → Lˣ,
      g⁻¹ * (x : ModGL .E6 L) * g = rootDiagUnit .E6 a :=
    fun x => exists_rootDiagUnit_eq_of_mem_torusGroup (hgA x x.2)
  let a : A → Fin Tag.E6.rank → Lˣ := fun x => Classical.choose (hcoord x)
  have ha_spec : ∀ x : A, g⁻¹ * (x : ModGL .E6 L) * g = rootDiagUnit .E6 (a x) :=
    fun x => Classical.choose_spec (hcoord x)
  have ha_pow : ∀ x : A, ∀ i, a x i ^ 3 = 1 := by
    intro x i
    have hmap : rootDiagUnit .E6 ((a x) ^ 3) = (rootDiagUnit .E6 (a x)) ^ 3 :=
      (rootDiagUnitHom .E6 L).map_pow (a x) 3
    have h1 : rootDiagUnit .E6 ((a x) ^ 3) = rootDiagUnit .E6 (1 : Fin Tag.E6.rank → Lˣ) := by
      rw [hmap, rootDiagUnit_one, ← ha_spec x]
      have hconj := conj_pow (a := g⁻¹) (b := (x : ModGL .E6 L)) (i := 3)
      rw [inv_inv] at hconj
      rw [hconj, hAel.2 x x.2]
      group
    have h2 : (a x) ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact congrFun h2 i
  let AT : Subgroup (ModGL .E6 L) :=
    Subgroup.closure (Set.range fun x : A => rootDiagUnit .E6 (a x))
  have hATeq : AT = A.map (MulAut.conj g⁻¹).toMonoidHom := by
    apply le_antisymm
    · refine (Subgroup.closure_le (A.map (MulAut.conj g⁻¹).toMonoidHom)).2 ?_
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(x : ModGL .E6 L), x.2, by
        change g⁻¹ * (x : ModGL .E6 L) * g = rootDiagUnit .E6 (a x)
        exact ha_spec x⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.subset_closure ⟨⟨x, hx⟩, (ha_spec ⟨x, hx⟩).symm⟩
  have hATcard : 3 ^ 5 ≤ Nat.card AT := by
    rw [hATeq, Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective]
    exact h5
  have hWG' : WeylGood (τ := Tag.E6) a := hWG a (fun x i => ha_pow x i) hATcard
  have hfam : familyCentralizer .E6 L a = familyGroup (K := L) a :=
    familyCentralizer_eq_of_weylGood a hWG'
  have ha_tor : ∀ x : A, rootDiagUnit .E6 (a x) ∈ S.D.torus :=
    fun x => hT3 (a x) (fun i => ha_pow x i)
  have hρΨ : Set.MapsTo S.ρ (familyKernel a) (familyKernel a) :=
    mapsTo_familyKernel_aux S.D S.frob ha_tor
  obtain ⟨f, hf1, hqf⟩ := exists_q_eq_two_pow_aux S
  have hLang := lang_solution_in_familyGroup_aux S.D hf1 hqf S.frob hρΨ
  have hstep_adj : S.D.step g ∈ adjointGroup .E6 L :=
    step_mem_adjointGroup_aux S.D S.ρ S.frob hgG
  have hstep_inv : g⁻¹ * S.D.step g ∈ familyGroup (K := L) a := by
    have hm0 : (S.D.step g)⁻¹ * g ∈ familyGroup (K := L) a := by
      rw [← hfam, mem_familyCentralizer]
      refine ⟨mul_mem (inv_mem hstep_adj) hgG, ?_⟩
      intro x
      have hF_w : S.D.step (rootDiagUnit .E6 (a x)) = rootDiagUnit .E6 (a x) := by
        change S.D.n * S.D.Φ (rootDiagUnit .E6 (a x)) * S.D.n⁻¹ = rootDiagUnit .E6 (a x)
        exact (mem_twistedTorusOf.1 (ha_tor x)).2
      have hF_x : S.D.step (x : ModGL .E6 L) = (x : ModGL .E6 L) := by
        have hxM := hA x.2
        rw [LangDatum.mem_model] at hxM
        change S.D.n * S.D.Φ (x : ModGL .E6 L) * S.D.n⁻¹ = (x : ModGL .E6 L)
        exact hxM.2
      have hstep_split : S.D.step (g⁻¹ * (x : ModGL .E6 L) * g) =
          (S.D.step g)⁻¹ * S.D.step (x : ModGL .E6 L) * S.D.step g := by
        rw [map_mul, map_mul, map_inv]
      have hmw : (S.D.step g)⁻¹ * g * (rootDiagUnit .E6 (a x)) *
          ((S.D.step g)⁻¹ * g)⁻¹ = rootDiagUnit .E6 (a x) := by
        calc (S.D.step g)⁻¹ * g * (rootDiagUnit .E6 (a x)) * ((S.D.step g)⁻¹ * g)⁻¹
            = (S.D.step g)⁻¹ * (g * (rootDiagUnit .E6 (a x)) * g⁻¹) * S.D.step g := by
              group
          _ = (S.D.step g)⁻¹ * (x : ModGL .E6 L) * S.D.step g := by
              rw [show g * (rootDiagUnit .E6 (a x)) * g⁻¹ = (x : ModGL .E6 L) by
                rw [← ha_spec x]; group]
          _ = S.D.step (g⁻¹ * (x : ModGL .E6 L) * g) := by rw [hstep_split, hF_x]
          _ = S.D.step (rootDiagUnit .E6 (a x)) := by rw [← ha_spec x]
          _ = rootDiagUnit .E6 (a x) := hF_w
      have hcomm : rootDiagUnit .E6 (a x) * ((S.D.step g)⁻¹ * g) =
          ((S.D.step g)⁻¹ * g) * rootDiagUnit .E6 (a x) := by
        have h := congrArg (fun t => t * ((S.D.step g)⁻¹ * g)) hmw
        simpa [mul_assoc] using h.symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hinv := inv_mem hm0
    rwa [mul_inv_rev, inv_inv] at hinv
  have hLang' : ∀ c ∈ familyGroup (K := L) a, ∃ z ∈ familyGroup (K := L) a,
      z⁻¹ * (1 * S.D.step z * 1⁻¹) = c := by
    intro c hc
    obtain ⟨z, hz, hzc⟩ := hLang c hc
    exact ⟨z, hz, by simpa using hzc⟩
  obtain ⟨z, hz, hzfix⟩ := exists_mem_lang_conj S.D.step
    (M := familyGroup (K := L) a) (Q := 1) (g := g) (m := g⁻¹ * S.D.step g)
    hstep_inv (by group) hLang'
  let h0 : ModGL .E6 L := g * z
  have hh0adj : h0 ∈ adjointGroup .E6 L :=
    mul_mem hgG (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a hz)).1
  have hh0fix : S.D.step h0 = h0 := by
    have h := congrArg (fun t => (g * z) * t) hzfix
    simpa [h0, mul_assoc] using h
  have hh0model : h0 ∈ S.D.model := by
    rw [LangDatum.mem_model]
    exact ⟨hh0adj, by change S.D.step h0 = h0; exact hh0fix⟩
  refine ⟨h0⁻¹, inv_mem hh0model, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  change h0⁻¹ * x * (h0⁻¹)⁻¹ ∈ S.D.torus
  have hz_comm : z * (g⁻¹ * (x : ModGL .E6 L) * g) =
      (g⁻¹ * (x : ModGL .E6 L) * g) * z := by
    have h := (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a hz)).2 ⟨x, hx⟩
    rw [← ha_spec ⟨x, hx⟩] at h
    have h2 := congrArg (fun t => t * (g⁻¹ * (x : ModGL .E6 L) * g)) h
    simpa [mul_assoc] using h2.symm
  rw [show h0⁻¹ * x * (h0⁻¹)⁻¹ = rootDiagUnit .E6 (a ⟨x, hx⟩) by
    calc h0⁻¹ * x * (h0⁻¹)⁻¹ = z⁻¹ * (g⁻¹ * (x : ModGL .E6 L) * g) * z := by
          dsimp [h0]; group
      _ = g⁻¹ * (x : ModGL .E6 L) * g := by
          have hzinv : z⁻¹ * (g⁻¹ * (x : ModGL .E6 L) * g) =
              (g⁻¹ * (x : ModGL .E6 L) * g) * z⁻¹ := by
            have h := congrArg (fun t => z⁻¹ * t * z⁻¹) hz_comm
            simpa [mul_assoc] using h.symm
          rw [hzinv]
          group
      _ = rootDiagUnit .E6 (a ⟨x, hx⟩) := ha_spec ⟨x, hx⟩]
  exact hT3 (a ⟨x, hx⟩) (fun i => ha_pow ⟨x, hx⟩ i)

end CFSG.StandardType
