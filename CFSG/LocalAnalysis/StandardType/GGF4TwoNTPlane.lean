module

public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTRoots
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCent
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KilledPlaneCubeRoot
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.LieType.SeitzGeneration.UnitaryNonabLift
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KLR.SL2Gen
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithNF
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43

public section

namespace CFSG.StandardType.F4TwoNonToral

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree TableB CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBF4TwoTB

section CertFree

private theorem rootChar_mul {L : Type} [Field L] (a b : Fin Tag.F4.rank → Lˣ)
    (v : Fin Tag.F4.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem rootChar_inv {L : Type} [Field L] (a : Fin Tag.F4.rank → Lˣ)
    (v : Fin Tag.F4.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

private theorem rootDiagUnit_pow_three {L : Type} [Field L] (a : Fin Tag.F4.rank → Lˣ) :
    rootDiagUnit .F4 (a ^ 3) = rootDiagUnit .F4 a ^ 3 :=
  map_pow (rootDiagUnitHom .F4 L) a 3

open CFSG.HardMathSupport.Timmesfeld.Steinberg in
private theorem triPairing_eq_dotRoot (y : Fin Tag.F4.rank → ZMod 3) (α : Fin Tag.F4.rank → ℤ) :
    triPairing (τ := .F4) y α = dotRoot α y :=
  Finset.sum_congr rfl fun i _ => mul_comm _ _

open CFSG.HardMathSupport.Timmesfeld.Steinberg in
private theorem card_triPairing_eq_twelve (y z : Fin Tag.F4.rank → ZMod 3) (hy : y ≠ 0)
    (hno : ∀ α ∈ rootFinset .F4,
      ¬ (triPairing (τ := .F4) y α = 0 ∧ triPairing (τ := .F4) z α = 0)) :
    ((rootFinset .F4).filter fun α => triPairing (τ := .F4) y α = 0).card = 12 := by
  simp only [triPairing_eq_dotRoot] at hno ⊢
  exact f4_card_trivial_eq_twelve y z hy hno

end CertFree

section Plane


open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ in
theorem exists_regular_plane
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hnd : IsEmpty (LangPlaneData .F4 K E)) {e : adjointGroup .F4 K} (heE : e ∈ E)
    (he1 : e ≠ 1) :
    ∃ P : Subgroup (adjointGroup .F4 K), e ∈ P ∧ P ≤ E ∧ Nat.card P = 3 ^ 2 ∧
      ∃ D : LangPlaneData .F4 K P, ∀ α, IsRoot .F4 α → ¬ D.Kills α := by
  classical
  have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have he3 : e ^ 3 = 1 := hE.2 e heE
  have hHcard : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  have hHdvd : Nat.card (Subgroup.zpowers e) ∣ 3 ^ 2 := by rw [hHcard]; norm_num
  have hLdvd : 3 ^ 2 ∣ Nat.card E := by rw [hcard]; norm_num
  have hHL : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.2 heE
  obtain ⟨P, hPc, heP, hPE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (G := adjointGroup .F4 K) Nat.prime_three
      (n := 2) (H := Subgroup.zpowers e) (L := E) hHdvd hLdvd hHL
  have hePmem : e ∈ P := heP (Subgroup.mem_zpowers e)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three K hK3 P
      (fun x hx => hE.2 x (hPE hx)) hPc
  let D : LangPlaneData .F4 K P := ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩
  refine ⟨P, hePmem, hPE, hPc, D, fun α hα hk => ?_⟩
  obtain ⟨D₀⟩ :=
    SeitzExcOpenRest8bAux.nonempty_langPlaneData_of_kills f4ThreeKilledPlaneWeyl_holds
      hK3 hE hcard hPE hPc D hα hk
  exact hnd.false D₀

open scoped Classical in
open CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore in
theorem threeC_data_of_regular_plane (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {P : Subgroup (adjointGroup .F4 K)} (hPc : Nat.card P = 3 ^ 2)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (D : LangPlaneData .F4 K P)
    (hreg : ∀ α, IsRoot .F4 α → ¬ D.Kills α) {e : adjointGroup .F4 K} (heP : e ∈ P)
    (he1 : e ≠ 1) :
    ∃ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit .F4 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * e * D.c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * D.g0 ∧
      ((rootFinset .F4).filter fun α => rootChar a α = 1).card = 12 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHcard : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP3 e heP) he1]
  have hHle : Subgroup.zpowers e ≤ P := Subgroup.zpowers_le.2 heP
  have hHne : Subgroup.zpowers e ≠ P := by
    intro hEq
    have hcard_eq : Nat.card (Subgroup.zpowers e) = Nat.card P := by rw [hEq]
    rw [hHcard, hPc] at hcard_eq
    norm_num at hcard_eq
  obtain ⟨-, f, hfP, hfH⟩ :=
    (SetLike.lt_iff_le_and_exists).1 (lt_of_le_of_ne hHle hHne)
  have hgen : P = Subgroup.closure ({e, f} : Set (adjointGroup .F4 K)) := by
    set C : Subgroup (adjointGroup .F4 K) :=
      Subgroup.closure ({e, f} : Set (adjointGroup .F4 K)) with hC
    have hle : C ≤ P := by
      rw [hC]
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | rfl)
      · exact heP
      · exact hfP
    have hHleC : Subgroup.zpowers e ≤ C := by
      rw [hC]
      exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (Or.inl rfl))
    have hfC : f ∈ C := by
      rw [hC]
      exact Subgroup.subset_closure (Or.inr rfl)
    have hHltC : Subgroup.zpowers e < C := by
      refine lt_of_le_of_ne hHleC ?_
      intro hEq
      exact hfH (hEq ▸ hfC)
    haveI : Finite C :=
      Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    have hcard_lt : Nat.card (Subgroup.zpowers e) < Nat.card C :=
      Subgroup.card_lt_of_lt hHltC
    have hdvd : Nat.card C ∣ 3 ^ 2 := by
      rw [← hPc]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk2, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hgt : 3 < Nat.card C := by
      rw [hHcard] at hcard_lt
      exact hcard_lt
    have hk : k = 2 := by
      have hgt' : 3 < 3 ^ k := by rw [← hkc]; exact hgt
      have h1 : 1 < k :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 (by simpa using hgt')
      omega
    have hCcard : Nat.card C = Nat.card P := by rw [hkc, hk, hPc]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hCcard.symm)).symm
  let bc : ModGL .F4 K →* ModGL .F4 (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K))
  let δ₀ : adjointGroup .F4 K →* ModGL .F4 (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp
      (bc.comp ((adjointGroup .F4 K).subtype.comp (MulAut.conj D.c).toMonoidHom))
  let δHom : P →* ModGL .F4 (AlgebraicClosure K) := δ₀.comp P.subtype
  have hδ₀ : ∀ x : adjointGroup .F4 K, δ₀ x =
      D.g0⁻¹ * bc ((D.c * x * D.c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * D.g0 := by
    intro x
    simp only [δ₀, MonoidHom.comp_apply, MulAut.conj_apply, inv_inv]
    rfl
  have hδtorus : ∀ x : P, δHom x ∈ torusGroup .F4 (AlgebraicClosure K) := by
    intro x
    obtain ⟨t, ht, hgt⟩ := Subgroup.mem_map.1 (D.hc (x : adjointGroup .F4 K) x.2)
    rw [mem_twistedTorusOf] at ht
    have hxeq : δHom x = t := by
      have hgt' : bc ((D.c * (x : adjointGroup .F4 K) * D.c⁻¹ : adjointGroup .F4 K) :
          ModGL .F4 K) = D.g0 * t * D.g0⁻¹ := by
        rw [← hgt]
        change (MulAut.conj D.g0) t = D.g0 * t * D.g0⁻¹
        rw [MulAut.conj_apply]
      rw [show δHom x = δ₀ (x : adjointGroup .F4 K) from rfl, hδ₀, hgt']
      group
    rw [hxeq]
    exact ht.1
  choose a ha using fun x : P =>
    exists_rootDiagUnit_eq_of_mem_torusGroup (hδtorus x)
  have ha3 : ∀ (x : P) (i : Fin Tag.F4.rank), a x i ^ 3 = 1 := by
    intro x
    have hx3P : x ^ 3 = 1 := Subtype.ext (hP3 (x : adjointGroup .F4 K) x.2)
    have h1 : rootDiagUnit .F4 (a x ^ 3) = rootDiagUnit .F4 1 := by
      rw [rootDiagUnit_pow_three, ← ha x, ← map_pow δHom x 3, hx3P, map_one,
        rootDiagUnit_one]
    have h2 : a x ^ 3 = 1 := rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hδ₀inj : Function.Injective δ₀ := by
    intro x y hxy
    simp only [δ₀, MonoidHom.comp_apply] at hxy
    have h1 : bc ((adjointGroup .F4 K).subtype ((MulAut.conj D.c) x)) =
        bc ((adjointGroup .F4 K).subtype ((MulAut.conj D.c) y)) :=
      (MulAut.conj D.g0⁻¹).injective hxy
    have h2 : (adjointGroup .F4 K).subtype ((MulAut.conj D.c) x) =
        (adjointGroup .F4 K).subtype ((MulAut.conj D.c) y) :=
      baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h1
    exact (MulAut.conj D.c).injective (Subtype.val_injective h2)
  have hae1 : a ⟨e, heP⟩ ≠ 1 := by
    intro hae
    apply he1
    have h1 : δ₀ e = 1 := by
      rw [show δ₀ e = δHom ⟨e, heP⟩ from rfl, ha ⟨e, heP⟩, hae, rootDiagUnit_one]
    exact hδ₀inj (h1.trans (map_one δ₀).symm)
  rcases forall_eq_one_or_exists_isPrimitiveRoot_pow a ha3 with hall | ⟨ω, hω, k, hk⟩
  · exact absurd (funext (hall ⟨e, heP⟩)) hae1
  · have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
    have hy : k ⟨e, heP⟩ ≠ 0 := by
      intro hy0
      apply hae1
      funext i
      rw [hk ⟨e, heP⟩ i, hy0]
      simp
    have hno : ∀ α ∈ rootFinset .F4,
        ¬ (triPairing (k ⟨e, heP⟩) α = 0 ∧ triPairing (k ⟨f, hfP⟩) α = 0) := by
      intro α hαmem hboth
      obtain ⟨hy0, hz0⟩ := hboth
      have hα : IsRoot .F4 α := mem_rootFinset.1 hαmem
      refine hreg α hα ?_
      intro x hx
      rw [hgen] at hx
      refine Subgroup.closure_induction (p := fun x _ =>
        ∃ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
          rootDiagUnit .F4 a = δ₀ x ∧ rootChar a α = 1) ?_ ?_ ?_ ?_ hx
      · intro x hxmem
        have hxe : x = e ∨ x = f := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem
        rcases hxe with hxe | hxe
        · rw [hxe]
          refine ⟨a ⟨e, heP⟩, ?_, ?_⟩
          · rw [← ha ⟨e, heP⟩]
            rfl
          · rw [rootChar_eq_pow_triPairing hω3 (hk ⟨e, heP⟩) α, hy0]
            simp
        · rw [hxe]
          refine ⟨a ⟨f, hfP⟩, ?_, ?_⟩
          · rw [← ha ⟨f, hfP⟩]
            rfl
          · rw [rootChar_eq_pow_triPairing hω3 (hk ⟨f, hfP⟩) α, hz0]
            simp
      · refine ⟨1, ?_, ?_⟩
        · rw [rootDiagUnit_one, map_one]
        · simp [rootChar]
      · intro x y hx hy hpx hpy
        obtain ⟨ax, hax, hcx⟩ := hpx
        obtain ⟨ay, hay, hcy⟩ := hpy
        refine ⟨ax * ay, ?_, ?_⟩
        · rw [rootDiagUnit_mul, hax, hay, map_mul]
        · rw [rootChar_mul, hcx, hcy, mul_one]
      · intro x hx hpx
        obtain ⟨ax, hax, hcx⟩ := hpx
        refine ⟨ax⁻¹, ?_, ?_⟩
        · rw [← rootDiagUnit_inv, hax, map_inv]
        · rw [rootChar_inv, hcx, inv_one]
    have hcard := card_triPairing_eq_twelve (k ⟨e, heP⟩) (k ⟨f, hfP⟩) hy hno
    refine ⟨a ⟨e, heP⟩, ?_, ?_⟩
    · rw [← ha ⟨e, heP⟩]
      exact hδ₀ e
    · have hiff : ∀ α ∈ rootFinset .F4,
          (rootChar (a ⟨e, heP⟩) α = 1) ↔ (triPairing (k ⟨e, heP⟩) α = 0) := by
        intro α _
        rw [rootChar_eq_pow_triPairing hω3 (hk ⟨e, heP⟩) α, hω.pow_eq_one_iff_dvd,
          ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]
      refine (Finset.card_bijective (id : (Fin Tag.F4.rank → ℤ) → _)
        Function.bijective_id ?_).trans hcard
      intro α
      rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, (hiff α h.1).1 h.2⟩, fun h => ⟨h.1, (hiff α h.1).2 h.2⟩⟩

end Plane


end CFSG.StandardType.F4TwoNonToral
