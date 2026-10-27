module

public import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
public import CFSG.LocalAnalysis.StandardType.GGLangTorusOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallPerfect
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LieType.Chevalley.E6EvenRootTorus
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed
public import CFSG.RankThree.Classical2.SLnRootAutomorphism
public import CFSG.RankThree.Classical2.SLnConjLemmas
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASuConj
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Timmesfeld.Proving.SimpleRootsCartan
public import CFSG.LieType.Chevalley.CorootCoordinates
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.QTwoCav

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootTorus CFSG.StandardType.LangRat
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Proving
open scoped commutatorElement MatrixGroups


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

@[expose] noncomputable def fullThreeTorus (S : LangSetup τ L p) : Subgroup (ModGL τ L) where
  carrier := {t | t ∈ S.D.torus ∧ t ^ 3 = 1}
  one_mem' := ⟨S.D.torus.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haT, ha3⟩ ⟨hbT, hb3⟩
    have hcomm : Commute a b :=
      torusGroup_mul_comm ((inf_le_left : S.D.torus ≤ torusGroup τ L) haT)
        ((inf_le_left : S.D.torus ≤ torusGroup τ L) hbT)
    refine ⟨S.D.torus.mul_mem haT hbT, ?_⟩
    rw [hcomm.mul_pow, ha3, hb3, one_mul]
  inv_mem' := by
    rintro a ⟨haT, ha3⟩
    refine ⟨S.D.torus.inv_mem haT, ?_⟩
    rw [inv_pow, ha3, inv_one]

theorem mem_fullThreeTorus (S : LangSetup τ L p) {t : ModGL τ L} :
    t ∈ fullThreeTorus S ↔ t ∈ S.D.torus ∧ t ^ 3 = 1 := Iff.rfl

theorem fullThreeTorus_le_torus (S : LangSetup τ L p) : fullThreeTorus S ≤ S.D.torus :=
  fun _ ht => ht.1

theorem fullThreeTorus_pow_three (S : LangSetup τ L p) {t : ModGL τ L}
    (ht : t ∈ fullThreeTorus S) : t ^ 3 = 1 := ht.2

theorem fullThreeTorus_one (S : LangSetup τ L p) : (1 : ModGL τ L) ∈ fullThreeTorus S :=
  ⟨S.D.torus.one_mem, by simp⟩

theorem fullThreeTorus_comm (S : LangSetup τ L p) {a b : ModGL τ L}
    (ha : a ∈ fullThreeTorus S) (hb : b ∈ fullThreeTorus S) : a * b = b * a :=
  torusGroup_mul_comm ((inf_le_left : S.D.torus ≤ torusGroup τ L) ha.1)
    ((inf_le_left : S.D.torus ≤ torusGroup τ L) hb.1)

theorem torus_pow_three_eq_one_of_rho_neg (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {b : Fin τ.rank → Lˣ}
    (hb : rootDiagUnit τ b ∈ S.D.torus) : (rootDiagUnit τ b) ^ 3 = 1 := by
  have hroot : ∀ j : Fin τ.rank, b j ^ 3 = 1 := by
    intro j
    have h := S.frob.rootChar_eq b hb (Pi.single j 1) (isRoot_single τ j)
    rw [hρ _ (isRoot_single τ j), hq] at h
    rw [show -(Pi.single j 1 : Fin τ.rank → ℤ) = 0 - Pi.single j 1 by simp, rootChar_sub,
      rootChar_zero, one_mul, rootChar_single] at h
    calc b j ^ 3 = b j * b j ^ 2 := by
          rw [show (3:ℕ) = 1 + 2 by norm_num, pow_add, pow_one]
      _ = b j * (b j)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  rw [rootDiagUnit_pow, show b ^ 3 = 1 from funext hroot, rootDiagUnit_one]

theorem fullThreeTorus_eq_torus (hq : S.D.q = 2) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) :
    fullThreeTorus S = S.D.torus := by
  refine le_antisymm (fullThreeTorus_le_torus S) fun t ht => ?_
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    ((inf_le_left : S.D.torus ≤ torusGroup τ L) ht)
  exact ⟨ht, torus_pow_three_eq_one_of_rho_neg S hq hρ ht⟩

theorem rootWeylSL2_mem_model_of_rho_neg [CharP L 2] {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hργ : S.ρ γ = -γ) : rootSL2 τ L γ WSL ∈ S.D.model :=
  rootSL2_WSL_mem_model_of_rho S hγ (Or.inr hργ)

theorem rootWeylSL2_mul_self_of_charTwo [CharP L 2] (γ : Fin τ.rank → ℤ) :
    rootSL2 τ L γ WSL * rootSL2 τ L γ WSL = 1 :=
  rootSL2_WSL_mul_self γ

theorem rootWeylSL2_mem_Γ_of_rho_neg (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hργ : S.ρ γ = -γ) : rootSL2 τ L γ WSL ∈ S.Γ :=
  rootSL2_WSL_mem_Γ_of_rho S hτ hq hAlg hγ (Or.inr hργ)

theorem exists_rootWeylSL2_mem_monomial_quotient (S : LangSetup τ L p)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ hn : rootSL2 τ L γ WSL ∈ monomialSubgroup τ L,
      weylQuotientHom τ L ⟨rootSL2 τ L γ WSL, hn⟩ = rootReflection γ := by
  obtain ⟨-, -, hn, -, hπ⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hγ
  obtain ⟨hn1, hπ1⟩ := hn 1
  have hW : rootSL2 τ L γ WSL = rootWeylSL2 τ L γ 1 := by
    rw [rootWeylSL2, nSL_one]
  rw [hW]
  exact ⟨hn1, hπ1⟩

theorem rootWeylSL2_mem_normalizer_torus [CharP L 2] {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hργ : S.ρ γ = -γ) :
    rootSL2 τ L γ WSL ∈ Subgroup.normalizer (S.D.torus : Set (ModGL τ L)) := by
  obtain ⟨hn, -⟩ := exists_rootWeylSL2_mem_monomial_quotient S hγ
  have hM : rootSL2 τ L γ WSL ∈ S.D.model := rootWeylSL2_mem_model_of_rho_neg S hγ hργ
  have hH : rootSL2 τ L γ WSL ∈
      Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    mem_normalizer_torusGroup_of_mem_monomialSubgroup hn
  have hstepN : S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ WSL :=
    (S.D.mem_model.1 hM).2
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨?_, ?_⟩
  · intro ht
    refine mem_twistedTorusOf.2 ⟨(Subgroup.mem_normalizer_iff.1 hH t).1 ht.1, ?_⟩
    change S.D.step (rootSL2 τ L γ WSL * t * (rootSL2 τ L γ WSL)⁻¹) =
      rootSL2 τ L γ WSL * t * (rootSL2 τ L γ WSL)⁻¹
    have htstep : S.D.step t = t := (mem_twistedTorusOf.1 ht).2
    rw [map_mul, map_mul, map_inv, hstepN, htstep]
  · intro ht
    have htH : t ∈ torusGroup τ L :=
      ((Subgroup.mem_normalizer_iff.1 hH) t).2 ht.1
    refine mem_twistedTorusOf.2 ⟨htH, ?_⟩
    change S.D.step t = t
    have hfix : S.D.step (rootSL2 τ L γ WSL * t * (rootSL2 τ L γ WSL)⁻¹) =
        rootSL2 τ L γ WSL * t * (rootSL2 τ L γ WSL)⁻¹ :=
      (mem_twistedTorusOf.1 ht).2
    have hstep : S.D.step t =
        (S.D.step (rootSL2 τ L γ WSL))⁻¹ * S.D.step (rootSL2 τ L γ WSL * t *
          (rootSL2 τ L γ WSL)⁻¹) * S.D.step (rootSL2 τ L γ WSL) := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [hstep, hfix, hstepN]
    group

theorem rootWeylSL2_mem_normalizer_fullThreeTorus [CharP L 2] {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hργ : S.ρ γ = -γ) :
    rootSL2 τ L γ WSL ∈
      Subgroup.normalizer (fullThreeTorus S : Set (ModGL τ L)) := by
  have hT := rootWeylSL2_mem_normalizer_torus S hγ hργ
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨?_, ?_⟩
  · intro ht
    refine (mem_fullThreeTorus S).2 ⟨(Subgroup.mem_normalizer_iff.1 hT t).1 ht.1, ?_⟩
    have hconj : (MulAut.conj (rootSL2 τ L γ WSL)) (t ^ 3) =
        ((MulAut.conj (rootSL2 τ L γ WSL)) t) ^ 3 := map_pow _ t 3
    have h3 : ((MulAut.conj (rootSL2 τ L γ WSL)) t) ^ 3 = 1 := by
      rw [← hconj, ht.2, map_one]
    exact h3
  · intro ht
    refine (mem_fullThreeTorus S).2 ⟨
      ((Subgroup.mem_normalizer_iff.1 hT) t).2 ht.1, ?_⟩
    have hconj : (MulAut.conj (rootSL2 τ L γ WSL)) (t ^ 3) =
        ((MulAut.conj (rootSL2 τ L γ WSL)) t) ^ 3 := map_pow _ t 3
    have h3 : ((MulAut.conj (rootSL2 τ L γ WSL)) t) ^ 3 = 1 := ht.2
    have h1 : (MulAut.conj (rootSL2 τ L γ WSL)) (t ^ 3) = 1 := by rw [hconj, h3]
    have h2 := congrArg (MulAut.conj ((rootSL2 τ L γ WSL)⁻¹)) h1
    simpa [MulAut.conj_apply, mul_assoc] using h2

theorem rootWeylSL2_conj_rootDiagUnit (S : LangSetup τ L p)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (b : Fin τ.rank → Lˣ) :
    rootSL2 τ L γ WSL * rootDiagUnit τ b * (rootSL2 τ L γ WSL)⁻¹ =
      rootDiagUnit τ (weylTuple (rootReflection γ) b) := by
  obtain ⟨hn, hπ⟩ := exists_rootWeylSL2_mem_monomial_quotient S hγ
  obtain ⟨w, k, hk, hnk⟩ := monomialSubgroup_le_torusWeylCosets (R := L) hn
  have hw : w = rootReflection γ := by
    have hmaps : MapsRootLines (rootSL2 τ L γ WSL) w := by
      rw [hnk]
      simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
    have h1 : weylQuotientHom τ L ⟨rootSL2 τ L γ WSL, hn⟩ = w :=
      weylQuotientHom_eq hmaps
    rw [← h1, hπ]
  rw [hnk, hw]
  have hkcomm : k * rootDiagUnit τ b = rootDiagUnit τ b * k :=
    torusGroup_mul_comm hk (rootDiagUnit_mem_torusGroup b)
  have hkcomm' : k * rootDiagUnit τ (weylTuple (rootReflection γ) b) =
      rootDiagUnit τ (weylTuple (rootReflection γ) b) * k :=
    torusGroup_mul_comm hk (rootDiagUnit_mem_torusGroup _)
  calc k * canonicalRep (coxeterSystem τ) L (rootReflection γ) * rootDiagUnit τ b *
        (k * canonicalRep (coxeterSystem τ) L (rootReflection γ))⁻¹
      = k * (canonicalRep (coxeterSystem τ) L (rootReflection γ) * rootDiagUnit τ b *
          (canonicalRep (coxeterSystem τ) L (rootReflection γ))⁻¹) * k⁻¹ := by group
    _ = k * rootDiagUnit τ (weylTuple (rootReflection γ) b) * k⁻¹ := by
        rw [canonicalRep_conj_rootDiagUnit]
    _ = rootDiagUnit τ (weylTuple (rootReflection γ) b) := by
        rw [hkcomm', mul_assoc, mul_inv_cancel, mul_one]


theorem closure_pair_eq_four {G : Type} [Group G] {g h : G}
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hne : g ≠ h) :
    (Subgroup.closure ({g, h} : Set G) : Set G) = {g * h, g, h, 1} := by
  classical
  have hmix : h * (g * h) = g := by
    rw [← mul_assoc, ← hcomm, mul_assoc, hh2, mul_one]
  have hab_ab : (g * h) * (g * h) = 1 := by
    rw [mul_assoc, hmix, hg2]
  have hab_g : (g * h) * g = h := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, hg2, one_mul]
  have hab_h : (g * h) * h = g := by
    rw [mul_assoc, hh2, mul_one]
  have hg_ab : g * (g * h) = h := by
    rw [← mul_assoc, hg2, one_mul]
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with rfl | rfl <;> simp
    | one => simp
    | mul x y hxK hyK ihx ihy =>
        rcases ihx with rfl | rfl | rfl | rfl <;>
          rcases ihy with rfl | rfl | rfl | rfl <;>
          simp [Set.mem_insert_iff, Set.mem_singleton_iff, hg2, hh2, hcomm.symm,
            hab_ab, hab_g, hab_h, hg_ab, hmix]
    | inv x hxK ihx =>
        rcases ihx with rfl | rfl | rfl | rfl <;>
          simp [Set.mem_insert_iff, Set.mem_singleton_iff,
            inv_eq_of_mul_eq_one_right hg2, inv_eq_of_mul_eq_one_right hh2,
            inv_eq_of_mul_eq_one_right hab_ab]
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _

theorem natCard_closure_pair_involutions {G : Type} [Group G] {g h : G}
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hne : g ≠ h) :
    Nat.card (Subgroup.closure ({g, h} : Set G)) = 4 := by
  classical
  have hgh : g * h ≠ 1 := by
    intro h1
    have h2 : g = h := by
      have := congrArg (fun x => x * h) h1
      simpa [mul_assoc, hh2] using this
    exact hne h2
  have hghg : g * h ≠ g := by
    intro h1
    exact hh1 (by simpa using h1)
  have hghh : g * h ≠ h := by
    intro h1
    exact hg1 (by simpa using h1)
  have hset := closure_pair_eq_four hg2 hh2 hcomm hg1 hh1 hne
  change ((Subgroup.closure ({g, h} : Set G) : Set G)).ncard = 4
  rw [hset]
  have h1 : g * h ∉ ({g, h, 1} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h' | h' | h')
    · exact hghg h'
    · exact hghh h'
    · exact hgh h'
  have h2 : g ∉ ({h, 1} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h' | h')
    · exact hne h'
    · exact hg1 h'
  have h3 : h ∉ ({1} : Set G) := by
    simp only [Set.mem_singleton_iff]
    exact hh1
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem h3]
  simp

theorem four_dvd_ggAutomizer_of_two_independent_involutions
    {G : Type} [Group G] {A J : Subgroup G} {g h : G}
    (hgJ : g ∈ J) (hhJ : h ∈ J)
    (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hhN : h ∈ Subgroup.normalizer (A : Set G))
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hne : g ≠ h)
    (hker : ∀ x ∈ Subgroup.closure ({g, h} : Set G),
      (∀ a ∈ A, x * a * x⁻¹ = a) → x = 1) :
    4 ∣ Nat.card (ggAutomizer J A) := by
  classical
  set φg : MulAut ↥A := ggConjAut A hgN with hφgdef
  set φh : MulAut ↥A := ggConjAut A hhN with hφhdef
  have hgK : g ∈ Subgroup.closure ({g, h} : Set G) := Subgroup.subset_closure (by simp)
  have hhK : h ∈ Subgroup.closure ({g, h} : Set G) := Subgroup.subset_closure (by simp)
  have hφg2 : φg * φg = 1 := by
    ext a
    simp only [hφgdef, MulAut.mul_apply, ggConjAut_apply, MulAut.one_apply]
    calc g * (g * ↑a * g⁻¹) * g⁻¹ = (g * g) * ↑a * (g * g)⁻¹ := by group
      _ = ↑a := by rw [hg2]; group
  have hφh2 : φh * φh = 1 := by
    ext a
    simp only [hφhdef, MulAut.mul_apply, ggConjAut_apply, MulAut.one_apply]
    calc h * (h * ↑a * h⁻¹) * h⁻¹ = (h * h) * ↑a * (h * h)⁻¹ := by group
      _ = ↑a := by rw [hh2]; group
  have hφcomm : φg * φh = φh * φg := by
    ext a
    simp only [hφgdef, hφhdef, MulAut.mul_apply, ggConjAut_apply]
    calc g * (h * a * h⁻¹) * g⁻¹ = (g * h) * a * (h⁻¹ * g⁻¹) := by group
      _ = (h * g) * a * (h⁻¹ * g⁻¹) := by rw [hcomm]
      _ = (h * g) * a * (g⁻¹ * h⁻¹) := by
          rw [show h⁻¹ * g⁻¹ = g⁻¹ * h⁻¹ by
            rw [← mul_inv_rev g h, hcomm, mul_inv_rev h g]]
      _ = h * (g * a * g⁻¹) * h⁻¹ := by group
  have hφg1 : φg ≠ 1 := by
    intro h1
    apply hg1
    refine hker g hgK fun a ha => ?_
    have := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : G)) h1
    simpa [hφgdef, ggConjAut_apply] using this
  have hφh1 : φh ≠ 1 := by
    intro h1
    apply hh1
    refine hker h hhK fun a ha => ?_
    have := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : G)) h1
    simpa [hφhdef, ggConjAut_apply] using this
  have hφne : φg ≠ φh := by
    intro h1
    apply hne
    have h2 : (h⁻¹ * g) ∈ Subgroup.closure ({g, h} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hhK) hgK
    have h3 : h⁻¹ * g = 1 := by
      refine hker (h⁻¹ * g) h2 fun a ha => ?_
      have h4 := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : G)) h1
      simp only [hφgdef, hφhdef, ggConjAut_apply] at h4
      calc (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹
          = h⁻¹ * (g * a * g⁻¹) * h := by group
        _ = h⁻¹ * (h * a * h⁻¹) * h := by rw [h4]
        _ = a := by group
    have h5 : g = h := by
      have := congrArg (fun x => h * x) h3
      simpa [mul_assoc, hh2] using this
    exact h5
  have hmemg : φg ∈ ggAutomizer J A := ggConjAut_mem_ggAutomizer hgJ hgN
  have hmemh : φh ∈ ggAutomizer J A := ggConjAut_mem_ggAutomizer hhJ hhN
  have hle : Subgroup.closure ({φg, φh} : Set (MulAut ↥A)) ≤ ggAutomizer J A :=
    (Subgroup.closure_le (ggAutomizer J A)).mpr (by
      rintro φ (rfl | rfl)
      · exact hmemg
      · exact hmemh)
  have hcard : Nat.card (Subgroup.closure ({φg, φh} : Set (MulAut ↥A))) = 4 :=
    natCard_closure_pair_involutions hφg2 hφh2 hφcomm hφg1 hφh1 hφne
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [hcard] at hdvd


theorem four_dvd_ggAutomizer_of_coroot_witnesses
    {G : Type} [Group G] {A J : Subgroup G} {g h d e : G}
    (hgJ : g ∈ J) (hhJ : h ∈ J)
    (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hhN : h ∈ Subgroup.normalizer (A : Set G))
    (hdA : d ∈ A) (heA : e ∈ A)
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hne : g ≠ h)
    (hmoveg : g * d * g⁻¹ ≠ d)
    (hmoveh : h * e * h⁻¹ ≠ e)
    (hfixh : h * d * h⁻¹ = d)
    (hfixg : g * e * g⁻¹ = e)
    (hmovegh : (g * h) * d * (g * h)⁻¹ ≠ d) :
    4 ∣ Nat.card (ggAutomizer J A) := by
  have hker : ∀ x ∈ Subgroup.closure ({g, h} : Set G),
      (∀ a ∈ A, x * a * x⁻¹ = a) → x = 1 := by
    intro x hx hcent
    have hset := closure_pair_eq_four hg2 hh2 hcomm hg1 hh1 hne
    change x ∈ (Subgroup.closure ({g, h} : Set G) : Set G) at hx
    rw [hset] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact absurd (hcent d hdA) hmovegh
    · exact absurd (hcent d hdA) hmoveg
    · exact absurd (hcent e heA) hmoveh
    · rfl
  exact four_dvd_ggAutomizer_of_two_independent_involutions hgJ hhJ hgN hhN
    hg2 hh2 hcomm hg1 hh1 hne hker

theorem exists_primitive_cube_root [CharP L 2] :
    ∃ ζ : Lˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree = 2 := by
    compute_degree!
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L) (by rw [hdeg]; norm_num)
  have hω' : ω ^ 2 + ω + 1 = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_add] using hω
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h] at hω'
    norm_num at hω'
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω'
    have h3 : (3 : L) = 0 := by linear_combination hω'
    have h3ne : (3 : L) ≠ 0 := by
      intro h0
      have hdvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h0
      norm_num at hdvd
    exact h3ne h3
  have hω3 : ω ^ 3 = 1 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω']; ring
    have h2 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [h2] at h1
    linear_combination h1
  refine ⟨Units.mk0 ω hω0, ?_, ?_⟩
  · exact Units.ext hω3
  · intro h
    exact hω1 (congrArg Units.val h)

theorem rootChar_corootTuple {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {ζ : Lˣ}
    (v : Fin τ.rank → ℤ) :
    rootChar (fun j => ζ ^ corootPair α (Pi.single j 1)) v = ζ ^ corootPair α v := by
  rw [rootChar_zpow]
  congr 1
  rw [dotProduct]
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv, CFSG.HardMathSupport.Timmesfeld.RootAut.corootPair_sum hα Finset.univ v
    (fun i => (Pi.single i 1 : Fin τ.rank → ℤ))]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem corootTuple_mem_torus (S : LangSetup τ L p)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) ∈ S.D.torus := by
  have hpq : ((3 : ℕ) : ℤ) ∣ (S.D.q : ℤ) - (-1) := by
    rw [hq]
    norm_num
  have hρα : S.ρ α = (-1 : ℤ) • α := by
    rw [hρ α hα, neg_one_smul]
  exact LangRat.langCorootFactor_mem_torus S hτ (Or.inr rfl) hpq hζ hα hρα

theorem corootTuple_mem_fullThreeTorus (S : LangSetup τ L p)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) ∈ fullThreeTorus S := by
  have hT := corootTuple_mem_torus S hτ hq hρ hα hζ
  refine (mem_fullThreeTorus S).2 ⟨hT, ?_⟩
  rw [rootDiagUnit_pow]
  have hb : (fun j => ζ ^ corootPair α (Pi.single j 1)) ^ 3 = 1 := by
    funext j
    rw [Pi.pow_apply]
    calc (ζ ^ corootPair α (Pi.single j 1)) ^ (3 : ℕ)
        = (ζ ^ corootPair α (Pi.single j 1)) ^ (((3 : ℕ) : ℤ)) := by
          rw [← zpow_natCast]
      _ = ζ ^ (corootPair α (Pi.single j 1) * (((3 : ℕ) : ℤ))) := by
          rw [← zpow_mul]
      _ = ζ ^ ((((3 : ℕ) : ℤ)) * corootPair α (Pi.single j 1)) := by
          rw [mul_comm]
      _ = (ζ ^ (((3 : ℕ) : ℤ))) ^ corootPair α (Pi.single j 1) := by
          rw [zpow_mul]
      _ = 1 := by
          rw [show ζ ^ (((3 : ℕ) : ℤ)) = 1 by
            rw [zpow_natCast]; exact hζ, one_zpow]
  rw [hb, rootDiagUnit_one]

theorem corootPair_self_eq_two {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : corootPair α α = 2 := by
  apply mul_right_cancel₀ (iform_self_pos_of_isRoot hα).ne'
  exact corootPair_mul hα α

theorem corootPair_eq_zero_of_orthogonal {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (horth : iform α β = 0) : corootPair α β = 0 := by
  have h := corootPair_mul hα β
  rw [horth, mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (iform_self_pos_of_isRoot hα).ne'

theorem rootWeylSL2_moves_corootTuple (S : LangSetup τ L p)
    {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    rootSL2 τ L α WSL *
        rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) *
        (rootSL2 τ L α WSL)⁻¹ ≠
      rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) := by
  set b : Fin τ.rank → Lˣ := fun j => ζ ^ corootPair α (Pi.single j 1) with hb
  intro hconj
  have hact := rootWeylSL2_conj_rootDiagUnit S hα b
  rw [hconj] at hact
  have hb_eq : weylTuple (rootReflection α) b = b := CFSG.LieType.Chevalley.rootDiagUnit_injective hact.symm
  have hchar := congrArg (fun c => rootChar c α) hb_eq
  rw [rootChar_weylTuple, rootReflection_inv hα, rootReflection_smul_self hα,
    show rootChar b (-α) = (rootChar b α)⁻¹ by
      rw [show -α = 0 - α by simp, rootChar_sub, rootChar_zero, one_mul],
    rootChar_corootTuple hα] at hchar
  have h2 : corootPair α α = 2 := corootPair_self_eq_two hα
  rw [h2] at hchar
  have h4 : ζ ^ 4 = 1 := by
    have h1 := congrArg (fun x => x * ζ ^ 2) hchar
    have h1' : ζ ^ 2 * ζ ^ 2 = 1 := by simpa [mul_assoc] using h1.symm
    calc ζ ^ 4 = ζ ^ 2 * ζ ^ 2 := by group
      _ = 1 := h1'
  have h1 : ζ = 1 := by
    calc ζ = ζ ^ 4 * (ζ ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hζ, inv_one, mul_one]
  exact hζ1 h1

theorem weylTuple_corootTuple_ne_self
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    {w : WeylGroup τ} (hw : w⁻¹ • α = -α) :
    rootDiagUnit τ (weylTuple w (fun j => ζ ^ corootPair α (Pi.single j 1))) ≠
      rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1)) := by
  set b : Fin τ.rank → Lˣ := fun j => ζ ^ corootPair α (Pi.single j 1) with hb
  intro h
  have hb_eq : weylTuple w b = b := CFSG.LieType.Chevalley.rootDiagUnit_injective h
  have hchar := congrArg (fun c => rootChar c α) hb_eq
  rw [rootChar_weylTuple, hw,
    show rootChar b (-α) = (rootChar b α)⁻¹ by
      rw [show -α = 0 - α by simp, rootChar_sub, rootChar_zero, one_mul]] at hchar
  rw [rootChar_corootTuple hα] at hchar
  rw [corootPair_self_eq_two hα] at hchar
  have h4 : ζ ^ 4 = 1 := by
    have h1 := congrArg (fun x => x * ζ ^ 2) hchar
    have h1' : ζ ^ 2 * ζ ^ 2 = 1 := by simpa [mul_assoc] using h1.symm
    calc ζ ^ 4 = ζ ^ 2 * ζ ^ 2 := by group
      _ = 1 := h1'
  have h1 : ζ = 1 := by
    calc ζ = ζ ^ 4 * (ζ ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hζ, inv_one, mul_one]
  exact hζ1 h1

theorem weylTuple_corootTuple_eq_self_of_orthogonal {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (horth : iform α β = 0) {ζ : Lˣ} :
    weylTuple (rootReflection β) (fun j => ζ ^ corootPair α (Pi.single j 1)) =
      fun j => ζ ^ corootPair α (Pi.single j 1) := by
  set b : Fin τ.rank → Lˣ := fun j => ζ ^ corootPair α (Pi.single j 1) with hb
  funext j
  have hβkill : rootChar b β = 1 := by
    rw [rootChar_corootTuple hα, corootPair_eq_zero_of_orthogonal hα horth, zpow_zero]
  have hchar : rootChar (weylTuple (rootReflection β) b) (Pi.single j 1) =
      rootChar b (Pi.single j 1) := by
    rw [rootChar_weylTuple, rootReflection_inv hβ, rootReflection_smul hβ,
      rootChar_sub, rootChar_zsmul, hβkill, one_zpow, inv_one, mul_one]
  rwa [rootChar_single, rootChar_single] at hchar

theorem rootWeylSL2_pair_action_data (S : LangSetup τ L p) [CharP L 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (horth : iform α β = 0)
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    let nα := rootSL2 τ L α WSL
    let nβ := rootSL2 τ L β WSL
    let d := rootDiagUnit τ (fun j => ζ ^ corootPair α (Pi.single j 1))
    let e := rootDiagUnit τ (fun j => ζ ^ corootPair β (Pi.single j 1))
    nα * nα = 1 ∧ nβ * nβ = 1 ∧ nα * nβ = nβ * nα ∧ nα ≠ 1 ∧ nβ ≠ 1 ∧
      nα ≠ nβ ∧ d ∈ fullThreeTorus S ∧ e ∈ fullThreeTorus S ∧
      nα * d * nα⁻¹ ≠ d ∧ nβ * e * nβ⁻¹ ≠ e ∧
      nβ * d * nβ⁻¹ = d ∧ nα * e * nα⁻¹ = e ∧
      (nα * nβ) * d * (nα * nβ)⁻¹ ≠ d ∧
      (∀ x ∈ Subgroup.closure ({nα, nβ} : Set (ModGL τ L)),
        (∀ t ∈ fullThreeTorus S, x * t * x⁻¹ = t) → x = 1) := by
  intro nα nβ d e
  have hα2 : nα * nα = 1 := rootSL2_WSL_mul_self α
  have hβ2 : nβ * nβ = 1 := rootSL2_WSL_mul_self β
  have hsl : ∀ j, τ.symmetrizer j j = 1 := by
    rcases hτ with rfl | rfl | rfl <;> simp [Tag.symmetrizer]
  have hsum : ¬ IsRoot τ (α + β) ∧ ¬ IsRoot τ (α - β) :=
    CFSG.RankThree.PartOne.KE.not_isRoot_add_sub_of_iform_eq_zero hsl hα hβ horth
  have hcomm : nα * nβ = nβ * nα := by
    have := exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ L hα hβ horth
      hsum.1 hsum.2
    exact this _ ⟨WSL, rfl⟩ _ ⟨WSL, rfl⟩
  have hdA : d ∈ fullThreeTorus S := corootTuple_mem_fullThreeTorus S (by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))) hq hρ hα hζ
  have heA : e ∈ fullThreeTorus S := corootTuple_mem_fullThreeTorus S (by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))) hq hρ hβ hζ
  have hmoveα : nα * d * nα⁻¹ ≠ d := by
    rw [rootWeylSL2_conj_rootDiagUnit S hα]
    exact weylTuple_corootTuple_ne_self hα hζ hζ1 (by
      rw [rootReflection_inv hα, rootReflection_smul_self hα])
  have hmoveβ : nβ * e * nβ⁻¹ ≠ e := by
    rw [rootWeylSL2_conj_rootDiagUnit S hβ]
    exact weylTuple_corootTuple_ne_self hβ hζ hζ1 (by
      rw [rootReflection_inv hβ, rootReflection_smul_self hβ])
  have hfixβ : nβ * d * nβ⁻¹ = d := by
    rw [rootWeylSL2_conj_rootDiagUnit S hβ,
      weylTuple_corootTuple_eq_self_of_orthogonal hα hβ horth]
  have hfixα : nα * e * nα⁻¹ = e := by
    rw [rootWeylSL2_conj_rootDiagUnit S hα,
      weylTuple_corootTuple_eq_self_of_orthogonal hβ hα (by rw [iform_comm]; exact horth)]
  have hprod : (nα * nβ) * d * (nα * nβ)⁻¹ =
      rootDiagUnit τ (weylTuple (rootReflection α * rootReflection β)
        (fun j => ζ ^ corootPair α (Pi.single j 1))) := by
    calc (nα * nβ) * d * (nα * nβ)⁻¹
        = nα * (nβ * d * nβ⁻¹) * nα⁻¹ := by group
      _ = nα * rootDiagUnit τ (weylTuple (rootReflection β)
            (fun j => ζ ^ corootPair α (Pi.single j 1))) * nα⁻¹ := by
          rw [rootWeylSL2_conj_rootDiagUnit S hβ]
      _ = rootDiagUnit τ (weylTuple (rootReflection α)
            (weylTuple (rootReflection β) (fun j => ζ ^ corootPair α (Pi.single j 1)))) := by
          rw [rootWeylSL2_conj_rootDiagUnit S hα]
      _ = rootDiagUnit τ (weylTuple (rootReflection α * rootReflection β)
            (fun j => ζ ^ corootPair α (Pi.single j 1))) := by
          rw [weylTuple_weylTuple]
  have hmoveab : (nα * nβ) * d * (nα * nβ)⁻¹ ≠ d := by
    rw [hprod]
    refine weylTuple_corootTuple_ne_self hα hζ hζ1 ?_
    have h0 : corootPair β α = 0 :=
      corootPair_eq_zero_of_orthogonal hβ (by rw [iform_comm]; exact horth)
    rw [mul_inv_rev, mul_smul, rootReflection_inv hβ, rootReflection_inv hα,
      rootReflection_smul_self hα, smul_neg, rootReflection_smul hβ, h0, zero_smul,
      sub_zero]
  have hα1 : nα ≠ 1 := by
    intro h1
    exact hmoveα (by rw [h1, one_mul, inv_one, mul_one])
  have hβ1 : nβ ≠ 1 := by
    intro h1
    exact hmoveβ (by rw [h1, one_mul, inv_one, mul_one])
  have hne : nα ≠ nβ := by
    intro h1
    exact hmoveα (by rw [h1]; exact hfixβ)
  have hker : ∀ x ∈ Subgroup.closure ({nα, nβ} : Set (ModGL τ L)),
      (∀ t ∈ fullThreeTorus S, x * t * x⁻¹ = t) → x = 1 := by
    intro x hx hcent
    have hset := closure_pair_eq_four hα2 hβ2 hcomm hα1 hβ1 hne
    change x ∈ (Subgroup.closure ({nα, nβ} : Set (ModGL τ L)) : Set (ModGL τ L)) at hx
    rw [hset] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact absurd (hcent d hdA) hmoveab
    · exact absurd (hcent d hdA) hmoveα
    · exact absurd (hcent e heA) hmoveβ
    · rfl
  exact ⟨hα2, hβ2, hcomm, hα1, hβ1, hne, hdA, heA, hmoveα, hmoveβ, hfixβ, hfixα,
    hmoveab, hker⟩


theorem four_dvd_aut_fullThreeTorus_of_weyl_mem
    (S : LangSetup τ L p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (horth : iform α β = 0)
    (hαJ : rootSL2 τ L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hβJ : rootSL2 τ L β WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i) (fullThreeTorus S)) := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  obtain ⟨ζ, hζ, hζ1⟩ := exists_primitive_cube_root (L := L)
  obtain ⟨hα2, hβ2, hcomm, hα1, hβ1, hne, -, -, -, -, -, -, -, hker⟩ :=
    rootWeylSL2_pair_action_data S hτ hq hρ hα hβ horth hζ hζ1
  exact four_dvd_ggAutomizer_of_two_independent_involutions hαJ hβJ
    (rootWeylSL2_mem_normalizer_fullThreeTorus S hα (hρ α hα))
    (rootWeylSL2_mem_normalizer_fullThreeTorus S hβ (hρ β hβ))
    hα2 hβ2 hcomm hα1 hβ1 hne hker


theorem frame_ker_ne_top_of_isSLFrame {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hν : 2 ≤ ν) (hψ : IsSLFrame ψ σ) :
    ψ.ker ≠ ⊤ := by
  intro htop
  have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
  have hmem : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σ _ _)] at hmem
  exact Units.ne_zero ε (pinnedX_injective τ L (σ _ _) hmem)

theorem odd_card_ker_of_frame_of_isSLFrame [CharP L 2] {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} (hker : ψ.ker ≠ ⊤) : Odd (Nat.card ψ.ker) := by
  have hle : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  exact Odd.of_dvd_nat
    (CFSG.RankThree.Classical2.finite_odd_card_center_specialLinearGroup
      (Ω := L) (n := ν) (by omega)).2
    (Subgroup.card_dvd_of_le hle)

theorem exists_unitary_source_perfect_of_frame_of_rho
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hν : 3 ≤ ν) (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → S.ρ (σ x y) = σ (π y) (π x))
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e)
    (hνq : (ν, r ^ e) ≠ (3, 2)) :
    ∃ F' : SL(ν, L) →* SL(ν, L),
      (∀ X, S.D.step (ψ X) = ψ (F' X)) ∧
        Group.IsPerfect (F'.eqLocus (MonoidHom.id _)) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r e
  have hσc : ∀ c, σQ c = c ^ (r ^ e) := by
    intro c
    have h1 : σQ c = iterateFrobenius L r e c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hσc' : ∀ c, σQ c = c ^ (r ^ (e * 1)) := by
    intro c
    rw [Nat.mul_one]
    exact hσc c
  obtain ⟨B, hstd⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_exists_pin
    S (s := 1) hν hψ π (fun x y hxy => hπ x y hxy) hq hσc'
  have hstd1 : ∀ X : SL(ν, L),
      ψ B * S.D.step (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    intro X
    simpa [iterHom_eq_iterate] using hstd X
  have hB : ∀ X : SL(ν, L),
      S.D.step (ψ X) = ψ (B⁻¹ * stdUnitary σQ.toRingHom X * B) := by
    intro X
    calc S.D.step (ψ X)
        = (ψ B)⁻¹ * (ψ B * S.D.step (ψ X) * (ψ B)⁻¹) * ψ B := by group
      _ = (ψ B)⁻¹ * ψ (stdUnitary σQ.toRingHom X) * ψ B := by rw [hstd1 X]
      _ = ψ (B⁻¹ * stdUnitary σQ.toRingHom X * B) := by rw [map_mul, map_mul, map_inv]
  let A : GL (Fin ν) L := Matrix.SpecialLinearGroup.toGL B⁻¹
  let F' : SL(ν, L) →* SL(ν, L) :=
    (CFSG.RankThree.Classical2.conjSLn A).comp (CFSG.RankThree.Classical2.invTransposeSL.comp (Matrix.SpecialLinearGroup.map σQ.toRingHom))
  have hF' : ∀ X, F' X = B⁻¹ * stdUnitary σQ.toRingHom X * B := by
    intro X
    simp only [F', MonoidHom.comp_apply]
    rw [CFSG.RankThree.Classical2.conjSLn_toGL]
    simp [stdUnitary]
  refine ⟨F', ?_, ?_⟩
  · intro X
    rw [hF' X]
    exact hB X
  · have hQ := CFSG.RankThree.Classical2.isQuasisimple_eqLocus_conjSLn_frobenius_unitary
      (k' := k') (Ω := L) (n := ν) (ℓ := r) (f := e) hr he hν hνq σQ.toRingHom hσc A
    simpa [F'] using hQ.2.1

theorem exists_unitary_source_perfect_of_frame
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hν : 3 ≤ ν) (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e)
    (hνq : (ν, r ^ e) ≠ (3, 2)) :
    ∃ F' : SL(ν, L) →* SL(ν, L),
      (∀ X, S.D.step (ψ X) = ψ (F' X)) ∧
        Group.IsPerfect (F'.eqLocus (MonoidHom.id _)) :=
  exists_unitary_source_perfect_of_frame_of_rho S hν hψ π
    (fun x y hxy => by simpa [hs1] using hπ x y hxy) (k' := k') hr he hq hνq

theorem map_eqLocus_le_commutator_of_frame
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    {Ψ : Set (Fin τ.rank → ℤ)} (hψ : IsSLFrame ψ σ) (hsub : frameRoots σ ⊆ Ψ)
    (hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L)) (hodd : Odd (Nat.card ψ.ker))
    (F' : SL(ν, L) →* SL(ν, L)) (hcomm : ∀ X, S.D.step (ψ X) = ψ (F' X))
    (hperf : Group.IsPerfect (F'.eqLocus (MonoidHom.id _)))
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L (frameRoots σ))
    (hgfix : S.D.step g = g) (hg2 : g ^ 2 = 1) :
    g ∈ ⁅rootSpan τ L Ψ ⊓ S.Γ, rootSpan τ L Ψ ⊓ S.Γ⁆ := by
  classical
  have hgRange : g ∈ ψ.range := by rw [hψ.range]; exact hg
  obtain ⟨y, hyψ, hy2⟩ := CFSG.Alternating.Multipliers.exists_lift_sq_eq_one hkercenter hodd
    hgRange hg2
  have hyΦ : F' y = y := by
    refine CFSG.Alternating.Multipliers.eq_of_sq_eq_one hkercenter hodd ?_ ?_ ?_
    · rw [← hcomm y]
      simpa [hyψ] using hgfix
    · rw [← map_pow, hy2, map_one]
    · exact hy2
  set C : Subgroup (SL(ν, L)) := F'.eqLocus (MonoidHom.id _) with hC
  have hyC : y ∈ C := hyΦ
  have hCmodel : ∀ c : C, ψ (c : SL(ν, L)) ∈ S.D.model := by
    intro c
    have h1 : ψ (c : SL(ν, L)) ∈ adjointGroup τ L :=
      hψ.range_le_adjointGroup ⟨c, rfl⟩
    have h2 : S.D.n * S.D.Φ (ψ (c : SL(ν, L))) * S.D.n⁻¹ = ψ (c : SL(ν, L)) := by
      change S.D.step (ψ (c : SL(ν, L))) = ψ (c : SL(ν, L))
      rw [hcomm]
      exact congrArg ψ c.2
    exact S.D.mem_model.mpr ⟨h1, h2⟩
  have hCΓ : ∀ c : C, ψ (c : SL(ν, L)) ∈ S.Γ :=
    map_mem_commutator_of_perfect hperf (ψ.comp C.subtype) S.D.model hCmodel
  have hCspan : ∀ c : C, ψ (c : SL(ν, L)) ∈ rootSpan τ L Ψ := by
    intro c
    refine rootSpan_mono (S := frameRoots σ) hsub ?_
    rw [← hψ.range]
    exact ⟨c, rfl⟩
  have hCrat : ∀ c : C, ψ (c : SL(ν, L)) ∈ rootSpan τ L Ψ ⊓ S.Γ := fun c =>
    Subgroup.mem_inf.2 ⟨hCspan c, hCΓ c⟩
  have hgmem : ψ y ∈ ⁅rootSpan τ L Ψ ⊓ S.Γ, rootSpan τ L Ψ ⊓ S.Γ⁆ :=
    map_mem_commutator_of_perfect hperf (ψ.comp C.subtype)
      (rootSpan τ L Ψ ⊓ S.Γ) hCrat ⟨y, hyC⟩
  simpa [MonoidHom.comp_apply, hyψ] using hgmem

theorem map_eqLocus_le_rationalComponent_of_frame
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hψ : IsSLFrame ψ σ) (hsub : frameRoots σ ⊆ componentRoots (rootCharHom a) i)
    (hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L)) (hodd : Odd (Nat.card ψ.ker))
    (F' : SL(ν, L) →* SL(ν, L)) (hcomm : ∀ X, S.D.step (ψ X) = ψ (F' X))
    (hperf : Group.IsPerfect (F'.eqLocus (MonoidHom.id _)))
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L (frameRoots σ))
    (hgfix : S.D.step g = g) (hg2 : g ^ 2 = 1) :
    g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
  map_eqLocus_le_commutator_of_frame S (Ψ := rationalRoots S.ρ (rootCharHom a) i) hψ
    (fun γ hγ => ⟨0, γ, hsub hγ, by simp⟩) hkercenter hodd F' hcomm hperf hg hgfix hg2

theorem exists_A_frame_and_weyl_mem
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hd3 : rootDiagUnit τ a ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ),
      4 ≤ ν ∧ IsSLFrame ψ σ ∧
        (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ ∧
        ∀ γ ∈ frameRoots σ,
          rootSL2 τ L γ WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hpL : (3 : L) ≠ 0 := by
    have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have h3L : (3 : L) = 1 := by
      have h3 : (3 : L) = (2 : L) + 1 := by norm_num
      rw [h3, h2L, zero_add]
    rw [h3L]
    exact one_ne_zero
  obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨeq⟩ : ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L)
      (σ : Fin ν → Fin ν → Fin τ.rank → ℤ), 3 ≤ ν ∧ IsSLFrame ψ σ ∧
      (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
      componentRoots (rootCharHom a) i = frameRoots σ := by
    rcases hτ with rfl | rfl | rfl
    · exact exists_frame_of_typeA_E6_T_of_prime S Nat.prime_three hpL hd3 i h2 hn
    · exact exists_frame_of_typeA_E7_T_of_prime S Nat.prime_three hpL hd3 i h2 hn
    · exact exists_frame_of_typeA_E8_T_of_prime S Nat.prime_three hpL hd3 i h2 hn
  have hν4 : 4 ≤ ν := by
    rcases Nat.eq_or_lt_of_le hν with h3' | h4
    · subst h3'
      have himg : frameRoots σ = (fun p : Fin 3 × Fin 3 => σ p.1 p.2) ''
          ((Finset.univ : Finset (Fin 3)).offDiag : Set (Fin 3 × Fin 3)) := by
        ext r
        constructor
        · rintro ⟨i, j, hij, rfl⟩
          exact ⟨(i, j), by simp [hij], rfl⟩
        · rintro ⟨⟨i, j⟩, hp, rfl⟩
          simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.coe_univ, Set.mem_univ,
            true_and] at hp
          exact ⟨i, j, hp, rfl⟩
      have h6 : (frameRoots σ).ncard ≤ 6 := by
        rw [himg]
        calc ((fun p : Fin 3 × Fin 3 => σ p.1 p.2) ''
              ((Finset.univ : Finset (Fin 3)).offDiag : Set (Fin 3 × Fin 3))).ncard
            ≤ ((Finset.univ : Finset (Fin 3)).offDiag : Set (Fin 3 × Fin 3)).ncard :=
              Set.ncard_image_le
          _ = 6 := by
              rw [Set.ncard_coe_finset, Finset.offDiag_card]
              decide
      rw [← hΨeq, hn] at h6
      have h12 : 12 ≤ compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := by nlinarith
      omega
    · omega
  have hker : ψ.ker ≠ ⊤ := frame_ker_ne_top_of_isSLFrame (by omega) hψ
  have hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) := odd_card_ker_of_frame_of_isSLFrame hν hker
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hstable : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hρ γ hγ.1.1]
    exact hΨ.neg_mem γ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hstable
  have hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ y x := by
    intro x y hxy
    rw [hs1, Function.iterate_one, hρ _ (hψ.isRoot x y hxy), hψ.neg x y]
  obtain ⟨K, hKfield, hKfin, hKalg, hKcard⟩ := S.exists_fixedField
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : Algebra K L := hKalg
  have hKclos : IsAlgClosure K L := ⟨inferInstance, ⟨fun c => by
    obtain ⟨n, hnpos, hc⟩ := hAlg c
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X, ?_, ?_⟩
    · have hq1 : 1 < S.D.q ^ n := Nat.one_lt_pow hnpos.ne' S.hqpow.1.one_lt
      exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hc, sub_self]⟩⟩
  letI : IsAlgClosure K L := hKclos
  obtain ⟨F', hcomm, hperf⟩ := exists_unitary_source_perfect_of_frame S i hν hψ 1 hπ hs1
    (k' := K) (r := 2) (e := 1) Nat.prime_two (by norm_num) (by rw [hq]; norm_num) (by
      intro hconj
      have hfst : ν = 3 := by simpa using congrArg Prod.fst hconj
      omega)
  refine ⟨ν, ψ, σ, hν4, hψ, hnorm, hΨeq, ?_⟩
  intro γ hγ
  have hγroot : IsRoot τ γ := hψ.frameRoots_isRoot γ hγ
  have hgframe : rootSL2 τ L γ WSL ∈ rootSpan τ L (frameRoots σ) := by
    refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hγroot WSL)
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hγ
    · obtain ⟨j, k, hjk, rfl⟩ := hγ
      exact ⟨k, j, hjk.symm, (hψ.neg j k).symm⟩
  have hmodel : rootSL2 τ L γ WSL ∈ S.D.model :=
    rootSL2_WSL_mem_model_of_rho S hγroot (Or.inr (hρ γ hγroot))
  have hgfix : S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ WSL :=
    (S.D.mem_model.1 hmodel).2
  have hg2 : rootSL2 τ L γ WSL ^ 2 = 1 := by
    rw [pow_two]
    exact rootSL2_WSL_mul_self γ
  exact map_eqLocus_le_rationalComponent_of_frame S i hψ
    (by intro γ hγ; rw [hΨeq]; exact hγ) hkercenter hodd F' hcomm hperf hgframe hgfix hg2

theorem exists_orthogonal_weyl_pair_of_subframe
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hν4 : 4 ≤ ν) (hψ : IsSLFrame ψ σ)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1)
    (hsub : frameRoots σ ⊆ componentRoots (rootCharHom a) i) :
    ∃ α β : Fin τ.rank → ℤ,
      α ∈ componentRoots (rootCharHom a) i ∧ β ∈ componentRoots (rootCharHom a) i ∧
      iform α β = 0 ∧
      rootSL2 τ L α WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      rootSL2 τ L β WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  have hν : 3 ≤ ν := by omega
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hker : ψ.ker ≠ ⊤ := frame_ker_ne_top_of_isSLFrame (by omega) hψ
  have hkercenter : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker (fun Y => ?_)
    rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
  have hodd : Odd (Nat.card ψ.ker) := odd_card_ker_of_frame_of_isSLFrame hν hker
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hstable : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hρ γ hγ.1.1]
    exact hΨ.neg_mem γ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hstable
  have hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ y x := by
    intro x y hxy
    rw [hs1, Function.iterate_one, hρ _ (hψ.isRoot x y hxy), hψ.neg x y]
  obtain ⟨K, hKfield, hKfin, hKalg, hKcard⟩ := S.exists_fixedField
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : Algebra K L := hKalg
  have hKclos : IsAlgClosure K L := ⟨inferInstance, ⟨fun c => by
    obtain ⟨n, hnpos, hc⟩ := hAlg c
    refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X, ?_, ?_⟩
    · have hq1 : 1 < S.D.q ^ n := Nat.one_lt_pow hnpos.ne' S.hqpow.1.one_lt
      exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hc, sub_self]⟩⟩
  letI : IsAlgClosure K L := hKclos
  obtain ⟨F', hcomm, hperf⟩ := exists_unitary_source_perfect_of_frame S i hν hψ 1 hπ hs1
    (k' := K) (r := 2) (e := 1) Nat.prime_two (by norm_num) (by rw [hq]; norm_num) (by
      intro hconj
      have hfst : ν = 3 := by simpa using congrArg Prod.fst hconj
      omega)
  have hmem : ∀ γ ∈ frameRoots σ,
      rootSL2 τ L γ WSL ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro γ hγ
    have hγroot : IsRoot τ γ := hψ.frameRoots_isRoot γ hγ
    have hgframe : rootSL2 τ L γ WSL ∈ rootSpan τ L (frameRoots σ) := by
      refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) hγroot WSL)
      intro δ hδ
      rcases hδ with rfl | rfl
      · exact hγ
      · obtain ⟨j, k, hjk, rfl⟩ := hγ
        exact ⟨k, j, hjk.symm, (hψ.neg j k).symm⟩
    have hmodel : rootSL2 τ L γ WSL ∈ S.D.model :=
      rootSL2_WSL_mem_model_of_rho S hγroot (Or.inr (hρ γ hγroot))
    have hgfix : S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L γ WSL :=
      (S.D.mem_model.1 hmodel).2
    have hg2 : rootSL2 τ L γ WSL ^ 2 = 1 := by
      rw [pow_two]
      exact rootSL2_WSL_mul_self γ
    exact map_eqLocus_le_rationalComponent_of_frame S i hψ hsub hkercenter hodd F' hcomm hperf
      hgframe hgfix hg2
  let i0 : Fin ν := ⟨0, by omega⟩
  let i1 : Fin ν := ⟨1, by omega⟩
  let i2 : Fin ν := ⟨2, by omega⟩
  let i3 : Fin ν := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have h23 : i2 ≠ i3 := by
    intro h; have := congrArg Fin.val h; simp [i2, i3] at this
  have hα : IsRoot τ (σ i0 i1) := hψ.isRoot i0 i1 h01
  have hβ : IsRoot τ (σ i2 i3) := hψ.isRoot i2 i3 h23
  have hαmem : rootSL2 τ L (σ i0 i1) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hmem (σ i0 i1) ⟨i0, i1, h01, rfl⟩
  have hβmem : rootSL2 τ L (σ i2 i3) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hmem (σ i2 i3) ⟨i2, i3, h23, rfl⟩
  have hff : framePairForm i0 i1 i2 i3 = 0 := by
    simp [framePairForm, i0, i1, i2, i3]
  have horth : iform (σ i0 i1) (σ i2 i3) = 0 := by
    have h := hψ.iform_eq hnorm i0 i1 i2 i3
    rw [hff, mul_zero] at h
    exact h
  exact ⟨σ i0 i1, σ i2 i3, hsub ⟨i0, i1, h01, rfl⟩,
    hsub ⟨i2, i3, h23, rfl⟩, horth, hαmem, hβmem⟩

theorem four_dvd_aut_of_subframe
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hν4 : 4 ≤ ν) (hψ : IsSLFrame ψ σ)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1)
    (hsub : frameRoots σ ⊆ componentRoots (rootCharHom a) i) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fullThreeTorus S)) := by
  obtain ⟨α, β, hα, hβ, horth, hαmem, hβmem⟩ :=
    exists_orthogonal_weyl_pair_of_subframe S hτ hq hAlg hρ i hν4 hψ hnorm hsub
  exact four_dvd_aut_fullThreeTorus_of_weyl_mem S hτ hq hρ i hα.1.1 hβ.1.1 horth hαmem hβmem

theorem four_dvd_aut_of_A_component
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hd3 : rootDiagUnit τ a ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fullThreeTorus S)) := by
  obtain ⟨ν, ψ, σ, hν4, hψ, hnorm, hΨeq, hmem⟩ :=
    exists_A_frame_and_weyl_mem S hτ hq hAlg hρ hd3 i h2 h3 hn
  let i0 : Fin ν := ⟨0, by omega⟩
  let i1 : Fin ν := ⟨1, by omega⟩
  let i2 : Fin ν := ⟨2, by omega⟩
  let i3 : Fin ν := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have h23 : i2 ≠ i3 := by
    intro h; have := congrArg Fin.val h; simp [i2, i3] at this
  have hα : IsRoot τ (σ i0 i1) := hψ.isRoot i0 i1 h01
  have hβ : IsRoot τ (σ i2 i3) := hψ.isRoot i2 i3 h23
  have hαmem : rootSL2 τ L (σ i0 i1) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hmem (σ i0 i1) ⟨i0, i1, h01, rfl⟩
  have hβmem : rootSL2 τ L (σ i2 i3) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hmem (σ i2 i3) ⟨i2, i3, h23, rfl⟩
  have hff : framePairForm i0 i1 i2 i3 = 0 := by
    simp [framePairForm, i0, i1, i2, i3]
  have horth : iform (σ i0 i1) (σ i2 i3) = 0 := by
    have h := hψ.iform_eq hnorm i0 i1 i2 i3
    rw [hff, mul_zero] at h
    exact h
  exact four_dvd_aut_fullThreeTorus_of_weyl_mem S hτ hq hρ (a := a) i hα hβ horth hαmem hβmem


theorem iform_simpleRoots_eq_zero_or_eq_neg_one_of_simplyLaced
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) (hγ : γ ∈ simpleRoots Ψ) (hne : β ≠ γ) :
    iform β γ = 0 ∨ iform β γ = -1 := by
  have hle := iform_simpleRoots_nonpos hΨ hβ hγ hne
  have hnorm : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ x → iform x x = 2 := fun hx => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hx
  have hsum : β + γ ≠ 0 := by
    intro h0
    have h1 := simpleRoots_height_pos hβ
    have h2 := simpleRoots_height_pos hγ
    have h3 := height_add β γ
    have h00 : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    rw [h0, h00] at h3
    omega
  have hpos := iform_self_pos hsum
  rw [iform_add_left, iform_add_right, iform_add_right, hnorm (simpleRoots_isRoot hβ),
    hnorm (simpleRoots_isRoot hγ), iform_comm γ β] at hpos
  omega

theorem exists_dynkinType_of_simplyLaced
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty) :
    ∃ (t : TauCeti.DynkinType) (e : simpleRoots Ψ ≃ Fin t.rank),
      t.Valid ∧ t.IsSimplyLaced ∧
        (∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ)) ∧
        (simpleRoots Ψ).card = t.rank := by
  classical
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (diagramGraph_simpleRoots_connected hΨ hne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hiform : ∀ β γ : simpleRoots Ψ, iform (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    rw [← he' β γ, corootPair_eq_iform_of_simplyLaced hτ (simpleRoots_isRoot β.2)]
  have hsl : t.cartanMatrix.IsSimplyLaced := by
    intro i j hij
    have hne' : ((e.symm i : simpleRoots Ψ) : Fin τ.rank → ℤ) ≠ (e.symm j : simpleRoots Ψ) :=
      fun h => hij (e.symm.injective (Subtype.ext h))
    have h := iform_simpleRoots_eq_zero_or_eq_neg_one_of_simplyLaced hτ hΨ
      (e.symm i).2 (e.symm j).2 hne'
    rw [hiform, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h
  have hcard : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  exact ⟨t, e, ht, (TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff_of_valid ht).1 hsl,
    hiform, hcard⟩

theorem exists_chain3_simpleRoots
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    (h3 : 3 ≤ compRank Ψ) :
    ∃ α β γ : Fin τ.rank → ℤ,
      α ∈ simpleRoots Ψ ∧ β ∈ simpleRoots Ψ ∧ γ ∈ simpleRoots Ψ ∧
        iform α β = -1 ∧ iform β γ = -1 ∧ iform α γ = 0 := by
  classical
  obtain ⟨t, e, ht, hsl, hcart, hcard⟩ := exists_dynkinType_of_simplyLaced hτ hΨ hne
  have hcomp := CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ
  have hrank3 : 3 ≤ t.rank := by omega
  haveI : Nontrivial (Fin t.rank) := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    intro h; have := congrArg Fin.val h; simp at this
  have hFT : TauCeti.IsFiniteType t.cartanMatrix := by
    cases t with
    | A n =>
      convert TauCeti.isFiniteType_cartanMatrix_A n using 1 <;>
        simp [TauCeti.DynkinType.rank_A, TauCeti.DynkinType.cartanMatrix_A]
    | B n =>
      convert TauCeti.isFiniteType_cartanMatrix_B n using 1 <;>
        simp [TauCeti.DynkinType.rank_B, TauCeti.DynkinType.cartanMatrix_B]
    | C n =>
      convert TauCeti.isFiniteType_cartanMatrix_C n using 1 <;>
        simp [TauCeti.DynkinType.rank_C, TauCeti.DynkinType.cartanMatrix_C]
    | D n =>
      convert TauCeti.isFiniteType_cartanMatrix_D n using 1 <;>
        simp [TauCeti.DynkinType.rank_D, TauCeti.DynkinType.cartanMatrix_D]
    | E6 =>
      convert TauCeti.DynkinType.isFiniteType_cartanMatrix_E6 using 1 <;>
        simp [TauCeti.DynkinType.rank_E6, TauCeti.DynkinType.cartanMatrix_E6]
    | E7 =>
      convert TauCeti.DynkinType.isFiniteType_cartanMatrix_E7 using 1 <;>
        simp [TauCeti.DynkinType.rank_E7, TauCeti.DynkinType.cartanMatrix_E7]
    | E8 =>
      convert TauCeti.DynkinType.isFiniteType_cartanMatrix_E8 using 1 <;>
        simp [TauCeti.DynkinType.rank_E8, TauCeti.DynkinType.cartanMatrix_E8]
    | F4 =>
      convert TauCeti.DynkinType.isFiniteType_cartanMatrix_F4 using 1 <;>
        simp [TauCeti.DynkinType.rank_F4, TauCeti.DynkinType.cartanMatrix_F4]
    | G2 =>
      convert TauCeti.DynkinType.isFiniteType_cartanMatrix_G2 using 1 <;>
        simp [TauCeti.DynkinType.rank_G2, TauCeti.DynkinType.cartanMatrix_G2]
  let G : SimpleGraph (Fin t.rank) := TauCeti.diagramGraph t.cartanMatrix
  have hconn : G.Connected := TauCeti.DynkinType.connected_diagramGraph_cartanMatrix ht
  have htree : G.IsTree := TauCeti.IsFiniteType.isTree_diagramGraph hFT hconn
  obtain ⟨v, hvdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
  obtain ⟨u, huv, huuniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1 hvdeg
  have h2rank : 2 < t.rank := by omega
  obtain ⟨w, hwv, hwu⟩ := Fin.exists_ne_and_ne_of_two_lt v u h2rank
  have hxy : v ≠ w := hwv.symm
  have hnxy : ¬G.Adj v w := fun h => hwu (huuniq w h)

  have hreach : G.Reachable v w := hconn v w
  have hdist : 1 < G.dist v w := hreach.one_lt_dist_of_ne_of_not_adj hxy hnxy
  obtain ⟨walk, hwalk⟩ := SimpleGraph.exists_walk_of_dist_ne_zero (by omega : G.dist v w ≠ 0)
  obtain ⟨a, b, c, hab, hbc, hac, habc⟩ :=
    SimpleGraph.Walk.exists_adj_adj_not_adj_ne hwalk hdist
  have hsl' : t.cartanMatrix.IsSimplyLaced :=
    (TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff_of_valid ht).2 hsl
  have hsym : t.cartanMatrix.IsSymm :=
    TauCeti.DynkinType.cartanMatrix_isSymm_of_isSimplyLaced hsl'
  have hoff : ∀ {i j : Fin t.rank}, i ≠ j → t.cartanMatrix i j ≠ 0 →
      t.cartanMatrix i j = -1 := by
    intro i j hij hne0
    have hle : t.cartanMatrix i j ≤ 0 := TauCeti.DynkinType.cartanMatrix_apply_le_zero_of_ne t hij
    have hprod : t.cartanMatrix i j * t.cartanMatrix j i ≤ 1 :=
      (TauCeti.IsFiniteType.isSimplyLaced_iff hFT).1 hsl' i j hij
    rw [hsym.apply i j] at hprod
    have hsquare : (t.cartanMatrix i j) ^ 2 ≤ 1 := by simpa [pow_two] using hprod
    have hlt : t.cartanMatrix i j < 0 := lt_of_le_of_ne hle hne0
    have : -1 ≤ t.cartanMatrix i j := by nlinarith
    omega
  have hab' : t.cartanMatrix a b = -1 := by
    rw [TauCeti.diagramGraph_adj] at hab
    exact hoff hab.1 hab.2.1
  have hbc' : t.cartanMatrix b c = -1 := by
    rw [TauCeti.diagramGraph_adj] at hbc
    exact hoff hbc.1 hbc.2.1
  have hac0 : t.cartanMatrix a c = 0 := by
    by_contra hne0
    apply hac
    rw [TauCeti.diagramGraph_adj]
    exact ⟨habc, hne0, by rwa [hsym.apply]⟩
  refine ⟨(e.symm a : simpleRoots Ψ), (e.symm b : simpleRoots Ψ), (e.symm c : simpleRoots Ψ),
    (e.symm a).2, (e.symm b).2, (e.symm c).2, ?_, ?_, ?_⟩
  · have h1 : iform ((e.symm a : simpleRoots Ψ) : Fin τ.rank → ℤ)
        ((e.symm b : simpleRoots Ψ) : Fin τ.rank → ℤ) = t.cartanMatrix a b := by
      simpa only [Equiv.apply_symm_apply] using hcart (e.symm a) (e.symm b)
    exact h1.trans hab'
  · have h1 : iform ((e.symm b : simpleRoots Ψ) : Fin τ.rank → ℤ)
        ((e.symm c : simpleRoots Ψ) : Fin τ.rank → ℤ) = t.cartanMatrix b c := by
      simpa only [Equiv.apply_symm_apply] using hcart (e.symm b) (e.symm c)
    exact h1.trans hbc'
  · have h1 : iform ((e.symm a : simpleRoots Ψ) : Fin τ.rank → ℤ)
        ((e.symm c : simpleRoots Ψ) : Fin τ.rank → ℤ) = t.cartanMatrix a c := by
      simpa only [Equiv.apply_symm_apply] using hcart (e.symm a) (e.symm c)
    exact h1.trans hac0


public def chain3OK (E : List (ℕ × ℕ)) (c : List ℕ) : Bool :=
  c.any fun x => c.any fun y => c.any fun z =>
    decide (x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ (x, y) ∈ E ∧ (y, z) ∈ E ∧ (x, z) ∉ E)

theorem chain3OK_spec {E : List (ℕ × ℕ)} {c : List ℕ} (h : chain3OK E c = true) :
    ∃ x ∈ c, ∃ y ∈ c, ∃ z ∈ c, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      (x, y) ∈ E ∧ (y, z) ∈ E ∧ (x, z) ∉ E := by
  simp only [chain3OK, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨y, hy, hy'⟩ := hx'
  obtain ⟨z, hz, hz'⟩ := hy'
  exact ⟨x, hx, y, hy, z, hz, hz'.1, hz'.2.1, hz'.2.2.1,
    hz'.2.2.2.1, hz'.2.2.2.2.1, hz'.2.2.2.2.2⟩

theorem a2_adj_iform {L : Type} [Field L] {τ : Tag} {ρ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) :
    iform (σ 0 1) (σ 1 2) = -1 := by
  have h01 : IsRoot τ (σ 0 1) := h.isRoot 0 1 (by decide)
  have h12 : IsRoot τ (σ 1 2) := h.isRoot 1 2 (by decide)
  have h02 : IsRoot τ (σ 0 2) := h.isRoot 0 2 (by decide)
  have hadd : σ 0 1 + σ 1 2 = σ 0 2 := h.add 0 1 2
  have hnorm : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ x → iform x x = 2 := fun hx => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hx
  have h1 : iform (σ 0 1) (σ 0 1) = 2 := hnorm h01
  have h2 : iform (σ 1 2) (σ 1 2) = 2 := hnorm h12
  have h3 : iform (σ 0 2) (σ 0 2) = 2 := hnorm h02
  have h4 : iform (σ 0 1 + σ 1 2) (σ 0 1 + σ 1 2) = 2 := by rw [hadd, h3]
  rw [iform_add_left, iform_add_right, iform_add_right, h1, h2, iform_comm (σ 1 2) (σ 0 1)] at h4
  linarith

section E6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
  (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup Tag.E6 L p)

def kacCheck (n : ℕ) (tp : ℕ → ℕ → List ℕ) (cands : List (List ℕ)) : Prop :=
  ((List.range n).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => cands.any (sameSet (compIdx n tp zl x))) = true

theorem exists_A3_subframe_of_kac
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hq : S.D.q = 2)
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts)
    {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ} {cands : List (List ℕ)}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hAdj : ∀ x y, K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    (hCheck : kacCheck (τ.rank + 1) tp cands)
    (hLt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hCard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    (hChain : ∀ c ∈ cands, 3 ≤ c.length → chain3OK E c = true)
    (hFrames : ∀ x y, (nodeIdx x, nodeIdx y) ∈ E →
      ∃ (ρ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧ σ 1 2 = K.extRoot y)
    {a : Fin τ.rank → Lˣ} (hd3 : rootDiagUnit τ a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (ψ : SL(4, L) →* ModGL τ L) (σ : Fin 4 → Fin 4 → Fin τ.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
      frameRoots σ ⊆ componentRoots (rootCharHom a) i := by

  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  have ha : ∀ j, a j ^ 3 = 1 := by
    have h1 : rootDiagUnit τ (a ^ 3) = 1 := by
      rw [← rootDiagUnit_pow]
      exact hd3
    have h2 : a ^ 3 = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective
      simpa [rootDiagUnit_one] using h1
    exact fun j => congrFun h2 j
  obtain ⟨ζ, hζpow, hζne⟩ := exists_primitive_cube_root (L := L)
  have hζprim : IsPrimitiveRoot (ζ : L) 3 := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_eq_prime_iff]
    exact ⟨by simpa using congrArg Units.val hζpow, by simpa using hζne⟩
  obtain ⟨v, μ, hμ, hall⟩ := K.exists_smul_rootsOf hK (by norm_num : 0 < 3) hζprim a ha
  obtain ⟨x0, hx0, hi0⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := K.exists_comp_eq_of_check hT hAdj
    (adm := fun _ => true) hCheck rfl hx0
  set C : Finset (Option (Fin τ.rank)) := (c.map (idxNode (r := τ.rank))).toFinset with hCdef
  have hCset : K.comp 3 μ x0 = (C : Set (Option (Fin τ.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      have hwlt : w < τ.rank + 1 := hLt c hc w hw
      simpa [nodeIdx_idxNode (r := τ.rank) hwlt] using hw
  have hi' : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (C : Set (Option (Fin τ.rank))) := by
    rw [hi0, hCset]
  have hCp : ∃ y, y ∉ (C : Set (Option (Fin τ.rank))) := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp K (by norm_num : 0 < 3) μ x0
    exact ⟨y, by rwa [hCset] at hy⟩
  have hCpF : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := hCp
    exact ⟨y, hy⟩
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image v]
    have hcr := compRank_rootsOf K hK hCpF
    rw [hcr]
    exact hCard c hc
  have hlen : 3 ≤ c.length := by rw [← hrank]; exact h3
  obtain ⟨x, hx, y, hy, z, hz, hxyne, hyzne, hxzne, hxyE, hyzE, hxzE⟩ :=
    chain3OK_spec (hChain c hc hlen)
  have hxlt : x < τ.rank + 1 := hLt c hc x hx
  have hylt : y < τ.rank + 1 := hLt c hc y hy
  have hzlt : z < τ.rank + 1 := hLt c hc z hz
  let l : Fin 3 → Option (Fin τ.rank) := ![idxNode x, idxNode y, idxNode z]
  have hidx_inj : ∀ {u v : ℕ}, u < τ.rank + 1 → v < τ.rank + 1 → idxNode (r := τ.rank) u = idxNode v → u = v := by
    intro u v hu hv h
    have := congrArg nodeIdx h
    rwa [nodeIdx_idxNode hu, nodeIdx_idxNode hv] at this
  have hl : Function.Injective l := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [l] at hab ⊢
    · exact (hxyne (hidx_inj (u := x) (v := y) hxlt hylt hab)).elim
    · exact (hxzne (hidx_inj (u := x) (v := z) hxlt hzlt hab)).elim
    · exact (hxyne (hidx_inj (u := y) (v := x) hylt hxlt hab).symm).elim
    · exact (hyzne (hidx_inj (u := y) (v := z) hylt hzlt hab)).elim
    · exact (hxzne (hidx_inj (u := z) (v := x) hzlt hxlt hab).symm).elim
    · exact (hyzne (hidx_inj (u := z) (v := y) hzlt hylt hab).symm).elim
  have adj_form : ∀ {u v : ℕ}, u < τ.rank + 1 → v < τ.rank + 1 → (u, v) ∈ E →
      iform (K.extRoot (idxNode (r := τ.rank) u)) (K.extRoot (idxNode (r := τ.rank) v)) = -1 := by
    intro u v hu hv huv
    have huv' : (nodeIdx (r := τ.rank) (idxNode (r := τ.rank) u), nodeIdx (r := τ.rank) (idxNode (r := τ.rank) v)) ∈ E := by
      simpa [nodeIdx_idxNode (r := τ.rank) hu, nodeIdx_idxNode (r := τ.rank) hv] using huv
    obtain ⟨ρ, σ, hfr, h01, h12⟩ := hFrames (idxNode (r := τ.rank) u) (idxNode (r := τ.rank) v) huv'
    have := a2_adj_iform (hτ) hfr
    simpa [h01, h12] using this
  have nonadj_form : ∀ {u v : ℕ}, u < τ.rank + 1 → v < τ.rank + 1 → u ≠ v → (u, v) ∉ E →
      iform (K.extRoot (idxNode (r := τ.rank) u)) (K.extRoot (idxNode (r := τ.rank) v)) = 0 := by
    intro u v hu hv huv huvE
    by_contra hne
    apply huvE
    have hAdj' : K.Adj (idxNode u) (idxNode v) := by
      refine ⟨?_, hne⟩
      intro h
      exact huv (hidx_inj (u := u) (v := v) hu hv h)
    have hE := (hAdj (idxNode u) (idxNode v)).1 hAdj'
    rwa [nodeIdx_idxNode (r := τ.rank) hu, nodeIdx_idxNode (r := τ.rank) hv] at hE
  have node_comm : ∀ u v : ℕ, iform (K.extRoot (idxNode (r := τ.rank) u)) (K.extRoot (idxNode (r := τ.rank) v)) =
      iform (K.extRoot (idxNode (r := τ.rank) v)) (K.extRoot (idxNode (r := τ.rank) u)) := by
    intro u v; rw [iform_comm]
  have edge_symm : ∀ {u v : ℕ}, u < τ.rank + 1 → v < τ.rank + 1 → (u, v) ∈ E → (v, u) ∈ E := by
    intro u v hu hv huv
    have hAdj' : K.Adj (idxNode u) (idxNode v) := by
      have hE : (nodeIdx (r := τ.rank) (idxNode (r := τ.rank) u), nodeIdx (r := τ.rank) (idxNode (r := τ.rank) v)) ∈ E := by
        simpa [nodeIdx_idxNode (r := τ.rank) hu, nodeIdx_idxNode (r := τ.rank) hv] using huv
      exact (hAdj (idxNode u) (idxNode v)).2 hE
    have hE := (hAdj (idxNode v) (idxNode u)).1 (K.adj_symm hAdj')
    rwa [nodeIdx_idxNode (r := τ.rank) hv, nodeIdx_idxNode (r := τ.rank) hu] at hE
  have nonedge_symm : ∀ {u v : ℕ}, u < τ.rank + 1 → v < τ.rank + 1 → (u, v) ∉ E → (v, u) ∉ E := by
    intro u v hu hv huv hvu
    apply huv
    have hE : (nodeIdx (r := τ.rank) (idxNode (r := τ.rank) v), nodeIdx (r := τ.rank) (idxNode (r := τ.rank) u)) ∈ E := by
      simpa [nodeIdx_idxNode (r := τ.rank) hv, nodeIdx_idxNode (r := τ.rank) hu] using hvu
    have hAdj' : K.Adj (idxNode v) (idxNode u) := (hAdj (idxNode v) (idxNode u)).2 hE
    have hE' := (hAdj (idxNode u) (idxNode v)).1 (K.adj_symm hAdj')
    rwa [nodeIdx_idxNode (r := τ.rank) hu, nodeIdx_idxNode (r := τ.rank) hv] at hE'
  have hnorm : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ x → iform x x = 2 := fun hx => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self (hτ) hx
  have hG : ∀ a b, iform (K.extRoot (l a)) (K.extRoot (l b)) = chainGram a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp only [l, chainGram]
    · exact hnorm (K.isRoot_extRoot _)
    · exact adj_form hxlt hylt hxyE
    · exact nonadj_form hxlt hzlt hxzne hxzE
    · exact adj_form hylt hxlt (edge_symm hxlt hylt hxyE)
    · exact hnorm (K.isRoot_extRoot _)
    · exact adj_form hylt hzlt hyzE
    · exact nonadj_form hzlt hxlt hxzne.symm (nonedge_symm hxlt hzlt hxzE)
    · exact adj_form hzlt hylt (edge_symm hylt hzlt hyzE)
    · exact hnorm (K.isRoot_extRoot _)
  have hA2 : ∀ (k : Fin 3) (h : (k : ℕ) + 1 < 3), ∃ (ρ : SL(3, L) →* ModGL τ L)
      (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ), CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧
        σ 0 1 = K.extRoot (l k) ∧ σ 1 2 = K.extRoot (l ⟨(k : ℕ) + 1, h⟩) := by
    intro k hk
    fin_cases k
    · simpa [l] using hFrames (idxNode x) (idxNode y)
        (by simpa [nodeIdx_idxNode hxlt, nodeIdx_idxNode hylt] using hxyE)
    · simpa [l] using hFrames (idxNode y) (idxNode z)
        (by simpa [nodeIdx_idxNode hylt, nodeIdx_idxNode hzlt] using hyzE)
    · norm_num at hk
  obtain ⟨ψ, σ, hψ, hroots⟩ := exists_frame_of_path (L := L) (hτ) K
    (m := 3) (l := l) hl hG hA2 v
  have hrange : Set.range l ⊆ (C : Set (Option (Fin τ.rank))) := by
    intro y hy
    rcases hy with ⟨k, rfl⟩
    fin_cases k <;> simp [l, hCdef]
    · exact ⟨x, hx, by simp [nodeIdx_idxNode (r := τ.rank) hxlt]⟩
    · exact ⟨y, hy, by simp [nodeIdx_idxNode (r := τ.rank) hylt]⟩
    · exact ⟨z, hz, by simp [nodeIdx_idxNode (r := τ.rank) hzlt]⟩
  have hsub : frameRoots σ ⊆ componentRoots (rootCharHom a) i := by
    rw [hroots, hi']
    rintro γ ⟨δ, hδ, rfl⟩
    exact ⟨δ, rootsOf_mono K hrange hδ, rfl⟩
  have hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1 := by
    intro a b hab
    have hroot := hψ.isRoot a b hab
    have := rootForm_self (hτ) hroot
    simpa [← dotProduct_mulVec_eq_iform] using this
  exact ⟨ψ, σ, hψ, hnorm, hsub⟩


theorem exists_A3_subframe_E6 (hq : S.D.q = 2)
    {a : Fin Tag.E6.rank → Lˣ} (hd3 : rootDiagUnit Tag.E6 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (ψ : SL(4, L) →* ModGL Tag.E6 L) (σ : Fin 4 → Fin 4 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
      frameRoots σ ⊆ componentRoots (rootCharHom a) i := by
  have e6_chain3 : ∀ c ∈ e6Conn, 3 ≤ c.length → chain3OK e6EdgeIdx c = true := by
    decide +kernel
  exact exists_A3_subframe_of_kac (hτ := Or.inr (Or.inl rfl)) S hq kacE6 facts_E6
    e6_tree e6_adj e6_check e6_lt e6_card e6_chain3 e6_frames hd3 i h3

end E6

section E7

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
  (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup Tag.E7 L p)

theorem exists_A3_subframe_E7 (hq : S.D.q = 2)
    {a : Fin Tag.E7.rank → Lˣ} (hd3 : rootDiagUnit Tag.E7 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (ψ : SL(4, L) →* ModGL Tag.E7 L) (σ : Fin 4 → Fin 4 → Fin Tag.E7.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
      frameRoots σ ⊆ componentRoots (rootCharHom a) i := by
  have e7_chain3 : ∀ c ∈ e7Conn, 3 ≤ c.length → chain3OK e7EdgeIdx c = true := by
    decide +kernel
  exact exists_A3_subframe_of_kac (hτ := Or.inr (Or.inr (Or.inl rfl))) S hq kacE7 facts_E7
    e7_tree e7_adj e7_check e7_lt e7_card e7_chain3 e7_frames hd3 i h3

end E7

section E8

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
  (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup Tag.E8 L p)

theorem exists_A3_subframe_E8 (hq : S.D.q = 2)
    {a : Fin Tag.E8.rank → Lˣ} (hd3 : rootDiagUnit Tag.E8 a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (ψ : SL(4, L) →* ModGL Tag.E8 L) (σ : Fin 4 → Fin 4 → Fin Tag.E8.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
      frameRoots σ ⊆ componentRoots (rootCharHom a) i := by
  have e8_chain3 : ∀ c ∈ e8Conn, 3 ≤ c.length → chain3OK e8EdgeIdx c = true := by
    decide +kernel
  exact exists_A3_subframe_of_kac (hτ := Or.inr (Or.inr (Or.inr rfl))) S hq kacE8 facts_E8
    e8_tree e8_adj e8_check e8_lt e8_card e8_chain3 e8_frames hd3 i h3

end E8

section DE

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem four_dvd_aut_of_DE_component
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hd3 : rootDiagUnit τ a ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fullThreeTorus S)) := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := exists_A3_subframe_E6 S hq hd3 i (by omega)
    exact four_dvd_aut_of_subframe S (Or.inl rfl) hq hAlg hρ i (by norm_num) hψ hnorm hsub
  · obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := exists_A3_subframe_E7 S hq hd3 i (by omega)
    exact four_dvd_aut_of_subframe S (Or.inr (Or.inl rfl)) hq hAlg hρ i (by norm_num) hψ hnorm hsub
  · obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := exists_A3_subframe_E8 S hq hd3 i (by omega)
    exact four_dvd_aut_of_subframe S (Or.inr (Or.inr rfl)) hq hAlg hρ i (by norm_num) hψ hnorm hsub

end DE

theorem four_dvd_aut_of_component_of_rank_three_le
    (S : LangSetup τ L p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hAlg : S.IsAlgebraic) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {a : Fin τ.rank → Lˣ} (hd3 : rootDiagUnit τ a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fullThreeTorus S)) := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := exists_A3_subframe_E6 S hq hd3 i h3
    exact four_dvd_aut_of_subframe S (Or.inl rfl) hq hAlg hρ i (by norm_num) hψ hnorm hsub
  · obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := exists_A3_subframe_E7 S hq hd3 i h3
    exact four_dvd_aut_of_subframe S (Or.inr (Or.inl rfl)) hq hAlg hρ i (by norm_num)
      hψ hnorm hsub
  · obtain ⟨ψ, σ, hψ, hnorm, hsub⟩ := exists_A3_subframe_E8 S hq hd3 i h3
    exact four_dvd_aut_of_subframe S (Or.inr (Or.inr rfl)) hq hAlg hρ i (by norm_num)
      hψ hnorm hsub

end CFSG.StandardType.QTwoCav

end
