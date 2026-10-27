module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwSmallThreeTwE6
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.RankThree.PartOne.KE.E8RootCharacterTorus
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyQuad

public section

namespace CFSG.StandardType.Q1E8Model

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType
  CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LieType.SemisimpleCentralizers.Held CFSG.LocalAnalysis.GLTheoremA.T171Sh

section InnerDiagonal

theorem hatAut_E8_range_eq_conj (K : Type) [Field K] :
    (hatAut .E8 K).range =
      (MulAut.conj : ↥(adjointGroup .E8 K) →* MulAut ↥(adjointGroup .E8 K)).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨g, hg, a, hxa⟩ := x.2
    have hxadj : g * rootDiagUnit .E8 a ∈ adjointGroup .E8 K :=
      mul_mem hg (CFSG.RankThree.PartOne.KE.rootDiagUnit_E8_mem_adjointGroup a)
    refine ⟨⟨g * rootDiagUnit .E8 a, hxadj⟩, ?_⟩
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_hatAut_apply, MulAut.conj_apply,
      show (x : ModGL .E8 K) = g * rootDiagUnit .E8 a from hxa]
    rfl
  · rintro _ ⟨g, rfl⟩
    exact ⟨⟨g, adjointGroup_le_hatGroup g.2⟩, by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [coe_hatAut_apply, MulAut.conj_apply]
      rfl⟩

end InnerDiagonal

section Rational

variable {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

theorem fix_eq_map_rationalImage_E8 {p : ℕ} (S : LangSetup .E8 L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) :
    S.D.fix = (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hfinModel : Finite ↥S.D.model := S.finite
  have hfin : Finite ↥S.D.fix := by
    rw [← LangDatum.map_conj_model (D := S.D)]
    exact Finite.of_surjective ((MulAut.conj S.D.g0).toMonoidHom.subgroupMap S.D.model)
      ((MulAut.conj S.D.g0).toMonoidHom.subgroupMap_surjective S.D.model)
  have hmain := finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr S.D.fix
    (fun x hx => ((LangDatum.mem_fix (D := S.D)).1 hx).1)
    (fun x hx => by rw [← hΦ]; exact ((LangDatum.mem_fix (D := S.D)).1 hx).2)
  have hrel : ((adjointGroup .E8 K).map (baseChangeGL (algebraMap K L))).relIndex S.D.fix = 1 :=
    Nat.dvd_one.1 hmain.1
  refine le_antisymm (Subgroup.relIndex_eq_one.1 hrel) ?_
  rintro _ ⟨g, hg, rfl⟩
  refine (LangDatum.mem_fix (D := S.D)).2 ⟨baseChangeGL_mem_adjointGroup _ hg, ?_⟩
  rw [hΦ]
  exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g

omit [Finite K] [Algebra.IsAlgebraic K L]
  in
theorem model_le_Gamma_E8 {p : ℕ} (S : LangSetup .E8 L p)
    (hperf : commutator ↥(adjointGroup .E8 K) = ⊤)
    (hfix : S.D.fix = (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L))) :
    S.D.model ≤ S.Γ := by
  classical
  refine model_le_Γ_of_fix_le_commutator S.D ?_
  rw [hfix]
  let ι : ↥(adjointGroup .E8 K) →* ModGL .E8 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E8 K).subtype
  have himg : ι.range = (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have htop : Subgroup.map ι (⊤ : Subgroup ↥(adjointGroup .E8 K)) =
      (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) := by
    rw [Subgroup.map_top]
    exact himg
  have hcomm : ⁅(⊤ : Subgroup ↥(adjointGroup .E8 K)), (⊤ : Subgroup ↥(adjointGroup .E8 K))⁆ =
      (⊤ : Subgroup ↥(adjointGroup .E8 K)) := by
    simpa only [commutator] using hperf
  have hperfect : ⁅(adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)),
      (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L))⁆ =
      (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) := by
    conv_lhs => rw [← htop]
    rw [← Subgroup.map_commutator, hcomm]
    exact htop
  rw [hperfect]

end Rational

section Model

theorem q1E8Model_exists_connectedAction
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut ↥(adjointGroup .E8 K))}
    (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : A ≤ (hatAut .E8 K).range)
    {u : MulAut ↥(adjointGroup .E8 K)} (hu : u ∈ A) (hu1 : u ≠ 1) :
    ∃ (S : LangSetup .E8 (AlgebraicClosure K) 5)
      (d : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
      (ψ : ↥(adjointGroup .E8 K) →* ModGL .E8 (AlgebraicClosure K))
      (ρ : ↥A →* ModGL .E8 (AlgebraicClosure K)),
      S.D.q = Nat.card K ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ Nat.card K) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      rootDiagUnit .E8 d ∈ S.D.torus ∧ (∀ j, d j ^ p = 1) ∧ rootDiagUnit .E8 d ≠ 1 ∧
      Function.Injective ψ ∧ ψ.range = S.Γ ∧
      ρ ⟨u, hu⟩ = rootDiagUnit .E8 d ∧
      ρ.range ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E8 d} ∧
      (∀ a ∈ ρ.range, a ^ p = 1) ∧
      (∀ a : ↥A, ∀ c : ↥(adjointGroup .E8 K),
        ψ ((a : MulAut ↥(adjointGroup .E8 K)) c) = ρ a * ψ c * (ρ a)⁻¹) ∧
      (Subgroup.map ψ (ggAutFixedSubgroup u) =
        S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E8 d}) ∧
      (∀ J : Subgroup ↥(adjointGroup .E8 K),
        CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u) →
          GGE0Concl ρ.range (Subgroup.map ψ J)) := by
  classical
  let L := AlgebraicClosure K
  have hCharL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hKcard : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    have h' : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
    norm_num at h'
  have hArange : A ≤ (MulAut.conj :
      ↥(adjointGroup .E8 K) →* MulAut ↥(adjointGroup .E8 K)).range :=
    hAI.trans (le_of_eq (hatAut_E8_range_eq_conj K))
  have hZ : Subgroup.center ↥(adjointGroup .E8 K) = ⊥ :=
    center_adjointGroup_eq_bot_field .E8 K
  have hconjinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup .E8 K) →* MulAut ↥(adjointGroup .E8 K)) := by
    refine (injective_iff_map_eq_one _).2 fun z hz => ?_
    have hzc : z ∈ Subgroup.center ↥(adjointGroup .E8 K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun φ : MulAut ↥(adjointGroup .E8 K) => φ x) hz
      rw [MulAut.one_apply, MulAut.conj_apply] at h
      have h2 : z * x = x * z := by
        calc z * x = (z * x * z⁻¹) * z := by group
          _ = x * z := by rw [h]
      exact h2.symm
    rw [hZ] at hzc
    exact Subgroup.mem_bot.1 hzc
  let cj : ↥(adjointGroup .E8 K) →* MulAut ↥(adjointGroup .E8 K) := MulAut.conj
  let A' : Subgroup ↥(adjointGroup .E8 K) := Subgroup.comap cj A
  have hA'map : Subgroup.map cj A' = A := Subgroup.map_comap_eq_self hArange
  let eA : ↥A' ≃* ↥A :=
    (Subgroup.equivMapOfInjective A' cj hconjinj).trans (MulEquiv.subgroupCongr hA'map)
  have heA : ∀ y : ↥A',
      ((eA y : ↥A) : MulAut ↥(adjointGroup .E8 K)) = cj (y : ↥(adjointGroup .E8 K)) :=
    fun _ => rfl
  have hexp : ∀ y : ↥A', (y : ↥(adjointGroup .E8 K)) ^ p = 1 := by
    intro y
    have hyA : cj (y : ↥(adjointGroup .E8 K)) ∈ A := y.2
    have h1 : cj ((y : ↥(adjointGroup .E8 K)) ^ p) = 1 := by
      rw [map_pow, hA.2 (cj (y : ↥(adjointGroup .E8 K))) hyA]
    have h2 : (y : ↥(adjointGroup .E8 K)) ^ p ∈ Subgroup.center ↥(adjointGroup .E8 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut ↥(adjointGroup .E8 K) => φ g) h1
      rw [MulAut.one_apply, MulAut.conj_apply] at h3
      have h4 : (y : ↥(adjointGroup .E8 K)) ^ p * g = g * (y : ↥(adjointGroup .E8 K)) ^ p := by
        calc (y : ↥(adjointGroup .E8 K)) ^ p * g =
            ((y : ↥(adjointGroup .E8 K)) ^ p * g * ((y : ↥(adjointGroup .E8 K)) ^ p)⁻¹) *
              (y : ↥(adjointGroup .E8 K)) ^ p := by group
          _ = g * (y : ↥(adjointGroup .E8 K)) ^ p := by rw [h3]
      exact h4.symm
    rw [hZ] at h2
    exact Subgroup.mem_bot.1 h2
  let x : ↥A' := eA.symm ⟨u, hu⟩
  have hx : cj (x : ↥(adjointGroup .E8 K)) = u := by
    have h1 : eA x = ⟨u, hu⟩ := eA.apply_symm_apply ⟨u, hu⟩
    have h2 := heA x
    rw [h1] at h2
    exact h2.symm
  have hx1 : (x : ↥(adjointGroup .E8 K)) ≠ 1 := by
    intro h
    apply hu1
    rw [← hx, h, map_one]
  have hxp : ((x : ↥A') : ↥(adjointGroup .E8 K)) ^ p = 1 := hexp x
  have hxpM : (((x : ↥A') : ↥(adjointGroup .E8 K)) : ModGL .E8 K) ^ p = 1 := by
    simpa using congrArg Subtype.val hxp
  have hx1M : (((x : ↥A') : ↥(adjointGroup .E8 K)) : ModGL .E8 K) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext h)
  have hβ : ∀ c : ↥(adjointGroup .E8 K),
      (u c : ModGL .E8 K) = (x : ↥(adjointGroup .E8 K)) * c *
        (x : ↥(adjointGroup .E8 K))⁻¹ := by
    intro c
    rw [show u = cj (x : ↥(adjointGroup .E8 K)) from hx.symm]
    exact congrArg Subtype.val (MulAut.conj_apply (x : ↥(adjointGroup .E8 K)) c)
  have hhL : baseChangeGL (algebraMap K L) (x : ModGL .E8 K) ∈ adjointGroup .E8 L :=
    baseChangeGL_mem_adjointGroup _ (x : ↥(adjointGroup .E8 K)).2
  have hmon : MonomialToralAt .E8 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hp hp2
  have hperf : commutator ↥(adjointGroup .E8 K) = ⊤ :=
    (CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 K).commutator_eq_top
  obtain ⟨S, d, ψ, hSq, hFrob, hT, hdp, hd1, hψinj, hψrange, hconjψ⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := .E8) (p₀ := 5)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp hpK Nat.prime_five h5K
      (Or.inl le_rfl) hmon hperf u (((x : ↥A') : ↥(adjointGroup .E8 K)) : ModGL .E8 K)
      hhL hβ hxpM hx1M
  obtain ⟨Fr, hFr, hΦ⟩ := hFrob
  have hfix : S.D.fix = (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) :=
    fix_eq_map_rationalImage_E8 (K := K) (L := L) S hFr hΦ
  have hmodel : S.D.model ≤ S.Γ :=
    model_le_Gamma_E8 (K := K) (L := L) S hperf hfix
  have hdΓ : rootDiagUnit .E8 d ∈ S.Γ :=
    hmodel ((LangDatum.torus_le_model (D := S.D)) hT)
  have hψx : ψ (x : ↥(adjointGroup .E8 K)) = rootDiagUnit .E8 d := by
    let y1 : ↥S.Γ := ⟨ψ (x : ↥(adjointGroup .E8 K)), by
      rw [← hψrange]
      exact ⟨x, rfl⟩⟩
    let y2 : ↥S.Γ := ⟨rootDiagUnit .E8 d, hdΓ⟩
    have hconjΓ : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) := by
      refine (injective_iff_map_eq_one _).2 fun z hz => ?_
      have hz1 : ∀ w : ↥S.Γ, z * w * z⁻¹ = w := by
        intro w
        have h := congrArg (fun φ : MulAut ↥S.Γ => φ w) hz
        rw [MulAut.one_apply, MulAut.conj_apply] at h
        exact h
      obtain ⟨c, hc⟩ : ∃ c : ↥(adjointGroup .E8 K), ψ c = (z : ModGL .E8 L) := by
        have hzmem : (z : ModGL .E8 L) ∈ ψ.range := by rw [hψrange]; exact z.2
        exact hzmem
      have hcZ : c ∈ Subgroup.center ↥(adjointGroup .E8 K) := by
        rw [Subgroup.mem_center_iff]
        intro c'
        have hmemw : ψ c' ∈ S.Γ := by rw [← hψrange]; exact ⟨c', rfl⟩
        have hval : (z : ModGL .E8 L) * ψ c' * ((z : ModGL .E8 L))⁻¹ = ψ c' :=
          congrArg Subtype.val (hz1 ⟨ψ c', hmemw⟩)
        rw [← hc] at hval
        have h2 : c * c' * c⁻¹ = c' := by
          apply hψinj
          rw [map_mul, map_mul, map_inv]
          exact hval
        calc c' * c = (c * c' * c⁻¹) * c := by rw [h2]
          _ = c * c' := by group
      have hc1 : c = 1 := by
        rw [hZ] at hcZ
        exact Subgroup.mem_bot.1 hcZ
      have hz1' : (z : ModGL .E8 L) = 1 := by
        rw [← hc, hc1, map_one]
      exact Subtype.ext hz1'
    have hy : y1 = y2 := by
      apply hconjΓ
      refine MulEquiv.ext fun w => ?_
      obtain ⟨c, hc⟩ : ∃ c : ↥(adjointGroup .E8 K), ψ c = (w : ModGL .E8 L) := by
        have hwmem : (w : ModGL .E8 L) ∈ ψ.range := by rw [hψrange]; exact w.2
        exact hwmem
      apply Subtype.ext
      rw [MulAut.conj_apply, MulAut.conj_apply]
      change ((y1 : ↥S.Γ) : ModGL .E8 L) * (w : ModGL .E8 L) *
          (((y1 : ↥S.Γ) : ModGL .E8 L))⁻¹ =
        ((y2 : ↥S.Γ) : ModGL .E8 L) * (w : ModGL .E8 L) *
          (((y2 : ↥S.Γ) : ModGL .E8 L))⁻¹
      rw [show ((y1 : ↥S.Γ) : ModGL .E8 L) = ψ (x : ↥(adjointGroup .E8 K)) from rfl,
        show ((y2 : ↥S.Γ) : ModGL .E8 L) = rootDiagUnit .E8 d from rfl, ← hc]
      have hxc : (x : ↥(adjointGroup .E8 K)) * c * (x : ↥(adjointGroup .E8 K))⁻¹ = u c := by
        change (cj (x : ↥(adjointGroup .E8 K))) c = u c
        rw [hx]
      calc ψ (x : ↥(adjointGroup .E8 K)) * ψ c * (ψ (x : ↥(adjointGroup .E8 K)))⁻¹
          = ψ ((x : ↥(adjointGroup .E8 K)) * c * (x : ↥(adjointGroup .E8 K))⁻¹) := by
            rw [map_mul, map_mul, map_inv]
        _ = ψ (u c) := by rw [hxc]
        _ = rootDiagUnit .E8 d * ψ c * (rootDiagUnit .E8 d)⁻¹ := hconjψ c
    exact congrArg Subtype.val hy
  let ρ : ↥A →* ModGL .E8 L := (ψ.comp A'.subtype).comp eA.symm.toMonoidHom
  have hρapply : ∀ a : ↥A,
      ρ a = ψ ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) := fun _ => rfl
  have hρu : ρ ⟨u, hu⟩ = rootDiagUnit .E8 d := by
    rw [hρapply]
    exact hψx
  have hρΓ : ρ.range ≤ S.Γ := by
    rintro _ ⟨a, rfl⟩
    rw [hρapply, ← hψrange]
    exact ⟨_, rfl⟩
  have hρC : ρ.range ≤ Subgroup.centralizer ({rootDiagUnit .E8 d} : Set (ModGL .E8 L)) := by
    rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [hρapply, ← hψx]
    have : IsMulCommutative ↥A := hA.1
    have hcommA : eA (eA.symm a) * ⟨u, hu⟩ = ⟨u, hu⟩ * eA (eA.symm a) := mul_comm' _ _
    have hcommM : cj ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) * u =
        u * cj ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) := by
      simpa only [Subgroup.coe_mul, heA] using congrArg Subtype.val hcommA
    have hxx : ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) * (x : _) =
        (x : _) * ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) := by
      apply hconjinj
      rw [map_mul, map_mul, hx]
      exact hcommM
    calc ψ ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) * ψ (x : _)
        = ψ (((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) * (x : _)) := by rw [map_mul]
      _ = ψ ((x : _) * ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K))) := by rw [hxx]
      _ = ψ (x : _) * ψ ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) := by rw [map_mul]
  have hρp : ∀ a ∈ ρ.range, a ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [hρapply, ← map_pow, hexp (eA.symm b), map_one]
  have hact : ∀ a : ↥A, ∀ c : ↥(adjointGroup .E8 K),
      ψ ((a : MulAut ↥(adjointGroup .E8 K)) c) = ρ a * ψ c * (ρ a)⁻¹ := by
    intro a c
    have ha : (a : MulAut ↥(adjointGroup .E8 K)) =
        cj ((eA.symm a : ↥A') : ↥(adjointGroup .E8 K)) := by
      have h1 := heA (eA.symm a)
      rw [eA.apply_symm_apply] at h1
      exact h1
    rw [ha, MulAut.conj_apply, hρapply, map_mul, map_mul, map_inv]
  have hfixmap : Subgroup.map ψ (ggAutFixedSubgroup u) =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E8 d} := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcu : u c = c := hc
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [← hψrange]
        exact ⟨c, rfl⟩
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        rw [← hψx]
        have h1 : (x : ↥(adjointGroup .E8 K)) * c * (x : ↥(adjointGroup .E8 K))⁻¹ = c := by
          change (cj (x : ↥(adjointGroup .E8 K))) c = c
          rw [hx]
          exact hcu
        have hcx' : (x : ↥(adjointGroup .E8 K)) * c = c * (x : ↥(adjointGroup .E8 K)) := by
          calc (x : ↥(adjointGroup .E8 K)) * c =
              ((x : ↥(adjointGroup .E8 K)) * c * (x : ↥(adjointGroup .E8 K))⁻¹) *
                (x : ↥(adjointGroup .E8 K)) := by group
            _ = c * (x : ↥(adjointGroup .E8 K)) := by rw [h1]
        have hcx : c * (x : ↥(adjointGroup .E8 K)) = (x : ↥(adjointGroup .E8 K)) * c :=
          hcx'.symm
        calc ψ c * ψ (x : ↥(adjointGroup .E8 K)) =
            ψ (c * (x : ↥(adjointGroup .E8 K))) := by rw [map_mul]
          _ = ψ ((x : ↥(adjointGroup .E8 K)) * c) := by rw [hcx]
          _ = ψ (x : ↥(adjointGroup .E8 K)) * ψ c := by rw [map_mul]
    · rintro ⟨hyΓ, hyC⟩
      rw [← hψrange] at hyΓ
      obtain ⟨c, hyc⟩ := hyΓ
      have hyC' : rootDiagUnit .E8 d * ψ c = ψ c * rootDiagUnit .E8 d := by
        have h := Subgroup.mem_centralizer_iff.1 hyC (rootDiagUnit .E8 d) (by simp)
        rwa [← hyc] at h
      refine ⟨c, ?_, hyc⟩
      refine (mem_ggAutFixedSubgroup u c).mpr ?_
      have hcomm : ψ c * ψ (x : ↥(adjointGroup .E8 K)) =
          ψ (x : ↥(adjointGroup .E8 K)) * ψ c := by
        rw [hψx]
        exact hyC'.symm
      have hcx : c * (x : ↥(adjointGroup .E8 K)) = (x : ↥(adjointGroup .E8 K)) * c := by
        apply hψinj
        rw [map_mul, map_mul]
        exact hcomm
      show u c = c
      rw [← hx]
      rw [MulAut.conj_apply]
      calc (x : ↥(adjointGroup .E8 K)) * c * (x : ↥(adjointGroup .E8 K))⁻¹ =
          (c * (x : ↥(adjointGroup .E8 K))) * (x : ↥(adjointGroup .E8 K))⁻¹ := by rw [hcx]
        _ = c := by group
  refine ⟨S, d, ψ, ρ, hSq, ⟨Fr, hFr, hΦ⟩, hT, hdp, hd1, hψinj, hψrange, hρu,
    le_inf hρΓ hρC, hρp, hact, hfixmap, ?_⟩
  intro J hJ
  have hX : CFSG.Assembly.IsComponentOf (Subgroup.map ψ J)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E8 d}) := by
    have hmap := isComponentOf_map_of_injective ψ hψinj hJ
    rwa [hfixmap] at hmap
  have hE : ρ.range ≤ S.D.model := hρΓ.trans (LangSetup.Γ_le_model S)
  exact langTorus_connectedModelAction (τ := .E8) (L := L) (Or.inr (Or.inr rfl)) hp hp2 S d hT
    hdp hd1 ρ.range (Subgroup.map ψ J) hE hρp (by
      have hker : familyKernel (fun _ : Unit => d) = rootCharKernel d := by
        ext α
        simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨h.1, h.2 ()⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
      have hEq : familyGroup (fun _ : Unit => d) = toralRootGroup .E8 L d := by
        rw [familyGroup, toralRootGroup, hker]
      rw [hEq]
      refine le_trans ?_ (toralCentralizer_le_toralRootGroup (τ := .E8) (k := L) d ?_)
      · refine le_inf ?_ hρC
        refine hρΓ.trans ?_
        intro z hz
        exact ((LangDatum.mem_model (D := S.D)).1 (LangSetup.Γ_le_model S hz)).1
      · intro w hw
        exact rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
          (fun h => absurd h (by decide)) hdp hw) hX

end Model

end CFSG.StandardType.Q1E8Model

end
