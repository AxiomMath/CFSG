module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5CWGamma
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5WeylDict
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5PlainFix
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5RankOne
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Bridge
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangDatum
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Plain
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5YBasic
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5YFrame
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5YOdd

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Theta

private theorem g5_reidx_injective {R N : ℕ} (h : R = N) :
    Function.Injective (ggLangReidx (R := R) (N := N) h) := by
  intro a b hab
  funext i
  have := congrFun hab (Fin.cast h i)
  simpa [ggLangReidx] using this

private theorem g5_reidx_symm_reidx {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx (R := R) (N := N) h (ggLangReidx (N := R) (R := N) h.symm v) = v := by
  funext k
  simp [ggLangReidx]

private theorem g5_permLattice_permCongr_one {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (v : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) v = v := by
  subst h
  rfl

private theorem g5_permLattice_permCongr_single {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (π : Equiv.Perm (Fin R)) (i : Fin R) :
    permLattice ((finCongr h).permCongr π) (Pi.single (Fin.cast h i) 1 : Fin τ.rank → ℤ) =
      Pi.single (Fin.cast h (π i)) 1 := by
  rw [permLattice_single]
  rfl

private theorem g5_permLattice_permCongr_single_of_fixed {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (π : Equiv.Perm (Fin R)) (j : Fin τ.rank)
    (hfix : π (Fin.cast h.symm j) = Fin.cast h.symm j) :
    permLattice ((finCongr h).permCongr π) (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single j 1 := by
  have hi : Fin.cast h (Fin.cast h.symm j) = j := by simp
  have h1 := g5_permLattice_permCongr_single (τ := τ) h π (Fin.cast h.symm j)
  rw [hi, hfix] at h1
  exact h1

private theorem g5_latPerm_eq_of_reidx
    {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (π : Equiv.Perm (Fin R)) {α : Fin R → ℤ}
    (hfix : permLattice ((finCongr h).permCongr π) (ggLangReidx h α) = ggLangReidx h α) :
    latPerm π α = α := by
  apply g5_reidx_injective h
  rw [ggReidx_latPerm_permLattice h π α]
  exact hfix

private theorem g5_normalizer_mem
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    (n : ℕ) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (F : GGLangFrame t p f ht) {x m : ModGL (langTag t) GGL}
    (hx : x ∈ F.M.D.fix) (hm : m ∈ (ggIota t n f hf).range) :
    x * m * x⁻¹ ∈ (ggIota t n f hf).range := by
  have hpkg : GGLangPkg F.M.D (ggIota t n f hf) :=
    (F.M.torusData (n := n) hf hp hp2 hreg).pkg
  have hmfix : m ∈ F.M.D.fix := by
    rw [← hpkg.desc.derived] at hm
    simpa only [sup_idem] using Subgroup.commutator_le_sup F.M.D.fix F.M.D.fix hm
  have hcomm : ⁅x, m⁆ ∈ (ggIota t n f hf).range := by
    rw [← hpkg.desc.derived]
    exact Subgroup.commutator_mem_commutator hx hmfix
  have hmul : x * m * x⁻¹ = ⁅x, m⁆ * m := by
    rw [commutatorElement_def]
    group
  rw [hmul]
  exact ((ggIota t n f hf).range).mul_mem hcomm hm

private theorem g5_Y_rootReflection_mem_of_fixed
    {t : StatedLieTag} {p f : ℕ} [NeZero p]
    {ht : GGExcFive t} (n : ℕ) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) (F : GGLangFrame t p f ht)
    {α : Fin (ggU (absTag t) 6 f).D.rank → ℤ}
    (hα : α ∈ (ggU (absTag t) 6 f).D.roots) (hfix : latPerm (piB t p f) α = α) :
    ggG5_Y F (rootReflection (ggLangReidx (rank_eq_langTag f ht) α)) ∈
      (ggIota t n f hf).range := by
  obtain ⟨β, hβF, u, hu, huβ⟩ := F.cover_rf α hα hfix
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).1 (F.frame_root β hβF)
  have hsimple : rootReflection (ggLangReidx (rank_eq_langTag f ht) α) =
      u * rootReflection (ggLangReidx (rank_eq_langTag f ht) β) * u⁻¹ := by
    rw [← huβ]
    exact rootReflection_smul_root u hβroot
  rw [hsimple, ggG5_Y_mul, ggG5_Y_mul, ggG5_Y_inv]
  exact g5_normalizer_mem n hf hp hp2 hreg F (ggG5_Y_mem_fix F u hu)
    (ggG5_Y_frame_refl n hf F hβF)

private theorem g5_Y_simple_mem_of_fixed
    {t : StatedLieTag} {p f : ℕ} [NeZero p]
    {ht : GGExcFive t} (n : ℕ) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) (F : GGLangFrame t p f ht) {j : Fin (langTag t).rank}
    (hfix : permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f))
      (Pi.single j 1 : Fin (langTag t).rank → ℤ) = Pi.single j 1) :
    ggG5_Y F (simple (langTag t) j) ∈ (ggIota t n f hf).range := by
  let hR := rank_eq_langTag f ht
  let α : Fin (ggU (absTag t) 6 f).D.rank → ℤ :=
    ggLangReidx (R := (langTag t).rank) (N := (ggU (absTag t) 6 f).D.rank) hR.symm
      (Pi.single j 1)
  have hre : ggLangReidx hR α = (Pi.single j 1 : Fin (langTag t).rank → ℤ) :=
    g5_reidx_symm_reidx hR (Pi.single j 1)
  have hα : α ∈ (ggU (absTag t) 6 f).D.roots := by
    rw [mem_roots_iff_isRoot f ht, hre]
    exact isRoot_single (langTag t) j
  have hfix_abs : latPerm (piB t p f) α = α := by
    apply g5_latPerm_eq_of_reidx hR (piB t p f)
    rw [hre]
    exact hfix
  have h1 := g5_Y_rootReflection_mem_of_fixed n hf hp hp2 hreg F hα hfix_abs
  have h2 : rootReflection (ggLangReidx hR α) = simple (langTag t) j := by
    rw [hre]
    have h := rootReflection_eq_conj (τ := langTag t)
      (β := (Pi.single j 1 : Fin (langTag t).rank → ℤ)) (w := 1) (j := j) (by rw [one_smul])
    simpa using h
  rwa [h2] at h1

private lemma g5_e6_orbitWord_one :
    TwistTag.E6.orbitWord (1 : Fin TwistTag.E6.foldedTag.rank) = [2, 4] := by decide

private lemma g5_e6_orbitWord_zero :
    TwistTag.E6.orbitWord (0 : Fin TwistTag.E6.foldedTag.rank) = [0, 5] := by decide

private lemma g5_e6_orbitReflection_one :
    TwistTag.E6.orbitReflection (1 : Fin TwistTag.E6.foldedTag.rank) =
      simple (langTag .E6) (2 : Fin 6) * simple (langTag .E6) (4 : Fin 6) := by
  unfold TwistTag.orbitReflection
  rw [g5_e6_orbitWord_one, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one]
  rfl

private lemma g5_e6_orbitReflection_zero :
    TwistTag.E6.orbitReflection (0 : Fin TwistTag.E6.foldedTag.rank) =
      simple (langTag .E6) (0 : Fin 6) * simple (langTag .E6) (5 : Fin 6) := by
  unfold TwistTag.orbitReflection
  rw [g5_e6_orbitWord_zero, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one]
  rfl

theorem ggG5_Y_mem_range
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} (n : ℕ)
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (F : GGLangFrame t p f ht) (u : WeylGroup (langTag t)) (hu : GGCommPi t p f ht u) :
    F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹ ∈
      (ggIota t n f hf).range := by
  let T : Subgroup (WeylGroup (langTag t)) :=
    { carrier := {u | ggG5_Y F u ∈ (ggIota t n f hf).range}
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [ggG5_Y_one]
        exact Subgroup.one_mem _
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [ggG5_Y_mul]
        exact Subgroup.mul_mem _ ha hb
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [ggG5_Y_inv]
        exact Subgroup.inv_mem _ ha }
  have huT : u ∈ T := by
    rcases eps_cases p f with heps | heps
    ·
      have hdvd : p ∣ 2 ^ f - 1 := (eps_eq_one_iff p f).1 heps
      have hnot : ¬ p ∣ 2 ^ f + 1 := not_dvd_pow_two_add_one_of_dvd hp hp2 f hdvd
      have hw1 : F.M.w = 1 := ggG5_w_eq_one_of_eps ht hp hp2 heps F.M.hw
      have hg0fix : F.M.D.g0 ∈ F.M.D.fix := by
        rw [LangDatum.mem_fix]
        refine ⟨F.M.D.g0_mem, ?_⟩
        have hn1 : F.M.D.n = 1 := by rw [F.M.hn, hw1, canonicalRep_one]
        rw [F.M.D.lang, hn1, mul_one]
      have hΦu : ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
          canonicalRep (coxeterSystem (langTag t)) GGL u := by
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact ggG5_phi_canonicalRep_untw (Or.inl rfl) f u
        · exact ggG5_phi_canonicalRep_untw (Or.inr (Or.inl rfl)) f u
        · exact ggG5_phi_canonicalRep_untw (Or.inr (Or.inr (Or.inl rfl))) f u
        · exact ggG5_phi_canonicalRep_untw (Or.inr (Or.inr (Or.inr rfl))) f u
        · have hu' : weylTwist TwistTag.E6 u = u :=
            (ggG5_commPi_iff_weylTwist_twistedE6
              (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hnot u).1 hu
          exact ggG5_phi_canonicalRep_twistedE6 f u hu'
      have hnu := ggG5_plain_mem_range ht n f hf u hΦu
      show ggG5_Y F u ∈ (ggIota t n f hf).range
      rw [show ggG5_Y F u = F.M.D.g0 *
          canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹ from rfl]
      exact g5_normalizer_mem n hf hp hp2 hreg F hg0fix hnu
    ·
      have hnd : ¬ p ∣ 2 ^ f - 1 := by
        intro h
        have h1 : eps p f = 1 := (eps_eq_one_iff p f).2 h
        rw [heps] at h1
        norm_num at h1
      rcases ht with rfl | rfl | rfl | rfl | rfl
      ·
        show ggG5_Y F u ∈ (ggIota .F4 n f hf).range
        have hgen : u ∈ Subgroup.closure
            (Set.range (coxeterSystem (langTag .F4)).simple) := by
          rw [CoxeterSystem.subgroup_closure_range_simple]
          exact Subgroup.mem_top u
        refine ((Subgroup.closure_le T).mpr ?_) hgen
        rintro x ⟨j, rfl⟩
        show ggG5_Y F ((coxeterSystem (langTag .F4)).simple j) ∈
          (ggIota .F4 n f hf).range
        exact g5_Y_simple_mem_of_fixed n hf hp hp2 hreg F (j := j)
          (by rw [piB_F4]; exact g5_permLattice_permCongr_one _ _)
      ·
        have hu' : weylTwist TwistTag.E6 u = u :=
          (ggG5_commPi_iff_weylTwist_E6 (Or.inr (Or.inl rfl)) hnd u).1 hu
        have hgen := ggG5_cwgamma_gen u hu'
        have hle : Subgroup.closure
            ({(simple (langTag .E6)) (1 : Fin 6),
              (simple (langTag .E6)) (3 : Fin 6),
              (simple (langTag .E6)) (2 : Fin 6) *
                (simple (langTag .E6)) (4 : Fin 6),
              (simple (langTag .E6)) (0 : Fin 6) *
                (simple (langTag .E6)) (5 : Fin 6)} :
              Set (WeylGroup (langTag .E6))) ≤ T := by
          refine (Subgroup.closure_le T).mpr ?_
          intro x hx
          have hx' := hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
          rcases hx' with rfl | rfl | rfl | rfl
          · show ggG5_Y F ((simple (langTag .E6)) (1 : Fin 6)) ∈
              (ggIota .E6 n f hf).range
            exact g5_Y_simple_mem_of_fixed n hf hp hp2 hreg F (j := (1 : Fin 6))
              (by
                rw [piB_E6_of_not_dvd f hnd]
                exact g5_permLattice_permCongr_single_of_fixed (τ := langTag .E6) _ (TwistTag.perm .E6)
                  (1 : Fin 6) (by apply Fin.ext; rfl))
          · show ggG5_Y F ((simple (langTag .E6)) (3 : Fin 6)) ∈
              (ggIota .E6 n f hf).range
            exact g5_Y_simple_mem_of_fixed n hf hp hp2 hreg F (j := (3 : Fin 6))
              (by
                rw [piB_E6_of_not_dvd f hnd]
                exact g5_permLattice_permCongr_single_of_fixed (τ := langTag .E6) _ (TwistTag.perm .E6)
                  (3 : Fin 6) (by apply Fin.ext; rfl))
          · show ggG5_Y F ((simple (langTag .E6)) (2 : Fin 6) *
              (simple (langTag .E6)) (4 : Fin 6)) ∈ (ggIota .E6 n f hf).range
            have hweyl : weylTwist TwistTag.E6 ((simple (langTag .E6)) (2 : Fin 6) *
                (simple (langTag .E6)) (4 : Fin 6)) =
                (simple (langTag .E6)) (2 : Fin 6) *
                  (simple (langTag .E6)) (4 : Fin 6) := by
              rw [← g5_e6_orbitReflection_one]
              exact (mem_relWeylTwist TwistTag.E6).1
                (TwistTag.E6.orbitReflection_mem (1 : Fin TwistTag.E6.foldedTag.rank))
            have hy : ggG5_Y F ((simple (langTag .E6)) (2 : Fin 6) *
                (simple (langTag .E6)) (4 : Fin 6)) ∈ F.M.D.fix :=
              ggG5_Y_mem_fix F _ ((ggG5_commPi_iff_weylTwist_E6
                (Or.inr (Or.inl rfl)) hnd _).2 hweyl)
            have hu1sq : ((simple (langTag .E6)) (2 : Fin 6) *
                (simple (langTag .E6)) (4 : Fin 6)) *
                ((simple (langTag .E6)) (2 : Fin 6) *
                  (simple (langTag .E6)) (4 : Fin 6)) = 1 := by
              rw [← g5_e6_orbitReflection_one]
              exact TwistTag.E6.orbitReflection_mul_self (1 : Fin TwistTag.E6.foldedTag.rank)
            have hy2 : ggG5_Y F ((simple (langTag .E6)) (2 : Fin 6) *
                (simple (langTag .E6)) (4 : Fin 6)) *
                ggG5_Y F ((simple (langTag .E6)) (2 : Fin 6) *
                  (simple (langTag .E6)) (4 : Fin 6)) = 1 := by
              rw [show ggG5_Y F ((simple (langTag .E6)) (2 : Fin 6) *
                    (simple (langTag .E6)) (4 : Fin 6)) *
                    ggG5_Y F ((simple (langTag .E6)) (2 : Fin 6) *
                      (simple (langTag .E6)) (4 : Fin 6)) =
                  ggG5_Y F (((simple (langTag .E6)) (2 : Fin 6) *
                      (simple (langTag .E6)) (4 : Fin 6)) *
                      ((simple (langTag .E6)) (2 : Fin 6) *
                        (simple (langTag .E6)) (4 : Fin 6))) from
                (ggG5_Y_mul F _ _).symm]
              rw [hu1sq]
              exact ggG5_Y_one F
            exact ggG5_involution_mem_range_E6 hf F.M.D F.M.hΦ (ggIota .E6 n f hf)
              (F.M.torusData (n := n) hf hp hp2 hreg).pkg hy hy2
          · show ggG5_Y F ((simple (langTag .E6)) (0 : Fin 6) *
              (simple (langTag .E6)) (5 : Fin 6)) ∈ (ggIota .E6 n f hf).range
            have hweyl : weylTwist TwistTag.E6 ((simple (langTag .E6)) (0 : Fin 6) *
                (simple (langTag .E6)) (5 : Fin 6)) =
                (simple (langTag .E6)) (0 : Fin 6) *
                  (simple (langTag .E6)) (5 : Fin 6) := by
              rw [← g5_e6_orbitReflection_zero]
              exact (mem_relWeylTwist TwistTag.E6).1
                (TwistTag.E6.orbitReflection_mem (0 : Fin TwistTag.E6.foldedTag.rank))
            have hy : ggG5_Y F ((simple (langTag .E6)) (0 : Fin 6) *
                (simple (langTag .E6)) (5 : Fin 6)) ∈ F.M.D.fix :=
              ggG5_Y_mem_fix F _ ((ggG5_commPi_iff_weylTwist_E6
                (Or.inr (Or.inl rfl)) hnd _).2 hweyl)
            have hu1sq : ((simple (langTag .E6)) (0 : Fin 6) *
                (simple (langTag .E6)) (5 : Fin 6)) *
                ((simple (langTag .E6)) (0 : Fin 6) *
                  (simple (langTag .E6)) (5 : Fin 6)) = 1 := by
              rw [← g5_e6_orbitReflection_zero]
              exact TwistTag.E6.orbitReflection_mul_self (0 : Fin TwistTag.E6.foldedTag.rank)
            have hy2 : ggG5_Y F ((simple (langTag .E6)) (0 : Fin 6) *
                (simple (langTag .E6)) (5 : Fin 6)) *
                ggG5_Y F ((simple (langTag .E6)) (0 : Fin 6) *
                  (simple (langTag .E6)) (5 : Fin 6)) = 1 := by
              rw [show ggG5_Y F ((simple (langTag .E6)) (0 : Fin 6) *
                    (simple (langTag .E6)) (5 : Fin 6)) *
                    ggG5_Y F ((simple (langTag .E6)) (0 : Fin 6) *
                      (simple (langTag .E6)) (5 : Fin 6)) =
                  ggG5_Y F (((simple (langTag .E6)) (0 : Fin 6) *
                      (simple (langTag .E6)) (5 : Fin 6)) *
                      ((simple (langTag .E6)) (0 : Fin 6) *
                        (simple (langTag .E6)) (5 : Fin 6))) from
                (ggG5_Y_mul F _ _).symm]
              rw [hu1sq]
              exact ggG5_Y_one F
            exact ggG5_involution_mem_range_E6 hf F.M.D F.M.hΦ (ggIota .E6 n f hf)
              (F.M.torusData (n := n) hf hp hp2 hreg).pkg hy hy2
        exact hle hgen
      ·
        show ggG5_Y F u ∈ (ggIota .E7 n f hf).range
        have hgen : u ∈ Subgroup.closure
            (Set.range (coxeterSystem (langTag .E7)).simple) := by
          rw [CoxeterSystem.subgroup_closure_range_simple]
          exact Subgroup.mem_top u
        refine ((Subgroup.closure_le T).mpr ?_) hgen
        rintro x ⟨j, rfl⟩
        show ggG5_Y F ((coxeterSystem (langTag .E7)).simple j) ∈
          (ggIota .E7 n f hf).range
        exact g5_Y_simple_mem_of_fixed n hf hp hp2 hreg F (j := j)
          (by rw [piB_E7]; exact g5_permLattice_permCongr_one _ _)
      ·
        show ggG5_Y F u ∈ (ggIota .E8 n f hf).range
        have hgen : u ∈ Subgroup.closure
            (Set.range (coxeterSystem (langTag .E8)).simple) := by
          rw [CoxeterSystem.subgroup_closure_range_simple]
          exact Subgroup.mem_top u
        refine ((Subgroup.closure_le T).mpr ?_) hgen
        rintro x ⟨j, rfl⟩
        show ggG5_Y F ((coxeterSystem (langTag .E8)).simple j) ∈
          (ggIota .E8 n f hf).range
        exact g5_Y_simple_mem_of_fixed n hf hp hp2 hreg F (j := j)
          (by rw [piB_E8]; exact g5_permLattice_permCongr_one _ _)
      ·
        have hdvd2 : p ∣ 2 ^ f + 1 := hreg.resolve_left hnd
        show ggG5_Y F u ∈ (ggIota .twistedE6 n f hf).range
        have hgen : u ∈ Subgroup.closure
            (Set.range (coxeterSystem (langTag .twistedE6)).simple) := by
          rw [CoxeterSystem.subgroup_closure_range_simple]
          exact Subgroup.mem_top u
        refine ((Subgroup.closure_le T).mpr ?_) hgen
        rintro x ⟨j, rfl⟩
        show ggG5_Y F ((coxeterSystem (langTag .twistedE6)).simple j) ∈
          (ggIota .twistedE6 n f hf).range
        exact g5_Y_simple_mem_of_fixed n hf hp hp2 hreg F (j := j)
          (by rw [piB_twistedE6_of_dvd f hdvd2]; exact g5_permLattice_permCongr_one _ _)
  exact huT

end Theta

end CFSG.StandardType.GGFinModel.G5
