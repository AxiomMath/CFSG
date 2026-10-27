module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.GroupTheory.SylowAutConj
import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR7iiiAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2
import all CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
import CFSG.RankThree.PartOne.K133H.F4Torus
import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.GLTheoremA.Y10F.LinEngine

private theorem factorization_card_sl_four {K : Type} [Field K] [Finite K] {r : ℕ}
    (hr : r.Prime) (hr7 : 7 ≤ r) (hrq : r ∣ Nat.card K - 1) :
    (Nat.card (SpecialLinearGroup (Fin 4) K)).factorization r =
      3 * (Nat.card K - 1).factorization r := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hr2 : r ≠ 2 := by omega
  have hqr : ¬ r ∣ Nat.card K := by
    intro hd
    have h1 := Nat.dvd_sub hd hrq
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h1
    exact hr.not_dvd_one h1
  have hne : ∀ j : ℕ, 1 ≤ j → Nat.card K ^ j - 1 ≠ 0 := by
    intro j hj
    have := Nat.le_self_pow (by omega : j ≠ 0) (Nat.card K)
    omega
  rw [card_SL_eq (by norm_num : 1 ≤ 4), Nat.factorization_mul (by positivity)
    (Finset.prod_ne_zero_iff.mpr fun j hj => hne j (by have := (Finset.mem_Icc.mp hj).1; omega)),
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd hqr, smul_zero, zero_add,
    Nat.factorization_prod (fun j hj => hne j (by have := (Finset.mem_Icc.mp hj).1; omega)),
    Finsupp.finset_sum_apply]
  have h : ∀ j ∈ Finset.Icc 2 4, (Nat.card K ^ j - 1).factorization r =
      (Nat.card K - 1).factorization r := by
    intro j hj
    obtain ⟨hj2, hj4⟩ := Finset.mem_Icc.mp hj
    exact CFSG.RankThree.PartOne.K133H.factorization_pow_sub_one hr hr2 hq hrq
      (by omega) (fun hd => by have := Nat.le_of_dvd (by omega : 0 < j) hd; omega)
  rw [Finset.sum_congr rfl h, Finset.sum_const]
  have hc : (Finset.Icc 2 4).card = 3 := by decide
  rw [hc]
  rfl

private theorem map_diagSLMat {K : Type} [Field K] {n q : ℕ}
    (σ : K ≃+* K) (e : Fin n → rootsOfUnity q K) :
    SpecialLinearGroup.map σ.toRingHom (diagSLMat e) =
      diagSLMat (fun i => ⟨Units.map σ.toMonoidHom (e i), by
        rw [mem_rootsOfUnity]
        change (Units.map σ.toMonoidHom) (e i) ^ q = 1
        rw [← map_pow, (mem_rootsOfUnity _ _).mp (e i).2, map_one]⟩) := by
  apply Subtype.ext
  change (Matrix.diagonal fun i => (diagEntry e i : K)).map σ = _
  ext i j
  simp only [diagSLMat, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst j
    unfold diagEntry
    split_ifs
    · rfl
    · simp [map_prod]
  · simp

private theorem map_mem_diagSLSub {K : Type} [Field K] {n q : ℕ}
    (σ : K ≃+* K) {g : SpecialLinearGroup (Fin (n + 1)) K} (hg : g ∈ diagSLSub n q) :
    SpecialLinearGroup.map σ.toRingHom g ∈ diagSLSub n q := by
  obtain ⟨e, rfl⟩ := hg
  rw [map_diagSLMat]
  exact ⟨_, rfl⟩

private theorem field_fixes_diagSLSub_torsion {K : Type} [Field K] {n q r k : ℕ}
    (hr : r.Prime) (σ : K ≃+* K) (hσ : σ ^ (r ^ k) = 1)
    {g : SpecialLinearGroup (Fin (n + 1)) K} (hg : g ∈ diagSLSub n q) (hgr : g ^ r = 1) :
    SpecialLinearGroup.map σ.toRingHom g = g := by
  obtain ⟨e, rfl⟩ := hg
  apply Subtype.ext
  change (Matrix.diagonal fun i => (diagEntry e i : K)).map σ = _
  ext i j
  simp only [diagSLMat, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst j
    apply CFSG.StandardType.fieldAut_fixes_pow_eq_one hr hσ
    have hm := congrArg (fun A : SpecialLinearGroup (Fin (n + 1)) K =>
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) hgr
    change (Matrix.diagonal fun i => (diagEntry e i : K)) ^ r = 1 at hm
    rw [Matrix.diagonal_pow] at hm
    have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) K => A i i) hm
    simpa using h
  · simp

private theorem linearAutGroup_eq_inner_four {K : Type} [Field K] [Finite K] [CharP K 2] :
    linearAutGroup 4 K = (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  apply le_antisymm
  · rintro α hα
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hα
    have hi : Function.Injective (fun u : Kˣ => u ^ 4) := by
      intro u v huv
      change u ^ 4 = v ^ 4 at huv
      have h : ((u * v⁻¹ : Kˣ) : K) ^ 4 = 1 := by
        have h4 : (u * v⁻¹) ^ 4 = 1 := by rw [mul_pow, huv, inv_pow, mul_inv_cancel]
        exact congrArg Units.val h4
      have hsq : ((u * v⁻¹ : Kˣ) : K) ^ 2 = 1 := CharTwo.sq_injective (by
        change (((u * v⁻¹ : Kˣ) : K) ^ 2) ^ 2 = (1 : K) ^ 2
        rw [← pow_mul]
        simpa using h)
      have h1 : ((u * v⁻¹ : Kˣ) : K) = 1 := CharTwo.sq_injective (by simpa using hsq)
      exact mul_inv_eq_one.mp (Units.ext h1)
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hi (GeneralLinearGroup.det A)
    exact conjAut_mem_range_conj_of_det_eq_pow hu.symm
  · exact (standard_outer_quotients (n := 4) (K := K)).1

private theorem exists_diagonal_sylow_four {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hrq : r ∣ Nat.card K - 1) :
    ∃ S₀ : Subgroup (projectiveSL 4 K), IsPGroup r S₀ ∧ ¬ r ∣ S₀.index ∧
      (∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) ∧
      (∀ σ : K ≃+* K, ∀ x ∈ S₀, fieldAut 4 K σ x ∈ S₀) ∧
      ∀ (σ : K ≃+* K) (k : ℕ), σ ^ (r ^ k) = 1 →
        ∀ x ∈ S₀, x ^ r = 1 → fieldAut 4 K σ x = x := by
  have : Fact r.Prime := ⟨hr⟩
  let a := (Nat.card K - 1).factorization r
  let q := r ^ a
  have : NeZero q := ⟨pow_ne_zero _ hr.ne_zero⟩
  let D : Subgroup (SpecialLinearGroup (Fin 4) K) := diagSLSub 3 q
  let S₀ : Subgroup (projectiveSL 4 K) := D.map (proj 4 K)
  have hq : q ∣ Nat.card K - 1 := Nat.ordProj_dvd _ _
  have hDcard : Nat.card D = r ^ (3 * a) := by
    rw [card_diagSLSub hq]
    change (r ^ a) ^ 3 = _
    rw [← pow_mul, mul_comm a 3]
  have hDp : IsPGroup r D := IsPGroup.of_card hDcard
  have hS₀p : IsPGroup r S₀ := hDp.map _
  have hS₀card : Nat.card S₀ = r ^ (Nat.card (projectiveSL 4 K)).factorization r := by
    rw [Subgroup.card_map_of_injective CFSG.SeitzReduction.LinearPilot.proj_four_injective,
      hDcard]
    let e : SpecialLinearGroup (Fin 4) K ≃* projectiveSL 4 K :=
      MulEquiv.ofBijective (proj 4 K)
        ⟨CFSG.SeitzReduction.LinearPilot.proj_four_injective, proj_surjective 4 K⟩
    rw [← Nat.card_congr e.toEquiv, factorization_card_sl_four hr hr7 hrq]
  have hS₀i : ¬ r ∣ S₀.index := by
    exact (Sylow.ofCard S₀ hS₀card).not_dvd_index
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have : IsMulCommutative D := isElemAbelian_diagSLSub.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : D) ⟨b, hb⟩)
  refine ⟨S₀, hS₀p, hS₀i, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hDc a ha b hb]
  · rintro σ _ ⟨g, hg, rfl⟩
    rw [fieldAut_proj]
    exact Subgroup.mem_map_of_mem _ (map_mem_diagSLSub σ hg)
  · rintro σ k hσ _ ⟨g, hg, rfl⟩ hgr
    have hgr' : g ^ r = 1 := CFSG.SeitzReduction.LinearPilot.proj_four_injective (by
      rw [map_pow, hgr, map_one])
    rw [fieldAut_proj, field_fixes_diagSLSub_torsion hr σ hσ hg hgr']

private theorem exists_field_sylow_four {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) :
    ∃ (σ : K ≃+* K) (k : ℕ), σ ^ (r ^ k) = 1 ∧
      ¬ r ∣ ((MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ⊔
        zpowers (fieldAut 4 K σ)).index := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : IsCyclic (RingAut K) := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_ringAut K
  obtain ⟨P⟩ : Nonempty (Sylow r (RingAut K)) := inferInstance
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := (P : Subgroup (RingAut K)))
  have hPgen : (P : Subgroup (RingAut K)) = zpowers (σ : RingAut K) := by
    have hgen : zpowers σ = (⊤ : Subgroup (P : Subgroup (RingAut K))) :=
      top_unique (fun x _ => hσ x)
    have hmap := congrArg (Subgroup.map (P : Subgroup (RingAut K)).subtype) hgen
    simpa only [MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subtype_apply] using hmap.symm
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hσk : (σ : RingAut K) ^ (r ^ k) = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := (P : Subgroup (RingAut K))) (x := σ))
    change (σ : RingAut K) ^ Nat.card (P : Subgroup (RingAut K)) = 1 at h
    rwa [hk] at h
  let I : Subgroup (MulAut (projectiveSL 4 K)) :=
    (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range
  have : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  let F : Subgroup (MulAut (projectiveSL 4 K)) := (fieldAut 4 K).range
  let P' : Subgroup (MulAut (projectiveSL 4 K)) := (P : Subgroup (RingAut K)).map (fieldAut 4 K)
  let E := semilinearAutGroup 4 K
  have hE : I ⊔ F = E := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact ((standard_outer_quotients (n := 4) (K := K)).1).trans (by
          intro x hx
          exact Subgroup.subset_closure (Or.inl hx))
      · rintro _ ⟨σ, rfl⟩
        exact fieldAut_mem_semilinearAutGroup σ
    · intro x hx
      obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hx
      have hA : conjAut 4 K A ∈ I := by
        change conjAut 4 K A ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range
        rw [← linearAutGroup_eq_inner_four]
        exact conjAut_mem_linearAutGroup A
      exact mul_mem (Subgroup.mem_sup_left hA) (Subgroup.mem_sup_right ⟨σ, rfl⟩)
  let N := I ⊔ P'
  have hNE : N ≤ E := by
    rw [← hE]
    exact sup_le le_sup_left ((Subgroup.map_le_range _ _).trans le_sup_right)
  let π : MulAut (projectiveSL 4 K) →* (MulAut (projectiveSL 4 K) ⧸ I) := QuotientGroup.mk' I
  let ψ := π.comp (fieldAut 4 K)
  have hrel : N.relIndex E = ((P : Subgroup (RingAut K)) ⊔ ψ.ker).index := by
    have h := Subgroup.relIndex_map_map π N E
    have hIker : π.ker = I := QuotientGroup.ker_mk' _
    have hImap : I.map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [hIker])
    rw [hIker, show N ⊔ I = N from sup_eq_left.mpr le_sup_left,
      show E ⊔ I = E from sup_eq_left.mpr (by rw [← hE]; exact le_sup_left)] at h
    rw [← h, show N = I ⊔ P' from rfl, ← hE, Subgroup.map_sup, Subgroup.map_sup,
      hImap, bot_sup_eq, bot_sup_eq, Subgroup.map_map]
    have hFmap : F.map π = ψ.range := (MonoidHom.range_comp π (fieldAut 4 K)).symm
    rw [hFmap]
    change ((P : Subgroup (RingAut K)).map ψ).relIndex ψ.range = _
    rw [← Subgroup.map_top ψ, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  have hrelr : ¬ r ∣ N.relIndex E := by
    rw [hrel]
    exact fun hd => P.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le le_sup_left))
  have hEi : E.index ≤ 2 := by
    have h := (standard_outer_quotients (n := 4) (K := K)).2.2.2.2.2.2.2.1
    change E.relIndex (standardAutGroup 4 K) ≤ 2 at h
    rw [(automorphism_generation (n := 4) (K := K) (by norm_num)).1,
      Subgroup.relIndex_top_right] at h
    exact h
  have hEr : ¬ r ∣ E.index := fun hd => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero E.index_ne_zero_of_finite) hd
    omega
  have hNr : ¬ r ∣ N.index := by
    rw [← Subgroup.relIndex_mul_index hNE]
    exact fun hd => (hr.dvd_mul.mp hd).elim hrelr hEr
  refine ⟨σ, k, hσk, ?_⟩
  have hP' : P' = zpowers (fieldAut 4 K (σ : RingAut K)) := by
    change (P : Subgroup (RingAut K)).map (fieldAut 4 K) = _
    have hmap := congrArg (Subgroup.map (fieldAut 4 K)) hPgen
    exact hmap.trans (MonoidHom.map_zpowers (fieldAut 4 K) (σ : RingAut K))

  simpa only [N, hP'] using hNr

theorem sylow_torsion_fixed_projectiveSL_four {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hrq : r ∣ Nat.card K - 1)
    (R : Sylow r (projectiveSL 4 K)) (α : MulAut (projectiveSL 4 K))
    (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαR : ∀ x ∈ (R : Subgroup (projectiveSL 4 K)), α x ∈ (R : Subgroup (projectiveSL 4 K))) :
    ∀ x ∈ (R : Subgroup (projectiveSL 4 K)), x ^ r = 1 → α x = x := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S₀, hS₀p, hS₀i, hS₀c, hS₀σ, hS₀fix⟩ := exists_diagonal_sylow_four hr hr7 hrq
  obtain ⟨σ, k, hσ, hi⟩ := exists_field_sylow_four (K := K) hr hr7
  have hφ : (fieldAut 4 K σ) ^ (r ^ k) = 1 := by rw [← map_pow, hσ, map_one]
  exact CFSG.apply_eq_self_of_pow_eq_one hS₀p hS₀i hS₀c ⟨k, hφ⟩ (hS₀σ σ) hi
    (hS₀fix σ k hσ) R.isPGroup' R.not_dvd_index hα hαR

theorem sylow_torsion_fixed_of_lieModel_psl_four
    {X : Type} [Group X] [Finite X] {f r : ℕ}
    (hX : LieModel X .PSL 4 2 f) (hr : r.Prime) (hr7 : 7 ≤ r)
    (hrq : r ∣ 2 ^ f - 1) (R : Sylow r X) (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ (r ^ k) = 1)
    (hαR : ∀ x ∈ (R : Subgroup X), α x ∈ (R : Subgroup X)) :
    ∀ x ∈ (R : Subgroup X), x ^ r = 1 → α x = x := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let α' := MulAut.congr e α
  have hR' : (R' : Subgroup (projectiveSL 4 K)) = (R : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective R
  have hα' : ∃ k : ℕ, α' ^ (r ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hαR' : ∀ x ∈ (R' : Subgroup (projectiveSL 4 K)), α' x ∈ (R' : Subgroup (projectiveSL 4 K)) := by
    rw [hR']
    rintro _ ⟨x, hx, rfl⟩
    have ha : α' (e x) = e (α x) := by simp [α', MulAut.congr_apply]
    have hmem := Subgroup.mem_map_of_mem e.toMonoidHom (hαR x hx)
    simpa only [MulEquiv.coe_toMonoidHom, ha] using hmem
  have h := sylow_torsion_fixed_projectiveSL_four hr hr7 (hK ▸ hrq) R' α' hα' hαR'
  intro x hx hxr
  apply e.injective
  have hexR : e x ∈ (R' : Subgroup (projectiveSL 4 K)) := by
    rw [hR']
    exact Subgroup.mem_map_of_mem _ hx
  have hfix := h (e x) hexR (by rw [← map_pow, hxr, map_one])
  simpa [α', MulAut.congr_apply] using hfix


end CFSG.LocalAnalysis.UniquenessCase.UC22
