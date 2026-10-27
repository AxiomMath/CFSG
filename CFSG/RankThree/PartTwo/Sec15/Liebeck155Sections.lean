module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenDefs
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
import CFSG.RankThree.SubgroupLists.CentralizerPerfect
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3IrrRed
import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearModelSchreier
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
import CFSG.Adapters.RankThreeOutcomesReverse
import CFSG.Adapters.LieModelSimple
import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.Quasithin.EmptyFaithful.S152He9A5
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.BenderSuzuki.MatrixGroups (PSL2MatrixGroup)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_classical_model_schreier linear_higher_classical_model_schreier
    unitary_classical_model_schreier)
open Matrix
open scoped MatrixGroups

private theorem exists_perfect_map_eq_top {G Q : Type*} [Group G] [Finite G] [Group Q]
    [Group.IsPerfect Q] (θ : G →* Q) (hθ : Function.Surjective θ) :
    ∃ D : Subgroup G, Group.IsPerfect D ∧ D.map θ = ⊤ := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, derivedSeries G (n + 1) = derivedSeries G n := by
    obtain ⟨a, b, hab, hfab⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => derivedSeries G n)
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, le_antisymm (derivedSeries_antitone G (Nat.le_succ a))
        (hfab.le.trans (derivedSeries_antitone G (Nat.succ_le_of_lt h)))⟩
    · exact ⟨b, le_antisymm (derivedSeries_antitone G (Nat.le_succ b))
        (hfab.ge.trans (derivedSeries_antitone G (Nat.succ_le_of_lt h)))⟩
  refine ⟨derivedSeries G n, Subgroup.isPerfect_iff.mpr (by rw [← derivedSeries_succ, hn]), ?_⟩
  rw [map_derivedSeries_eq hθ, Group.IsPerfect.derivedSeries_eq_top]

private def InList (e : ℕ) (K : Type) [Group K] : Prop :=
  (∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
    StatedClassicalModel K .PSL 2 3 2 ∨
    (∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧
      (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt K 2 f))

private theorem InList.of_mulEquiv {e : ℕ} {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')
    (h : InList e K) : InList e K' := by
  rcases h with ⟨j, hj, hm⟩ | hm | ⟨f, hf, hfe, hL⟩
  · exact Or.inl ⟨j, hj, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv φ hm⟩
  · exact Or.inr (Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv φ hm))
  · refine Or.inr (Or.inr ⟨f, hf, hfe, ?_⟩)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hL with ⟨⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨φ.symm.trans ψ⟩
    · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩

private theorem outer_solvable_of_inList {e : ℕ} {K : Type} [Group K] (h : InList e K) :
    Group.IsSolvable (Outer K) := by
  rcases h with ⟨j, -, hj⟩ | h9 | ⟨f, hf, -, hL⟩
  · exact (linear_two_classical_model_schreier hj).2
  · exact (linear_two_classical_model_schreier h9).2
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hL with ⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact (linear_higher_classical_model_schreier (by norm_num)
        (CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL
          ⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩ φ)).2
    · refine (unitary_classical_model_schreier
        (CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSU
          ⟨Nat.prime_two, hf, by norm_num, fun h => ?_⟩ φ)).2
      have h2 : 2 ^ f = 2 := by simpa using congrArg Prod.snd h
      omega

private theorem eq_one_of_finrank_eq_one {F : Type*} [Field F] {E : Type*} [AddCommGroup E]
    [Module F E] (hE : Module.finrank F E = 1) {Y : Type*} [Group Y] [Group.IsPerfect Y]
    (χ : Y →* (Module.End F E)ˣ) (y : Y) : χ y = 1 := by
  have hcomm : ∀ a b : (Module.End F E)ˣ, a * b = b * a := by
    intro a b
    apply Units.ext
    obtain ⟨c, hc, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hE (a : Module.End F E)
    obtain ⟨d, hd, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hE (b : Module.End F E)
    rw [Units.val_mul, Units.val_mul, hc, hd]
    ext v
    simp [smul_smul, mul_comm]
  have hle : commutator Y ≤ χ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hy : y ∈ commutator Y := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top y
  exact (MonoidHom.mem_ker).mp (hle hy)

private theorem statedClassicalModel_of_sl2_perfect {F : Type}
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {S : Type}
    [Group S] [Group.IsPerfect S] [Nontrivial S] {P : Subgroup SL(2, F)} (φ : S ≃* P) :
    ∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel S .PSL 2 2 j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hns : ¬ Group.IsSolvable S := Group.IsPerfect.not_isSolvable S
  let σ : SL(2, F) ≃* PSL2MatrixGroup F :=
    (CFSG.RankThree.projectiveSpecialLinearTwoEquivSLOfCharTwo F).symm
  set Q : Subgroup (PSL2MatrixGroup F) := P.map σ.toMonoidHom with hQ
  let ψ : S ≃* Q := φ.trans (Subgroup.equivMapOfInjective P σ.toMonoidHom σ.injective)
  have hcase : ∀ m : ℕ, 1 ≤ m → Nonempty (S ≃* PSL2MatrixGroup (GaloisField 2 m)) →
      ∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel S .PSL 2 2 j := by
    rintro m hm ⟨χ⟩
    have hm2 : 2 ≤ m := by
      by_contra hm2
      have hm1 : m = 1 := by omega
      subst hm1
      apply hns
      have hc := CFSG.GH74.Uniqueness.Bender.card_psl2_even 1 le_rfl
      have := Fintype.ofFinite (PSL2MatrixGroup (GaloisField 2 1))
      have hsolv : Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 1)) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
      exact Group.isSolvable_of_surjective (f := χ.symm.toMonoidHom) χ.symm.surjective
    refine ⟨m, hm2, ⟨Nat.prime_two, hm, le_rfl, ?_, ?_⟩, GaloisField 2 m, inferInstance,
      inferInstance, GaloisField.card 2 m (by omega),
      ⟨χ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 m))⟩⟩
    · intro h
      have h2 : 2 ^ m = 2 ^ 1 := by simpa using congrArg Prod.snd h
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    · intro h
      have h2 : 2 ^ m = 3 := by simpa using congrArg Prod.snd h
      have : 2 ∣ 3 := h2 ▸ dvd_pow_self 2 (by omega)
      omega
  rcases CFSG.GH74.GLS.IVK.Lifted.psl2_subgroup_dichotomy hF Q with hsol | hA5 | ⟨m, hm, ⟨χ⟩⟩ |
      ⟨m, hm, ⟨χ⟩⟩
  · exact absurd (Group.isSolvable_of_surjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective) hns
  · obtain ⟨χ⟩ := hA5
    obtain ⟨ε⟩ := CFSG.Quasithin.He9.nonempty_psl2_gf4_mulEquiv_alternating
    exact hcase 2 (by norm_num) ⟨(ψ.trans χ).trans ε.symm⟩
  · have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        have := Nat.eq_zero_of_zero_dvd hm
        omega
      · exact h
    exact hcase m hm1 ⟨ψ.trans χ⟩
  · have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        rw [mul_zero] at hm
        have := Nat.eq_zero_of_zero_dvd hm
        omega
      · exact h
    obtain ⟨ε⟩ := CFSG.GH74.Uniqueness.Bender.nonempty_pgl2_mulEquiv_psl2 m hm1
    exact hcase m hm1 ⟨(ψ.trans χ).trans ε⟩

private theorem reducible_case {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {D : Subgroup (GL (Fin 3) F)}
    [Group.IsPerfect D] {Q : Type} [Group Q] [Nontrivial Q] (θ : D →* Q)
    (hθ : Function.Surjective θ) (hQ : CFSG.pCore 2 Q = ⊥) {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ D, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) (hW0 : W ≠ ⊥)
    (hWt : W ≠ ⊤) : IsSimpleGroup Q ∧ ∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel Q .PSL 2 2 j := by
  have hinv : ∀ g ∈ D, ∀ v ∈ W, Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F) v ∈ W :=
    fun g hg v hv => by rw [Matrix.toLin'_apply]; exact hW g hg v hv
  let baseW : D →* Module.End F W :=
    { toFun := fun g => (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict
        (hinv g g.2)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [Matrix.mulVec_mulVec] }
  let baseQ : D →* Module.End F ((Fin 3 → F) ⧸ W) :=
    { toFun := fun g => W.mapQ W (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        (fun v hv => hinv g g.2 v hv)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp }
  have hdim := Submodule.finrank_quotient_add_finrank W
  rw [Module.finrank_fin_fun] at hdim
  have hW1 : Module.finrank F W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hW3 : Module.finrank F W < 3 := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  have hsq : ∀ g : D, baseW.toHomUnits g = 1 → baseQ.toHomUnits g = 1 → g * g = 1 := by
    intro g h1 h2
    set gm : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgm
    have hfixW : ∀ v ∈ W, gm *ᵥ v = v := by
      intro v hv
      have h3 := congrArg (fun u : (Module.End F W)ˣ => ((u : Module.End F W) ⟨v, hv⟩ : Fin 3 → F))
        h1
      simpa [baseW] using h3
    have hfixQ : ∀ v : Fin 3 → F, gm *ᵥ v - v ∈ W := by
      intro v
      have h3 := congrArg (fun u : (Module.End F ((Fin 3 → F) ⧸ W))ˣ =>
        ((u : Module.End F ((Fin 3 → F) ⧸ W)) (W.mkQ v))) h2
      simp only [MonoidHom.toHomUnits, baseQ, Units.val_one, Module.End.one_apply] at h3
      change W.mkQ (Matrix.toLin' gm v) = W.mkQ v at h3
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
        Matrix.toLin'_apply] at h3
      exact h3
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have h1 := hfixW _ (hfixQ v)
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [Matrix.mulVec_sub] at h1
    have h3 : gm *ᵥ (gm *ᵥ v) = (2 : F) • (gm *ᵥ v) - v := by
      rw [sub_eq_iff_eq_add] at h1
      rw [h1, two_smul]
      abel
    change Matrix.toLin' (gm * gm) v = Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) F) v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h3, h2, zero_smul,
      zero_sub, Matrix.one_mulVec]
    funext i
    exact CharTwo.neg_eq _
  let U : Subgroup D := baseW.toHomUnits.ker ⊓ baseQ.toHomUnits.ker
  have hUn : U.Normal := inferInstance
  have hUθ : U ≤ θ.ker := by
    have hTn : (U.map θ).Normal := Subgroup.Normal.map hUn θ hθ
    have hT : IsPGroup 2 (U.map θ) := by
      intro t
      obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp t.2
      refine ⟨1, Subtype.ext ?_⟩
      have h1 := hsq u hu.1 hu.2
      calc ((t ^ 2 ^ 1 : U.map θ) : Q) = (t : Q) ^ 2 := by simp
        _ = θ (u * u) := by rw [map_mul, hut, sq]
        _ = 1 := by rw [h1, map_one]
    have hle : U.map θ ≤ CFSG.pCore 2 Q := le_sSup ⟨hTn, hT⟩
    rw [hQ] at hle
    intro g hg
    exact Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem θ hg))
  have hrep : ∀ (E : Type) [AddCommGroup E] [Module F E], Module.finrank F E = 2 →
      ∀ ρ : D →* (Module.End F E)ˣ, ρ.ker ≤ U →
      IsSimpleGroup Q ∧ ∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel Q .PSL 2 2 j := by
    intro E _ _ hE ρ hρU
    have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
    let b := Module.finBasisOfFinrankEq F E hE
    let τ : (Module.End F E)ˣ ≃* GL (Fin 2) F :=
      Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
    let ρ' : D →* GL (Fin 2) F := τ.toMonoidHom.comp ρ
    have hker : ρ'.ker ≤ θ.ker := by
      intro g hg
      refine hUθ (hρU ?_)
      rw [MonoidHom.mem_ker] at hg ⊢
      exact τ.injective (by simpa [ρ'] using hg)
    obtain ⟨P, ⟨φ⟩⟩ := SubgroupLists.exists_sl2_copy_of_perfect (QuotientGroup.kerLift ρ')
      (QuotientGroup.kerLift_injective ρ')
    let θ' : D ⧸ ρ'.ker →* Q := QuotientGroup.lift ρ'.ker θ hker
    have hθ' : Function.Surjective θ' := by
      intro q
      obtain ⟨g, rfl⟩ := hθ q
      exact ⟨QuotientGroup.mk g, rfl⟩
    haveI : Nontrivial (D ⧸ ρ'.ker) := hθ'.nontrivial
    obtain ⟨j, hj, hM⟩ := statedClassicalModel_of_sl2_perfect hF hn φ
    haveI hSs : IsSimpleGroup (D ⧸ ρ'.ker) :=
      CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hM
    have hinj : Function.Injective θ' :=
      CFSG.GH74.GLS.IVK.Lifted.injective_of_surjective_simple θ' hθ'
    let ε : D ⧸ ρ'.ker ≃* Q := MulEquiv.ofBijective θ' ⟨hinj, hθ'⟩
    exact ⟨MulEquiv.isSimpleGroup ε.symm, j, hj,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ε hM⟩
  rcases (by omega : Module.finrank F W = 1 ∨ Module.finrank F W = 2) with h1 | h2
  ·
    have hWt : ∀ g : D, baseW.toHomUnits g = 1 := eq_one_of_finrank_eq_one h1 _
    exact hrep _ (by omega) baseQ.toHomUnits fun g hg => ⟨hWt g, hg⟩
  ·
    have hQt : ∀ g : D, baseQ.toHomUnits g = 1 :=
      eq_one_of_finrank_eq_one (by omega) _
    exact hrep _ h2 baseW.toHomUnits fun g hg => ⟨hg, hQt g⟩

private theorem exists_lift {F : Type} [Field F] [Finite F] {Hm : Subgroup (GL (Fin 3) F)}
    {X : Type} [Group X] (σ : ↥Hm →* X) (hσs : Function.Surjective σ) {Q : Type} [Group Q]
    [Group.IsPerfect Q] (H : Subgroup X) (N : Subgroup H) [N.Normal] (e : Q ≃* ↥H ⧸ N) :
    ∃ (D : Subgroup (GL (Fin 3) F)) (hDH : D ≤ Hm), Group.IsPerfect ↥D ∧
      ∃ θ : ↥D →* Q, Function.Surjective θ ∧
        ∀ z : ↥D, σ (Subgroup.inclusion hDH z) = 1 → θ z = 1 := by
  classical
  set Ĥ : Subgroup ↥Hm := H.comap σ with hĤ
  let ξ : ↥Ĥ →* ↥H := (σ.comp Ĥ.subtype).codRestrict H fun x => x.2
  let θ₀ : ↥Ĥ →* Q := e.symm.toMonoidHom.comp ((QuotientGroup.mk' N).comp ξ)
  have hθ₀ : Function.Surjective θ₀ := by
    intro q
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (e q)
    obtain ⟨y, hy⟩ := hσs (h : X)
    have hyĤ : y ∈ Ĥ := by
      rw [hĤ, Subgroup.mem_comap, hy]
      exact h.2
    refine ⟨⟨y, hyĤ⟩, ?_⟩
    have hξ : ξ ⟨y, hyĤ⟩ = h := Subtype.ext hy
    change e.symm (QuotientGroup.mk' N (ξ ⟨y, hyĤ⟩)) = q
    rw [hξ]
    change e.symm (QuotientGroup.mk h) = q
    rw [hh, MulEquiv.symm_apply_apply]
  obtain ⟨D₀, hD₀, hmap⟩ := exists_perfect_map_eq_top θ₀ hθ₀
  set D₁ : Subgroup ↥Hm := D₀.map Ĥ.subtype with hD₁
  set D : Subgroup (GL (Fin 3) F) := D₁.map Hm.subtype with hD
  let ι : ↥D₀ ≃* ↥D :=
    (D₀.equivMapOfInjective Ĥ.subtype Ĥ.subtype_injective).trans
      (D₁.equivMapOfInjective Hm.subtype Hm.subtype_injective)
  have hDH : D ≤ Hm := Subgroup.map_subtype_le _
  refine ⟨D, hDH, ?_, (θ₀.comp D₀.subtype).comp ι.symm.toMonoidHom, ?_, ?_⟩
  · haveI := hD₀
    exact Group.IsPerfect.ofSurjective (f := ι.toMonoidHom) ι.surjective
  · have hs : Function.Surjective (θ₀.comp D₀.subtype) := by
      intro q
      have hq : q ∈ D₀.map θ₀ := by rw [hmap]; trivial
      obtain ⟨d, hd, hdq⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨d, hd⟩, hdq⟩
    exact hs.comp ι.symm.surjective
  · intro z hz
    obtain ⟨d, rfl⟩ := ι.surjective z
    have hincl : Subgroup.inclusion hDH (ι d) = ((d : ↥Ĥ) : ↥Hm) := Subtype.ext rfl
    rw [hincl] at hz
    have hξ : ξ (d : ↥Ĥ) = 1 := Subtype.ext hz
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    change e.symm (QuotientGroup.mk' N (ξ (d : ↥Ĥ))) = 1
    rw [hξ, map_one, map_one]

private theorem irreducible_case {F : Type} [Field F] [Finite F] {Hm : Subgroup (GL (Fin 3) F)}
    {X : Type} [Group X] (σ : ↥Hm →* X)
    (hσ : ∀ z : ↥Hm, σ z = 1 ↔
      ∃ c : F, ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c)
    {D : Subgroup (GL (Fin 3) F)} (hDH : D ≤ Hm) [Group.IsPerfect D]
    (hirr : SubgroupLists.IsIrreducibleOn D) {Q : Type} [Group Q] [Nontrivial Q] (θ : D →* Q)
    (hθ : Function.Surjective θ) (hker : ∀ z : ↥D, σ (Subgroup.inclusion hDH z) = 1 → θ z = 1)
    {e : ℕ}
    (hS : ∀ K : Subgroup X, IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → InList e K) :
    IsSimpleGroup Q ∧ InList e Q := by
  classical
  have hDnt : Nontrivial D := hθ.nontrivial
  have hnsolv : ¬ Group.IsSolvable D := Group.IsPerfect.not_isSolvable D
  rcases CFSG.Quasithin.A312U3.solvable_or_quasisimple_gl3
      (SubgroupLists.isIrreducibleOn_iff.mp hirr) with hsolv | ⟨L, hLD, hLn, hLq, -, hLcomm, -, -⟩
  · exact absurd hsolv hnsolv
  have hLH : L ≤ Hm := hLD.trans hDH
  let ΦL : ↥L →* X := σ.comp (Subgroup.inclusion hLH)
  have hΦL : ∀ x : ↥L, ΦL x = 1 ↔ x ∈ Subgroup.center ↥L := by
    intro x
    change σ (Subgroup.inclusion hLH x) = 1 ↔ _
    rw [hσ]
    constructor
    · rintro ⟨c, hc⟩
      exact SubgroupLists.mem_center_of_scalar hc
    · intro hx
      obtain ⟨c, hc⟩ := hLcomm ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) fun y hy => by
        have := Subgroup.mem_center_iff.mp hx ⟨y, hy⟩
        have h2 := congrArg (fun w : ↥L => ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) this
        simpa using h2
      exact ⟨c, hc⟩
  have hkerΦ : ΦL.ker = Subgroup.center ↥L := by
    ext x
    exact hΦL x
  haveI hLsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2.1
  let eR : ↥L ⧸ Subgroup.center ↥L ≃* ↥ΦL.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerΦ.symm).trans (QuotientGroup.quotientKerEquivRange ΦL)
  have hKs : IsSimpleGroup ↥ΦL.range := MulEquiv.isSimpleGroup eR.symm
  have hKn : ∃ a b : ↥ΦL.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLq.2.2
    exact ⟨eR a, eR b, fun h => hab (eR.injective (by rw [map_mul, map_mul, h]))⟩
  have hlist : InList e ↥ΦL.range := hS _ hKs hKn
  have hOutK : Group.IsSolvable (Outer ↥ΦL.range) := outer_solvable_of_inList hlist
  haveI : Group.IsPerfect ↥L := hLq.1
  haveI : Group.IsSolvable (Outer (↥L ⧸ Subgroup.center ↥L)) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eR.symm).2.mp hOutK
  have hOutL : Group.IsSolvable (Outer ↥L) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥L
  have hHN : D ≤ Subgroup.normalizer (L : Set (GL (Fin 3) F)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hLn g hg x hx, fun hx => ?_⟩
    have h1 := hLn g⁻¹ (D.inv_mem hg) _ hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1
  have hK : Group.IsSolvable ↥(Subgroup.centralizer (L : Set (GL (Fin 3) F)) ⊓ D) := by
    apply Group.isSolvable_of_comm
    intro a b
    have hsc : ∀ c : ↥(Subgroup.centralizer (L : Set (GL (Fin 3) F)) ⊓ D),
        ∃ r : F, ((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) r := by
      intro c
      refine hLcomm _ fun y hy => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp c.2.1 y hy
      simpa using congrArg (fun w : GL (Fin 3) F => (w : Matrix (Fin 3) (Fin 3) F)) h1
    obtain ⟨r, hr⟩ := hsc a
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hr]
    exact (Matrix.scalar_commute r (fun r' => Commute.all r r') _).eq
  have hDL : D ≤ L := CFSG.SeitzReduction.perfect_le_of_isSolvable_outer hOutL hLD hHN hK
    (Subgroup.isPerfect_iff.mp ‹Group.IsPerfect ↥D›) le_rfl
  have hLeq : L = D := le_antisymm hLD hDL
  subst hLeq
  have hcent : Subgroup.center ↥L ≤ θ.ker := fun z hz => hker z ((hΦL z).mpr hz)
  let θ' : ↥L ⧸ Subgroup.center ↥L →* Q := QuotientGroup.lift _ θ hcent
  have hθ' : Function.Surjective θ' := by
    intro q
    obtain ⟨g, rfl⟩ := hθ q
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hinj : Function.Injective θ' :=
    CFSG.GH74.GLS.IVK.Lifted.injective_of_surjective_simple θ' hθ'
  let ε : ↥L ⧸ Subgroup.center ↥L ≃* Q := MulEquiv.ofBijective θ' ⟨hinj, hθ'⟩
  exact ⟨MulEquiv.isSimpleGroup ε.symm, InList.of_mulEquiv (eR.symm.trans ε) hlist⟩

theorem evenPerfectSection_of (hS : Sec14.Ronan148T.EvenSimpleList) :
    ∀ (X : Type) [Group X] [Finite X] (e : ℕ), 1 ≤ e →
      (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; Sec4.IsoLThreePi X 2 e) →
      ∀ (Q : Type) [Group Q] [Finite Q] (H : Subgroup X) (N : Subgroup H) [N.Normal],
        Nonempty (Q ≃* ↥H ⧸ N) → Group.IsPerfect Q → Nontrivial Q → CFSG.pCore 2 Q = ⊥ →
        IsSimpleGroup Q ∧
        ((∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel Q .PSL 2 2 j) ∨
          StatedClassicalModel Q .PSL 2 3 2 ∨
          (∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧
            (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt Q 2 f))) := by
  intro X _ _ e he hiso Q _ _ H N _ hQe hperf hnt hQ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hperf
  haveI := hnt
  obtain ⟨eQ⟩ := hQe
  obtain ⟨π, F, _, hF, hq, ⟨φ⟩⟩ := Ronan148T.exists_slPi_quotient he hiso
  haveI := hF.finite
  haveI := Ronan148T.charP_of_piField hF
  obtain ⟨n, hn1, hnF⟩ : ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n := by
    cases π
    · refine ⟨2 * e, by omega, ?_⟩
      rw [hF.card]
      change (2 ^ e) ^ 2 = 2 ^ (2 * e)
      rw [← pow_mul, mul_comm]
    · exact ⟨e, he, hF.card⟩
  set Hm := Sec4.slPi π 3 (2 ^ e) F with hHm
  let σ : ↥Hm →* X := φ.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Hm))
  have hσs : Function.Surjective σ := φ.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hσ : ∀ z : ↥Hm, σ z = 1 ↔
      ∃ c : F, ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c := by
    intro z
    have h1 : σ z = 1 ↔ z ∈ Subgroup.center ↥Hm := by
      change φ.symm (QuotientGroup.mk z) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rw [h1, Ronan148T.mem_center_slPi_iff hF hq z, CFSG.Open.StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  obtain ⟨D, hDH, hDp, θ, hθ, hker⟩ := exists_lift σ hσs H N eQ
  haveI := hDp
  by_cases hirr : SubgroupLists.IsIrreducibleOn D
  · exact irreducible_case σ hσ hDH hirr θ hθ hker (hS X e he hiso)
  · unfold SubgroupLists.IsIrreducibleOn at hirr
    push Not at hirr
    obtain ⟨W, hW, hW0, hWt⟩ := hirr
    obtain ⟨hs, j, hj, hm⟩ := reducible_case hnF hn1 θ hθ hQ hW hW0 hWt
    exact ⟨hs, Or.inl ⟨j, hj, hm⟩⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck155
