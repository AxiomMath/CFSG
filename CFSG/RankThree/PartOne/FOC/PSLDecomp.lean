module

public import CFSG.RankThree.PartOne.FOC.PSLSetup
public import CFSG.RankThree.PartOne.S11d.LayerDecomp
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Matrix Subgroup CFSG
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCLinPlane
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Solvable

theorem isSolvable_pi_of_finite {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose k hk using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup k, ?_⟩⟩
  have hle : ∀ m : ℕ, derivedSeries (∀ i, G i) m ≤
      Subgroup.pi Set.univ (fun i => derivedSeries (G i) m) := by
    intro m
    induction m with
    | zero =>
      intro x _
      simp [Subgroup.mem_pi]
    | succ m ih =>
      simp only [derivedSeries_succ]
      exact (Subgroup.commutator_mono ih ih).trans (Subgroup.commutator_pi_pi_le _ _)
  rw [eq_bot_iff]
  intro x hx
  have hx' := hle _ hx
  rw [Subgroup.mem_pi] at hx'
  funext i
  have h1 : derivedSeries (G i) (Finset.univ.sup k) = ⊥ := by
    rw [eq_bot_iff]
    calc derivedSeries (G i) (Finset.univ.sup k) ≤ derivedSeries (G i) (k i) :=
          derivedSeries_antitone (G i) (Finset.le_sup (Finset.mem_univ i))
      _ = ⊥ := hk i
  have := hx' i (Set.mem_univ i)
  rw [h1, Subgroup.mem_bot] at this
  exact this

theorem isSolvable_GL_of_small {k : ℕ} {F : Type} [Field F] [Finite F]
    (h : k ≤ 1 ∨ (k = 2 ∧ Nat.card F ≤ 3)) : Group.IsSolvable (GL (Fin k) F) := by
  rcases h with hk | ⟨rfl, hF⟩
  · exact Group.isSolvable_of_comm (fun u v => commute_of_le_one hk u v)
  · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (by have : 2 ≤ Nat.card F := Finite.one_lt_card; omega)

theorem mem_center_of_commute_SL {k : ℕ} {F : Type} [Field F] (g : GL (Fin k) F)
    (h : ∀ s : Matrix.SpecialLinearGroup (Fin k) F,
      Matrix.SpecialLinearGroup.toGL s * g = g * Matrix.SpecialLinearGroup.toGL s) :
    g ∈ Subgroup.center (GL (Fin k) F) := by
  have hcomm : ∀ s : Matrix.SpecialLinearGroup (Fin k) F,
      Commute (s : Matrix (Fin k) (Fin k) F) (g : Matrix (Fin k) (Fin k) F) := by
    intro s
    have h2 := congrArg (fun u : GL (Fin k) F => (u : Matrix (Fin k) (Fin k) F)) (h s)
    exact (show (s : Matrix (Fin k) (Fin k) F) * (g : Matrix (Fin k) (Fin k) F) =
      (g : Matrix (Fin k) (Fin k) F) * s by simpa using h2)
  have hsc : (g : Matrix (Fin k) (Fin k) F) ∈ Set.range (Matrix.scalar (Fin k)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    exact hcomm ⟨t.toMatrix, t.det⟩
  exact GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hsc

end Solvable

section Decomp

open scoped _root_.Classical

variable {n : ℕ} {K : Type} [Field K] [Finite K] {A : Matrix.SpecialLinearGroup (Fin n) K}

instance finite_Efac {x : Module.End K (Fin n → K)} (a : primaryFactors x) : Finite (Efac x a) := by
  have : Module.Finite K (Efac x a) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finite
  exact Module.finite_of_finite K

@[expose] noncomputable def goodCentral (x : Module.End K (Fin n → K)) :
    Subgroup (PiGL (Efac x) (mult x)) :=
  ⨅ b : {b : primaryFactors x // GoodBlock b},
    (Subgroup.center (GL (Fin (mult x b.1)) (Efac x b.1))).comap
      (Pi.evalMonoidHom (fun c : primaryFactors x => GL (Fin (mult x c)) (Efac x c)) b.1)

omit [Finite K] in
theorem mem_goodCentral {x : Module.End K (Fin n → K)} {w : PiGL (Efac x) (mult x)} :
    w ∈ goodCentral x ↔ ∀ b : primaryFactors x, GoodBlock b →
      w b ∈ Subgroup.center (GL (Fin (mult x b)) (Efac x b)) := by
  simp only [goodCentral, Subgroup.mem_iInf, Subgroup.mem_comap, Pi.evalMonoidHom_apply,
    Subtype.forall]

theorem isSolvable_GL_of_not_good {x : Module.End K (Fin n → K)} {b : primaryFactors x}
    (hb : ¬ GoodBlock b) : Group.IsSolvable (GL (Fin (mult x b)) (Efac x b)) := by
  refine isSolvable_GL_of_small ?_
  unfold GoodBlock at hb
  omega

theorem isSolvable_goodCentral (x : Module.End K (Fin n → K)) :
    Group.IsSolvable ↥(goodCentral x) := by
  let ρ : ↥(goodCentral x) →*
      (∀ b : {b : primaryFactors x // ¬ GoodBlock b}, GL (Fin (mult x b.1)) (Efac x b.1)) :=
    { toFun := fun w b => (w : PiGL (Efac x) (mult x)) b.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have : ∀ b : {b : primaryFactors x // ¬ GoodBlock b},
      Group.IsSolvable (GL (Fin (mult x b.1)) (Efac x b.1)) := fun b =>
    isSolvable_GL_of_not_good b.2
  have hcodom : Group.IsSolvable
      (∀ b : {b : primaryFactors x // ¬ GoodBlock b}, GL (Fin (mult x b.1)) (Efac x b.1)) :=
    isSolvable_pi_of_finite
  have hker : Group.IsSolvable ↥ρ.ker := by
    refine Group.isSolvable_of_comm ?_
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    apply Subtype.ext
    apply Subtype.ext
    funext c
    show (u : PiGL (Efac x) (mult x)) c * (v : PiGL (Efac x) (mult x)) c =
      (v : PiGL (Efac x) (mult x)) c * (u : PiGL (Efac x) (mult x)) c
    by_cases hc : GoodBlock c
    · exact (Subgroup.mem_center_iff.mp ((mem_goodCentral.mp u.2) c hc) _).symm
    · have h1 : (u : PiGL (Efac x) (mult x)) c = 1 := congrFun (MonoidHom.mem_ker.mp hu) ⟨c, hc⟩
      rw [h1, one_mul, mul_one]
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (by
    intro w hw
    exact ⟨⟨w, hw⟩, rfl⟩)

theorem solvable_centralizer_Qb {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (scalars n K))
    (hAp : A ^ p = 1) (hsq : Squarefree (minpoly K (slEnd A))) :
    Group.IsSolvable ↥(Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K)) ⊓
      Subgroup.centralizer
        ((⨆ b : {b : primaryFactors (slEnd A) // GoodBlock b}, Qb hsq b.1 :
          Subgroup (projectiveSL n K)) : Set (projectiveSL n K))) := by
  set Ĝ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) :=
    Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) K)) ⊓
      ⨅ b : {b : primaryFactors (slEnd A) // GoodBlock b},
        Subgroup.centralizer (blkSL hsq b.1 : Set (Matrix.SpecialLinearGroup (Fin n) K))
    with hĜ
  have hS : Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K)) ⊓
      Subgroup.centralizer
        ((⨆ b : {b : primaryFactors (slEnd A) // GoodBlock b}, Qb hsq b.1 :
          Subgroup (projectiveSL n K)) : Set (projectiveSL n K)) ≤ Ĝ.map (proj n K) := by
    intro u hu
    obtain ⟨G, rfl, hAG⟩ := exists_lift_centralizer hp hZ hAp hu.1
    refine ⟨G, ⟨Subgroup.mem_centralizer_singleton_iff.mpr hAG.symm, ?_⟩, rfl⟩
    show G ∈ ⨅ b : {b : primaryFactors (slEnd A) // GoodBlock b},
      Subgroup.centralizer (blkSL hsq b.1 : Set (Matrix.SpecialLinearGroup (Fin n) K))
    rw [Subgroup.mem_iInf]
    intro b
    have hperf : Group.IsPerfect ↥(blkSL hsq b.1) := (blkSL_quasisimple b.2).1
    have hc := commute_of_commutator_central hperf (G := G) (fun q hq => by
      rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have h1 : proj n K q * proj n K G = proj n K G * proj n K q :=
        Subgroup.mem_centralizer_iff.mp hu.2 (proj n K q)
          (Subgroup.mem_iSup_of_mem b ⟨q, hq, rfl⟩)
      rw [← h1]
      group)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hc q hq).symm
  have hmemΘ : ∀ g ∈ Ĝ, Matrix.SpecialLinearGroup.toGL g ∈ (blockTheta hsq).range := by
    intro g hg
    rw [range_blockTheta, range_commutantUnitsToGL_eq_centralizer (x := slEnd A)
      (Matrix.SpecialLinearGroup.toGL A) rfl]
    exact toGL_mem_centralizer hg.1
  let φ' : Ĝ →* ↥(blockTheta hsq).range :=
    ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) K →* GL (Fin n) K).comp
      Ĝ.subtype).codRestrict (blockTheta hsq).range (fun g => hmemΘ g g.2)
  let e : PiGL (Efac (slEnd A)) (mult (slEnd A)) ≃* ↥(blockTheta hsq).range :=
    MonoidHom.ofInjective (blockTheta_injective hsq)
  let ι0 : Ĝ →* PiGL (Efac (slEnd A)) (mult (slEnd A)) := e.symm.toMonoidHom.comp φ'
  have hι : ∀ g : Ĝ, blockTheta hsq (ι0 g) = Matrix.SpecialLinearGroup.toGL (g : Matrix.SpecialLinearGroup (Fin n) K) := by
    intro g
    have h1 : e (ι0 g) = φ' g := e.apply_symm_apply (φ' g)
    exact congrArg Subtype.val h1
  have hιgood : ∀ g : Ĝ, ι0 g ∈ goodCentral (slEnd A) := by
    intro g
    rw [mem_goodCentral]
    intro b hb
    refine mem_center_of_commute_SL _ (fun s => ?_)
    have hmemf : blockTheta hsq (blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b s) ∈
        blockImage hsq b := mem_blockImage.mpr ⟨s, rfl⟩
    obtain ⟨f, hf⟩ := blockImage_le_range_toGL_of_good hsq b hb hmemf
    have hfB : f ∈ blkSL hsq b := by
      rw [mem_blkSL, hf]
      exact hmemf
    have hcomm : (g : Matrix.SpecialLinearGroup (Fin n) K) * f = f * g :=
      Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_iInf.mp g.2.2) ⟨b, hb⟩) f hfB |>.symm
    have h2 : blockTheta hsq (ι0 g * blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b s) =
        blockTheta hsq (blockEmbed (Efac (slEnd A)) (mult (slEnd A)) b s * ι0 g) := by
      rw [map_mul, map_mul, hι, ← hf, ← map_mul, ← map_mul, hcomm]
    have h3 := blockTheta_injective hsq h2
    have h4 := congrFun h3 b
    simp only [Pi.mul_apply, blockEmbed_apply_self] at h4
    exact h4.symm
  have hιinj : Function.Injective ι0 := by
    intro g g' h
    have := e.symm.injective h
    have h5 : φ' g = φ' g' := e.symm.injective h
    apply Subtype.ext
    exact Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h5)
  let ι' : Ĝ →* ↥(goodCentral (slEnd A)) := ι0.codRestrict (goodCentral (slEnd A)) hιgood
  have : Group.IsSolvable ↥(goodCentral (slEnd A)) := isSolvable_goodCentral _
  have hĜsolv : Group.IsSolvable ↥Ĝ :=
    Group.isSolvable_of_isSolvable_injective (f := ι') (fun g g' h => hιinj (congrArg Subtype.val h))
  have hmapsolv : Group.IsSolvable ↥(Ĝ.map (proj n K)) :=
    Group.isSolvable_of_surjective (f := (proj n K).subgroupMap Ĝ)
      ((proj n K).subgroupMap_surjective Ĝ)
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hS)
    (Subgroup.inclusion_injective hS)

theorem exists_good_block_of_component {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (scalars n K)) (hAp : A ^ p = 1)
    (hsq : Squarefree (minpoly K (slEnd A))) {E : Subgroup (projectiveSL n K)}
    (hE : IsComponentOf (Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) E) :
    ∃ b : primaryFactors (slEnd A), GoodBlock b ∧ E = Qb hsq b := by
  obtain ⟨b, hb⟩ := isComponentOf_eq_of_decomposition
    (fun b : {b : primaryFactors (slEnd A) // GoodBlock b} => Qb hsq b.1)
    (fun b => isComponentOf_Qb b.2) (solvable_centralizer_Qb hp hZ hAp hsq) hE
  exact ⟨b.1, b.2, hb⟩

end Decomp

end CFSG.RankThree.PartOne.FOC
