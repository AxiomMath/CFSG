module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartInputs
public import CFSG.Milestones.ASVolI.F48.Small.Sp43Base
public import Certificates.Certificate7538
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Card
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Ctx
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42

section Words

variable {m : ℕ}

@[expose] def burnsideF48s_sp43c_ev {G : Type*} [Group G] (h : Fin m → G)
    (w : List (Fin m × Bool)) : G :=
  (w.map fun l => cond l.2 (h l.1) (h l.1)⁻¹).prod

theorem burnsideF48s_sp43c_ev_nil {G : Type*} [Group G] (h : Fin m → G) :
    burnsideF48s_sp43c_ev h [] = 1 := by
  simp [burnsideF48s_sp43c_ev]

theorem burnsideF48s_sp43c_ev_cons {G : Type*} [Group G] (h : Fin m → G) (l : Fin m × Bool)
    (w : List (Fin m × Bool)) :
    burnsideF48s_sp43c_ev h (l :: w) = cond l.2 (h l.1) (h l.1)⁻¹ * burnsideF48s_sp43c_ev h w := by
  simp [burnsideF48s_sp43c_ev]

theorem burnsideF48s_sp43c_ev_append {G : Type*} [Group G] (h : Fin m → G)
    (u v : List (Fin m × Bool)) :
    burnsideF48s_sp43c_ev h (u ++ v) = burnsideF48s_sp43c_ev h u * burnsideF48s_sp43c_ev h v := by
  simp [burnsideF48s_sp43c_ev, List.map_append, List.prod_append]

theorem burnsideF48s_sp43c_ev_invW {G : Type*} [Group G] (h : Fin m → G)
    (w : List (Fin m × Bool)) :
    burnsideF48s_sp43c_ev h (burnsideF48s_sp43c_invW w) = (burnsideF48s_sp43c_ev h w)⁻¹ := by
  induction w with
  | nil => simp [burnsideF48s_sp43c_invW, burnsideF48s_sp43c_ev_nil]
  | cons l w ih =>
    have e : burnsideF48s_sp43c_invW (l :: w) = burnsideF48s_sp43c_invW w ++ [(l.1, !l.2)] := by
      simp [burnsideF48s_sp43c_invW]
    rw [e, burnsideF48s_sp43c_ev_append, ih, burnsideF48s_sp43c_ev_cons, burnsideF48s_sp43c_ev_cons,
      burnsideF48s_sp43c_ev_nil, mul_one, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp

theorem burnsideF48s_sp43c_ev_mem {G : Type*} [Group G] {K : Subgroup G} (h : Fin m → G)
    (hK : ∀ k, h k ∈ K) (w : List (Fin m × Bool)) : burnsideF48s_sp43c_ev h w ∈ K := by
  induction w with
  | nil => rw [burnsideF48s_sp43c_ev_nil]; exact K.one_mem
  | cons l w ih =>
    rw [burnsideF48s_sp43c_ev_cons]
    refine K.mul_mem ?_ ih
    obtain ⟨i, b⟩ := l
    cases b
    · exact K.inv_mem (hK i)
    · exact hK i

theorem burnsideF48s_sp43c_repL_ev (h : Fin m → Y) (gl gli : Fin m → List ℕ)
    (hl : ∀ k, RepL (gl k) ((h k : Y) : P45)) (hli : ∀ k, RepL (gli k) (((h k)⁻¹ : Y) : P45))
    (w : List (Fin m × Bool)) :
    RepL (burnsideF48s_sp43c_evL gl gli w) ((burnsideF48s_sp43c_ev h w : Y) : P45) := by
  have hlet : ∀ l : Fin m × Bool, RepL (burnsideF48s_sp43c_letL gl gli l)
      ((cond l.2 (h l.1) (h l.1)⁻¹ : Y) : P45) := by
    rintro ⟨i, b⟩
    cases b
    · exact hli i
    · exact hl i
  have key : ∀ (w : List (Fin m × Bool)) (acc : List ℕ) (σ : P45), RepL acc σ →
      RepL (w.foldl (fun acc l => compL acc (burnsideF48s_sp43c_letL gl gli l)) acc)
        (σ * ((burnsideF48s_sp43c_ev h w : Y) : P45)) := by
    intro w
    induction w with
    | nil =>
      intro acc σ hacc
      simpa [burnsideF48s_sp43c_ev_nil] using hacc
    | cons l w ih =>
      intro acc σ hacc
      rw [List.foldl_cons, burnsideF48s_sp43c_ev_cons, Subgroup.coe_mul, ← mul_assoc]
      exact ih _ _ (repL_mul hacc (hlet l))
  have := key w (List.range 45) 1 (repL_one 45)
  rwa [one_mul] at this

end Words

section WordLists

variable {m : ℕ} (h : Fin m → Y) (gl gli : Fin m → List ℕ)

theorem burnsideF48s_sp43c_groupB_spec {W : List (List (Fin m × Bool))} {n : ℕ}
    (hW : burnsideF48s_sp43c_groupB gl gli W n = true) :
    W.length = n ∧ [] ∈ W ∧ (W.map (burnsideF48s_sp43c_evL gl gli)).Nodup ∧
      ∀ x ∈ W.map (burnsideF48s_sp43c_evL gl gli), ∀ k,
        compL x (gl k) ∈ W.map (burnsideF48s_sp43c_evL gl gli) := by
  simp only [burnsideF48s_sp43c_groupB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies, List.contains_eq_mem] at hW
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hW
  exact ⟨h1, h2, h3, h4⟩

variable {h gl gli}

theorem burnsideF48s_sp43c_cover_of (hl : ∀ k, RepL (gl k) ((h k : Y) : P45))
    (hli : ∀ k, RepL (gli k) (((h k)⁻¹ : Y) : P45)) {W : List (List (Fin m × Bool))} {n : ℕ}
    (hW : burnsideF48s_sp43c_groupB gl gli W n = true) {T : Set Y} (hT : ∀ s ∈ T, ∃ k, s = h k) :
    ∀ z ∈ Subgroup.closure T, ∃ w ∈ W, z = burnsideF48s_sp43c_ev h w := by
  obtain ⟨-, h0, -, hcl⟩ := burnsideF48s_sp43c_groupB_spec gl gli hW
  intro z hz
  refine closure_subset_of_right_closed (S := T)
    (P := {z | ∃ w ∈ W, z = burnsideF48s_sp43c_ev h w})
    (fun s _ => (isOfFinOrder_of_finite s).exists_pow_eq_one) ⟨[], h0, rfl⟩ ?_ hz
  rintro _ ⟨w, hw, rfl⟩ s hs
  obtain ⟨k, rfl⟩ := hT s hs
  obtain ⟨w', hw', he⟩ := List.mem_map.1 (hcl _ (List.mem_map_of_mem hw) k)
  refine ⟨w', hw', Subtype.ext (eq_of_repL ?_ (burnsideF48s_sp43c_repL_ev h gl gli hl hli w'))⟩
  rw [he, Subgroup.coe_mul]
  exact repL_mul (burnsideF48s_sp43c_repL_ev h gl gli hl hli w) (hl k)

theorem burnsideF48s_sp43c_not_mem_of (hl : ∀ k, RepL (gl k) ((h k : Y) : P45))
    (hli : ∀ k, RepL (gli k) (((h k)⁻¹ : Y) : P45)) {W : List (List (Fin m × Bool))} {n : ℕ}
    (hW : burnsideF48s_sp43c_groupB gl gli W n = true) {T : Set Y} (hT : ∀ s ∈ T, ∃ k, s = h k)
    {z : Y} {l : List ℕ} (hz : RepL l (z : P45))
    (hl' : (W.map (burnsideF48s_sp43c_evL gl gli)).contains l = false) :
    z ∉ Subgroup.closure T := by
  intro hzT
  obtain ⟨w, hw, rfl⟩ := burnsideF48s_sp43c_cover_of hl hli hW hT z hzT
  have e : l = burnsideF48s_sp43c_evL gl gli w :=
    repL_unique hz (burnsideF48s_sp43c_repL_ev h gl gli hl hli w)
  have : (W.map (burnsideF48s_sp43c_evL gl gli)).contains l = true := by
    rw [List.contains_eq_mem, decide_eq_true_eq, e]
    exact List.mem_map_of_mem hw
  rw [hl'] at this
  exact Bool.false_ne_true this

theorem burnsideF48s_sp43c_mem_of (hl : ∀ k, RepL (gl k) ((h k : Y) : P45))
    (hli : ∀ k, RepL (gli k) (((h k)⁻¹ : Y) : P45)) {W : List (List (Fin m × Bool))}
    {K : Subgroup Y} (hK : ∀ k, h k ∈ K) {z : Y} {l : List ℕ} (hz : RepL l (z : P45))
    (hl' : l ∈ W.map (burnsideF48s_sp43c_evL gl gli)) : z ∈ K := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl'
  have e : z = burnsideF48s_sp43c_ev h w :=
    Subtype.ext (eq_of_repL hz (burnsideF48s_sp43c_repL_ev h gl gli hl hli w))
  rw [e]
  exact burnsideF48s_sp43c_ev_mem h hK w

theorem burnsideF48s_sp43c_card_of (hl : ∀ k, RepL (gl k) ((h k : Y) : P45))
    (hli : ∀ k, RepL (gli k) (((h k)⁻¹ : Y) : P45)) {W : List (List (Fin m × Bool))} {n : ℕ}
    (hW : burnsideF48s_sp43c_groupB gl gli W n = true) {T : Set Y} (hT : ∀ s ∈ T, ∃ k, s = h k)
    (hK : ∀ k, h k ∈ Subgroup.closure T) : Nat.card ↥(Subgroup.closure T) = n := by
  obtain ⟨hn, -, hnd, -⟩ := burnsideF48s_sp43c_groupB_spec gl gli hW
  let f : Fin W.length → ↥(Subgroup.closure T) := fun i =>
    ⟨burnsideF48s_sp43c_ev h W[i], burnsideF48s_sp43c_ev_mem h hK _⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => ?_, fun z => ?_⟩
    · have e1 : burnsideF48s_sp43c_ev h W[i] = burnsideF48s_sp43c_ev h W[j] :=
        congrArg Subtype.val hij
      have e2 : burnsideF48s_sp43c_evL gl gli W[i] = burnsideF48s_sp43c_evL gl gli W[j] :=
        repL_unique (burnsideF48s_sp43c_repL_ev h gl gli hl hli _)
          (e1 ▸ burnsideF48s_sp43c_repL_ev h gl gli hl hli _)
      have e3 : (W.map (burnsideF48s_sp43c_evL gl gli))[(i : ℕ)]'(by simp) =
          (W.map (burnsideF48s_sp43c_evL gl gli))[(j : ℕ)]'(by simp) := by
        simpa using e2
      exact Fin.ext ((hnd.getElem_inj_iff).1 e3)
    · obtain ⟨w, hw, hz⟩ := burnsideF48s_sp43c_cover_of hl hli hW hT z z.2
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
      exact ⟨⟨i, hi⟩, Subtype.ext hz.symm⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin, hn]

end WordLists

section Model

local notation "aY" => burnsideF48s_sp43G 0
local notation "bY" => burnsideF48s_sp43G 1
local notation "pY" => burnsideF48s_sp43G 2
local notation "qY" => burnsideF48s_sp43G 3

theorem burnsideF48s_sp43c_repL_G (i : Fin 4) :
    RepL (burnsideF48s_sp43c_L i) ((burnsideF48s_sp43G i : Y) : P45) ∧
      RepL (burnsideF48s_sp43c_Li i) (((burnsideF48s_sp43G i)⁻¹ : Y) : P45) := by
  have h := Certificates.certificate7538.1
  simp only [burnsideF48s_sp43c_checkGens, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h i i.2
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact repL_wordP _
  · rw [h2, Subgroup.coe_inv]
    have e : ((burnsideF48s_sp43G i : Y) : P45) = wordP (burnsideF48s_sp43XY.getD i []) := rfl
    rw [e, ← wordP_invW]
    exact repL_wordP _

theorem burnsideF48s_sp43c_repL_G4 :
    (∀ k, RepL (burnsideF48s_sp43c_gl4 k) ((burnsideF48s_sp43G k : Y) : P45)) ∧
      ∀ k, RepL (burnsideF48s_sp43c_gli4 k) (((burnsideF48s_sp43G k)⁻¹ : Y) : P45) :=
  ⟨fun k => (burnsideF48s_sp43c_repL_G k).1, fun k => (burnsideF48s_sp43c_repL_G k).2⟩

@[expose] def burnsideF48s_sp43c_ev4 (w : List (Fin 4 × Bool)) : Y :=
  burnsideF48s_sp43c_ev burnsideF48s_sp43G w

theorem burnsideF48s_sp43c_repL_ev4 (w : List (Fin 4 × Bool)) :
    RepL (burnsideF48s_sp43c_evL4 w) ((burnsideF48s_sp43c_ev4 w : Y) : P45) :=
  burnsideF48s_sp43c_repL_ev _ _ _ burnsideF48s_sp43c_repL_G4.1 burnsideF48s_sp43c_repL_G4.2 w

@[expose] def burnsideF48s_sp43c_hB : Fin 2 → Y := ![aY, bY]

@[expose] def burnsideF48s_sp43c_hP1 : Fin 3 → Y := ![aY, bY, pY]

@[expose] def burnsideF48s_sp43c_hP2 : Fin 3 → Y := ![aY, bY, qY]

@[expose] def burnsideF48s_sp43c_hS : Fin 2 → Y := ![bY, aY * aY]

@[expose] def burnsideF48s_sp43c_S : Subgroup Y := Subgroup.closure {bY, aY * aY}

theorem burnsideF48s_sp43c_repL_hB :
    (∀ k, RepL (burnsideF48s_sp43c_glB k) ((burnsideF48s_sp43c_hB k : Y) : P45)) ∧
      ∀ k, RepL (burnsideF48s_sp43c_gliB k) (((burnsideF48s_sp43c_hB k)⁻¹ : Y) : P45) := by
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k
  · exact (burnsideF48s_sp43c_repL_G 0).1
  · exact (burnsideF48s_sp43c_repL_G 1).1
  · exact (burnsideF48s_sp43c_repL_G 0).2
  · exact (burnsideF48s_sp43c_repL_G 1).2

theorem burnsideF48s_sp43c_repL_hP1 :
    (∀ k, RepL (burnsideF48s_sp43c_glP1 k) ((burnsideF48s_sp43c_hP1 k : Y) : P45)) ∧
      ∀ k, RepL (burnsideF48s_sp43c_gliP1 k) (((burnsideF48s_sp43c_hP1 k)⁻¹ : Y) : P45) := by
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k
  · exact (burnsideF48s_sp43c_repL_G 0).1
  · exact (burnsideF48s_sp43c_repL_G 1).1
  · exact (burnsideF48s_sp43c_repL_G 2).1
  · exact (burnsideF48s_sp43c_repL_G 0).2
  · exact (burnsideF48s_sp43c_repL_G 1).2
  · exact (burnsideF48s_sp43c_repL_G 2).2

theorem burnsideF48s_sp43c_repL_hP2 :
    (∀ k, RepL (burnsideF48s_sp43c_glP2 k) ((burnsideF48s_sp43c_hP2 k : Y) : P45)) ∧
      ∀ k, RepL (burnsideF48s_sp43c_gliP2 k) (((burnsideF48s_sp43c_hP2 k)⁻¹ : Y) : P45) := by
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k
  · exact (burnsideF48s_sp43c_repL_G 0).1
  · exact (burnsideF48s_sp43c_repL_G 1).1
  · exact (burnsideF48s_sp43c_repL_G 3).1
  · exact (burnsideF48s_sp43c_repL_G 0).2
  · exact (burnsideF48s_sp43c_repL_G 1).2
  · exact (burnsideF48s_sp43c_repL_G 3).2

theorem burnsideF48s_sp43c_repL_hS :
    (∀ k, RepL (burnsideF48s_sp43c_glS k) ((burnsideF48s_sp43c_hS k : Y) : P45)) ∧
      ∀ k, RepL (burnsideF48s_sp43c_gliS k) (((burnsideF48s_sp43c_hS k)⁻¹ : Y) : P45) := by
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k
  · exact (burnsideF48s_sp43c_repL_G 1).1
  · show RepL (compL (burnsideF48s_sp43c_L 0) (burnsideF48s_sp43c_L 0)) ((aY * aY : Y) : P45)
    rw [Subgroup.coe_mul]
    exact repL_mul (burnsideF48s_sp43c_repL_G 0).1 (burnsideF48s_sp43c_repL_G 0).1
  · exact (burnsideF48s_sp43c_repL_G 1).2
  · show RepL (compL (burnsideF48s_sp43c_Li 0) (burnsideF48s_sp43c_Li 0)) (((aY * aY)⁻¹ : Y) : P45)
    rw [mul_inv_rev, Subgroup.coe_mul]
    exact repL_mul (burnsideF48s_sp43c_repL_G 0).2 (burnsideF48s_sp43c_repL_G 0).2

theorem burnsideF48s_sp43c_gens_B : ∀ s ∈ ({aY, bY} : Set Y), ∃ k, s = burnsideF48s_sp43c_hB k := by
  rintro s (rfl | rfl)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem burnsideF48s_sp43c_gens_P1 :
    ∀ s ∈ ({aY, bY, pY} : Set Y), ∃ k, s = burnsideF48s_sp43c_hP1 k := by
  rintro s (rfl | rfl | rfl)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem burnsideF48s_sp43c_gens_P2 :
    ∀ s ∈ ({aY, bY, qY} : Set Y), ∃ k, s = burnsideF48s_sp43c_hP2 k := by
  rintro s (rfl | rfl | rfl)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem burnsideF48s_sp43c_gens_S :
    ∀ s ∈ ({bY, aY * aY} : Set Y), ∃ k, s = burnsideF48s_sp43c_hS k := by
  rintro s (rfl | rfl)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem burnsideF48s_sp43c_hB_mem : ∀ k, burnsideF48s_sp43c_hB k ∈ burnsideF48s_sp43B := by
  intro k
  fin_cases k <;> exact Subgroup.subset_closure (by simp [burnsideF48s_sp43c_hB])

theorem burnsideF48s_sp43c_hS_mem : ∀ k, burnsideF48s_sp43c_hS k ∈ burnsideF48s_sp43c_S := by
  intro k
  fin_cases k <;> exact Subgroup.subset_closure (by simp [burnsideF48s_sp43c_hS])

theorem burnsideF48s_sp43c_sub :
    burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glB burnsideF48s_sp43c_gliB
        (burnsideF48s_sp43c_BW ()) 162 = true ∧
      burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glS burnsideF48s_sp43c_gliS
        (burnsideF48s_sp43c_SW ()) 81 = true ∧
      burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glP1 burnsideF48s_sp43c_gliP1
        (burnsideF48s_sp43c_P1W ()) 648 = true ∧
      burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glP2 burnsideF48s_sp43c_gliP2
        (burnsideF48s_sp43c_P2W ()) 648 = true := by
  have h := Certificates.certificate7538.2.1
  simp only [burnsideF48s_sp43c_checkSub, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem burnsideF48s_sp43c_card_B : Nat.card ↥burnsideF48s_sp43B = 162 :=
  burnsideF48s_sp43c_card_of burnsideF48s_sp43c_repL_hB.1 burnsideF48s_sp43c_repL_hB.2
    burnsideF48s_sp43c_sub.1 burnsideF48s_sp43c_gens_B burnsideF48s_sp43c_hB_mem

theorem burnsideF48s_sp43c_card_S : Nat.card ↥burnsideF48s_sp43c_S = 81 :=
  burnsideF48s_sp43c_card_of burnsideF48s_sp43c_repL_hS.1 burnsideF48s_sp43c_repL_hS.2
    burnsideF48s_sp43c_sub.2.1 burnsideF48s_sp43c_gens_S burnsideF48s_sp43c_hS_mem

theorem burnsideF48s_sp43c_B_le_P1 : burnsideF48s_sp43B ≤ burnsideF48s_sp43P1 := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem burnsideF48s_sp43c_B_le_P2 : burnsideF48s_sp43B ≤ burnsideF48s_sp43P2 := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem burnsideF48s_sp43c_p_mem_P1 : pY ∈ burnsideF48s_sp43P1 :=
  Subgroup.subset_closure (by simp)

theorem burnsideF48s_sp43c_q_mem_P2 : qY ∈ burnsideF48s_sp43P2 :=
  Subgroup.subset_closure (by simp)

theorem burnsideF48s_sp43c_p_not_mem_P2 : pY ∉ burnsideF48s_sp43P2 ∧ qY ∉ burnsideF48s_sp43P1 := by
  have h := Certificates.certificate7538.2.2.2.2.2.2
  simp only [burnsideF48s_sp43c_checkNot, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨burnsideF48s_sp43c_not_mem_of burnsideF48s_sp43c_repL_hP2.1 burnsideF48s_sp43c_repL_hP2.2
      burnsideF48s_sp43c_sub.2.2.2 burnsideF48s_sp43c_gens_P2 (burnsideF48s_sp43c_repL_G 2).1 h.1,
    burnsideF48s_sp43c_not_mem_of burnsideF48s_sp43c_repL_hP1.1 burnsideF48s_sp43c_repL_hP1.2
      burnsideF48s_sp43c_sub.2.2.1 burnsideF48s_sp43c_gens_P1 (burnsideF48s_sp43c_repL_G 3).1 h.2⟩

theorem burnsideF48s_sp43c_p_not_mem_B : pY ∉ burnsideF48s_sp43B := fun h =>
  burnsideF48s_sp43c_p_not_mem_P2.1 (burnsideF48s_sp43c_B_le_P2 h)

theorem burnsideF48s_sp43c_closure_xy :
    Subgroup.closure ({⟨x45, x45_mem⟩, ⟨y45, y45_mem⟩} : Set Y) = ⊤ := by
  apply Subgroup.map_injective (f := Xs.subtype) Xs.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  have : (Xs.subtype : Y →* P45) '' ({⟨x45, x45_mem⟩, ⟨y45, y45_mem⟩} : Set Y) =
      ({x45, y45} : Set P45) := by
    rw [Set.image_pair]
    rfl
  rw [this]
  rfl

theorem burnsideF48s_sp43c_ev4_mem {K : Subgroup Y} (hK : ∀ k, burnsideF48s_sp43G k ∈ K)
    (w : List (Fin 4 × Bool)) : burnsideF48s_sp43c_ev4 w ∈ K :=
  burnsideF48s_sp43c_ev_mem _ hK w

theorem burnsideF48s_sp43c_top_le {K : Subgroup Y} (hK : ∀ k, burnsideF48s_sp43G k ∈ K) :
    K = ⊤ := by
  have h := Certificates.certificate7538.2.2.2.2.1
  simp only [burnsideF48s_sp43c_checkXY, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [eq_top_iff, ← burnsideF48s_sp43c_closure_xy, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · have e : (⟨x45, x45_mem⟩ : Y) = burnsideF48s_sp43c_ev4 burnsideF48s_sp43c_xw :=
      Subtype.ext (eq_of_repL repL_x (h.1 ▸ burnsideF48s_sp43c_repL_ev4 _))
    rw [SetLike.mem_coe, e]
    exact burnsideF48s_sp43c_ev4_mem hK _
  · have e : (⟨y45, y45_mem⟩ : Y) = burnsideF48s_sp43c_ev4 burnsideF48s_sp43c_yw :=
      Subtype.ext (eq_of_repL repL_y (h.2 ▸ burnsideF48s_sp43c_repL_ev4 _))
    rw [SetLike.mem_coe, e]
    exact burnsideF48s_sp43c_ev4_mem hK _

theorem burnsideF48s_sp43c_sup : burnsideF48s_sp43P1 ⊔ burnsideF48s_sp43P2 = ⊤ := by
  apply burnsideF48s_sp43c_top_le
  intro k
  fin_cases k
  · exact Subgroup.mem_sup_left (burnsideF48s_sp43c_B_le_P1 (burnsideF48s_sp43c_hB_mem 0))
  · exact Subgroup.mem_sup_left (burnsideF48s_sp43c_B_le_P1 (burnsideF48s_sp43c_hB_mem 1))
  · exact Subgroup.mem_sup_left burnsideF48s_sp43c_p_mem_P1
  · exact Subgroup.mem_sup_right burnsideF48s_sp43c_q_mem_P2

@[expose] def burnsideF48s_sp43c_Bel (i : ℕ) : Y :=
  burnsideF48s_sp43c_ev burnsideF48s_sp43c_hB
    (burnsideF48s_sp43c_wordB (burnsideF48s_sp43c_Bw.getD i ""))

theorem burnsideF48s_sp43c_Bel_mem (i : ℕ) : burnsideF48s_sp43c_Bel i ∈ burnsideF48s_sp43B :=
  burnsideF48s_sp43c_ev_mem _ burnsideF48s_sp43c_hB_mem _

theorem burnsideF48s_sp43c_repL_Bel (i : ℕ) :
    RepL (burnsideF48s_sp43c_Bl i) ((burnsideF48s_sp43c_Bel i : Y) : P45) :=
  burnsideF48s_sp43c_repL_ev _ _ _ burnsideF48s_sp43c_repL_hB.1 burnsideF48s_sp43c_repL_hB.2 _

theorem burnsideF48s_sp43c_exists_Bel {b : Y} (hb : b ∈ burnsideF48s_sp43B) :
    ∃ i < 162, b = burnsideF48s_sp43c_Bel i := by
  obtain ⟨w, hw, rfl⟩ := burnsideF48s_sp43c_cover_of burnsideF48s_sp43c_repL_hB.1
    burnsideF48s_sp43c_repL_hB.2 burnsideF48s_sp43c_sub.1 burnsideF48s_sp43c_gens_B b hb
  have hlen := (burnsideF48s_sp43c_groupB_spec _ _ burnsideF48s_sp43c_sub.1).1
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hw
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
  have hlen' : burnsideF48s_sp43c_Bw.length = 162 := by
    rw [← hlen]
    simp [burnsideF48s_sp43c_BW]
  refine ⟨i, hlen' ▸ hi, ?_⟩
  unfold burnsideF48s_sp43c_Bel
  rw [List.getD_eq_getElem _ _ hi]

@[expose] def burnsideF48s_sp43c_D (j : ℕ) : Y :=
  burnsideF48s_sp43c_ev4 (burnsideF48s_sp43c_Dw.getD j [])

theorem burnsideF48s_sp43c_repL_D (j : ℕ) :
    RepL (burnsideF48s_sp43c_Dl j) ((burnsideF48s_sp43c_D j : Y) : P45) :=
  burnsideF48s_sp43c_repL_ev4 _

theorem burnsideF48s_sp43c_repL_Dinv (j : ℕ) :
    RepL (burnsideF48s_sp43c_Dli j) (((burnsideF48s_sp43c_D j)⁻¹ : Y) : P45) := by
  have e : (burnsideF48s_sp43c_D j)⁻¹ =
      burnsideF48s_sp43c_ev4 (burnsideF48s_sp43c_invW (burnsideF48s_sp43c_Dw.getD j [])) :=
    (burnsideF48s_sp43c_ev_invW _ _).symm
  rw [e]
  exact burnsideF48s_sp43c_repL_ev4 _

theorem burnsideF48s_sp43c_D_zero : burnsideF48s_sp43c_D 0 = 1 := by
  show burnsideF48s_sp43c_ev burnsideF48s_sp43G [] = 1
  exact burnsideF48s_sp43c_ev_nil _

theorem burnsideF48s_sp43c_D_one : burnsideF48s_sp43c_D 1 = pY := by
  show burnsideF48s_sp43c_ev burnsideF48s_sp43G [(2, true)] = pY
  rw [burnsideF48s_sp43c_ev_cons, burnsideF48s_sp43c_ev_nil, mul_one]
  rfl

theorem burnsideF48s_sp43c_D_two : burnsideF48s_sp43c_D 2 = qY := by
  show burnsideF48s_sp43c_ev burnsideF48s_sp43G [(3, true)] = qY
  rw [burnsideF48s_sp43c_ev_cons, burnsideF48s_sp43c_ev_nil, mul_one]
  rfl

theorem burnsideF48s_sp43c_coverB_spec (s : Fin 4) {tr : List ℕ} {wit : List (ℕ × ℕ)}
    {dec : List (List (ℕ × ℕ × ℕ))} (hc : burnsideF48s_sp43c_coverB s tr wit dec = true) :
    (∀ i < 162, (wit.getD i (0, 0)).1 < 3 ∧
      burnsideF48s_sp43c_Bel i * burnsideF48s_sp43G s =
        burnsideF48s_sp43c_Bel (tr.getD (wit.getD i (0, 0)).1 0) * burnsideF48s_sp43G s *
          burnsideF48s_sp43c_Bel (wit.getD i (0, 0)).2) ∧
    ∀ j < 8, ∀ t < 3, ((dec.getD j []).getD t (0, 0, 0)).1 < 8 ∧
      burnsideF48s_sp43c_D j * burnsideF48s_sp43c_Bel (tr.getD t 0) * burnsideF48s_sp43G s =
        burnsideF48s_sp43c_Bel ((dec.getD j []).getD t (0, 0, 0)).2.1 *
          burnsideF48s_sp43c_D ((dec.getD j []).getD t (0, 0, 0)).1 *
          burnsideF48s_sp43c_Bel ((dec.getD j []).getD t (0, 0, 0)).2.2 := by
  simp only [burnsideF48s_sp43c_coverB, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨h1, h2⟩ := hc
  have hs := (burnsideF48s_sp43c_repL_G s).1
  refine ⟨fun i hi => ⟨(h1 i hi).1, ?_⟩, fun j hj t ht => ⟨(h2 j hj t ht).1, ?_⟩⟩
  · have e1 : RepL (compL (burnsideF48s_sp43c_Bl i) (burnsideF48s_sp43c_L s))
        ((burnsideF48s_sp43c_Bel i * burnsideF48s_sp43G s : Y) : P45) := by
      rw [Subgroup.coe_mul]
      exact repL_mul (burnsideF48s_sp43c_repL_Bel i) hs
    have e2 : RepL (compL (burnsideF48s_sp43c_Bl i) (burnsideF48s_sp43c_L s))
        ((burnsideF48s_sp43c_Bel (tr.getD (wit.getD i (0, 0)).1 0) * burnsideF48s_sp43G s *
          burnsideF48s_sp43c_Bel (wit.getD i (0, 0)).2 : Y) : P45) := by
      rw [(h1 i hi).2, Subgroup.coe_mul, Subgroup.coe_mul]
      exact repL_mul (repL_mul (burnsideF48s_sp43c_repL_Bel _) hs) (burnsideF48s_sp43c_repL_Bel _)
    exact Subtype.ext (eq_of_repL e1 e2)
  · have e1 : RepL (compL (compL (burnsideF48s_sp43c_Dl j) (burnsideF48s_sp43c_Bl (tr.getD t 0)))
          (burnsideF48s_sp43c_L s))
        ((burnsideF48s_sp43c_D j * burnsideF48s_sp43c_Bel (tr.getD t 0) * burnsideF48s_sp43G s :
          Y) : P45) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact repL_mul (repL_mul (burnsideF48s_sp43c_repL_D j) (burnsideF48s_sp43c_repL_Bel _)) hs
    have e2 : RepL (compL (compL (burnsideF48s_sp43c_Dl j) (burnsideF48s_sp43c_Bl (tr.getD t 0)))
          (burnsideF48s_sp43c_L s))
        ((burnsideF48s_sp43c_Bel ((dec.getD j []).getD t (0, 0, 0)).2.1 *
          burnsideF48s_sp43c_D ((dec.getD j []).getD t (0, 0, 0)).1 *
          burnsideF48s_sp43c_Bel ((dec.getD j []).getD t (0, 0, 0)).2.2 : Y) : P45) := by
      rw [(h2 j hj t ht).2, Subgroup.coe_mul, Subgroup.coe_mul]
      exact repL_mul (repL_mul (burnsideF48s_sp43c_repL_Bel _) (burnsideF48s_sp43c_repL_D _))
        (burnsideF48s_sp43c_repL_Bel _)
    exact Subtype.ext (eq_of_repL e1 e2)

theorem burnsideF48s_sp43c_mul_mem_cover {s : Fin 4} (hs : s = 2 ∨ s = 3) {g : Y}
    (hg : ∃ j < 8, ∃ b ∈ burnsideF48s_sp43B, ∃ b' ∈ burnsideF48s_sp43B,
      g = b * burnsideF48s_sp43c_D j * b') :
    ∃ j < 8, ∃ b ∈ burnsideF48s_sp43B, ∃ b' ∈ burnsideF48s_sp43B,
      g * burnsideF48s_sp43G s = b * burnsideF48s_sp43c_D j * b' := by
  have hc := Certificates.certificate7538.2.2.1
  simp only [burnsideF48s_sp43c_checkCover, Bool.and_eq_true] at hc
  obtain ⟨tr, wit, dec, hspec⟩ : ∃ tr wit dec, burnsideF48s_sp43c_coverB s tr wit dec = true := by
    rcases hs with rfl | rfl
    · exact ⟨_, _, _, hc.1⟩
    · exact ⟨_, _, _, hc.2⟩
  obtain ⟨hw, hd⟩ := burnsideF48s_sp43c_coverB_spec s hspec
  obtain ⟨j, hj, b, hb, b', hb', rfl⟩ := hg
  obtain ⟨i, hi, rfl⟩ := burnsideF48s_sp43c_exists_Bel hb'
  obtain ⟨ht, e1⟩ := hw i hi
  set t := (wit.getD i (0, 0)).1
  set i' := (wit.getD i (0, 0)).2
  obtain ⟨hk, e2⟩ := hd j hj t ht
  set d := (dec.getD j []).getD t (0, 0, 0)
  refine ⟨d.1, hk, b * burnsideF48s_sp43c_Bel d.2.1, burnsideF48s_sp43B.mul_mem hb
    (burnsideF48s_sp43c_Bel_mem _), burnsideF48s_sp43c_Bel d.2.2 * burnsideF48s_sp43c_Bel i',
    burnsideF48s_sp43B.mul_mem (burnsideF48s_sp43c_Bel_mem _) (burnsideF48s_sp43c_Bel_mem _), ?_⟩
  calc b * burnsideF48s_sp43c_D j * burnsideF48s_sp43c_Bel i * burnsideF48s_sp43G s
      = b * burnsideF48s_sp43c_D j * (burnsideF48s_sp43c_Bel i * burnsideF48s_sp43G s) := by
        group
    _ = b * (burnsideF48s_sp43c_D j * burnsideF48s_sp43c_Bel (tr.getD t 0) *
          burnsideF48s_sp43G s) * burnsideF48s_sp43c_Bel i' := by
        rw [e1]
        group
    _ = b * burnsideF48s_sp43c_Bel d.2.1 * burnsideF48s_sp43c_D d.1 *
          (burnsideF48s_sp43c_Bel d.2.2 * burnsideF48s_sp43c_Bel i') := by
        rw [e2]
        group

theorem burnsideF48s_sp43c_cover (g : Y) :
    ∃ j < 8, ∃ b ∈ burnsideF48s_sp43B, ∃ b' ∈ burnsideF48s_sp43B,
      g = b * burnsideF48s_sp43c_D j * b' := by
  let C : Set Y := {g | ∃ j < 8, ∃ b ∈ burnsideF48s_sp43B, ∃ b' ∈ burnsideF48s_sp43B,
    g = b * burnsideF48s_sp43c_D j * b'}
  have hsub := closure_subset_of_right_closed (S := Set.range burnsideF48s_sp43G) (P := C)
    (fun s _ => (isOfFinOrder_of_finite s).exists_pow_eq_one)
    ⟨0, by norm_num, 1, burnsideF48s_sp43B.one_mem, 1, burnsideF48s_sp43B.one_mem, by
      rw [burnsideF48s_sp43c_D_zero]
      group⟩ (by
      rintro p hp _ ⟨s, rfl⟩
      have hs4 : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
        fin_cases s <;> simp
      rcases hs4 with rfl | rfl | hs
      · obtain ⟨j, hj, b, hb, b', hb', rfl⟩ := hp
        exact ⟨j, hj, b, hb, b' * aY,
          burnsideF48s_sp43B.mul_mem hb' (burnsideF48s_sp43c_hB_mem 0 : aY ∈ burnsideF48s_sp43B),
          mul_assoc _ _ _⟩
      · obtain ⟨j, hj, b, hb, b', hb', rfl⟩ := hp
        exact ⟨j, hj, b, hb, b' * bY,
          burnsideF48s_sp43B.mul_mem hb' (burnsideF48s_sp43c_hB_mem 1 : bY ∈ burnsideF48s_sp43B),
          mul_assoc _ _ _⟩
      · exact burnsideF48s_sp43c_mul_mem_cover hs hp)
  have htop : Subgroup.closure (Set.range burnsideF48s_sp43G) = ⊤ :=
    burnsideF48s_sp43c_top_le fun k => Subgroup.subset_closure ⟨k, rfl⟩
  exact hsub (htop ▸ Subgroup.mem_top g)

theorem burnsideF48s_sp43c_repL_hF (j : ℕ) :
    (∀ k, RepL (burnsideF48s_sp43c_glF j k)
        ((![burnsideF48s_sp43G 0, burnsideF48s_sp43G 1, burnsideF48s_sp43c_D j] k : Y) : P45)) ∧
      ∀ k, RepL (burnsideF48s_sp43c_gliF j k)
        (((![burnsideF48s_sp43G 0, burnsideF48s_sp43G 1, burnsideF48s_sp43c_D j] k)⁻¹ : Y) :
          P45) := by
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> fin_cases k
  · exact (burnsideF48s_sp43c_repL_G 0).1
  · exact (burnsideF48s_sp43c_repL_G 1).1
  · exact burnsideF48s_sp43c_repL_D j
  · exact (burnsideF48s_sp43c_repL_G 0).2
  · exact (burnsideF48s_sp43c_repL_G 1).2
  · exact burnsideF48s_sp43c_repL_Dinv j

theorem burnsideF48s_sp43c_far {H : Subgroup Y} (hB : burnsideF48s_sp43B ≤ H) {j : ℕ}
    (hj3 : 3 ≤ j) (hj8 : j < 8) (hD : burnsideF48s_sp43c_D j ∈ H) : pY ∈ H ∧ qY ∈ H := by
  have h := Certificates.certificate7538.2.2.2.1
  simp only [burnsideF48s_sp43c_checkFar, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h (j - 3) (by omega)
  rw [show j - 3 + 3 = j by omega] at h1 h2
  have hK : ∀ k, ![burnsideF48s_sp43G 0, burnsideF48s_sp43G 1, burnsideF48s_sp43c_D j] k ∈ H := by
    intro k
    fin_cases k
    · exact hB (burnsideF48s_sp43c_hB_mem 0)
    · exact hB (burnsideF48s_sp43c_hB_mem 1)
    · exact hD
  obtain ⟨hl, hli⟩ := burnsideF48s_sp43c_repL_hF j
  refine ⟨?_, ?_⟩
  · have e : burnsideF48s_sp43c_ev ![burnsideF48s_sp43G 0, burnsideF48s_sp43G 1,
        burnsideF48s_sp43c_D j] (burnsideF48s_sp43c_farW.getD (j - 3) ([], [])).1 = pY :=
      Subtype.ext (eq_of_repL (burnsideF48s_sp43c_repL_ev _ _ _ hl hli _)
        (h1 ▸ (burnsideF48s_sp43c_repL_G 2).1))
    rw [← e]
    exact burnsideF48s_sp43c_ev_mem _ hK _
  · have e : burnsideF48s_sp43c_ev ![burnsideF48s_sp43G 0, burnsideF48s_sp43G 1,
        burnsideF48s_sp43c_D j] (burnsideF48s_sp43c_farW.getD (j - 3) ([], [])).2 = qY :=
      Subtype.ext (eq_of_repL (burnsideF48s_sp43c_repL_ev _ _ _ hl hli _)
        (h2 ▸ (burnsideF48s_sp43c_repL_G 3).1))
    rw [← e]
    exact burnsideF48s_sp43c_ev_mem _ hK _

theorem burnsideF48s_sp43c_P1_le {H : Subgroup Y} (hB : burnsideF48s_sp43B ≤ H) (hp : pY ∈ H) :
    burnsideF48s_sp43P1 ≤ H := by
  rw [burnsideF48s_sp43P1, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact hB (burnsideF48s_sp43c_hB_mem 0)
  · exact hB (burnsideF48s_sp43c_hB_mem 1)
  · exact hp

theorem burnsideF48s_sp43c_P2_le {H : Subgroup Y} (hB : burnsideF48s_sp43B ≤ H) (hq : qY ∈ H) :
    burnsideF48s_sp43P2 ≤ H := by
  rw [burnsideF48s_sp43P2, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact hB (burnsideF48s_sp43c_hB_mem 0)
  · exact hB (burnsideF48s_sp43c_hB_mem 1)
  · exact hq

theorem burnsideF48s_sp43c_lattice {H : Subgroup Y} (hB : burnsideF48s_sp43B ≤ H) :
    H = burnsideF48s_sp43B ∨ H = burnsideF48s_sp43P1 ∨ H = burnsideF48s_sp43P2 ∨ H = ⊤ := by
  have hcov : ∀ g ∈ H, ∃ j < 8, burnsideF48s_sp43c_D j ∈ H ∧ ∃ b ∈ burnsideF48s_sp43B,
      ∃ b' ∈ burnsideF48s_sp43B, g = b * burnsideF48s_sp43c_D j * b' := by
    intro g hg
    obtain ⟨j, hj, b, hb, b', hb', rfl⟩ := burnsideF48s_sp43c_cover g
    refine ⟨j, hj, ?_, b, hb, b', hb', rfl⟩
    have : burnsideF48s_sp43c_D j = b⁻¹ * (b * burnsideF48s_sp43c_D j * b') * b'⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hB hb)) hg) (H.inv_mem (hB hb'))
  have htop : ∀ (_ : pY ∈ H) (_ : qY ∈ H), H = ⊤ := fun hp hq => by
    rw [eq_top_iff, ← burnsideF48s_sp43c_sup]
    exact sup_le (burnsideF48s_sp43c_P1_le hB hp) (burnsideF48s_sp43c_P2_le hB hq)
  by_cases hfar : ∃ j, 3 ≤ j ∧ j < 8 ∧ burnsideF48s_sp43c_D j ∈ H
  · obtain ⟨j, hj3, hj8, hjH⟩ := hfar
    obtain ⟨hp, hq⟩ := burnsideF48s_sp43c_far hB hj3 hj8 hjH
    exact Or.inr (Or.inr (Or.inr (htop hp hq)))
  · have hcases : ∀ g ∈ H, g ∈ burnsideF48s_sp43B ∨ (pY ∈ H ∧ g ∈ burnsideF48s_sp43P1) ∨
        (qY ∈ H ∧ g ∈ burnsideF48s_sp43P2) := by
      intro g hg
      obtain ⟨j, hj, hjH, b, hb, b', hb', rfl⟩ := hcov g hg
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | rfl | h3
      · left
        rw [burnsideF48s_sp43c_D_zero, mul_one]
        exact burnsideF48s_sp43B.mul_mem hb hb'
      · right; left
        rw [burnsideF48s_sp43c_D_one] at hjH ⊢
        exact ⟨hjH, burnsideF48s_sp43P1.mul_mem (burnsideF48s_sp43P1.mul_mem
          (burnsideF48s_sp43c_B_le_P1 hb) burnsideF48s_sp43c_p_mem_P1)
          (burnsideF48s_sp43c_B_le_P1 hb')⟩
      · right; right
        rw [burnsideF48s_sp43c_D_two] at hjH ⊢
        exact ⟨hjH, burnsideF48s_sp43P2.mul_mem (burnsideF48s_sp43P2.mul_mem
          (burnsideF48s_sp43c_B_le_P2 hb) burnsideF48s_sp43c_q_mem_P2)
          (burnsideF48s_sp43c_B_le_P2 hb')⟩
      · exact absurd ⟨j, h3, hj, hjH⟩ hfar
    by_cases hp : pY ∈ H
    · by_cases hq : qY ∈ H
      · exact Or.inr (Or.inr (Or.inr (htop hp hq)))
      · refine Or.inr (Or.inl (le_antisymm (fun g hg => ?_) (burnsideF48s_sp43c_P1_le hB hp)))
        rcases hcases g hg with hgB | ⟨-, hgP⟩ | ⟨hq', -⟩
        · exact burnsideF48s_sp43c_B_le_P1 hgB
        · exact hgP
        · exact absurd hq' hq
    · by_cases hq : qY ∈ H
      · refine Or.inr (Or.inr (Or.inl (le_antisymm (fun g hg => ?_)
          (burnsideF48s_sp43c_P2_le hB hq))))
        rcases hcases g hg with hgB | ⟨hp', -⟩ | ⟨-, hgP⟩
        · exact burnsideF48s_sp43c_B_le_P2 hgB
        · exact absurd hp' hp
        · exact hgP
      · refine Or.inl (le_antisymm (fun g hg => ?_) hB)
        rcases hcases g hg with hgB | ⟨hp', -⟩ | ⟨hq', -⟩
        · exact hgB
        · exact absurd hp' hp
        · exact absurd hq' hq

theorem burnsideF48s_sp43c_inf : burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2 = burnsideF48s_sp43B := by
  rcases burnsideF48s_sp43c_lattice (le_inf burnsideF48s_sp43c_B_le_P1 burnsideF48s_sp43c_B_le_P2)
    with h | h | h | h
  · exact h
  · exact absurd ((inf_eq_left.1 h) burnsideF48s_sp43c_p_mem_P1) burnsideF48s_sp43c_p_not_mem_P2.1
  · exact absurd ((inf_eq_right.1 h) burnsideF48s_sp43c_q_mem_P2) burnsideF48s_sp43c_p_not_mem_P2.2
  · exact absurd ((inf_eq_top_iff.1 h).2 ▸ Subgroup.mem_top pY) burnsideF48s_sp43c_p_not_mem_P2.1

theorem burnsideF48s_sp43c_checkS_spec :
    (∀ x ∈ burnsideF48s_sp43c_SL (), ∀ g ∈ [(burnsideF48s_sp43c_L 0, burnsideF48s_sp43c_Li 0),
        (burnsideF48s_sp43c_Li 0, burnsideF48s_sp43c_L 0),
        (burnsideF48s_sp43c_L 1, burnsideF48s_sp43c_Li 1),
        (burnsideF48s_sp43c_Li 1, burnsideF48s_sp43c_L 1)],
        compL (compL g.1 x) g.2 ∈ burnsideF48s_sp43c_SL ()) ∧
      (burnsideF48s_sp43c_SL ()).contains (compL (compL (burnsideF48s_sp43c_L 2)
        (burnsideF48s_sp43c_L 1)) (burnsideF48s_sp43c_Li 2)) = false ∧
      (burnsideF48s_sp43c_SL ()).contains (compL (compL (burnsideF48s_sp43c_L 3)
        (compL (burnsideF48s_sp43c_L 0) (burnsideF48s_sp43c_L 0))) (burnsideF48s_sp43c_Li 3)) =
        false := by
  have h := Certificates.certificate7538.2.2.2.2.2.1
  simp only [burnsideF48s_sp43c_checkS, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_eq_mem, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [List.contains_eq_mem]; exact h2
  · rw [List.contains_eq_mem]; exact h3

theorem burnsideF48s_sp43c_conj_mem_S {u : Y} {lu lui : List ℕ} (hu : RepL lu (u : P45))
    (hui : RepL lui ((u⁻¹ : Y) : P45))
    (hS : ∀ x ∈ burnsideF48s_sp43c_SL (), compL (compL lu x) lui ∈ burnsideF48s_sp43c_SL ())
    {z : Y} (hz : z ∈ burnsideF48s_sp43c_S) : u * z * u⁻¹ ∈ burnsideF48s_sp43c_S := by
  obtain ⟨w, hw, rfl⟩ := burnsideF48s_sp43c_cover_of burnsideF48s_sp43c_repL_hS.1
    burnsideF48s_sp43c_repL_hS.2 burnsideF48s_sp43c_sub.2.1 burnsideF48s_sp43c_gens_S z hz
  have hx : burnsideF48s_sp43c_evL burnsideF48s_sp43c_glS burnsideF48s_sp43c_gliS w ∈
      burnsideF48s_sp43c_SL () := List.mem_map_of_mem hw
  refine burnsideF48s_sp43c_mem_of burnsideF48s_sp43c_repL_hS.1 burnsideF48s_sp43c_repL_hS.2
    burnsideF48s_sp43c_hS_mem ?_ (hS _ hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact repL_mul (repL_mul hu (burnsideF48s_sp43c_repL_ev _ _ _ burnsideF48s_sp43c_repL_hS.1
    burnsideF48s_sp43c_repL_hS.2 w)) hui

theorem burnsideF48s_sp43c_mem_normalizer {u : Y}
    (h1 : ∀ z ∈ burnsideF48s_sp43c_S, u * z * u⁻¹ ∈ burnsideF48s_sp43c_S)
    (h2 : ∀ z ∈ burnsideF48s_sp43c_S, u⁻¹ * z * u⁻¹⁻¹ ∈ burnsideF48s_sp43c_S) :
    u ∈ Subgroup.normalizer (burnsideF48s_sp43c_S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h1 z, fun hz => ?_⟩
  have := h2 _ hz
  simpa [mul_assoc] using this

theorem burnsideF48s_sp43c_B_le_normalizer :
    burnsideF48s_sp43B ≤ Subgroup.normalizer (burnsideF48s_sp43c_S : Set Y) := by
  obtain ⟨hS, -, -⟩ := burnsideF48s_sp43c_checkS_spec
  have hu : ∀ i : Fin 4, i = 0 ∨ i = 1 → burnsideF48s_sp43G i ∈
      Subgroup.normalizer (burnsideF48s_sp43c_S : Set Y) := by
    rintro i hi
    have hi' : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
      rcases hi with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hmem1 : (burnsideF48s_sp43c_L i, burnsideF48s_sp43c_Li i) ∈
        [(burnsideF48s_sp43c_L 0, burnsideF48s_sp43c_Li 0),
          (burnsideF48s_sp43c_Li 0, burnsideF48s_sp43c_L 0),
          (burnsideF48s_sp43c_L 1, burnsideF48s_sp43c_Li 1),
          (burnsideF48s_sp43c_Li 1, burnsideF48s_sp43c_L 1)] := by
      rcases hi' with h | h <;> rw [h] <;> simp
    have hmem2 : (burnsideF48s_sp43c_Li i, burnsideF48s_sp43c_L i) ∈
        [(burnsideF48s_sp43c_L 0, burnsideF48s_sp43c_Li 0),
          (burnsideF48s_sp43c_Li 0, burnsideF48s_sp43c_L 0),
          (burnsideF48s_sp43c_L 1, burnsideF48s_sp43c_Li 1),
          (burnsideF48s_sp43c_Li 1, burnsideF48s_sp43c_L 1)] := by
      rcases hi' with h | h <;> rw [h] <;> simp
    refine burnsideF48s_sp43c_mem_normalizer
      (fun z hz => burnsideF48s_sp43c_conj_mem_S (burnsideF48s_sp43c_repL_G i).1
        (burnsideF48s_sp43c_repL_G i).2 (fun x hx => hS x hx _ hmem1) hz)
      (fun z hz => burnsideF48s_sp43c_conj_mem_S (burnsideF48s_sp43c_repL_G i).2
        (by rw [inv_inv]; exact (burnsideF48s_sp43c_repL_G i).1) (fun x hx => hS x hx _ hmem2) hz)
  rw [burnsideF48s_sp43B, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact hu 0 (Or.inl rfl)
  · exact hu 1 (Or.inr rfl)

theorem burnsideF48s_sp43c_not_normalizer :
    pY ∉ Subgroup.normalizer (burnsideF48s_sp43c_S : Set Y) ∧
      qY ∉ Subgroup.normalizer (burnsideF48s_sp43c_S : Set Y) := by
  obtain ⟨-, hp, hq⟩ := burnsideF48s_sp43c_checkS_spec
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have hb : bY ∈ burnsideF48s_sp43c_S := burnsideF48s_sp43c_hS_mem 0
    have hc := (Subgroup.mem_normalizer_iff.1 hn bY).1 hb
    refine burnsideF48s_sp43c_not_mem_of burnsideF48s_sp43c_repL_hS.1 burnsideF48s_sp43c_repL_hS.2
      burnsideF48s_sp43c_sub.2.1 burnsideF48s_sp43c_gens_S ?_ hp hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact repL_mul (repL_mul (burnsideF48s_sp43c_repL_G 2).1 (burnsideF48s_sp43c_repL_G 1).1)
      (burnsideF48s_sp43c_repL_G 2).2
  · have hc' : aY * aY ∈ burnsideF48s_sp43c_S := burnsideF48s_sp43c_hS_mem 1
    have hc := (Subgroup.mem_normalizer_iff.1 hn (aY * aY)).1 hc'
    refine burnsideF48s_sp43c_not_mem_of burnsideF48s_sp43c_repL_hS.1 burnsideF48s_sp43c_repL_hS.2
      burnsideF48s_sp43c_sub.2.1 burnsideF48s_sp43c_gens_S ?_ hq hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact repL_mul (repL_mul (burnsideF48s_sp43c_repL_G 3).1
      (repL_mul (burnsideF48s_sp43c_repL_G 0).1 (burnsideF48s_sp43c_repL_G 0).1))
      (burnsideF48s_sp43c_repL_G 3).2

theorem burnsideF48s_sp43c_normalizer :
    Subgroup.normalizer (burnsideF48s_sp43c_S : Set Y) = burnsideF48s_sp43B := by
  obtain ⟨hp, hq⟩ := burnsideF48s_sp43c_not_normalizer
  rcases burnsideF48s_sp43c_lattice burnsideF48s_sp43c_B_le_normalizer with h | h | h | h
  · exact h
  · exact absurd (h ▸ burnsideF48s_sp43c_p_mem_P1) hp
  · exact absurd (h ▸ burnsideF48s_sp43c_q_mem_P2) hq
  · exact absurd (h ▸ Subgroup.mem_top pY) hp

theorem burnsideF48s_sp43c_index_S : burnsideF48s_sp43c_S.index = 320 := by
  have h := Subgroup.card_mul_index burnsideF48s_sp43c_S
  rw [burnsideF48s_sp43c_card_S, show Nat.card Y = 25920 from card_Xs] at h
  omega

theorem burnsideF48s_sp43c_P1_ne_top : burnsideF48s_sp43P1 ≠ ⊤ := fun h =>
  burnsideF48s_sp43c_p_not_mem_P2.2 (h ▸ Subgroup.mem_top qY)

theorem burnsideF48s_sp43c_P2_ne_top : burnsideF48s_sp43P2 ≠ ⊤ := fun h =>
  burnsideF48s_sp43c_p_not_mem_P2.1 (h ▸ Subgroup.mem_top pY)

theorem burnsideF48s_sp43c_isCoatom_P1 : IsCoatom burnsideF48s_sp43P1 := by
  refine ⟨burnsideF48s_sp43c_P1_ne_top, fun R hR => ?_⟩
  rcases burnsideF48s_sp43c_lattice (burnsideF48s_sp43c_B_le_P1.trans hR.le) with h | h | h | h
  · subst h
    exact absurd burnsideF48s_sp43c_B_le_P1 (not_le_of_gt hR)
  · exact absurd h hR.ne'
  · subst h
    exact absurd (hR.le burnsideF48s_sp43c_p_mem_P1) burnsideF48s_sp43c_p_not_mem_P2.1
  · exact h

theorem burnsideF48s_sp43c_isCoatom_P2 : IsCoatom burnsideF48s_sp43P2 := by
  refine ⟨burnsideF48s_sp43c_P2_ne_top, fun R hR => ?_⟩
  rcases burnsideF48s_sp43c_lattice (burnsideF48s_sp43c_B_le_P2.trans hR.le) with h | h | h | h
  · subst h
    exact absurd burnsideF48s_sp43c_B_le_P2 (not_le_of_gt hR)
  · subst h
    exact absurd (hR.le burnsideF48s_sp43c_q_mem_P2) burnsideF48s_sp43c_p_not_mem_P2.2
  · exact absurd h hR.ne'
  · exact h

theorem burnsideF48s_sp43c_isLieParabolics :
    ChF.IsLieParabolics 3 (⊤ : Subgroup Y) burnsideF48s_sp43B burnsideF48s_sp43P1
      burnsideF48s_sp43P2 := by
  have hne : burnsideF48s_sp43P1 ≠ burnsideF48s_sp43P2 := fun h =>
    burnsideF48s_sp43c_p_not_mem_P2.1 (h ▸ burnsideF48s_sp43c_p_mem_P1)
  refine burnsideF4h_cl_isLieParabolics_top_of (S := burnsideF48s_sp43c_S)
    (IsPGroup.of_card (n := 4) (by rw [burnsideF48s_sp43c_card_S]; norm_num))
    (by rw [burnsideF48s_sp43c_index_S]; decide) burnsideF48s_sp43c_normalizer hne
    burnsideF48s_sp43c_inf burnsideF48s_sp43c_isCoatom_P1 burnsideF48s_sp43c_isCoatom_P2
    fun Q hBQ hQc => ?_
  rcases burnsideF48s_sp43c_lattice hBQ with h | h | h | h
  · subst h
    exact absurd (hQc.2 _ (lt_of_le_of_ne burnsideF48s_sp43c_B_le_P1 fun h =>
      burnsideF48s_sp43c_p_not_mem_B (h ▸ burnsideF48s_sp43c_p_mem_P1)))
      burnsideF48s_sp43c_P1_ne_top
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hQc.1

end Model

end CFSG.ASVolI
