module

public import CFSG.GH74.QTGen4.Recog.G23.NativeFacts
public import CFSG.GH74.QTGen4.Recog.G23.MLettersB
public import CFSG.GH74.QTGen4.Recog.G23.Abstract
public import CFSG.Sporadic.Recognition.PresentedWordsExpSum
public import Certificates.Certificate687007
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three
open CFSG.Sporadic.Recognition.PresentedWords

theorem g23WordsM_iff {X : Type*} [Group X] (ρ : Fin 6 → X) :
    SatisfiesWords g23WordsM ρ ↔ ∀ r ∈ g23PM,
      FreeGroup.lift (![evalW ρ dWord₁, evalW ρ dWord₂, ρ 5] : Fin 3 → X)
        (FreeGroup.mk r) = 1 := by
  constructor
  · intro h r hr
    have h1 := h (FreeGroup.reduce (substWord r)) (List.mem_map_of_mem hr)
    rw [FreeGroup.reduce.self, lift_substWord] at h1
    exact h1
  · intro h r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    rw [FreeGroup.reduce.self, lift_substWord]
    exact h r' hr'

theorem commutator_closure_g23PM {X : Type*} [Group X] (m : Fin 3 → X)
    (hm : ∀ r ∈ g23PM, FreeGroup.lift m (FreeGroup.mk r) = 1) :
    ⁅Subgroup.closure (Set.range m), Subgroup.closure (Set.range m)⁆ =
      Subgroup.closure (Set.range m) := by
  let M : Subgroup X := Subgroup.closure (Set.range m)
  have hmM : ∀ i, m i ∈ M := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  let m' : Fin 3 → ↥M := fun i => ⟨m i, hmM i⟩
  have hm' : ∀ r ∈ g23PM, FreeGroup.lift m' (FreeGroup.mk r) = 1 := by
    intro r hr
    apply Subtype.ext
    have hcomp : M.subtype.comp (FreeGroup.lift m') = FreeGroup.lift m := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp [m']
    have h : ((FreeGroup.lift m' (FreeGroup.mk r) : ↥M) : X) =
        FreeGroup.lift m (FreeGroup.mk r) :=
      congrArg (fun φ => φ (FreeGroup.mk r)) hcomp
    rw [h, hm r hr]
    rfl
  let a : Fin 3 → Abelianization ↥M := fun i => Abelianization.of (m' i)
  have ha : ∀ r ∈ g23PM, FreeGroup.lift a (FreeGroup.mk r) = 1 := by
    intro r hr
    have hcomp : Abelianization.of.comp (FreeGroup.lift m') = FreeGroup.lift a := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp [a]
    rw [← hcomp, MonoidHom.comp_apply, hm' r hr, map_one]
  have h0 : a 0 = 1 := by
    have h := ha (g23PM.get ⟨1, by decide⟩) (List.get_mem _ _)
    rw [lift_mk, wprod_eq_prod_zpow_expSum, Fin.prod_univ_three] at h
    have e0 : expSum (0 : Fin 3) (g23PM.get ⟨1, by decide⟩) = 1 := by decide
    have e1 : expSum (1 : Fin 3) (g23PM.get ⟨1, by decide⟩) = 0 := by decide
    have e2 : expSum (2 : Fin 3) (g23PM.get ⟨1, by decide⟩) = 0 := by decide
    rw [e0, e1, e2] at h
    simpa using h
  have h1 : a 1 = 1 := by
    have h := ha (g23PM.get ⟨3, by decide⟩) (List.get_mem _ _)
    rw [lift_mk, wprod_eq_prod_zpow_expSum, Fin.prod_univ_three] at h
    have e0 : expSum (0 : Fin 3) (g23PM.get ⟨3, by decide⟩) = -1 := by decide
    have e1 : expSum (1 : Fin 3) (g23PM.get ⟨3, by decide⟩) = 1 := by decide
    have e2 : expSum (2 : Fin 3) (g23PM.get ⟨3, by decide⟩) = 0 := by decide
    rw [e0, e1, e2, h0] at h
    simpa using h
  have h2 : a 2 = 1 := by
    have h := ha (g23PM.get ⟨7, by decide⟩) (List.get_mem _ _)
    rw [lift_mk, wprod_eq_prod_zpow_expSum, Fin.prod_univ_three] at h
    have e0 : expSum (0 : Fin 3) (g23PM.get ⟨7, by decide⟩) = -1 := by decide
    have e1 : expSum (1 : Fin 3) (g23PM.get ⟨7, by decide⟩) = 4 := by decide
    have e2 : expSum (2 : Fin 3) (g23PM.get ⟨7, by decide⟩) = -1 := by decide
    rw [e0, e1, e2, h0, h1] at h
    simpa using h
  have hmem : ∀ i, m i ∈ ⁅M, M⁆ := by
    intro i
    have hai : a i = 1 := by fin_cases i <;> assumption
    have hcomm : (⟨m i, hmM i⟩ : ↥M) ∈ commutator ↥M := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact hai
    have h1 := Subgroup.mem_map_of_mem M.subtype hcomm
    rw [Subgroup.map_subtype_commutator] at h1
    simpa using h1
  refine le_antisymm (Subgroup.commutator_le_self M) ?_
  change M ≤ ⁅M, M⁆
  rw [show M = Subgroup.closure (Set.range m) from rfl, Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  exact hmem i

theorem relIndex_closure_g23PM {X : Type*} [Group X]
    (m : Fin 3 → X) (hm : ∀ r ∈ g23PM, FreeGroup.lift m (FreeGroup.mk r) = 1) :
    0 < (Subgroup.closure {m 0, m 1}).relIndex (Subgroup.closure (Set.range m)) ∧
      (Subgroup.closure {m 0, m 1}).relIndex (Subgroup.closure (Set.range m)) ≤ 7 := by
  have hmw : ∀ r ∈ g23PM, wprod m r = 1 := by
    intro r hr
    rw [← lift_mk]
    exact hm r hr
  let M : Subgroup X := (pgHom m hmw).range
  let D : Subgroup X := Subgroup.closure ({m 0, m 1} : Set X)
  let rels : Set (FreeGroup (Fin 3)) := {r | r ∈ g23PM.map FreeGroup.mk}
  let S : List (Fin 3) := subsetOf 3 [0, 1]
  let H : Subgroup (PG 3 g23PM) := genSub rels S
  obtain ⟨hHfin, hHidx⟩ : H.FiniteIndex ∧ H.index ≤ 7 := g23PM_subgroup_closes
  let φ : PG 3 g23PM →* X := pgHom m hmw
  have hgen : Subgroup.closure (Set.range (PresentedGroup.of : Fin 3 → PG 3 g23PM)) = ⊤ :=
    PresentedGroup.closure_range_of rels
  have hrange : M = Subgroup.closure (Set.range m) := by
    change φ.range = Subgroup.closure (Set.range m)
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      have hy : y ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 3 → PG 3 g23PM)) := by
        rw [hgen]
        trivial
      refine Subgroup.closure_induction (p := fun y _ => φ y ∈ Subgroup.closure (Set.range m))
        ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        exact Subgroup.subset_closure ⟨i, (pgHom_of m hmw i).symm⟩
      · rw [map_one]
        exact (Subgroup.closure (Set.range m)).one_mem
      · intro a b _ _ ha hb
        rw [map_mul]
        exact (Subgroup.closure (Set.range m)).mul_mem ha hb
      · intro a _ ha
        rw [map_inv]
        exact (Subgroup.closure (Set.range m)).inv_mem ha
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨PresentedGroup.of i, pgHom_of m hmw i⟩
  let f : PG 3 g23PM →* M := φ.rangeRestrict
  have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
  have hHle : H.map f ≤ D.subgroupOf M := by
    rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.closure ((fun x => PresentedGroup.of x) '' {x | x ∈ S}) ≤
      Subgroup.comap f (D.subgroupOf M)
    rw [Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    change PresentedGroup.of z ∈ Subgroup.comap f (D.subgroupOf M)
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    have hz' : z = 0 ∨ z = 1 := by
      have hsub : S = [0, 1] := by decide
      have hzS : z ∈ ([0, 1] : List (Fin 3)) := by simpa [hsub] using hz
      simpa using hzS
    have hfz : ((f (PresentedGroup.of z) : M) : X) = m z := by
      change φ (PresentedGroup.of z) = m z
      rw [pgHom_of]
    rw [hfz]
    rcases hz' with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hdvd : (H.map f).index ∣ H.index := Subgroup.index_map_dvd H hf
  have hmapne : (H.map f).index ≠ 0 := by
    intro h0
    exact hHfin.index_ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  haveI : (H.map f).FiniteIndex := Subgroup.FiniteIndex.mk hmapne
  have hmaple : (H.map f).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hHfin.index_ne_zero) hdvd
  have hDle : (D.subgroupOf M).index ≤ (H.map f).index := Subgroup.index_antitone hHle
  haveI : (D.subgroupOf M).FiniteIndex := Subgroup.finiteIndex_of_le hHle
  have hDpos : 0 < (D.subgroupOf M).index :=
    Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  rw [← hrange]
  exact ⟨hDpos, hDle.trans (hmaple.trans hHidx)⟩

theorem g23PD_twist {X : Type*} [Group X] (d : Fin 2 → X) (c : X) (hc : ∀ i, Commute c (d i))
    (hc3 : c ^ 3 = 1) (k : Fin 2 → ℤ)
    (hd : ∀ r ∈ g23PD, FreeGroup.lift d (FreeGroup.mk r) = 1)
    (hdk : ∀ r ∈ g23PD, FreeGroup.lift (fun i => d i * c ^ k i) (FreeGroup.mk r) = 1) :
    ∀ i, c ^ k i = 1 := by
  have key : ∀ r ∈ g23PD, c ^ (∑ i, k i * expSum i r) = 1 := by
    intro r hr
    have h1 : wprod d r = 1 := by rw [← lift_mk]; exact hd r hr
    have h2 : wprod (fun i => d i * c ^ k i) r = 1 := by rw [← lift_mk]; exact hdk r hr
    rw [wprod_mul_zpow_of_commute d c hc k r, h1, one_mul] at h2
    exact h2
  have hrow1 := key (g23PD.get ⟨1, by decide⟩) (List.get_mem _ _)
  have e1 : (∑ i : Fin 2, k i * expSum i (g23PD.get ⟨1, by decide⟩)) = -4 * k 0 := by
    rw [Fin.sum_univ_two]
    have e0 : expSum (0 : Fin 2) (g23PD.get ⟨1, by decide⟩) = -4 := by decide
    have e1' : expSum (1 : Fin 2) (g23PD.get ⟨1, by decide⟩) = 0 := by decide
    rw [e0, e1']
    ring
  rw [e1] at hrow1
  have hrow3 := key (g23PD.get ⟨3, by decide⟩) (List.get_mem _ _)
  have e3 : (∑ i : Fin 2, k i * expSum i (g23PD.get ⟨3, by decide⟩)) = 2 * k 1 := by
    rw [Fin.sum_univ_two]
    have e0 : expSum (0 : Fin 2) (g23PD.get ⟨3, by decide⟩) = 0 := by decide
    have e1' : expSum (1 : Fin 2) (g23PD.get ⟨3, by decide⟩) = 2 := by decide
    rw [e0, e1']
    ring
  rw [e3] at hrow3
  have h3mul : ∀ j : Fin 2, c ^ (3 * k j) = 1 := by
    intro j
    rw [show (3 : ℤ) * k j = ((3 : ℕ) : ℤ) * k j from rfl, zpow_mul, zpow_natCast, hc3,
      one_zpow]
  intro i
  fin_cases i
  · have h4 : c ^ (4 * k 0) = 1 := by
      rw [show 4 * k 0 = -(-4 * k 0) by ring, zpow_neg, hrow1, inv_one]
    have h3 : c ^ (3 * k 0) = 1 := h3mul 0
    have h3neg : c ^ (-(3 * k 0)) = 1 := by rw [zpow_neg, h3, inv_one]
    have h : c ^ (4 * k 0 + -(3 * k 0)) = 1 := by
      rw [zpow_add, h4, h3neg, mul_one]
    rwa [show 4 * k 0 + -(3 * k 0) = k 0 by ring] at h
  · have h3 : c ^ (3 * k 1) = 1 := h3mul 1
    have h2neg : c ^ (-(2 * k 1)) = 1 := by rw [zpow_neg, hrow3, inv_one]
    have h : c ^ (3 * k 1 + -(2 * k 1)) = 1 := by
      rw [zpow_add, h3, h2neg, mul_one]
    rwa [show 3 * k 1 + -(2 * k 1) = k 1 by ring] at h

private theorem canon14_evalCode (r : List (Fin 6 × Bool)) : canon14 (evalCode r) = true := by
  have key : ∀ (r : List (Fin 6 × Bool)) (acc : List ℕ), canon14 acc = true →
      canon14 (r.foldl (fun acc l => mul14 acc (letterCode l)) acc) = true := by
    intro r
    induction r with
    | nil => intro acc h; exact h
    | cons l r ih =>
      intro acc h
      rw [List.foldl_cons]
      exact ih (mul14 acc (letterCode l)) (canon14_mul14 acc (letterCode l))
  exact key r one14 canon14_one14

private theorem lift_dEmbed {X : Type*} [Group X] (d : Fin 2 → X) (m : X)
    (r : List (Fin 2 × Bool)) :
    FreeGroup.lift d (FreeGroup.mk r) =
      FreeGroup.lift ![d 0, d 1, m] (FreeGroup.mk (dEmbed r)) := by
  rw [lift_mk, lift_mk, dEmbed, wprod_comp_letters]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem lift_flatten_replicate {X : Type*} [Group X] (m : Fin 3 → X)
    (w : List (Fin 3 × Bool)) (k : ℕ) :
    FreeGroup.lift m (FreeGroup.mk (List.flatten (List.replicate k w))) =
      (FreeGroup.lift m (FreeGroup.mk w)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, map_mul, ih, pow_succ']

theorem exists_letters_native_split
    (hinv : ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹)
    (j : Ghat) (hj : orderOf j = 2) :
    ∃ u : Fin 6 → Ghat, SatisfiesG23Words u ∧ Subgroup.closure (Set.range u) = ⊤ ∧
      (∀ i : Fin 5, Commute j (u (Fin.castSucc i))) ∧
      (∀ r ∈ g23PD,
        FreeGroup.lift (![evalW u dWord₁, evalW u dWord₂] : Fin 2 → Ghat) (FreeGroup.mk r) = 1) ∧
      orderOf (FreeGroup.lift (![evalW u dWord₁, evalW u dWord₂, u 5] : Fin 3 → Ghat)
        (FreeGroup.mk d2mWord)) = 7 := by
  obtain ⟨hz0sq_code, hz0ne_code, hz0comm_code, hpd_code, hd2mne_code, hd2mpow_code⟩ :=
    Certificates.certificate687007
  let u0 : Fin 6 → Ghat := fun i => adjointEquivR3.symm ⟨eEl i, eEl_mem i⟩
  have hu0 : ∀ i, (adjointEquivR3 (u0 i) : ↥R3) = ⟨eEl i, eEl_mem i⟩ := by
    intro i
    simp [u0]
  let f : Fin 6 → GL (Fin 14) (ZMod 3) := fun i => (adjointEquivR3 (u0 i) : ↥R3)
  have hf : ∀ i, f i = eEl i := by
    intro i
    simp [f, hu0]
  have evalW_append : ∀ (w w' : List (Fin 6 × Bool)),
      evalW u0 (w ++ w') = evalW u0 w * evalW u0 w' := by
    intro w w'
    simp only [evalW, lift_mk, wprod_append]
  have evalW_cons : ∀ (l : Fin 6 × Bool) (w : List (Fin 6 × Bool)),
      evalW u0 (l :: w) = (if l.2 then u0 l.1 else (u0 l.1)⁻¹) * evalW u0 w := by
    intro l w
    simp only [evalW, lift_mk, wprod_cons]
  have evalW_single : ∀ (i : Fin 6) (b : Bool),
      evalW u0 [(i, b)] = if b then u0 i else (u0 i)⁻¹ := by
    intro i b
    rw [evalW]
    exact lift_mk_single u0 i b
  have hf_cons : ∀ (l : Fin 6 × Bool) (w : List (Fin 6 × Bool)),
      FreeGroup.lift f (FreeGroup.mk (l :: w)) =
        (if l.2 then f l.1 else (f l.1)⁻¹) * FreeGroup.lift f (FreeGroup.mk w) := by
    intro l w
    rw [lift_mk, wprod_cons, ← lift_mk]
  have hlift : ∀ w : List (Fin 6 × Bool),
      ((adjointEquivR3 (evalW u0 w) : ↥R3) : GL (Fin 14) (ZMod 3)) =
        FreeGroup.lift f (FreeGroup.mk w) := by
    intro w
    induction w with
    | nil => simp [evalW]
    | cons l w ih =>
      rw [evalW_cons, map_mul, Subgroup.coe_mul, ih, hf_cons]
      congr 1
      obtain ⟨i, b⟩ := l
      cases b
      · simp [f]
      · simp [f]
  have hpsi_lift : ∀ w : List (Fin 6 × Bool),
      (((adjointEquivR3 (evalW u0 w) : ↥R3) : GL (Fin 14) (ZMod 3)) :
        Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 (evalCode w) := by
    intro w
    have h1 : ((adjointEquivR3 (evalW u0 w) : ↥R3) : GL (Fin 14) (ZMod 3)) =
        ((w.map Lt).prod : GL (Fin 14) (ZMod 3)) := by
      rw [hlift w, funext hf, lift_mk_eq]
    rw [h1, coe_Lt_prod]
  have hevalW_one : ∀ {w : List (Fin 6 × Bool)}, evalCode w = one14 → evalW u0 w = 1 := by
    intro w h
    apply adjointEquivR3.injective
    apply Subtype.ext
    apply Units.ext
    rw [hpsi_lift w, h, dec14_one14]
    simp
  have hevalW_ne : ∀ {w : List (Fin 6 × Bool)}, evalCode w ≠ one14 → evalW u0 w ≠ 1 := by
    intro w h h1
    apply h
    have hmat := hpsi_lift w
    rw [h1, map_one] at hmat
    simp at hmat
    exact dec14_injective (canon14_evalCode w) canon14_one14
      (hmat.symm.trans dec14_one14.symm)
  have hevalW_eq : ∀ {w w' : List (Fin 6 × Bool)}, evalCode w = evalCode w' →
      evalW u0 w = evalW u0 w' := by
    intro w w' h
    apply adjointEquivR3.injective
    apply Subtype.ext
    apply Units.ext
    rw [hpsi_lift w, hpsi_lift w', h]
  have hu0_sat : SatisfiesG23Words u0 := by
    intro r hr
    have h : ((adjointEquivR3 (evalW u0 r) : ↥R3) : GL (Fin 14) (ZMod 3)) = 1 := by
      rw [hlift r, funext hf]
      exact relator_eEl r hr
    apply adjointEquivR3.injective
    apply Subtype.ext
    apply Units.ext
    change (((adjointEquivR3 (evalW u0 r) : ↥R3) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) =
        (((adjointEquivR3 (1 : Ghat) : ↥R3) : GL (Fin 14) (ZMod 3)) :
          Matrix (Fin 14) (Fin 14) (ZMod 3))
    rw [h]
    simp
  have hR3closure : Subgroup.closure (Set.range eEl) ≤ R3 :=
    (Subgroup.closure_le R3).mpr (by rintro _ ⟨i, rfl⟩; exact eEl_mem i)
  have hgenR : Subgroup.closure (Set.range (fun i => adjointEquivR3 (u0 i))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hyGL : (y : GL (Fin 14) (ZMod 3)) ∈ Subgroup.closure (Set.range eEl) :=
      R3_le_closure y.2
    have hmem : (⟨(y : GL (Fin 14) (ZMod 3)), hR3closure hyGL⟩ : ↥R3) ∈
        Subgroup.closure (Set.range (fun i => adjointEquivR3 (u0 i))) := by
      refine Subgroup.closure_induction (p := fun z hz =>
        (⟨z, hR3closure hz⟩ : ↥R3) ∈
          Subgroup.closure (Set.range (fun i => adjointEquivR3 (u0 i)))) ?_ ?_ ?_ ?_ hyGL
      · rintro _ ⟨i, rfl⟩
        have h : (⟨eEl i, hR3closure (Subgroup.subset_closure ⟨i, rfl⟩)⟩ : ↥R3) =
            adjointEquivR3 (u0 i) := by
          apply Subtype.ext
          simp [hu0]
        rw [h]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · have h : (⟨1, hR3closure (Subgroup.one_mem _)⟩ : ↥R3) = 1 := Subtype.ext rfl
        rw [h]
        exact (Subgroup.closure _).one_mem
      · intro a b ha hb ha' hb'
        have h : (⟨a * b, hR3closure (Subgroup.mul_mem _ ha hb)⟩ : ↥R3) =
            (⟨a, hR3closure ha⟩ : ↥R3) * (⟨b, hR3closure hb⟩ : ↥R3) := Subtype.ext rfl
        rw [h]
        exact (Subgroup.closure _).mul_mem ha' hb'
      · intro a ha ha'
        have h : (⟨a⁻¹, hR3closure (Subgroup.inv_mem _ ha)⟩ : ↥R3) =
            (⟨a, hR3closure ha⟩ : ↥R3)⁻¹ := Subtype.ext rfl
        rw [h]
        exact (Subgroup.closure _).inv_mem ha'
    convert hmem using 1
  have hu0_gen : Subgroup.closure (Set.range u0) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxR : adjointEquivR3 x ∈
        Subgroup.closure (Set.range (fun i => adjointEquivR3 (u0 i))) := by
      rw [hgenR]
      trivial
    have hpre : adjointEquivR3.symm (adjointEquivR3 x) ∈
        Subgroup.closure (Set.range u0) := by
      refine Subgroup.closure_induction (p := fun z _ =>
        adjointEquivR3.symm z ∈ Subgroup.closure (Set.range u0)) ?_ ?_ ?_ ?_ hxR
      · rintro _ ⟨i, rfl⟩
        have h : adjointEquivR3.symm (adjointEquivR3 (u0 i)) = u0 i := by simp
        rw [h]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · simp
      · intro a b _ _ ha hb
        rw [map_mul]
        exact (Subgroup.closure _).mul_mem ha hb
      · intro a _ ha
        rw [map_inv]
        exact (Subgroup.closure _).inv_mem ha
    simpa using hpre
  let z0 : Ghat := evalW u0 z0Word
  have hz0sq : z0 * z0 = 1 := by
    have h1 : evalW u0 (z0Word ++ z0Word) = 1 := hevalW_one hz0sq_code
    rw [← h1, evalW_append]
  have hz0ne : z0 ≠ 1 := hevalW_ne hz0ne_code
  have hz0comm : ∀ i : Fin 5, Commute z0 (u0 (Fin.castSucc i)) := by
    intro i
    have h1 : evalW u0 (z0Word ++ [(Fin.castSucc i, true)]) =
        evalW u0 ((Fin.castSucc i, true) :: z0Word) := hevalW_eq (hz0comm_code i)
    rw [evalW_append, evalW_single, evalW_cons] at h1
    exact h1
  have hz0ord : orderOf z0 = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hz0sq
    · exact hz0ne
  obtain ⟨g, hg⟩ := hinv z0 j hz0ord hj
  let u : Fin 6 → Ghat := fun i => g * u0 i * g⁻¹
  have hu_lift : FreeGroup.lift u = (MulAut.conj g).toMonoidHom.comp (FreeGroup.lift u0) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [u, MulAut.conj_apply]
  have hu_sat : SatisfiesG23Words u := by
    intro r hr
    rw [hu_lift, MonoidHom.comp_apply, hu0_sat r hr, map_one]
  have hu_gen : Subgroup.closure (Set.range u) = ⊤ := by
    have hrange : Set.range u = MulAut.conj g '' Set.range u0 := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨u0 i, ⟨i, rfl⟩, by simp [u, MulAut.conj_apply]⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp [u, MulAut.conj_apply]⟩
    rw [hrange]
    have hmap : Subgroup.closure (⇑(MulAut.conj g) '' Set.range u0) =
        Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.closure (Set.range u0)) :=
      (MonoidHom.map_closure (MulAut.conj g).toMonoidHom (Set.range u0)).symm
    rw [hmap, hu0_gen]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  have hu_comm : ∀ i : Fin 5, Commute j (u (Fin.castSucc i)) := by
    intro i
    have hzi : Commute z0 (u0 (Fin.castSucc i)) := hz0comm i
    rw [hg]
    show (g * z0 * g⁻¹) * (g * u0 (Fin.castSucc i) * g⁻¹) =
      (g * u0 (Fin.castSucc i) * g⁻¹) * (g * z0 * g⁻¹)
    calc (g * z0 * g⁻¹) * (g * u0 (Fin.castSucc i) * g⁻¹)
        = g * (z0 * u0 (Fin.castSucc i)) * g⁻¹ := by group
      _ = g * (u0 (Fin.castSucc i) * z0) * g⁻¹ := by rw [hzi.eq]
      _ = (g * u0 (Fin.castSucc i) * g⁻¹) * (g * z0 * g⁻¹) := by group
  have evalW_conj : ∀ w : List (Fin 6 × Bool),
      evalW u w = g * evalW u0 w * g⁻¹ := by
    intro w
    rw [evalW, hu_lift, MonoidHom.comp_apply]
    change (MulAut.conj g) (FreeGroup.lift u0 (FreeGroup.mk w)) =
      g * evalW u0 w * g⁻¹
    rw [MulAut.conj_apply]
    rfl
  have hu_pd : ∀ r ∈ g23PD,
      FreeGroup.lift (![evalW u dWord₁, evalW u dWord₂] : Fin 2 → Ghat)
        (FreeGroup.mk r) = 1 := by
    intro r hr
    let dU : Fin 2 → Ghat := ![evalW u dWord₁, evalW u dWord₂]
    let d0 : Fin 2 → Ghat := ![evalW u0 dWord₁, evalW u0 dWord₂]
    have hU : dU = fun i => g * d0 i * g⁻¹ := by
      funext i
      fin_cases i <;> simp [dU, d0, evalW_conj]
    have hlift : FreeGroup.lift dU (FreeGroup.mk r) =
        g * FreeGroup.lift d0 (FreeGroup.mk r) * g⁻¹ := by
      rw [hU]
      have hcomp : FreeGroup.lift (fun i => g * d0 i * g⁻¹) =
          (MulAut.conj g).toMonoidHom.comp (FreeGroup.lift d0) := by
        refine FreeGroup.ext_hom _ _ fun i => ?_
        simp [MulAut.conj_apply]
      rw [hcomp, MonoidHom.comp_apply]
      change (MulAut.conj g) (FreeGroup.lift d0 (FreeGroup.mk r)) =
        g * FreeGroup.lift d0 (FreeGroup.mk r) * g⁻¹
      rw [MulAut.conj_apply]
    rw [hlift]
    have h0 : FreeGroup.lift d0 (FreeGroup.mk r) = 1 := by
      rw [lift_dEmbed d0 (u0 5) r]
      have h := hevalW_one (hpd_code r hr)
      rw [evalW] at h
      rw [lift_substWord u0 (dEmbed r)] at h
      simpa [d0] using h
    rw [h0, mul_one, mul_inv_cancel]
  have hu_order : orderOf (FreeGroup.lift
      (![evalW u dWord₁, evalW u dWord₂, u 5] : Fin 3 → Ghat)
      (FreeGroup.mk d2mWord)) = 7 := by
    let mU : Fin 3 → Ghat := ![evalW u dWord₁, evalW u dWord₂, u 5]
    let m0 : Fin 3 → Ghat := ![evalW u0 dWord₁, evalW u0 dWord₂, u0 5]
    have hmU : mU = fun i => g * m0 i * g⁻¹ := by
      funext i
      fin_cases i <;> simp [mU, m0, evalW_conj, u]
    have hx_conj : FreeGroup.lift mU (FreeGroup.mk d2mWord) =
        g * FreeGroup.lift m0 (FreeGroup.mk d2mWord) * g⁻¹ := by
      rw [hmU]
      have hcomp : FreeGroup.lift (fun i => g * m0 i * g⁻¹) =
          (MulAut.conj g).toMonoidHom.comp (FreeGroup.lift m0) := by
        refine FreeGroup.ext_hom _ _ fun i => ?_
        simp [MulAut.conj_apply]
      rw [hcomp, MonoidHom.comp_apply]
      change (MulAut.conj g) (FreeGroup.lift m0 (FreeGroup.mk d2mWord)) =
        g * FreeGroup.lift m0 (FreeGroup.mk d2mWord) * g⁻¹
      rw [MulAut.conj_apply]
    have hx0_ne : FreeGroup.lift m0 (FreeGroup.mk d2mWord) ≠ 1 := by
      have h := hevalW_ne hd2mne_code
      rw [evalW] at h
      rwa [lift_substWord u0 d2mWord] at h
    have hx0_pow : (FreeGroup.lift m0 (FreeGroup.mk d2mWord)) ^ 7 = 1 := by
      have h := hevalW_one hd2mpow_code
      rw [evalW] at h
      rw [lift_substWord u0 (List.flatten (List.replicate 7 d2mWord))] at h
      rw [lift_flatten_replicate m0 d2mWord 7] at h
      exact h
    have hx0_ord : orderOf (FreeGroup.lift m0 (FreeGroup.mk d2mWord)) = 7 := by
      apply orderOf_eq_prime
      · exact hx0_pow
      · exact hx0_ne
    rw [hx_conj]
    rw [show g * FreeGroup.lift m0 (FreeGroup.mk d2mWord) * g⁻¹ =
      (MulAut.conj g) (FreeGroup.lift m0 (FreeGroup.mk d2mWord)) from by
        rw [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq]
    exact hx0_ord
  exact ⟨u, hu_sat, hu_gen, hu_comm, hu_pd, hu_order⟩

end CFSG.Sporadic.Th.Recog

end
