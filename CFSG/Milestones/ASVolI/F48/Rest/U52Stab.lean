module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Facts
public import CFSG.Milestones.ASVolI.F48.Rest.G23Stab
public import Certificates.Certificate7770

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr

@[expose] def burnsideF48t_u52pA : Fin 462 := ⟨0, by norm_num⟩

@[expose] def burnsideF48t_u52pB : Fin 462 := ⟨165, by norm_num⟩

@[expose] noncomputable def burnsideF48t_u52hA (j : ℕ) : Equiv.Perm (Fin 462) :=
  burnsideF48s_ev (fun i : Fin 6 => burnsideF48t_u52γ i) (burnsideF48t_u52HA.getD j [])

@[expose] noncomputable def burnsideF48t_u52hB (j : ℕ) : Equiv.Perm (Fin 462) :=
  burnsideF48s_ev (fun i : Fin 6 => burnsideF48t_u52γ i) (burnsideF48t_u52HB.getD j [])

@[expose] noncomputable def burnsideF48t_u52κ (i : ℕ) : Equiv.Perm (Fin 462) :=
  burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52KW.getD i [])

section Model

theorem burnsideF48t_u52_recG : burnsideF48t_RecL 462 (burnsideF48t_u52Gens ())
    ((burnsideF48t_u52Gens ()).map (pinvCand 462)) (fun i : Fin 6 => burnsideF48t_u52γ i) :=
  fun i => burnsideF48t_u52_prep_γ i.2

theorem burnsideF48t_u52_X_lt {g : Equiv.Perm (Fin 462)} (hg : g ∈ burnsideF48t_u52X)
    {x : Fin 462} (hx : (x : ℕ) < 165) : ((g x : Fin 462) : ℕ) < 165 :=
  (burnsideF48t_u52_orbX.1 _).1 (MulAction.mem_orbit_of_mem_orbit (⟨g, hg⟩ : burnsideF48t_u52X)
    ((burnsideF48t_u52_orbX.1 x).2 hx))

theorem burnsideF48t_u52_X_ge {g : Equiv.Perm (Fin 462)} (hg : g ∈ burnsideF48t_u52X)
    {x : Fin 462} (hx : 165 ≤ (x : ℕ)) : 165 ≤ ((g x : Fin 462) : ℕ) := by
  by_contra h
  have := burnsideF48t_u52_X_lt (burnsideF48t_u52X.inv_mem hg) (not_le.1 h)
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at this
  omega

theorem burnsideF48t_u52_P1'_le_X : burnsideF48t_u52P1' ≤ burnsideF48t_u52X := by
  rw [burnsideF48t_u52_P1'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  have hk : (k : ℕ) < 3 := burnsideF48t_u52_P1Arr.1 ▸ k.2
  exact burnsideF48t_u52_σ_mem (by unfold burnsideF48t_u52P1Idx; omega)

theorem burnsideF48t_u52_P2'_le_X : burnsideF48t_u52P2' ≤ burnsideF48t_u52X := by
  rw [burnsideF48t_u52_P2'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  have hk : (k : ℕ) < 3 := burnsideF48t_u52_P2Arr.1 ▸ k.2
  exact burnsideF48t_u52_σ_mem (by unfold burnsideF48t_u52P2Idx; omega)

theorem burnsideF48t_u52_σ_val {i : ℕ} (hi : i < 4) (x : Fin 462) :
    ((burnsideF48t_u52σ i x : Fin 462) : ℕ) = (burnsideF48t_u52LArr[i]!)[(x : ℕ)]! :=
  ((burnsideF48t_u52_prep_σ hi).1 x).symm

theorem burnsideF48t_u52_σ_fix :
    burnsideF48t_u52σ 0 burnsideF48t_u52pA = burnsideF48t_u52pA ∧
    burnsideF48t_u52σ 0 burnsideF48t_u52pB = burnsideF48t_u52pB ∧
    burnsideF48t_u52σ 1 burnsideF48t_u52pA = burnsideF48t_u52pA ∧
    burnsideF48t_u52σ 1 burnsideF48t_u52pB = burnsideF48t_u52pB ∧
    burnsideF48t_u52σ 2 burnsideF48t_u52pA = burnsideF48t_u52pA ∧
    burnsideF48t_u52σ 3 burnsideF48t_u52pB = burnsideF48t_u52pB ∧
    burnsideF48t_u52σ 3 burnsideF48t_u52pA ≠ burnsideF48t_u52pA ∧
    burnsideF48t_u52σ 2 burnsideF48t_u52pB ≠ burnsideF48t_u52pB := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := burnsideF48t_u52_fix
  refine ⟨Fin.ext ((burnsideF48t_u52_σ_val (i := 0) (by norm_num) _).trans f1),
    Fin.ext ((burnsideF48t_u52_σ_val (i := 0) (by norm_num) _).trans f2),
    Fin.ext ((burnsideF48t_u52_σ_val (i := 1) (by norm_num) _).trans f3),
    Fin.ext ((burnsideF48t_u52_σ_val (i := 1) (by norm_num) _).trans f4),
    Fin.ext ((burnsideF48t_u52_σ_val (i := 2) (by norm_num) _).trans f5),
    Fin.ext ((burnsideF48t_u52_σ_val (i := 3) (by norm_num) _).trans f6),
    fun h => f7 ((burnsideF48t_u52_σ_val (i := 3) (by norm_num) _).symm.trans
      (congrArg Fin.val h)),
    fun h => f8 ((burnsideF48t_u52_σ_val (i := 2) (by norm_num) _).symm.trans
      (congrArg Fin.val h))⟩

theorem burnsideF48t_u52_P1Idx_cases (k : Fin burnsideF48t_u52P1Arr.size) :
    burnsideF48t_u52P1Idx k = 0 ∨ burnsideF48t_u52P1Idx k = 1 ∨ burnsideF48t_u52P1Idx k = 2 := by
  have : (k : ℕ) < 3 := burnsideF48t_u52_P1Arr.1 ▸ k.2
  unfold burnsideF48t_u52P1Idx
  omega

theorem burnsideF48t_u52_P2Idx_cases (k : Fin burnsideF48t_u52P2Arr.size) :
    burnsideF48t_u52P2Idx k = 0 ∨ burnsideF48t_u52P2Idx k = 1 ∨ burnsideF48t_u52P2Idx k = 3 := by
  have : (k : ℕ) < 3 := burnsideF48t_u52_P2Arr.1 ▸ k.2
  unfold burnsideF48t_u52P2Idx
  omega

theorem burnsideF48t_u52_P1'_le_stab : burnsideF48t_u52P1' ≤
    MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pA := by
  rw [burnsideF48t_u52_P1'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨f0, -, f1, -, f2, -⟩ := burnsideF48t_u52_σ_fix
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  rcases burnsideF48t_u52_P1Idx_cases k with h | h | h <;> simp only [h] <;> assumption

theorem burnsideF48t_u52_P2'_le_stab : burnsideF48t_u52P2' ≤
    MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB := by
  rw [burnsideF48t_u52_P2'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨-, f0, -, f1, -, f3, -⟩ := burnsideF48t_u52_σ_fix
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  rcases burnsideF48t_u52_P2Idx_cases k with h | h | h <;> simp only [h] <;> assumption

theorem burnsideF48t_u52_card_orbit_mul (K : Subgroup (Equiv.Perm (Fin 462))) (b : Fin 462) :
    Nat.card (MulAction.orbit K b) *
      Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) b) = Nat.card K := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K b), Nat.card_prod]
  congr 1
  exact Nat.card_congr
    { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

theorem burnsideF48t_u52_card_pts : Nat.card {p : Fin 462 | (p : ℕ) < 165} = 165 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  decide +kernel

theorem burnsideF48t_u52_card_lines : Nat.card {p : Fin 462 | 165 ≤ (p : ℕ)} = 297 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  decide +kernel

theorem burnsideF48t_u52_eq_of_orbit {O : Array (Array ℕ)} {t : Array ℕ}
    {h : Equiv.Perm (Fin 462)} (ht : PRep 462 t h) {root : Fin 462} {S : Set (Fin 462)}
    (hS : ∀ p, p ∈ MulAction.orbit (arrGen 462 (O.push t)) root ↔ p ∈ S)
    {P X Q : Subgroup (Equiv.Perm (Fin 462))} (hPO : P = arrGen 462 O)
    (hPfix : P ≤ MulAction.stabilizer (Equiv.Perm (Fin 462)) root)
    (hcard : Nat.card X ≤ Nat.card S * Nat.card P) (hPQ : P ≤ Q) (hhQ : h ∈ Q) (hQX : Q ≤ X) :
    Q = X := by
  have hCQ : arrGen 462 (O.push t) ≤ Q := burnsideF48t_arrGen_le fun t' ht' => by
    rcases Array.mem_push.1 ht' with h1 | rfl
    · exact hPQ (hPO ▸ burnsideF48t_permOfArr_mem_arrGen h1)
    · rw [permOfArr_eq_of_prep ht]
      exact hhQ
  have hPC : P ≤ arrGen 462 (O.push t) := hPO ▸ burnsideF48t_arrGen_le fun t' ht' =>
    burnsideF48t_permOfArr_mem_arrGen (Array.mem_push.2 (Or.inl ht'))
  have h1 := burnsideF48t_u52_card_orbit_mul (arrGen 462 (O.push t)) root
  rw [Set.ext hS] at h1
  have h2 : Nat.card P ≤ Nat.card ↥(arrGen 462 (O.push t) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 462)) root) :=
    Subgroup.card_le_of_le (le_inf hPC hPfix)
  have h3 : Nat.card X ≤ Nat.card Q :=
    calc Nat.card X ≤ Nat.card S * Nat.card P := hcard
      _ ≤ Nat.card S * Nat.card ↥(arrGen 462 (O.push t) ⊓
          MulAction.stabilizer (Equiv.Perm (Fin 462)) root) := Nat.mul_le_mul_left _ h2
      _ = Nat.card (arrGen 462 (O.push t)) := h1
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hCQ
  exact Subgroup.eq_of_le_of_card_ge hQX h3

theorem burnsideF48t_u52_P1'_eq : burnsideF48t_u52P1' =
    burnsideF48t_u52X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pA := by
  refine Subgroup.eq_of_le_of_card_ge
    (le_inf burnsideF48t_u52_P1'_le_X burnsideF48t_u52_P1'_le_stab) ?_
  have h := burnsideF48t_u52_card_orbit_mul burnsideF48t_u52X burnsideF48t_u52pA
  have e : MulAction.orbit burnsideF48t_u52X burnsideF48t_u52pA = {p : Fin 462 | (p : ℕ) < 165} :=
    Set.ext burnsideF48t_u52_orbX.1
  rw [e, burnsideF48t_u52_card_pts, burnsideF48t_u52_card_X] at h
  rw [burnsideF48t_u52_card_P1']
  omega

theorem burnsideF48t_u52_P2'_eq : burnsideF48t_u52P2' =
    burnsideF48t_u52X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB := by
  refine Subgroup.eq_of_le_of_card_ge
    (le_inf burnsideF48t_u52_P2'_le_X burnsideF48t_u52_P2'_le_stab) ?_
  have h := burnsideF48t_u52_card_orbit_mul burnsideF48t_u52X burnsideF48t_u52pB
  have e : MulAction.orbit burnsideF48t_u52X burnsideF48t_u52pB = {p : Fin 462 | 165 ≤ (p : ℕ)} :=
    Set.ext burnsideF48t_u52_orbX.2
  rw [e, burnsideF48t_u52_card_lines, burnsideF48t_u52_card_X] at h
  rw [burnsideF48t_u52_card_P2']
  omega

theorem burnsideF48t_u52_orbP1 :
    Nat.card (MulAction.orbit burnsideF48t_u52P1' burnsideF48t_u52pB) = 9 ∧
    (∀ p : Fin 462, 1 ≤ (p : ℕ) → (p : ℕ) < 165 →
      p ∈ MulAction.orbit burnsideF48t_u52P1' (1 : Fin 462) ∨
        p ∈ MulAction.orbit burnsideF48t_u52P1' (15 : Fin 462)) ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HA)[0]!)[0]! = 1 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HA)[1]!)[0]! = 15 ∧
    ∀ j < 2, ∀ p : Fin 462, p ∈ MulAction.orbit (arrGen 462
      (burnsideF48t_u52P1Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]!))
        burnsideF48t_u52pA ↔ p ∈ {p : Fin 462 | (p : ℕ) < 165} := by
  obtain ⟨-, -, c9, -, -, cov, -, e0, e1, horb, -⟩ := Certificates.certificate7769
  exact ⟨c9, cov, e0, e1, horb⟩

theorem burnsideF48t_u52_orbP2 :
    (∀ p : Fin 462, 166 ≤ (p : ℕ) →
      p ∈ MulAction.orbit burnsideF48t_u52P2' (166 : Fin 462) ∨
        p ∈ MulAction.orbit burnsideF48t_u52P2' (175 : Fin 462)) ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HB)[0]!)[165]! = 166 ∧
    ((burnsideF48t_u52HArr burnsideF48t_u52HB)[1]!)[165]! = 175 ∧
    ∀ j < 2, ∀ p : Fin 462, p ∈ MulAction.orbit (arrGen 462
      (burnsideF48t_u52P2Arr.push (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]!))
        burnsideF48t_u52pB ↔ p ∈ {p : Fin 462 | 165 ≤ (p : ℕ)} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, cov, -, e0, e1, horb, -⟩ :=
    Certificates.certificate7769
  exact ⟨cov, e0, e1, horb⟩

theorem burnsideF48t_u52_B'_eq : burnsideF48t_u52B' = burnsideF48t_u52P1' ⊓ burnsideF48t_u52P2' := by
  have hle : burnsideF48t_u52B' ≤ burnsideF48t_u52P1' ⊓ burnsideF48t_u52P2' := by
    rw [burnsideF48t_u52_B'_eq_closure, Subgroup.closure_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    have hk2 : k < 2 := burnsideF48t_u52_BArr.1 ▸ hk
    refine ⟨?_, ?_⟩
    · rw [burnsideF48t_u52_P1'_eq_closure]
      exact Subgroup.subset_closure ⟨⟨k, by rw [burnsideF48t_u52_P1Arr.1]; omega⟩, rfl⟩
    · rw [burnsideF48t_u52_P2'_eq_closure]
      refine Subgroup.subset_closure ⟨⟨k, by rw [burnsideF48t_u52_P2Arr.1]; omega⟩, ?_⟩
      show burnsideF48t_u52σ (burnsideF48t_u52P2Idx k) = burnsideF48t_u52σ (burnsideF48t_u52P1Idx k)
      congr 1
      unfold burnsideF48t_u52P2Idx burnsideF48t_u52P1Idx
      omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h := burnsideF48t_u52_card_orbit_mul burnsideF48t_u52P1' burnsideF48t_u52pB
  rw [burnsideF48t_u52_orbP1.1, burnsideF48t_u52_card_P1'] at h
  have hinf : burnsideF48t_u52P1' ⊓ burnsideF48t_u52P2' =
      burnsideF48t_u52P1' ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB := by
    rw [burnsideF48t_u52_P2'_eq, ← inf_assoc, inf_eq_left.2 burnsideF48t_u52_P1'_le_X]
  rw [hinf, burnsideF48t_u52_card_B']
  omega

theorem burnsideF48t_u52_prep_hA {j : ℕ} (hj : j < 2) :
    PRep 462 (burnsideF48t_u52HArr burnsideF48t_u52HA)[j]! (burnsideF48t_u52hA j) := by
  unfold burnsideF48t_u52HArr
  rw [burnsideF48t_getElem!_toArray_map _ _ (by simpa [burnsideF48t_u52HA] using hj) []]
  exact burnsideF48t_prep_evA burnsideF48t_u52_recG _

theorem burnsideF48t_u52_prep_hB {j : ℕ} (hj : j < 2) :
    PRep 462 (burnsideF48t_u52HArr burnsideF48t_u52HB)[j]! (burnsideF48t_u52hB j) := by
  unfold burnsideF48t_u52HArr
  rw [burnsideF48t_getElem!_toArray_map _ _ (by simpa [burnsideF48t_u52HB] using hj) []]
  exact burnsideF48t_prep_evA burnsideF48t_u52_recG _

theorem burnsideF48t_u52_hA_mem (j : ℕ) : burnsideF48t_u52hA j ∈ burnsideF48t_u52X :=
  burnsideF48s_ev_mem _ _ fun l _ => burnsideF48t_u52_γ_mem l.1.2

theorem burnsideF48t_u52_hB_mem (j : ℕ) : burnsideF48t_u52hB j ∈ burnsideF48t_u52X :=
  burnsideF48s_ev_mem _ _ fun l _ => burnsideF48t_u52_γ_mem l.1.2

theorem burnsideF48t_u52_P1'_max {R : Subgroup (Equiv.Perm (Fin 462))}
    (hlt : burnsideF48t_u52P1' < R) (hRX : R ≤ burnsideF48t_u52X) : R = burnsideF48t_u52X := by
  refine burnsideF48t_max_of_stab burnsideF48t_u52_P1'_eq ?_ hlt hRX
  intro g hg hgpt
  obtain ⟨-, hcov, e0, e1, horb⟩ := burnsideF48t_u52_orbP1
  have hr : ((g burnsideF48t_u52pA : Fin 462) : ℕ) < 165 :=
    burnsideF48t_u52_X_lt hg (show ((burnsideF48t_u52pA : Fin 462) : ℕ) < 165 by decide)
  have hr0 : ((g burnsideF48t_u52pA : Fin 462) : ℕ) ≠ 0 := fun h => hgpt (Fin.ext h)
  have hgen : ∀ j < 2, ∀ Q : Subgroup (Equiv.Perm (Fin 462)), burnsideF48t_u52P1' ≤ Q →
      burnsideF48t_u52hA j ∈ Q → Q ≤ burnsideF48t_u52X → Q = burnsideF48t_u52X :=
    fun j hj Q h1 h2 h3 => burnsideF48t_u52_eq_of_orbit (burnsideF48t_u52_prep_hA hj) (horb j hj)
      (P := burnsideF48t_u52P1') rfl burnsideF48t_u52_P1'_le_stab
      (by rw [burnsideF48t_u52_card_pts, burnsideF48t_u52_card_X, burnsideF48t_u52_card_P1'])
      h1 h2 h3
  have hfin : ∀ j < 2, ∀ r : Fin 462, ((burnsideF48t_u52HArr burnsideF48t_u52HA)[j]!)[0]! = (r : ℕ) →
      g burnsideF48t_u52pA ∈ MulAction.orbit burnsideF48t_u52P1' r →
      ∃ q ∈ burnsideF48t_u52P1', ∃ h ∈ burnsideF48t_u52X,
        q (h burnsideF48t_u52pA) = g burnsideF48t_u52pA ∧
        ∀ Q : Subgroup (Equiv.Perm (Fin 462)), burnsideF48t_u52P1' ≤ Q → h ∈ Q →
          Q ≤ burnsideF48t_u52X → Q = burnsideF48t_u52X := by
    rintro j hj r he ⟨⟨q, hq⟩, hqe⟩
    refine ⟨q, hq, burnsideF48t_u52hA j, burnsideF48t_u52_hA_mem j, ?_, hgen j hj⟩
    have e : burnsideF48t_u52hA j burnsideF48t_u52pA = r :=
      Fin.ext (((burnsideF48t_u52_prep_hA hj) burnsideF48t_u52pA).symm.trans he)
    rw [e]
    exact hqe
  rcases hcov (g burnsideF48t_u52pA) (by omega) hr with h | h
  · exact hfin 0 (by decide) 1 e0 h
  · exact hfin 1 (by decide) 15 e1 h

theorem burnsideF48t_u52_P2'_max {R : Subgroup (Equiv.Perm (Fin 462))}
    (hlt : burnsideF48t_u52P2' < R) (hRX : R ≤ burnsideF48t_u52X) : R = burnsideF48t_u52X := by
  refine burnsideF48t_max_of_stab burnsideF48t_u52_P2'_eq ?_ hlt hRX
  intro g hg hgpt
  obtain ⟨hcov, e0, e1, horb⟩ := burnsideF48t_u52_orbP2
  have hr : 165 ≤ ((g burnsideF48t_u52pB : Fin 462) : ℕ) :=
    burnsideF48t_u52_X_ge hg (show 165 ≤ ((burnsideF48t_u52pB : Fin 462) : ℕ) by decide)
  have hr0 : ((g burnsideF48t_u52pB : Fin 462) : ℕ) ≠ 165 := fun h => hgpt (Fin.ext h)
  have hgen : ∀ j < 2, ∀ Q : Subgroup (Equiv.Perm (Fin 462)), burnsideF48t_u52P2' ≤ Q →
      burnsideF48t_u52hB j ∈ Q → Q ≤ burnsideF48t_u52X → Q = burnsideF48t_u52X :=
    fun j hj Q h1 h2 h3 => burnsideF48t_u52_eq_of_orbit (burnsideF48t_u52_prep_hB hj) (horb j hj)
      (P := burnsideF48t_u52P2') rfl burnsideF48t_u52_P2'_le_stab
      (by rw [burnsideF48t_u52_card_lines, burnsideF48t_u52_card_X, burnsideF48t_u52_card_P2'])
      h1 h2 h3
  have hfin : ∀ j < 2, ∀ r : Fin 462, ((burnsideF48t_u52HArr burnsideF48t_u52HB)[j]!)[165]! = (r : ℕ) →
      g burnsideF48t_u52pB ∈ MulAction.orbit burnsideF48t_u52P2' r →
      ∃ q ∈ burnsideF48t_u52P2', ∃ h ∈ burnsideF48t_u52X,
        q (h burnsideF48t_u52pB) = g burnsideF48t_u52pB ∧
        ∀ Q : Subgroup (Equiv.Perm (Fin 462)), burnsideF48t_u52P2' ≤ Q → h ∈ Q →
          Q ≤ burnsideF48t_u52X → Q = burnsideF48t_u52X := by
    rintro j hj r he ⟨⟨q, hq⟩, hqe⟩
    refine ⟨q, hq, burnsideF48t_u52hB j, burnsideF48t_u52_hB_mem j, ?_, hgen j hj⟩
    have e : burnsideF48t_u52hB j burnsideF48t_u52pB = r :=
      Fin.ext (((burnsideF48t_u52_prep_hB hj) burnsideF48t_u52pB).symm.trans he)
    rw [e]
    exact hqe
  rcases hcov (g burnsideF48t_u52pB) (by omega) with h | h
  · exact hfin 0 (by decide) 166 e0 h
  · exact hfin 1 (by decide) 175 e1 h

end Model

section Norm

theorem burnsideF48t_u52_S0Arr_rep {t : Array ℕ} (ht : t ∈ burnsideF48t_u52S0Arr ()) :
    ∃ w ∈ burnsideF48t_u52SW,
      PRep 462 t (burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_u52σ i) w) := by
  simp only [burnsideF48t_u52S0Arr, List.mem_toArray, List.mem_map] at ht
  obtain ⟨w, hw, rfl⟩ := ht
  exact ⟨w, hw, burnsideF48t_prep_evA burnsideF48t_u52_recL w⟩

theorem burnsideF48t_u52_S0'_le_X : burnsideF48t_u52S0' ≤ burnsideF48t_u52X := by
  refine burnsideF48t_arrGen_le fun t ht => ?_
  obtain ⟨w, -, hw⟩ := burnsideF48t_u52_S0Arr_rep ht
  rw [permOfArr_eq_of_prep hw]
  exact burnsideF48s_ev_mem _ w fun l _ => burnsideF48t_u52_σ_mem l.1.2

theorem burnsideF48t_u52_S0'_fix {s : Equiv.Perm (Fin 462)} (hs : s ∈ burnsideF48t_u52S0') :
    s burnsideF48t_u52pA = burnsideF48t_u52pA ∧ s burnsideF48t_u52pB = burnsideF48t_u52pB := by
  have hle : burnsideF48t_u52S0' ≤
      MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pA ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 462)) burnsideF48t_u52pB := by
    refine burnsideF48t_arrGen_le fun t ht => ?_
    obtain ⟨w, -, hw⟩ := burnsideF48t_u52_S0Arr_rep ht
    have hfix := burnsideF48t_u52_fix.2.2.2.2.2.2.2.2.1 t ht
    rw [permOfArr_eq_of_prep hw]
    refine ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩ <;>
      rw [Equiv.Perm.smul_def] <;> apply Fin.ext
    · rw [← hw burnsideF48t_u52pA]; exact hfix.1
    · rw [← hw burnsideF48t_u52pB]; exact hfix.2
  have := hle hs
  exact ⟨MulAction.mem_stabilizer_iff.1 this.1, MulAction.mem_stabilizer_iff.1 this.2⟩

theorem burnsideF48t_u52_S0'_moves {p : Fin 462} (h0 : p ≠ burnsideF48t_u52pA)
    (h165 : p ≠ burnsideF48t_u52pB) : ∃ s ∈ burnsideF48t_u52S0', s p ≠ p := by
  obtain ⟨t, ht, htp⟩ := burnsideF48t_u52_fix.2.2.2.2.2.2.2.2.2 p p.2
    (fun h => h0 (Fin.ext h)) (fun h => h165 (Fin.ext h))
  obtain ⟨w, -, hw⟩ := burnsideF48t_u52_S0Arr_rep ht
  refine ⟨CFSG.Monster.B.Co2.permOfArr 462 t, burnsideF48t_permOfArr_mem_arrGen ht,
    fun he => htp ?_⟩
  rw [permOfArr_eq_of_prep hw] at he
  rw [hw p, he]

theorem burnsideF48t_u52_fix_of_norm {g : Equiv.Perm (Fin 462)} (hg : g ∈ burnsideF48t_u52X)
    (hn : ∀ s ∈ burnsideF48t_u52S0', g⁻¹ * s * g ∈ burnsideF48t_u52S0') :
    g burnsideF48t_u52pA = burnsideF48t_u52pA ∧ g burnsideF48t_u52pB = burnsideF48t_u52pB := by
  have hfixed : ∀ x, (x = burnsideF48t_u52pA ∨ x = burnsideF48t_u52pB) →
      (g x = burnsideF48t_u52pA ∨ g x = burnsideF48t_u52pB) := by
    intro x hx
    by_contra hne
    rw [not_or] at hne
    obtain ⟨s, hs, hsx⟩ := burnsideF48t_u52_S0'_moves hne.1 hne.2
    have h1 := burnsideF48t_u52_S0'_fix (hn s hs)
    apply hsx
    have : (g⁻¹ * s * g) x = x := by rcases hx with rfl | rfl; exacts [h1.1, h1.2]
    simp only [Equiv.Perm.mul_apply] at this
    calc s (g x) = g (g⁻¹ (s (g x))) := by simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
      _ = g x := by rw [this]
  have hA := hfixed burnsideF48t_u52pA (Or.inl rfl)
  have hB := hfixed burnsideF48t_u52pB (Or.inr rfl)
  have hlt : ((g burnsideF48t_u52pA : Fin 462) : ℕ) < 165 :=
    burnsideF48t_u52_X_lt hg (show ((burnsideF48t_u52pA : Fin 462) : ℕ) < 165 by decide)
  have hge : 165 ≤ ((g burnsideF48t_u52pB : Fin 462) : ℕ) :=
    burnsideF48t_u52_X_ge hg (show 165 ≤ ((burnsideF48t_u52pB : Fin 462) : ℕ) by decide)
  refine ⟨hA.resolve_right fun h => ?_, hB.resolve_left fun h => ?_⟩
  · rw [h] at hlt; exact absurd hlt (by decide)
  · rw [h] at hge; exact absurd hge (by decide)

theorem burnsideF48t_u52_B'_le_normalizer :
    burnsideF48t_u52B' ≤ Subgroup.normalizer (burnsideF48t_u52S0' : Set (Equiv.Perm (Fin 462))) := by
  rw [burnsideF48t_u52_B'_eq_closure, Subgroup.closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  have hk2 : k < 2 := burnsideF48t_u52_BArr.1 ▸ hk
  have h := burnsideF48t_u52_s0Norm
  simp only [burnsideF48t_u52S0NormOK] at h
  have hk' := allBelowN_spec h hk2
  refine burnsideF48t_mem_normalizer_of_conj fun x hx => ?_
  have hle : burnsideF48t_u52S0' ≤ burnsideF48t_u52S0'.comap
      (MulAut.conj (burnsideF48t_u52σ (burnsideF48t_u52P1Idx k))).toMonoidHom := by
    refine burnsideF48t_arrGen_le fun t ht => ?_
    obtain ⟨w, -, hw⟩ := burnsideF48t_u52_S0Arr_rep ht
    have hp : PRep 462 t (CFSG.Monster.B.Co2.permOfArr 462 t) := by
      rw [permOfArr_eq_of_prep hw]; exact hw
    rw [Subgroup.mem_comap]
    show burnsideF48t_u52σ (burnsideF48t_u52P1Idx k) * CFSG.Monster.B.Co2.permOfArr 462 t *
      (burnsideF48t_u52σ (burnsideF48t_u52P1Idx k))⁻¹ ∈ burnsideF48t_u52S0'
    refine burnsideF48t_u52_mem_S0_of_sift (prep_pcomp (prep_pcomp
      (burnsideF48t_u52_prep_σ (show burnsideF48t_u52P1Idx k < 4 by
        unfold burnsideF48t_u52P1Idx; omega)).1 hp)
      (burnsideF48t_u52_prep_σ (show burnsideF48t_u52P1Idx k < 4 by
        unfold burnsideF48t_u52P1Idx; omega)).2) ?_
    exact Array.all_eq_true_iff_forall_mem.1 hk' t ht
  exact hle hx

end Norm

section K

theorem burnsideF48t_u52_cosets :
    (∀ c ∈ burnsideF48t_u52K', ∃ m < 9, c = burnsideF48t_u52κ m) ∧
    (∀ m < 9, burnsideF48t_u52κ m ∈ burnsideF48t_u52K') ∧
    (∀ x ∈ burnsideF48t_u52P1', x ∉ burnsideF48t_u52P2' →
      (∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K') → x * x ∈ burnsideF48t_u52K' →
      ∃ w ∈ burnsideF48t_u52XW,
        (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * x ∈ burnsideF48t_u52K') ∧
    (∀ y ∈ burnsideF48t_u52P2', y ∉ burnsideF48t_u52P1' →
      (∀ k ∈ burnsideF48t_u52K', y * k * y⁻¹ ∈ burnsideF48t_u52K') → y * y ∈ burnsideF48t_u52K' →
      ∃ w ∈ burnsideF48t_u52YW,
        (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * y ∈ burnsideF48t_u52K') :=
  Certificates.certificate7770

theorem burnsideF48t_u52_KW_length : burnsideF48t_u52KW.length = 9 := rfl

theorem burnsideF48t_u52_KArr_size : (burnsideF48t_u52KArr ()).size = 2 := by
  simp [burnsideF48t_u52KArr, burnsideF48t_u52KGenIdx]

@[expose] def burnsideF48t_u52KGen (s : ℕ) : ℕ := burnsideF48t_u52KGenIdx.getD s 0

theorem burnsideF48t_u52_KRep : ∀ s < (burnsideF48t_u52KArr ()).size,
    PRep 462 (burnsideF48t_u52KArr ())[s]! (burnsideF48t_u52κ (burnsideF48t_u52KGen s)) := by
  intro s hs
  have hs2 : s < 2 := burnsideF48t_u52_KArr_size ▸ hs
  unfold burnsideF48t_u52KArr
  rw [burnsideF48t_getElem!_toArray_map _ _ (by simpa [burnsideF48t_u52KGenIdx] using hs2) 0]
  exact burnsideF48t_prep_evA burnsideF48t_u52_recL _

theorem burnsideF48t_u52_prep_κ {m : ℕ} (hm : m < 9) :
    PRep 462 ((burnsideF48t_u52KL ()).getD m (pid 462)) (burnsideF48t_u52κ m) := by
  have hm' : m < burnsideF48t_u52KW.length := by rw [burnsideF48t_u52_KW_length]; exact hm
  have := burnsideF48t_prep_evA burnsideF48t_u52_recL (burnsideF48t_u52KW.getD m [])
  simp only [burnsideF48t_u52KL]
  rw [List.getD_eq_getElem _ _ (by simpa using hm'), List.getElem_map]
  unfold burnsideF48t_u52κ
  rw [List.getD_eq_getElem _ _ hm'] at this ⊢
  exact this

theorem burnsideF48t_u52_K'_eq : burnsideF48t_u52K' =
    Subgroup.closure (Set.range fun s : Fin (burnsideF48t_u52KArr ()).size =>
      burnsideF48t_u52κ (burnsideF48t_u52KGen s)) :=
  arrGen_eq (σ := fun s => burnsideF48t_u52κ (burnsideF48t_u52KGen s)) burnsideF48t_u52_KRep

theorem burnsideF48t_u52_K'_cases {c : Equiv.Perm (Fin 462)} (hc : c ∈ burnsideF48t_u52K') :
    ∃ m < 9, c = burnsideF48t_u52κ m :=
  burnsideF48t_u52_cosets.1 c hc

theorem burnsideF48t_u52_κ_mem {m : ℕ} (hm : m < 9) : burnsideF48t_u52κ m ∈ burnsideF48t_u52K' :=
  burnsideF48t_u52_cosets.2.1 m hm

theorem burnsideF48t_u52_xred {x : Equiv.Perm (Fin 462)} (hx : x ∈ burnsideF48t_u52P1')
    (hx2 : x ∉ burnsideF48t_u52P2') (hxK : ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K')
    (hxx : x * x ∈ burnsideF48t_u52K') :
    ∃ w ∈ burnsideF48t_u52XW,
      (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * x ∈ burnsideF48t_u52K' :=
  burnsideF48t_u52_cosets.2.2.1 x hx hx2 hxK hxx

theorem burnsideF48t_u52_yred {y : Equiv.Perm (Fin 462)} (hy : y ∈ burnsideF48t_u52P2')
    (hy1 : y ∉ burnsideF48t_u52P1') (hyK : ∀ k ∈ burnsideF48t_u52K', y * k * y⁻¹ ∈ burnsideF48t_u52K')
    (hyy : y * y ∈ burnsideF48t_u52K') :
    ∃ w ∈ burnsideF48t_u52YW,
      (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * y ∈ burnsideF48t_u52K' :=
  burnsideF48t_u52_cosets.2.2.2 y hy hy1 hyK hyy

theorem burnsideF48t_u52_K'_le_B' : burnsideF48t_u52K' ≤ burnsideF48t_u52B' := by
  intro c hc
  obtain ⟨m, hm, rfl⟩ := burnsideF48t_u52_K'_cases hc
  have hab : burnsideF48t_u52σ 0 ∈ burnsideF48t_u52B' ∧ burnsideF48t_u52σ 1 ∈ burnsideF48t_u52B' := by
    rw [burnsideF48t_u52_B'_eq_closure]
    exact ⟨Subgroup.subset_closure ⟨⟨0, by rw [burnsideF48t_u52_BArr.1]; norm_num⟩, rfl⟩,
      Subgroup.subset_closure ⟨⟨1, by rw [burnsideF48t_u52_BArr.1]; norm_num⟩, rfl⟩⟩
  have hlet : ∀ w ∈ burnsideF48t_u52KW, ∀ l ∈ w, (l.1 : ℕ) < 2 := by decide
  refine burnsideF48s_ev_mem _ _ fun l hl => ?_
  have hw : burnsideF48t_u52KW.getD m [] ∈ burnsideF48t_u52KW := by
    rw [List.getD_eq_getElem _ _ (by rw [burnsideF48t_u52_KW_length]; exact hm)]
    exact List.getElem_mem _
  have := hlet _ hw l hl
  rcases (show (l.1 : ℕ) = 0 ∨ (l.1 : ℕ) = 1 by omega) with h | h
  · rw [show l.1 = 0 from Fin.ext h]; exact hab.1
  · rw [show l.1 = 1 from Fin.ext h]; exact hab.2

end K

end CFSG.ASVolI
