
module

public import CFSG.Sporadic.HNOddCore.FourPairBBase

public import CFSG.Sporadic.HNOddCore.FourPairA
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

@[expose] def rhoGen
    (s : ℕ) : Perm (Fin 800) := if h : s < 11 then rho4 (gC4 ⟨s, h⟩) else 1

theorem prep_rhoGen
    {s : ℕ} (hs : s < 11) : PRep 800 InvData.s4Perms[s]! (rhoGen s) := by
  rw [rhoGen, dite_eq_left hs]
  exact prep_rho_gC ⟨s, hs⟩

theorem prep_rhoGen_inv
    {s : ℕ} (hs : s < 11) :
    PRep 800 (pinvs 800 InvData.s4Perms)[s]! (rhoGen s)⁻¹ :=
  prep_inv_of_pisInv (prep_rhoGen hs) (q_parts.2.2.2.2.1 s hs)

theorem rhoGen_mem
    {s : ℕ} (hs : s < 11) : rhoGen s ∈ rho4.range := by
  rw [rhoGen, dite_eq_left hs]
  exact ⟨_, rfl⟩

theorem q_word
    {i : ℕ} (hi : i < 8) : ∃ σ ∈ rho4.range, PRep 800 InvData.qPerms[i]! σ := by
  obtain ⟨hl, hp⟩ := q_parts.2.2.2.2.2.1 i hi
  obtain ⟨σ, hσ, hw⟩ := prep_pword_mem (fun h hh => prep_rhoGen hh)
    (fun h hh => prep_rhoGen_inv hh) (fun h hh => rhoGen_mem hh) _ hl
  exact ⟨σ, hσ, prep_of_peq_left hp hw⟩

theorem prep_qbar
    {i : ℕ} (hi : i < 8) : PRep 800 InvData.qPerms[i]! (qbar i) := by
  obtain ⟨σ, -, hp⟩ := q_word hi
  rw [qbar, permOfArr_eq_of_prep hp]
  exact hp

theorem qbar_mem_range
    {i : ℕ} (hi : i < 8) : qbar i ∈ rho4.range := by
  obtain ⟨σ, hσ, hp⟩ := q_word hi
  rw [qbar, permOfArr_eq_of_prep hp]
  exact hσ

theorem qbar_comm
    {i j : ℕ} (hi : i < 8) (hj : j < 8) : qbar i * qbar j = qbar j * qbar i :=
  eq_of_peq (prep_pcomp (prep_qbar hi) (prep_qbar hj)) (prep_pcomp (prep_qbar hj) (prep_qbar hi))
    (q_parts.2.2.2.2.2.2.1 i hi j hj)

theorem qbar_sq
    {i : ℕ} (hi : i < 8) : qbar i * qbar i = 1 :=
  eq_of_peq (prep_pcomp (prep_qbar hi) (prep_qbar hi)) prep_pid (q_parts.2.2.2.2.2.2.2.1 i hi)

theorem Qbar_le_range :
    Qbar ≤ rho4.range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact qbar_mem_range i.2

theorem Qbar_comm
    {x y : Perm (Fin 800)} (hx : x ∈ Qbar) (hy : y ∈ Qbar) : x * y = y * x := by
  have hc : (Set.range fun i : Fin 8 => qbar i).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact qbar_comm i.2 j.2
  have := (Subgroup.isMulCommutative_closure hc).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem Qbar_sq
    {x : Perm (Fin 800)} (hx : x ∈ Qbar) : x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    rw [pow_two]
    exact qbar_sq i.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (Qbar_comm hx hy) 2), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem card_Qbar :
    Nat.card Qbar = 256 := by
  have hO : ∀ k < InvData.qPerms.size, PRep 800 InvData.qPerms[k]! (qbar k) := fun k hk =>
    prep_qbar (by rw [← qPerms_size]; exact hk)
  have e : Subgroup.closure (Set.range fun i : Fin 8 => qbar i) = arrGen 800 InvData.qPerms := by
    rw [arrGen_eq hO]
    congr 1
    ext σ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, by rw [qPerms_size]; exact i.2⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨⟨k, by rw [← qPerms_size]; exact hk⟩, rfl⟩
  show Nat.card (Subgroup.closure (Set.range fun i : Fin 8 => qbar i)) = 256
  rw [e, card_arrGen_of_chainCheck (by norm_num) (by decide) q_parts.2.2.2.2.2.2.2.2.2.2.1]
  decide

theorem subQ_foldl
    (m : ℕ) : ∀ (L : List ℕ) (acc : Array ℕ) (σ : Perm (Fin 800)), σ ∈ Qbar →
    PRep 800 acc σ → (∀ i ∈ L, i < 8) → ∃ τ ∈ Qbar, PRep 800 (L.foldl (fun acc i =>
      if m.testBit i then pcomp 800 acc InvData.qPerms[i]! else acc) acc) τ
  | [], acc, σ, hσ, hp, _ => ⟨σ, hσ, hp⟩
  | i :: L, acc, σ, hσ, hp, hL => by
    have hL' : ∀ j ∈ L, j < 8 := fun j hj => hL j (List.mem_cons_of_mem _ hj)
    have hi : i < 8 := hL i List.mem_cons_self
    by_cases hb : m.testBit i = true
    · simp only [List.foldl_cons, hb, ite_true]
      exact subQ_foldl m L _ _ (Qbar.mul_mem hσ (qbar_mem hi)) (prep_pcomp hp (prep_qbar hi)) hL'
    · simp only [List.foldl_cons, hb]
      exact subQ_foldl m L _ _ hσ hp hL'

theorem subQ_mem
    (m : ℕ) : ∃ σ ∈ Qbar, PRep 800 (subQ 800 InvData.qPerms m) σ := by
  unfold subQ
  exact subQ_foldl m _ _ 1 Qbar.one_mem prep_pid fun i hi => by
    rw [List.mem_range, qPerms_size] at hi
    exact hi

theorem qb_spec
    {m : ℕ} (hm : m < 256) :
    qb m ∈ Qbar ∧ PRep 800 (qbList 800 InvData.qPerms)[m]! (qb m) := by
  obtain ⟨σ, hσ, hp⟩ := subQ_mem m
  rw [← qbList_get hm] at hp
  rw [qb, permOfArr_eq_of_prep hp]
  exact ⟨hσ, hp⟩

theorem qb_zero :
    qb 0 = 1 := by
  have hp := (qb_spec (m := 0) (by norm_num)).2
  rw [qbList_get (by norm_num), subQ] at hp
  simp only [Nat.zero_testBit, Bool.false_eq_true, ite_false] at hp
  rw [foldl_acc] at hp
  exact hp.unique prep_pid

theorem Qbar_subset :
    (Qbar : Set (Perm (Fin 800))) ⊆ Set.range fun m : Fin 256 => qb m := by
  refine closure_subset_of_mul_mem (T := Set.range fun m : Fin 256 => qb m) ⟨0, qb_zero⟩ ?_
  rintro _ ⟨i, rfl⟩ _ ⟨m, rfl⟩
  obtain ⟨hlt, hp⟩ := q_parts.2.2.2.2.2.2.2.2.1 i i.2 m m.2
  refine ⟨⟨_, hlt⟩, ?_⟩
  exact (eq_of_peq (prep_pcomp (prep_qbar i.2) (qb_spec m.2).2) (qb_spec hlt).2 hp).symm

theorem qb_injective :
    Function.Injective fun m : Fin 256 => (⟨qb m, (qb_spec m.2).1⟩ : Qbar) := by
  have hs : Function.Surjective fun m : Fin 256 => (⟨qb m, (qb_spec m.2).1⟩ : Qbar) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := Qbar_subset hx
    exact ⟨m, Subtype.ext hm⟩
  have hc : Nat.card (Fin 256) = Nat.card Qbar := by rw [Nat.card_eq_fintype_card,
    Fintype.card_fin, card_Qbar]
  exact (Function.Surjective.bijective_of_nat_card_le hs hc.le).1

@[expose] def qbEquiv :
    Fin 256 ≃ Qbar :=
  Equiv.ofBijective _ ⟨qb_injective, fun x => by
    obtain ⟨m, hm⟩ := Qbar_subset x.2
    exact ⟨m, Subtype.ext hm⟩⟩

theorem qbEquiv_apply
    (m : Fin 256) : (qbEquiv m : Perm (Fin 800)) = qb m := rfl

theorem colPerm_spec
    {g : ℕ} (hg : g < 11) {m : ℕ} (hm : m < 256) :
    (rhoGen g)⁻¹ * (qb m * rhoGen g) = qb (colPerms[g]!)[m]! := by
  obtain ⟨-, h⟩ := q_parts.2.2.2.2.2.2.2.2.2.1 g hg
  obtain ⟨hlt, hp⟩ := h m hm
  exact eq_of_peq (prep_pcomp (prep_rhoGen_inv hg) (prep_pcomp (qb_spec hm).2 (prep_rhoGen hg)))
    (qb_spec hlt).2 hp

theorem conj_gen_mem
    {g : ℕ} (hg : g < 11) {y : Perm (Fin 800)} (hy : y ∈ Qbar) :
    (rhoGen g)⁻¹ * y * (rhoGen g)⁻¹⁻¹ ∈ Qbar := by
  obtain ⟨m, rfl⟩ := Qbar_subset hy
  rw [inv_inv, mul_assoc, colPerm_spec hg m.2]
  exact (qb_spec (colPerm_lt hg m.2)).1

theorem range_eq_closure_rhoGen :
    rho4.range = Subgroup.closure (Set.range fun s : Fin 11 => rhoGen s) := by
  rw [range_eq_closure rho4 closure_gC4]
  congr 2
  funext s
  rw [rhoGen, dite_eq_left s.2]

theorem range_le_normalizer :
    rho4.range ≤ Subgroup.normalizer (Qbar : Set (Perm (Fin 800))) := by
  rw [range_eq_closure_rhoGen, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have h : (rhoGen s)⁻¹ ∈ Subgroup.normalizer (Qbar : Set (Perm (Fin 800))) :=
    mem_normalizer_of_conj fun y hy => conj_gen_mem s.2 hy
  simpa using (Subgroup.normalizer (Qbar : Set (Perm (Fin 800)))).inv_mem h

theorem Qbar_normal :
    (Qbar.subgroupOf rho4.range).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Qbar_le_range).2 range_le_normalizer

end CFSG.Sporadic.HNOddCore
