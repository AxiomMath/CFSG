
module

public import CFSG.Sporadic.HNOddCore.SylABase

public import CFSG.Sporadic.HNOddCore.FourPair
public import CFSG.Sporadic.HNOddCore.PCheck
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.PCheckInputs
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.HNOddCore.QCheckInputs
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
public import CFSG.Sporadic.HNSchreier.SylowCheck

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

@[expose] def gC4'
    (s : ℕ) : C4 := if h : s < 11 then gC4 ⟨s, h⟩ else 1

theorem rho4_gC4'
    (s : ℕ) : rho4 (gC4' s) = rhoGen s := by
  unfold gC4' rhoGen
  split_ifs
  · rfl
  · exact map_one _

@[expose] def gensC
    (i : ℕ) : C4 := wordVal gC4' pWords[i]!

theorem p_parts :
    InvData.s4Perms.size = 11 ∧ InvData.pgenPerms.size = 14 ∧ pWords.size = 14 ∧
    (∀ i < 14, plettersOK 11 pWords[i]! = true ∧
      peq 800 (pword 800 InvData.s4Perms (pinvs 800 InvData.s4Perms) pWords[i]!)
        InvData.pgenPerms[i]! = true ∧
      pisInv 800 InvData.pgenPerms[i]! (pinvs 800 InvData.pgenPerms)[i]! = true) ∧
    InvData.parRecs.size = 16384 ∧ (pEnum InvData.pgenPerms InvData.parRecs).size = 16384 ∧
    peq 800 (pEnum InvData.pgenPerms InvData.parRecs)[0]! (pid 800) = true ∧
    (∀ k < 16384, 0 < k → ppar k < k ∧ plab k < 14 ∧
      peq 800 (pEnum InvData.pgenPerms InvData.parRecs)[k]!
        (pcomp 800 InvData.pgenPerms[plab k]!
          (pEnum InvData.pgenPerms InvData.parRecs)[ppar k]!) = true) ∧
    InvData.pleftTabs.size = 14 ∧
    (∀ g < 14, ∀ k < 16384, (InvData.pleftTabs[g]!)[k]! < 16384 ∧
      peq 800 (pcomp 800 InvData.pgenPerms[g]! (pEnum InvData.pgenPerms InvData.parRecs)[k]!)
        (pEnum InvData.pgenPerms InvData.parRecs)[(InvData.pleftTabs[g]!)[k]!]! = true) ∧
    chainCheck 800 InvData.pgenPerms QData.pbarWords QData.pbarBase QData.pbarSizes = true ∧
    (List.range 16384).countP (fun k => peq 800 (pcomp 800
      (pEnum InvData.pgenPerms InvData.parRecs)[k]! (pEnum InvData.pgenPerms InvData.parRecs)[k]!)
        (pid 800)) = 880 := by
  have h := CFSG.Sporadic.HNOddCore.Native.sylow_cert
  unfold CFSG.Sporadic.HNOddCore.Native.sylowChecks sylowChecksE sylowChecksH at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, -⟩,
    -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, h5, h6, h7, fun k hk hk0 => ?_, h9, fun g hg k hk => ?_,
    h11, h12⟩
  · have := allBelowN_spec h4 hi
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allBelowN_spec h8 hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h0 | ⟨⟨ha, hb⟩, hc⟩
    · omega
    · exact ⟨ha, hb, hc⟩
  · have := allBelowN_spec (allBelowN_spec h10 hg) hk
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

theorem prep_pg
    {i : ℕ} (hi : i < 14) :
    PRep 800 InvData.pgenPerms[i]! (rho4 (gensC i)) := by
  obtain ⟨hl, hp, -⟩ := p_parts.2.2.2.1 i hi
  have hw := prep_pword_wordVal (g := rhoGen) (fun h hh => prep_rhoGen hh)
    (fun h hh => prep_rhoGen_inv hh) _ hl
  have e : rho4 (gensC i) = wordVal rhoGen pWords[i]! := by
    rw [gensC, map_wordVal]
    congr 1
    funext s
    exact rho4_gC4' s
  rw [e]
  exact prep_of_peq_left hp hw

theorem pbarPerm_eq
    {i : ℕ} (hi : i < 14) : pbarPerm i = rho4 (gensC i) := by
  rw [pbarPerm, permOfArr_eq_of_prep (prep_pg hi)]

theorem prep_pbarPerm
    {i : ℕ} (hi : i < 14) : PRep 800 InvData.pgenPerms[i]! (pbarPerm i) := by
  rw [pbarPerm_eq hi]
  exact prep_pg hi

@[expose] def liftCF :
    ℕ → ℕ → C4
  | 0, _ => 1
  | f + 1, r => if r = 0 then 1 else gensC (plab r) * liftCF f (ppar r)

@[expose] def liftC
    (r : ℕ) : C4 := liftCF r r

theorem liftCF_eq :
    ∀ r < 16384, ∀ f, r ≤ f → liftCF f r = liftC r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr f hf
    by_cases hr0 : r = 0
    · subst hr0
      cases f <;> rfl
    · obtain ⟨hpar, -, -⟩ := p_parts.2.2.2.2.2.2.2.1 r hr (Nat.pos_of_ne_zero hr0)
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      show (if r' + 1 = 0 then 1 else gensC (plab (r' + 1)) * liftCF f' (ppar (r' + 1))) =
        (if r' + 1 = 0 then 1 else gensC (plab (r' + 1)) * liftCF r' (ppar (r' + 1)))
      rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ih _ hpar (by omega) f' (by omega), ih _ hpar (by omega) r' (by omega)]

theorem liftC_zero :
    liftC 0 = 1 := rfl

theorem liftC_succ
    {k : ℕ} (hk : k < 16384) (hk0 : 0 < k) :
    liftC k = gensC (plab k) * liftC (ppar k) := by
  obtain ⟨hpar, -, -⟩ := p_parts.2.2.2.2.2.2.2.1 k hk hk0
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show (if k' + 1 = 0 then 1 else gensC (plab (k' + 1)) * liftCF k' (ppar (k' + 1))) = _
  rw [ite_eq_right (by omega), liftCF_eq _ (by omega) k' (by omega)]

theorem prep_pE :
    ∀ k < 16384, PRep 800 pE[k]! (rho4 (liftC k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [liftC_zero, map_one]
      exact prep_of_peq_right p_parts.2.2.2.2.2.2.1 prep_pid
    · obtain ⟨hpar, hlab, heq⟩ := p_parts.2.2.2.2.2.2.2.1 k hk (Nat.pos_of_ne_zero hk0)
      rw [liftC_succ hk (Nat.pos_of_ne_zero hk0), map_mul]
      exact prep_of_peq_right heq (prep_pcomp (prep_pg hlab) (ih _ hpar (by omega)))

theorem ePerm_eq
    {k : ℕ} (hk : k < 16384) : ePerm k = rho4 (liftC k) := by
  rw [ePerm, permOfArr_eq_of_prep (prep_pE k hk)]

theorem prep_ePerm
    {k : ℕ} (hk : k < 16384) : PRep 800 pE[k]! (ePerm k) := by
  rw [ePerm_eq hk]
  exact prep_pE k hk

theorem ePerm_mem :
    ∀ k < 16384, ePerm k ∈ Pbar := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [ePerm_eq (by norm_num), liftC_zero, map_one]
      exact Pbar.one_mem
    · obtain ⟨hpar, hlab, -⟩ := p_parts.2.2.2.2.2.2.2.1 k hk (Nat.pos_of_ne_zero hk0)
      rw [ePerm_eq hk, liftC_succ hk (Nat.pos_of_ne_zero hk0), map_mul, ← pbarPerm_eq hlab,
        ← ePerm_eq (by omega)]
      exact Pbar.mul_mem (pbarPerm_mem hlab) (ih _ hpar (by omega))

theorem Pbar_subset :
    (Pbar : Set (Perm (Fin 800))) ⊆ Set.range fun k : Fin 16384 => ePerm k := by
  refine closure_subset_of_mul_mem (T := Set.range fun k : Fin 16384 => ePerm k)
    ⟨0, show ePerm 0 = 1 by rw [ePerm_eq (by norm_num), liftC_zero, map_one]⟩ ?_
  rintro _ ⟨g, rfl⟩ _ ⟨k, rfl⟩
  obtain ⟨hlt, hp⟩ := p_parts.2.2.2.2.2.2.2.2.2.1 g g.2 k k.2
  exact ⟨⟨_, hlt⟩, (eq_of_peq (prep_pcomp (prep_pbarPerm g.2) (prep_ePerm k.2))
    (prep_ePerm hlt) hp).symm⟩

theorem pbar_size : InvData.pgenPerms.size = 14 := p_parts.2.1

theorem card_Pbar :
    Nat.card Pbar = 16384 := by
  have hO : ∀ k < InvData.pgenPerms.size, PRep 800 InvData.pgenPerms[k]! (pbarPerm k) :=
    fun k hk => prep_pbarPerm (by rw [← pbar_size]; exact hk)
  have e : Subgroup.closure (Set.range fun i : Fin 14 => pbarPerm i) =
      arrGen 800 InvData.pgenPerms := by
    rw [arrGen_eq hO]
    congr 1
    ext σ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, by rw [pbar_size]; exact i.2⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨⟨k, by rw [← pbar_size]; exact hk⟩, rfl⟩
  show Nat.card (Subgroup.closure (Set.range fun i : Fin 14 => pbarPerm i)) = 16384
  rw [e, card_arrGen_of_chainCheck (by norm_num) (by decide) p_parts.2.2.2.2.2.2.2.2.2.2.1]
  decide

@[expose] def eMap
    (k : Fin 16384) : Pbar := ⟨ePerm k, ePerm_mem k k.2⟩

theorem eMap_bijective :
    Function.Bijective eMap := by
  have hs : Function.Surjective eMap := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := Pbar_subset hx
    exact ⟨k, Subtype.ext hk⟩
  refine (Function.Surjective.bijective_of_nat_card_le hs ?_)
  rw [card_Pbar, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ePerm_injective
    {k l : ℕ} (hk : k < 16384) (hl : l < 16384) (h : ePerm k = ePerm l) :
    k = l := by
  have := eMap_bijective.1 (a₁ := ⟨k, hk⟩) (a₂ := ⟨l, hl⟩) (Subtype.ext h)
  exact congrArg Fin.val this

end CFSG.Sporadic.HNOddCore
