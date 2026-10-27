module

public import CFSG.Sporadic.HNOddCore.SixC
public import CFSG.RankThree.Native.HSMcLSmall
public import Certificates.Certificate14981

public noncomputable section

namespace CFSG.RankThree.PartOne.HNRed

open Equiv Subgroup
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.RankThree.Native
open CFSG.RankThree.PartOne.HNRed.Native CFSG.ONSchreier
open CFSG.Blueprint.NativeSporadic (Carrier)

section Embedding

@[expose] def embedPair : Perm (Fin 1100) × Perm (Fin 100) →* Perm (Fin 1200) :=
  (finSumFinEquiv : Fin 1100 ⊕ Fin 100 ≃ Fin 1200).permCongrHom.toMonoidHom.comp
    (Perm.sumCongrHom (Fin 1100) (Fin 100))

theorem embedPair_injective : Function.Injective embedPair := fun _ _ h =>
  Perm.sumCongrHom_injective ((Equiv.permCongrHom _).injective h)

theorem embedPair_castAdd (σ : Perm (Fin 1100)) (τ : Perm (Fin 100)) (i : Fin 1100) :
    embedPair (σ, τ) (Fin.castAdd 100 i) = Fin.castAdd 100 (σ i) := by
  show finSumFinEquiv (Perm.sumCongr σ τ (finSumFinEquiv.symm (Fin.castAdd 100 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem embedPair_natAdd (σ : Perm (Fin 1100)) (τ : Perm (Fin 100)) (j : Fin 100) :
    embedPair (σ, τ) (Fin.natAdd 1100 j) = Fin.natAdd 1100 (τ j) := by
  show finSumFinEquiv (Perm.sumCongr σ τ (finSumFinEquiv.symm (Fin.natAdd 1100 j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem embedPair_val_lt (σ : Perm (Fin 1100)) (τ : Perm (Fin 100)) (i : ℕ) (hi : i < 1200)
    (hx : i < 1100) :
    ((embedPair (σ, τ) ⟨i, hi⟩ : Fin 1200) : ℕ) = (σ ⟨i, hx⟩ : ℕ) :=
  congrArg Fin.val (embedPair_castAdd σ τ ⟨i, hx⟩)

theorem embedPair_val_ge (σ : Perm (Fin 1100)) (τ : Perm (Fin 100)) (i : ℕ) (hi : i < 1200)
    (hx : 1100 ≤ i) :
    ((embedPair (σ, τ) ⟨i, hi⟩ : Fin 1200) : ℕ) = 1100 + (τ ⟨i - 1100, by omega⟩ : ℕ) := by
  have h := embedPair_natAdd σ τ ⟨i - 1100, by omega⟩
  have e : (Fin.natAdd 1100 ⟨i - 1100, (by omega : i - 1100 < 100)⟩ : Fin 1200) = ⟨i, hi⟩ :=
    Fin.ext (by simp; omega)
  rw [e] at h
  exact congrArg Fin.val h

theorem prep_embedPair {s t : Array ℕ} {σ : Perm (Fin 1100)} {τ : Perm (Fin 100)}
    (hs : s.size = 1100) (ht : t.size = 100) (hσ : PRep 1100 s σ) (hτ : PRep 100 t τ) :
    PRep 1200 (s ++ t.map (· + 1100)) (embedPair (σ, τ)) := by
  rintro ⟨i, hi⟩
  by_cases hx : i < 1100
  · show (s ++ t.map (· + 1100))[i]! = ((embedPair (σ, τ) ⟨i, hi⟩ : Fin 1200) : ℕ)
    rw [embedPair_val_lt σ τ i hi hx, getElem!_pos (s ++ t.map (· + 1100)) i (by simp [hs]; omega),
      Array.getElem_append_left (by omega), ← getElem!_pos s i (by omega)]
    exact hσ ⟨i, hx⟩
  · have hx' : 1100 ≤ i := by omega
    show (s ++ t.map (· + 1100))[i]! = ((embedPair (σ, τ) ⟨i, hi⟩ : Fin 1200) : ℕ)
    rw [embedPair_val_ge σ τ i hi hx', getElem!_pos (s ++ t.map (· + 1100)) i
      (by simp [hs]; omega), Array.getElem_append_right (by omega)]
    have := hτ ⟨i - 1100, by omega⟩
    simp only [Array.getElem_map, hs]
    rw [getElem!_pos t (i - 1100) (by omega)] at this
    simp only [this]
    omega

end Embedding

section Sizes

theorem size_ppow (n : ℕ) (t : Array ℕ) (e : ℕ) :
    (CFSG.Sporadic.HNSchreier.Native.ppow n t e).size = n := by
  induction e with
  | zero => simp [CFSG.Sporadic.HNSchreier.Native.ppow, CFSG.ONSchreier.Native.pid]
  | succ e ih => simp [CFSG.Sporadic.HNSchreier.Native.ppow, CFSG.ONSchreier.Native.pcomp]

theorem size_dA : (dA om0Gens).size = 1100 := size_ppow _ _ _

theorem size_dB : (dB om0Gens).size = 1100 := size_ppow _ _ _

theorem size_hs100Arr (k : ℕ) : (hs100Arr k).size = 100 := by
  simp [hs100Arr, CFSG.Monster.B.Fischer.hexTable3]

end Sizes

section Pair

@[expose] def pairGen (k : ℕ) : Perm (Fin 1100) × Perm (Fin 100) :=
  if k = 0 then (aD, hs100A) else (bD, hs100B)

@[expose] def pairGroup : Subgroup (Perm (Fin 1100) × Perm (Fin 100)) :=
  Subgroup.closure ({(aD, hs100A), (bD, hs100B)} : Set (Perm (Fin 1100) × Perm (Fin 100)))

theorem prep_pairA :
    PRep 1200 pairA (embedPair (aD, hs100A)) := by
  have hA : PRep 1100 (dA om0Gens) aD := by rw [← aArr_eq]; exact prep_aD
  exact prep_embedPair size_dA (size_hs100Arr 0) hA (fun x => rep_hs100A x)

theorem prep_pairB :
    PRep 1200 pairB (embedPair (bD, hs100B)) := by
  have hB : PRep 1100 (dB om0Gens) bD := by rw [← bArr_eq]; exact prep_bD
  exact prep_embedPair size_dB (size_hs100Arr 1) hB (fun x => rep_hs100B x)

theorem prep_pairGen
    {k : ℕ} (hk : k < 2) :
    PRep 1200 (#[pairA, pairB] : Array (Array ℕ))[k]! (embedPair (pairGen k)) := by
  interval_cases k
  · exact prep_pairA
  · exact prep_pairB

theorem range_pairGen : Set.range (fun k : Fin 2 => pairGen k) =
    ({(aD, hs100A), (bD, hs100B)} : Set (Perm (Fin 1100) × Perm (Fin 100))) := by
  ext σ
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem pair_chain_check : pairCheck = true :=
  Certificates.certificate14981

theorem card_pairGroup :
    Nat.card pairGroup = 44352000 := by
  have h1 : Nat.card (arrGen 1200 #[pairA, pairB]) = 44352000 := by
    rw [card_arrGen_of_chainCheck (by norm_num) (by decide) pair_chain_check]
    decide
  have h2 : arrGen 1200 #[pairA, pairB] = pairGroup.map embedPair := by
    rw [arrGen_eq (σ := fun k => embedPair (pairGen k))
      fun k hk => prep_pairGen (by simpa using hk), pairGroup, MonoidHom.map_closure]
    congr 1
    rw [← range_pairGen, ← Set.range_comp]
    rfl
  rw [h2, Subgroup.card_map_of_injective embedPair_injective] at h1
  exact h1

end Pair

section Projections

theorem injective_of_card_range_eq {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (h : Nat.card f.range = Nat.card A) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, h] at h1
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h2 : Nat.card f.ker = 1 := by
    have : Nat.card f.ker * Nat.card A = 1 * Nat.card A := by rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  exact Subgroup.eq_bot_of_card_eq _ h2

@[expose] def pairFst : pairGroup →* Perm (Fin 1100) := (MonoidHom.fst _ _).comp pairGroup.subtype

@[expose] def pairSnd : pairGroup →* Perm (Fin 100) := (MonoidHom.snd _ _).comp pairGroup.subtype

theorem range_pairFst : pairFst.range = Dsub := by
  rw [pairFst, MonoidHom.range_comp, Subgroup.range_subtype, pairGroup, MonoidHom.map_closure,
    Set.image_pair]
  rfl

theorem range_pairSnd : pairSnd.range = hs100P := by
  rw [pairSnd, MonoidHom.range_comp, Subgroup.range_subtype, pairGroup, MonoidHom.map_closure,
    Set.image_pair]
  rfl

theorem pairFst_injective :
    Function.Injective pairFst := by
  have : Finite pairGroup := Nat.finite_of_card_ne_zero (by rw [card_pairGroup]; norm_num)
  refine injective_of_card_range_eq _ ?_
  rw [range_pairFst, card_Dsub, card_pairGroup]

theorem pairSnd_injective :
    Function.Injective pairSnd := by
  have : Finite pairGroup := Nat.finite_of_card_ne_zero (by rw [card_pairGroup]; norm_num)
  refine injective_of_card_range_eq _ ?_
  rw [range_pairSnd, card_hs100P, card_pairGroup]

theorem nonempty_Dsub_mulEquiv_hs100P :
    Nonempty (Dsub ≃* hs100P) :=
  ⟨((MonoidHom.ofInjective pairFst_injective).trans
      (MulEquiv.subgroupCongr range_pairFst)).symm.trans
    ((MonoidHom.ofInjective pairSnd_injective).trans (MulEquiv.subgroupCongr range_pairSnd))⟩

theorem nonempty_Dsub_mulEquiv_HS :
    Nonempty (Dsub ≃* Carrier .HS) := by
  obtain ⟨e⟩ := nonempty_Dsub_mulEquiv_hs100P
  exact ⟨e.trans hs100Equiv.symm⟩

end Projections

end CFSG.RankThree.PartOne.HNRed
