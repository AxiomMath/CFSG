
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowBase

public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import CFSG.Sporadic.FischerOddCore.EmbAction
public import CFSG.Monster.B.Fischer.Fi22ModelBase1
public import CFSG.Monster.B.Fischer.Fi22CoverBase1
public import Mathlib.GroupTheory.Sylow
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22CentralizerBase1
public import CFSG.Monster.B.Fischer.Fi22GraphAutBase1

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer

theorem rep_fi22ExtQ :
    Rep 3510 (fi22ExtArr 0) fi22ExtQ := rep_fi22ExtPerm (by norm_num)

theorem rep_fi22ExtV :
    Rep 3510 (fi22ExtArr 1) fi22ExtV := rep_fi22ExtPerm (by norm_num)

theorem rep_fi22ExtQi : Rep 3510 fi22ExtQiArr fi22ExtQ⁻¹ :=
  rep_inv_of_isInvA rep_fi22ExtQ (fi22Ext_check.2.2.1 0 (by norm_num))

theorem rep_fi22ExtVi : Rep 3510 fi22ExtViArr fi22ExtV⁻¹ :=
  rep_inv_of_isInvA rep_fi22ExtV (fi22Ext_check.2.2.1 1 (by norm_num))

theorem rep_fi22ExtSubGen {k : ℕ} (hk : k < 9) :
    Rep 3510 (fi22ExtArr (2 + k)) (fi22ExtSubGen k) :=
  rep_fi22ExtPerm (by omega)

theorem rep_fi22ExtFullGen {k : ℕ} (hk : k < 10) :
    Rep 3510 (fi22ExtArr (11 + k)) (fi22ExtFullGen k) :=
  rep_fi22ExtPerm (by omega)

theorem fi22InT_iff
    {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hG : Rep 3510 g G) :
    fi22InT g = true ↔ G ∈ fi22OuterT :=
  siftA_iff_mem_originalSubgroup fi22OuterChainT_arrays (by norm_num) fi22Local_check.2.2.1 hG

theorem rep_fi22TSeed
    {k : ℕ} (hk : k < 9) : Rep 3510 (fi22OuterStrong3510 4)[k]! (fi22TSeed k) :=
  rep_fi22OuterTStrong (by omega)

theorem fi22ExtQ_mem :
    fi22ExtQ ∈ fi22P := (fi22InP_iff rep_fi22ExtQ).1 fi22ExtSylow_check.1

theorem fi22ExtV_not_mem :
    fi22ExtV ∉ fi22P := fun h => by
  have := (fi22InP_iff rep_fi22ExtV).2 h
  rw [fi22ExtSylow_check.2.1] at this
  exact Bool.false_ne_true this

theorem fi22ExtV_mem_R :
    fi22ExtV ∈ fi22R :=
  (mem_fi22R_iff _).2 (Or.inr ((fi22InP_iff (rep_compA rep_fi22U rep_fi22ExtV)).1
    fi22ExtSylow_check.2.2.1))

theorem fi22ExtSubGen_eq
    {k : ℕ} (hk : k < 9) :
    fi22ExtSubGen k = fi22ExtQ * fi22TSeed k * fi22ExtQ⁻¹ := by
  have h := eq_of_eqA (rep_compA (rep_fi22ExtSubGen hk) rep_fi22ExtQ)
    (rep_compA rep_fi22ExtQ (rep_fi22TSeed hk)) (fi22ExtSylow_check.2.2.2.1 k hk)
  rw [← h, mul_inv_cancel_right]

theorem fi22ExtFullGen_eq
    {k : ℕ} (hk : k < 9) : fi22ExtFullGen k = fi22ExtSubGen k :=
  eq_of_eqA (rep_fi22ExtFullGen (by omega)) (rep_fi22ExtSubGen hk)
    (fi22ExtSylow_check.2.2.2.2.1 k hk)

theorem fi22ExtFullGen_nine :
    fi22ExtFullGen 9 = fi22ExtV :=
  eq_of_eqA (rep_fi22ExtFullGen (by norm_num)) rep_fi22ExtV fi22ExtSylow_check.2.2.2.2.2.1

theorem fi22ExtT0_eq_closure :
    fi22ExtT0 = Subgroup.closure {g | ∃ k < 9, fi22ExtSubGen k = g} := by
  rw [fi22ExtT0, fi22OuterT_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by rw [fi22ExtSubGen_eq hk]; rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, by rw [fi22ExtSubGen_eq hk]; rfl⟩

theorem card_fi22ExtT0 : Nat.card fi22ExtT0 = 131072 := by
  rw [fi22ExtT0, Subgroup.card_map_of_injective (MulAut.conj fi22ExtQ).injective, card_fi22OuterT]

theorem fi22ExtT0_le_P :
    fi22ExtT0 ≤ fi22P := by
  rintro _ ⟨t, ht, rfl⟩
  rw [conj_apply_eq]
  exact fi22P.mul_mem (fi22P.mul_mem fi22ExtQ_mem (fi22OuterT_le ht)) (fi22P.inv_mem fi22ExtQ_mem)

theorem fi22ExtV_not_mem_T0 :
    fi22ExtV ∉ fi22ExtT0 := fun h => fi22ExtV_not_mem (fi22ExtT0_le_P h)

theorem fi22ExtV_sq_mem :
    fi22ExtV ^ 2 ∈ fi22ExtT0 := by
  have h := (fi22InT_iff (rep_compA rep_fi22ExtQi (rep_compA rep_fi22ExtV
    (rep_compA rep_fi22ExtV rep_fi22ExtQ)))).1 fi22ExtSylow_check.2.2.2.2.2.2.1
  refine ⟨_, h, ?_⟩
  rw [conj_apply_eq, pow_two]
  group

theorem fi22ExtV_conj_mem
    {k : ℕ} (hk : k < 9) :
    fi22ExtV * fi22ExtSubGen k * fi22ExtV⁻¹ ∈ fi22ExtT0 := by
  have h := (fi22InT_iff (rep_compA rep_fi22ExtQi (rep_compA rep_fi22ExtV
    (rep_compA (rep_fi22ExtSubGen hk) (rep_compA rep_fi22ExtVi rep_fi22ExtQ))))).1
    (fi22ExtSylow_check.2.2.2.2.2.2.2.1 k hk)
  refine ⟨_, h, ?_⟩
  rw [conj_apply_eq]
  group

theorem fi22ExtV_conj_eq :

    fi22ExtT0.map (MulAut.conj fi22ExtV).toMonoidHom = fi22ExtT0 := by
  have hle : fi22ExtT0.map (MulAut.conj fi22ExtV).toMonoidHom ≤ fi22ExtT0 := by
    conv_lhs => rw [fi22ExtT0_eq_closure]
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact fi22ExtV_conj_mem hk
  have : Finite fi22ExtT0 := Nat.finite_of_card_ne_zero (by rw [card_fi22ExtT0]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj fi22ExtV).injective])

theorem fi22ExtV_conj_mem_T0
    {t : Equiv.Perm (Fin 3510)} (ht : t ∈ fi22ExtT0) :
    fi22ExtV * t * fi22ExtV⁻¹ ∈ fi22ExtT0 := by
  rw [← fi22ExtV_conj_eq]
  exact ⟨t, ht, rfl⟩

theorem fi22ExtV_inv_conj_mem_T0
    {t : Equiv.Perm (Fin 3510)} (ht : t ∈ fi22ExtT0) :
    fi22ExtV⁻¹ * t * fi22ExtV ∈ fi22ExtT0 := by
  rw [← fi22ExtV_conj_eq] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rw [conj_apply_eq]
  have e : fi22ExtV⁻¹ * (fi22ExtV * s * fi22ExtV⁻¹) * fi22ExtV = s := by group
  rw [e]
  exact hs

@[expose] def fi22ExtSx :
    Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {g | g ∈ fi22ExtT0 ∨ g * fi22ExtV ∈ fi22ExtT0}
  mul_mem' {g h} hg hh := by
    have hv2 : fi22ExtV⁻¹ * fi22ExtV⁻¹ ∈ fi22ExtT0 := by
      have := fi22ExtT0.inv_mem fi22ExtV_sq_mem
      rwa [pow_two, mul_inv_rev] at this
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact Or.inl (fi22ExtT0.mul_mem hg hh)
    · exact Or.inr (by rw [mul_assoc]; exact fi22ExtT0.mul_mem hg hh)
    · refine Or.inr ?_
      have := fi22ExtT0.mul_mem hg (fi22ExtV_inv_conj_mem_T0 hh)
      convert this using 1
      group
    · refine Or.inl ?_
      have := fi22ExtT0.mul_mem (fi22ExtT0.mul_mem hg (fi22ExtV_inv_conj_mem_T0 hh)) hv2
      convert this using 1
      group
  one_mem' := Or.inl fi22ExtT0.one_mem
  inv_mem' {g} hg := by
    rcases hg with hg | hg
    · exact Or.inl (fi22ExtT0.inv_mem hg)
    · refine Or.inr ?_
      have := fi22ExtT0.mul_mem (fi22ExtV_conj_mem_T0 (fi22ExtT0.inv_mem hg)) fi22ExtV_sq_mem
      convert this using 1
      group

theorem mem_fi22ExtSx
    {g : Equiv.Perm (Fin 3510)} :
    g ∈ fi22ExtSx ↔ g ∈ fi22ExtT0 ∨ g * fi22ExtV ∈ fi22ExtT0 :=
  Iff.rfl

theorem fi22ExtS_eq_Sx :
    fi22ExtS = fi22ExtSx := by
  apply le_antisymm
  · rw [fi22ExtS, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Or.inr (by rw [← pow_two]; exact fi22ExtV_sq_mem)
    · exact Or.inl hg
  · rintro g (hg | hg)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
    · have h1 : g * fi22ExtV ∈ fi22ExtS := Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
      have h2 : fi22ExtV ∈ fi22ExtS := Subgroup.subset_closure (Set.mem_insert _ _)
      simpa using fi22ExtS.mul_mem h1 (fi22ExtS.inv_mem h2)

theorem card_fi22ExtS :
    Nat.card fi22ExtS = 262144 := by
  have hidx : (fi22ExtT0.subgroupOf fi22ExtS).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨fi22ExtV, fi22ExtV_mem_S⟩, fun b => ?_⟩
    have hb : (b : Equiv.Perm (Fin 3510)) ∈ fi22ExtSx := fi22ExtS_eq_Sx ▸ b.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | hb
    · refine Or.inr ⟨hb, fun h => fi22ExtV_not_mem_T0 ?_⟩
      simpa using fi22ExtT0.mul_mem (fi22ExtT0.inv_mem hb) h
    · refine Or.inl ⟨hb, fun h => fi22ExtV_not_mem_T0 ?_⟩
      simpa using fi22ExtT0.mul_mem (fi22ExtT0.inv_mem h) hb
  have h := (fi22ExtT0.subgroupOf fi22ExtS).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22ExtT0_le_S).toEquiv,
    card_fi22ExtT0] at h
  omega

theorem fi22ExtS_le_R :
    fi22ExtS ≤ fi22R := by
  rw [fi22ExtS, Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact fi22ExtV_mem_R
  · exact fi22P_le_R (fi22ExtT0_le_P hg)

theorem factorization_card_fi22R_two :
    (Nat.card fi22R).factorization 2 = 18 := by
  rw [card_fi22R, show (129123503308800 : ℕ) = 2 ^ 18 * 492567075 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem fi22ExtS_sylow :
    ∃ Q : Sylow 2 fi22R, (Q : Subgroup fi22R) = fi22ExtS.subgroupOf fi22R := by
  have hcard : Nat.card (fi22ExtS.subgroupOf fi22R) = 2 ^ (Nat.card fi22R).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fi22ExtS_le_R).toEquiv, card_fi22ExtS,
      factorization_card_fi22R_two]
    norm_num
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem fi22ExtS_eq_closure_full :
    fi22ExtS = Subgroup.closure {g | ∃ k < 10, fi22ExtFullGen k = g} := by
  rw [fi22ExtS, fi22ExtT0_eq_closure, closure_insert_closure]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨9, by norm_num, fi22ExtFullGen_nine⟩
    · exact ⟨k, by omega, fi22ExtFullGen_eq hk⟩
  · rintro ⟨k, hk, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact Or.inr ⟨k, hk, (fi22ExtFullGen_eq hk).symm⟩
    · exact Or.inl fi22ExtFullGen_nine

theorem fi22ExtDArr_get
    (i : Fin 256) : fi22ExtDArr[(i : ℕ)]! = (fi22ExtDeltaPt i : ℕ) := by
  rw [fi22ExtDeltaPt_val, fi22ExtDArr, fi22ExtSmallPointsNat_getD,
    getElem!_pos _ _ (by simp [fi22ExtSmallPointsNat_length]), List.getElem_toArray]

theorem fi22ExtFullGen_apply
    {k : ℕ} (hk : k < 10) (i : Fin 256) :
    fi22ExtFullGen k (fi22ExtDeltaPt i) = fi22ExtDeltaPt (fi22ExtPerm256 k i) := by
  obtain ⟨-, heq⟩ := fi22ExtSylow_check.2.2.2.2.2.2.2.2.1 k hk i i.2
  apply Fin.ext
  have h1 := rep_fi22ExtFullGen hk (fi22ExtDeltaPt i)
  have h2 := rep_fi22ExtPerm256 (L := k) (by omega) i
  rw [← h1, ← fi22ExtDArr_get, ← heq, h2, fi22ExtDArr_get]

theorem fi22ExtFullGen_mem_embStab
    {k : ℕ} (hk : k < 10) :
    fi22ExtFullGen k ∈ embStab fi22ExtDeltaPt :=
  mem_embStab_of_apply (fi22ExtPerm256 k) (fi22ExtFullGen_apply hk)

theorem fi22ExtS_le_embStab :
    fi22ExtS ≤ embStab fi22ExtDeltaPt := by
  rw [fi22ExtS_eq_closure_full, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact fi22ExtFullGen_mem_embStab hk

@[expose] def fi22ExtRes :
    fi22ExtS →* Equiv.Perm (Fin 256) :=
  (embPos fi22ExtDeltaPt fi22ExtDeltaPt_injective).comp (Subgroup.inclusion fi22ExtS_le_embStab)

theorem fi22ExtRes_apply
    (s : fi22ExtS) (i : Fin 256) :
    fi22ExtDeltaPt (fi22ExtRes s i) = (s : Equiv.Perm (Fin 3510)) (fi22ExtDeltaPt i) :=
  embPos_apply _ _ _ _

theorem fi22ExtRes_mk_apply
    (g : Equiv.Perm (Fin 3510)) (hg : g ∈ fi22ExtS) (i : Fin 256) :
    fi22ExtDeltaPt (fi22ExtRes ⟨g, hg⟩ i) = g (fi22ExtDeltaPt i) :=
  embPos_apply _ _ _ _

theorem fi22ExtFullGen_mem
    {k : ℕ} (hk : k < 10) : fi22ExtFullGen k ∈ fi22ExtS := by
  rw [fi22ExtS_eq_closure_full]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem fi22ExtRes_fullGen
    {k : ℕ} (hk : k < 10) :
    fi22ExtRes ⟨fi22ExtFullGen k, fi22ExtFullGen_mem hk⟩ = fi22ExtPerm256 k :=
  embPos_ext _ fi22ExtDeltaPt_injective fun i =>
    (fi22ExtRes_mk_apply _ _ i).trans (fi22ExtFullGen_apply hk i)

theorem fi22ExtSmallChain_arrays :
    ChainArrays fi22ExtSmallChain (fi22ExtSmallStrong.extract 0 10)
    fi22ExtSmallStrong #[0, 1, 2, 3, 4, 6] (fi22WordsArr 10 18 fi22ExtSmallDerivations) := by
  have h := chainArrays_ofArrays (n := 256) (hn := by decide) (k := fi22ExtSmallGenCount)
    (hk := by rw [fi22ExtSmallStrong, Array.size_ofFn]; decide)
    (base := fi22FinList 256 (by decide) fi22ExtSmallBase) (hb := by decide)
    (W := fi22WordsArr fi22ExtSmallGenCount 18 fi22ExtSmallDerivations)
    (chainCheckFacts fi22ExtSylow_check.2.2.2.2.2.2.2.2.2.2.1).strong_inv
  have hb : ((fi22FinList 256 (by decide) fi22ExtSmallBase).map Fin.val).toArray =
      #[0, 1, 2, 3, 4, 6] := rfl
  rw [hb] at h
  exact h

theorem fi22ExtSmallChain_valid : ValidSchreier fi22ExtSmallChain :=
  (validSchreier_of_chainOK fi22ExtSmallChain_arrays (by norm_num)
    fi22ExtSylow_check.2.2.2.2.2.2.2.2.2.2.1).1

theorem card_fi22ExtSmallChain :
    Nat.card fi22ExtSmallChain.originalSubgroup = 262144 := by
  rw [card_originalSubgroup_of_chainOK fi22ExtSmallChain_arrays (by norm_num)
    fi22ExtSylow_check.2.2.2.2.2.2.2.2.2.2.1, fi22ExtSylow_check.2.2.2.2.2.2.2.2.2.2.2]
  rfl

theorem fi22ExtRes_range :
    fi22ExtRes.range = fi22ExtSmallChain.originalSubgroup := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hg' := hg
    rw [fi22ExtS_eq_closure_full] at hg'
    revert hg
    induction hg' using Subgroup.closure_induction with
    | mem x hx =>
      intro hx'
      obtain ⟨k, hk, rfl⟩ := hx
      rw [show (⟨fi22ExtFullGen k, hx'⟩ : fi22ExtS) = ⟨fi22ExtFullGen k, fi22ExtFullGen_mem hk⟩
        from rfl, fi22ExtRes_fullGen hk]
      exact Subgroup.subset_closure (mem_fi22ExtSmallChain_original.2 ⟨k, hk, rfl⟩)
    | one =>
      intro h1
      rw [show (⟨1, h1⟩ : fi22ExtS) = 1 from rfl, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxy
      have hx' : x ∈ fi22ExtS := by rw [fi22ExtS_eq_closure_full]; exact hx
      have hy' : y ∈ fi22ExtS := by rw [fi22ExtS_eq_closure_full]; exact hy
      rw [show (⟨x * y, hxy⟩ : fi22ExtS) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from rfl, map_mul]
      exact Subgroup.mul_mem _ (ihx hx') (ihy hy')
    | inv x hx ih =>
      intro hxi
      have hx' : x ∈ fi22ExtS := by rw [fi22ExtS_eq_closure_full]; exact hx
      rw [show (⟨x⁻¹, hxi⟩ : fi22ExtS) = (⟨x, hx'⟩ : fi22ExtS)⁻¹ from rfl, map_inv]
      exact Subgroup.inv_mem _ (ih hx')
  · rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := mem_fi22ExtSmallChain_original.1 hg
    exact ⟨_, fi22ExtRes_fullGen hk⟩

theorem fi22ExtRes_injective :
    Function.Injective fi22ExtRes := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup fi22ExtRes.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange fi22ExtRes).toEquiv, fi22ExtRes_range,
    card_fi22ExtSmallChain, card_fi22ExtS] at h
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem CTUC_Fi22_extension_Sylow_faithful_action :
    fi22ExtQ ∈ fi22P ∧ fi22ExtV ∈ fi22R ∧ fi22ExtV ∉ fi22P ∧ fi22ExtV ^ 2 ∈ fi22ExtT0 ∧
    fi22ExtT0.map (MulAut.conj fi22ExtV).toMonoidHom = fi22ExtT0 ∧
    Subgroup.closure {g | ∃ k < 9, fi22ExtSubGen k = g} = fi22ExtT0 ∧
    Subgroup.closure {g | ∃ k < 10, fi22ExtFullGen k = g} = fi22ExtS ∧
    fi22ExtS ≤ fi22R ∧ Nat.card fi22ExtS = 262144 ∧
    (∃ Q : Sylow 2 fi22R, (Q : Subgroup fi22R) = fi22ExtS.subgroupOf fi22R) ∧
    fi22ExtS ≤ embStab fi22ExtDeltaPt ∧ Function.Injective fi22ExtRes ∧
    (∀ (k : ℕ) (hk : k < 10),
      fi22ExtRes ⟨fi22ExtFullGen k, fi22ExtFullGen_mem hk⟩ = fi22ExtPerm256 k) ∧
    ValidSchreier fi22ExtSmallChain ∧ fi22ExtRes.range = fi22ExtSmallChain.originalSubgroup ∧
    Nat.card fi22ExtSmallChain.originalSubgroup = 262144 :=
  ⟨fi22ExtQ_mem, fi22ExtV_mem_R, fi22ExtV_not_mem, fi22ExtV_sq_mem, fi22ExtV_conj_eq,
    fi22ExtT0_eq_closure.symm, fi22ExtS_eq_closure_full.symm, fi22ExtS_le_R, card_fi22ExtS,
    fi22ExtS_sylow, fi22ExtS_le_embStab, fi22ExtRes_injective, fun _ hk => fi22ExtRes_fullGen hk,
    fi22ExtSmallChain_valid, fi22ExtRes_range, card_fi22ExtSmallChain⟩

end CFSG.Sporadic.FischerOddCore
