module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieRes

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

theorem e114OneRes_of_e114ForE22R (h : Vol2.Ch11.SecE3.E114ForE22R) : E114OneRes :=
  fun G _ _ T hSQ hFs hT hFT hty => (h G T hSQ hFs hT hFT).2 hty

theorem nParam_sup_eq_of_typeLieR (h114 : Vol2.Ch11.SecE3.E114ForE22R) {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hSQ : SQTKGroup X) (hT : TypeLie n X) {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    E1.nParam ((MulAut.conj : X →* MulAut X).range ⊔ B) = n := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hIn : I.Normal := normal_range_conj X
  have hSQI : SQTKGroup ↥I :=
    sqtkGroup_of_mulEquiv (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm hSQ
  have hSQZ : SQTKGroup ↥Z := InternalSec.sqtkGroup_of_two_pow le_sup_left
    (fun y _ k hk => hIn.conj_mem k hk y) (pow_mem_of_mem_sup hB) hSQI
  set e := generalizedFittingEquiv hnab B with he
  have hFs : IsSimpleGroup (ASInputs.FStar ↥Z) := e.isSimpleGroup
  have hFT : TypeLie n (ASInputs.FStar ↥Z) := TypeLie.of_mulEquiv e hT
  have key : E1.nParam (⊤ : Subgroup ↥Z) = n :=
    (h114 ↥Z (B.subgroupOf Z) hSQZ hFs (isSylowTwo_sup hB hBI)
      (generalizedFitting_sup_sup hnab B)).1 n hn hFT
  rw [E1.nParam_subgroupOf, key]

end CFSG.Quasithin.E2.E22N
