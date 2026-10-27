module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Vol2.Ch10SecCFacts2
public import CFSG.Quasithin.Vol2.Ch10SecKIK2d
public import CFSG.Quasithin.Vol2.Ch11SecABasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA

variable {Γ : Type} [Group Γ] [Finite Γ] {H R J L V : Subgroup Γ} {hV : IsElemAbelian 2 V}

theorem even_card_modO2 (hc : S5Core H R J L V hV) :
    Even (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLfam, -, -, hLs, -, -⟩ := hc
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect ↥L :=
    Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp (show L ∈ cComp (L ⊔ R) from hLfam))
  have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  have : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := hLs.toNontrivial
  exact Group.IsPerfect.not_isSolvable _ hsolv

omit [Finite Γ] in
theorem inf_centralizer_of_ker (hJN : J ≤ Subgroup.normalizer (V : Set Γ))
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ)) (hk : (piJ hV hJN hO).ker = ⊥) :
    J ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 J := by
  refine le_antisymm (fun x hx => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 J) hO)
  have h1 : piJ hV hJN hO (QuotientGroup.mk ⟨x, hx.1⟩) = 1 :=
    (piJ_mk_eq_one_iff hV hJN hO ⟨x, hx.1⟩).2 hx.2
  have h2 : (QuotientGroup.mk ⟨x, hx.1⟩ : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ (piJ hV hJN hO).ker := h1
  rw [hk, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h2
  exact (C1Pack.coe_mem_pCoreOf_iff J ⟨x, hx.1⟩).mpr h2

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
