module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23L34Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Norm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesBase
public import Certificates.Certificate4170
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.A312Words CFSG.Quasithin.A312ExtShapes
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ]

variable [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem isPSL_l34_of_facts {Y : Subgroup Γ} (hF : L34Facts Y)
    (hcard : Nat.card Y = 40320) {S B' : Subgroup Γ} (hS : IsPGroup 2 S) (hB' : B' ∈ lFamily S)
    (hY : B' ⊔ S = Y) : IsPSL 3 2 2 ↥B' := by
  classical
  obtain ⟨ol, t, hdata, hn, u, v, huN, hvN, hrelG, holsub⟩ := hF
  obtain ⟨hA, hcomm, hYle, -, -⟩ := perfectCore_eq_closure hS hB' hY hdata hn
  have hgen : Subgroup.closure {x | x ∈ ol} = Subgroup.closure ({u, v} : Set Γ) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr holsub) ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl | rfl)
    · exact huN
    · exact hvN
  have hcardN : 20160 ≤ Nat.card (Subgroup.closure {x | x ∈ ol}) := by omega
  have hPSL : IsPSL 3 2 2 ↥(Subgroup.closure {x | x ∈ ol}) :=
    isPSL_three_four_of_gens huN hvN hgen hrelG hcardN
  obtain ⟨hnt, hsimple⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hPSL
  have hperf : ⁅Subgroup.closure {x | x ∈ ol}, Subgroup.closure {x | x ∈ ol}⁆ =
      Subgroup.closure {x | x ∈ ol} := by
    rw [← hA]
    exact perfectCore_perfect _
  have hIP : Group.IsPerfect ↥(Subgroup.closure {x | x ∈ ol}) := Subgroup.isPerfect_iff.mpr hperf
  have hnab : ∃ a b : ↥(Subgroup.closure {x | x ∈ ol}), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative ↥(Subgroup.closure {x | x ∈ ol}) ⟨⟨hcon⟩⟩
  have hker : Group.IsSolvable (MonoidHom.id ↥(Subgroup.closure {x | x ∈ ol})).ker := by
    have : (MonoidHom.id ↥(Subgroup.closure {x | x ∈ ol})).ker = ⊥ := MonoidHom.ker_id
    rw [this]
    infer_instance
  have hBN : B' = Subgroup.closure {x | x ∈ ol} :=
    eq_of_perfect_simple_quotient hB' hY ((Subgroup.closure_le _).mpr fun g hg => hdata.mem g hg)
      hcomm hperf hnab (MonoidHom.id _) Function.surjective_id hker
  subst hBN
  exact hPSL

end CFSG.Quasithin.A312M23
