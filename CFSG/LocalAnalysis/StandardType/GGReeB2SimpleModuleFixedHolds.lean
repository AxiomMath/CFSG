module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SimpleModule
public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairBasic
public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairComm
public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairTorus
public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairRadical
public import CFSG.LocalAnalysis.StandardType.GGReeB2TheoremH
public import CFSG.LocalAnalysis.StandardType.GGReeB2CondCOfIM
public import CFSG.LocalAnalysis.StandardType.GGReeB2CondHOfCondC
public import CFSG.LocalAnalysis.StandardType.GGReeB2IMHolds

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.B45Sz

theorem condH_holds (m : ℕ) (hm : 1 ≤ m) : CondH m :=
  condH_of_condC m (condC_of_IM (2 * m + 1) ⟨m, rfl⟩ (by omega)
    (IM_holds (2 * m + 1) ⟨m, rfl⟩ (by omega)))

theorem exists_szPair
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∃ 𝔇 : SzPairDatum K m (reeFixed ReeTag.F4 K m),
      𝔇.φ₁ = reeSz₁ hK hm ∧ 𝔇.φ₂ = reeSz₂ hK hm := by
  haveI : CharP K 2 := inferInstanceAs (CharP K ReeTag.F4.prime)
  refine ⟨{
    φ₁ := reeSz₁ hK hm
    φ₂ := reeSz₂ hK hm
    comm := reeSz_comm hK hm
    U := reeU K m
    Ub := reeUb K m
    pgroup := reeU_isPGroup
    Ub_le := reeUb_le
    up₁ := reeSz₁_up hK hm
    up₂ := reeSz₂_up hK hm
    Ub_norm := reeUb_norm hK hm
    T_norm := reeT_norm hK hm
    na := reeNa K m
    na_sq := reeNa_sq
    na_conj := reeNa_conj_tau hK hm
    na_up₁ := (reeNa_up hK hm).1
    na_up₂ := (reeNa_up hK hm).2 }, rfl, rfl⟩

theorem ggReeB2SimpleModuleFixed_of_condH
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (m : ℕ)
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (hm : 1 ≤ m) (hC : CondH m) (w : Kˣ)
    (e : reeFixed ReeTag.F4 K m)
    (he : (e : adjointGroup ReeTag.F4.tag K) = F4Chief.reeB2Elt K m w)
    (W : Type) [AddCommGroup W] [Module (AlgebraicClosure (ZMod 2)) W]
    [Module.Finite (AlgebraicClosure (ZMod 2)) W]
    (ρ : Representation (AlgebraicClosure (ZMod 2)) (reeFixed ReeTag.F4 K m) W) [Nontrivial W] :
    ∃ v : W, v ≠ 0 ∧ ρ e v = v := by
  haveI : CharP K 2 := inferInstanceAs (CharP K ReeTag.F4.prime)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Algebra.IsAlgebraic (ZMod 2) K := inferInstance
  letI : Algebra K (AlgebraicClosure (ZMod 2)) :=
    (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := AlgebraicClosure (ZMod 2))).toRingHom.toAlgebra
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1) := hK
  obtain ⟨𝔇, _, h₂⟩ := exists_szPair (K := K) hK' hm
  obtain ⟨v, hv, hfix⟩ := theoremH (AlgebraicClosure (ZMod 2)) hK hC 𝔇 ρ
  obtain ⟨l, hl⟩ := reeB0_mem (K := K) hK' hm w e he
  refine ⟨v, hv, ?_⟩
  rw [hl, ← h₂]
  exact hfix l

theorem ggReeB2SimpleModuleFixedInput_holds :
    GGReeB2SimpleModuleFixedInput := by
  intro K hField hFinite hCharP m hK p hp w hw e he W hAdd hMod hFin ρ hSimple
  haveI : IsSimpleModule (MonoidAlgebra (AlgebraicClosure (ZMod 2))
      (reeFixed ReeTag.F4 K m)) ρ.asModule := hSimple
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hcard : Nat.card K = 2 := by simpa using hK
    have hunits : Nat.card Kˣ = 1 := by
      rw [Nat.card_units, hcard]
    haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
    have hw1 : w = 1 := Subsingleton.elim w 1
    have horder : orderOf w = 1 := by rw [hw1, orderOf_one]
    have hp1 : p = 1 := by rw [← hw]; exact horder
    exact absurd hp1 hp.ne_one
  · haveI : CharP K 2 := inferInstanceAs (CharP K ReeTag.F4.prime)
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Nontrivial W := IsSimpleModule.nontrivial
      (MonoidAlgebra (AlgebraicClosure (ZMod 2)) (reeFixed ReeTag.F4 K m)) ρ.asModule
    exact ggReeB2SimpleModuleFixed_of_condH (K := K) m hK hmpos
      (condH_holds m hmpos) w e he W ρ

end CFSG.StandardType.ReeB2Fixed
