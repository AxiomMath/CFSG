module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Card
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6TransA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A6TransB
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique CFSG.Quasithin.C41Pf.AltN
open Equiv

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private def s16t3_allOnes6 : ↥(evenWeight 6) :=
  ⟨fun _ => (1 : ZMod 2), by show ∑ _i : Fin 6, (1 : ZMod 2) = 0; decide⟩

private theorem s16t3_allOnes6_mem : s16t3_allOnes6 ∈ constWeight 6 := fun _ _ => rfl

private theorem s16t3_alt6_fun_cases (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    (∃ i j : Fin 6, i ≠ j ∧ x = (pairVec i j : Fin 6 → ZMod 2)) ∨
    (∃ i j : Fin 6, i ≠ j ∧ x = (pairVec i j : Fin 6 → ZMod 2) + fun _ => 1) ∨
    x = 0 ∨ x = fun _ => (1 : ZMod 2) := by
  revert x hx
  decide

private theorem s16t3_alt6_mk_pair (y : AltHeart 6) (hy : y ≠ 0) :
    ∃ i j : Fin 6, i ≠ j ∧ y = (QuotientAddGroup.mk (pairVec i j) : AltHeart 6) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rcases s16t3_alt6_fun_cases (x : Fin 6 → ZMod 2) x.2 with
    ⟨i, j, hij, hx⟩ | ⟨i, j, hij, hx⟩ | hx0 | hx1
  · exact ⟨i, j, hij, by rw [Subtype.ext hx]⟩
  · have hx' : x = pairVec i j + s16t3_allOnes6 := by
      apply Subtype.ext
      show (x : Fin 6 → ZMod 2) =
        (pairVec i j : Fin 6 → ZMod 2) + (s16t3_allOnes6 : Fin 6 → ZMod 2)
      rw [hx]
      rfl
    refine ⟨i, j, hij, ?_⟩
    rw [hx', QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff s16t3_allOnes6).2 s16t3_allOnes6_mem, add_zero]
  · exact absurd ((QuotientAddGroup.eq_zero_iff x).2
      (by intro i j; simp [congrFun hx0 i, congrFun hx0 j])) hy
  · exact absurd ((QuotientAddGroup.eq_zero_iff x).2
      (by intro i j; simp [congrFun hx1 i, congrFun hx1 j])) hy

private theorem s16t3_alt6_transitive (y z : AltHeart 6) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ σ : ↥(alternatingGroup (Fin 6)), hAct 6 (σ : Perm (Fin 6)) y = z := by
  obtain ⟨i, j, hij, rfl⟩ := s16t3_alt6_mk_pair y hy
  obtain ⟨k, l, hkl, rfl⟩ := s16t3_alt6_mk_pair z hz
  obtain ⟨τ, hτ, hτi, hτj⟩ := alt_two_transitive (m := 6) (by norm_num) hij hkl
  exact ⟨⟨τ, hτ⟩, by rw [hAct_mk, permWeight_pairVec, hτi, hτj]⟩

private theorem s16t3_altHeart_six_card : Nat.card (Multiplicative (AltHeart 6)) = 16 := by
  rw [Nat.card_congr Multiplicative.toAdd, CFSG.Quasithin.H23P4.card_altHeart_six]
  norm_num

private theorem s16t3_alt6_exists_beta {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
    (hR : (FFModel.altDn 6).RealizesVia H U Z π) :
    ∃ β' : ↥U →* Multiplicative (AltHeart 6),
      Function.Surjective β' ∧
      (∀ u : ↥U, β' u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : ↥(alternatingGroup (Fin 6))) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
        β' ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (hAct 6 (γ : Equiv.Perm (Fin 6))
            (Multiplicative.toAdd (β' u))) := by
  obtain ⟨-, -, -, -, -, hsecinv, -, β, hβs, hβk, hβe⟩ := hR
  let e : (↥(FFModel.altDn 6).sec ⧸
      (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) ≃* Multiplicative (AltHeart 6) :=
    CFSG.Quasithin.C124.altQuotEquiv 6 (by norm_num)
  refine ⟨e.toMonoidHom.comp β, e.surjective.comp hβs, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply]
    change e (β u) = 1 ↔ (u : W) ∈ Z
    rw [e.map_eq_one_iff, hβk u]
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn 6).act γ (m : (FFModel.altDn 6).Amb) ∈
        (FFModel.altDn 6).sec := hsecinv γ m m.2
    have h1 := hβe γ u m hu hsec hmu
    calc e (β ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) =
        e (QuotientGroup.mk ⟨(FFModel.altDn 6).act γ (m : (FFModel.altDn 6).Amb), hsec⟩) :=
          congrArg e h1
      _ = Multiplicative.ofAdd (hAct 6 (γ : Equiv.Perm (Fin 6))
            (Multiplicative.toAdd (e (QuotientGroup.mk m)))) := rfl
      _ = Multiplicative.ofAdd (hAct 6 (γ : Equiv.Perm (Fin 6))
            (Multiplicative.toAdd (e (β u)))) := by rw [← hmu]

theorem s16t3_alt6_shape (hq : CFSG.Open.IsQuasisimple ↥L) (hL : UC22.IsAlt ↥L 6)
    {I : Subgroup W} (hI : SumOfNatShape L I (I ⊓ fixV L) 1) :
    AlternatingNatural L I (I ⊓ fixV L) 6 := by
  have hc : Nat.card ↥L = 360 := s16t3_card_of_isAlt_six hL
  obtain ⟨n, h | h | h | h | ⟨hn, hN⟩⟩ := hI
  · exact absurd hc (s16t3_card_ne_of_isSLn h.1)
  · exact absurd hc (s16t3_card_ne_of_isSpn h.1)
  · exact absurd hc (s16t3_card_ne_of_isOmegaPlus h.1)
  · exact absurd hc (s16t3_card_ne_of_isOmegaMinus h.1)
  · obtain rfl : n = 6 := s16t3_eq_six_of_isAlt_card hn hc
    exact s16t3_sumOfNat_one hN

theorem s16t3_alt6_natural (hq : CFSG.Open.IsQuasisimple ↥L) (hL : UC22.IsAlt ↥L 6)
    {I : Subgroup W} (hI : SumOfNatShape L I (I ⊓ fixV L) 1) :
    Nat.card ↥I = 16 * Nat.card ↥(I ⊓ fixV L) ∧
      ∀ x ∈ I, x ∉ fixV L → ∀ y ∈ I, y ∉ fixV L →
        ∃ l ∈ L, ((l : MulAut W) x) * y⁻¹ ∈ fixV L := by
  obtain ⟨π, hR⟩ := s16t3_alt6_shape hq hL hI
  let π' : ↥(alternatingGroup (Fin 6)) →* ↥L := π
  have hR' : (FFModel.altDn 6).RealizesVia L I (I ⊓ fixV L) π' := hR
  obtain ⟨β', hβs, hβk, hβe⟩ := s16t3_alt6_exists_beta hR'
  have hUinv : ∀ h : ↥L, ∀ u ∈ I, (h : MulAut W) u ∈ I := hR'.2.2.2.1
  have hcard : Nat.card ↥I = 16 * Nat.card ↥(I ⊓ fixV L) := by
    have hker : β'.ker = (I ⊓ fixV L).subgroupOf I := by
      ext u
      rw [MonoidHom.mem_ker, hβk u, Subgroup.mem_subgroupOf]
    have hcardZ : Nat.card ↥((I ⊓ fixV L).subgroupOf I) = Nat.card ↥(I ⊓ fixV L) :=
      Nat.card_congr
        { toFun := fun z => (⟨(z : W), Subgroup.mem_subgroupOf.1 z.2⟩ : ↥(I ⊓ fixV L))
          invFun := fun z =>
            (⟨⟨z, z.2.1⟩, Subgroup.mem_subgroupOf.2 z.2⟩ : ↥((I ⊓ fixV L).subgroupOf I))
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hquot : Nat.card (↥I ⧸ (I ⊓ fixV L).subgroupOf I) =
        Nat.card (Multiplicative (AltHeart 6)) := by
      rw [← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β' hβs).toEquiv
    have hbase := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((I ⊓ fixV L).subgroupOf I)
    rw [hquot, hcardZ, s16t3_altHeart_six_card] at hbase
    exact hbase
  refine ⟨hcard, ?_⟩
  intro x hxI hxL y hyI hyL
  let u : ↥I := ⟨x, hxI⟩
  let v : ↥I := ⟨y, hyI⟩
  have hxu : x ∉ I ⊓ fixV L := fun h => hxL h.2
  have hyu : y ∉ I ⊓ fixV L := fun h => hyL h.2
  have hβu : β' u ≠ 1 := fun h => hxu ((hβk u).1 h)
  have hβv : β' v ≠ 1 := fun h => hyu ((hβk v).1 h)
  have ha : Multiplicative.toAdd (β' u) ≠ 0 := fun h => hβu (by
    have := congrArg Multiplicative.ofAdd h
    simpa using this)
  have hb : Multiplicative.toAdd (β' v) ≠ 0 := fun h => hβv (by
    have := congrArg Multiplicative.ofAdd h
    simpa using this)
  obtain ⟨σ, hσ⟩ := s16t3_alt6_transitive (Multiplicative.toAdd (β' u))
    (Multiplicative.toAdd (β' v)) ha hb
  have hlx : ((π' σ : ↥L) : MulAut W) (u : W) ∈ I := hUinv (π' σ) (u : W) u.2
  have hβlx : β' ⟨((π' σ : ↥L) : MulAut W) (u : W), hlx⟩ = β' v := by
    have h1 := hβe σ u hlx
    rw [h1]
    simpa using congrArg Multiplicative.ofAdd hσ
  refine ⟨π' σ, (π' σ).2, ?_⟩
  change ((π' σ : ↥L) : MulAut W) (u : W) * (v : W)⁻¹ ∈ fixV L
  have hmem : ((π' σ : ↥L) : MulAut W) (u : W) * (v : W)⁻¹ ∈ I :=
    I.mul_mem hlx (I.inv_mem v.2)
  have hβw : β' ⟨((π' σ : ↥L) : MulAut W) (u : W) * (v : W)⁻¹, hmem⟩ = 1 := by
    have hmul : β' ⟨((π' σ : ↥L) : MulAut W) (u : W) * (v : W)⁻¹, hmem⟩ =
        β' (⟨((π' σ : ↥L) : MulAut W) (u : W), hlx⟩ * v⁻¹) := rfl
    rw [hmul, map_mul, map_inv, hβlx, mul_inv_cancel]
  exact ((hβk ⟨((π' σ : ↥L) : MulAut W) (u : W) * (v : W)⁻¹, hmem⟩).1 hβw).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
