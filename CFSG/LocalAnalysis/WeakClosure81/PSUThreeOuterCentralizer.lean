module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3InvType
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Real
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
public import CFSG.LocalAnalysis.WeakClosure81.OuterInvolutionCentralizer
public import CFSG.Quasithin.Vol2.Ch11SecU1U3C

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11 CFSG.Blueprint
open scoped commutatorElement

theorem sigmaFacts_psu3_outer
    {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hAS : SecE3.AlmostSimple L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hL : LieModel ↥L .PSU 3 p f)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    SecU1.SigmaFacts L b := by
  classical
  obtain ⟨-, -, F, hFld, hFin, hFcard, ⟨e⟩⟩ :=
    CFSG.GH74.Generic.lieModel_psu_data hL
  letI : Field F := hFld
  letI : Finite F := hFin
  have hcard : Nat.card F = p ^ (2 * f) := by
    rw [hFcard, pow_two, ← pow_add]
    congr 1
    omega
  let hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F := ⟨hp, by omega, hcard⟩
  obtain ⟨θ, hθ⟩ := CFSG.GH74.KGroups.L3Eps.Uni.exists_cover_of_equiv hU e
  let σ : MulAut ↥L := MulAut.conjNormal b
  have hbb : b * b = 1 := by
    rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hσ : σ * σ = 1 := by
    ext x
    simp only [MulAut.mul_apply, MulAut.one_apply]
    simp only [σ, MulAut.conjNormal_apply]
    have hbinv : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hbb, inv_one]
    calc b * (b * ↑x * b⁻¹) * b⁻¹ = (b * b) * ↑x * (b⁻¹ * b⁻¹) := by group
      _ = ↑x := by rw [hbb, hbinv]; group
  have hout : σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    intro hin
    apply hbL
    apply CFSG.Quasithin.Vol2.Ch11.SecU1.U3.mem_of_isInnerAut hAS.centralizer_eq (t := b)
    obtain ⟨l, hl⟩ := hin
    refine ⟨l⁻¹, fun x => ?_⟩
    have hx : MulAut.conjNormal (H := L) b x = MulAut.conj l x :=
      DFunLike.congr_fun hl.symm x
    rw [hx, MulAut.conj_apply, inv_inv]
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hp2le : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have h9 : 9 ≤ p ^ 2 := by nlinarith [pow_two p]
  have hmono : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have h3 : 3 ≤ p ^ f := le_trans (by norm_num : 3 ≤ 9) (le_trans h9 hmono)
  have h5 : 5 ≤ p ^ f := le_trans (by norm_num : 5 ≤ 9) (le_trans h9 hmono)
  rcases CFSG.GH74.GLS.Stage2.Signalizer.Odd87.involution_type_of_three_le hU hp2 h3 hθ hσ with
    ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := CFSG.GH74.KGroups.L3Eps.Uni.exists_conj_of_typeI hU hθ hAu hAA hrel
    exact hout ⟨y, hy⟩
  ·
    obtain ⟨N, hGD, ⟨eN⟩⟩ :=
      CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3.graphData_of_typeII_psl2 hU h5 hodd hθ hφ hAu hAA hrel
    obtain ⟨D⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.outerData_of_typeII hU hp2 h3 hθ hφ hAu hAA hrel
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥hU.fixedField) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [hU.card_fixedField]
        omega)
    have hsimpleN : IsSimpleGroup ↥N := eN.isSimpleGroup
    have hperfectN : Group.IsPerfect ↥N := hGD.quasisimple.1
    let L0K : Subgroup ↥L := (D.Ψ.range).map θ
    have hΨperf : Group.IsPerfect ↥(D.Ψ.range) := by
      have hkodd : Odd (Nat.card ↥hU.fixedField) := by
        rwa [hU.card_fixedField]
      have hk5 : 5 ≤ Nat.card ↥hU.fixedField := by
        rwa [hU.card_fixedField]
      haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) ↥hU.fixedField) :=
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.sl2_perfect_of_five_le hkodd hk5
      exact Group.IsPerfect.range (f := D.Ψ)
    have hL0K_perf : Group.IsPerfect ↥L0K := by
      haveI : Group.IsPerfect ↥(D.Ψ.range) := hΨperf
      simpa [L0K] using (Group.IsPerfect.map (f := θ) : Group.IsPerfect ↥((D.Ψ.range).map θ))
    have hL0K_fixed : ∀ x ∈ L0K, σ x = x := by
      intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨S, hS⟩ := MonoidHom.mem_range.mp (show s ∈ D.Ψ.range from hs)
      simpa [hS] using D.fixed S
    have hL0K_le_N : L0K ≤ N := by
      have hperf : ⁅L0K, L0K⁆ = L0K := Subgroup.isPerfect_iff.mp hL0K_perf
      calc L0K = ⁅L0K, L0K⁆ := hperf.symm
        _ ≤ N := by
          rw [Subgroup.commutator_le]
          intro x hx y hy
          exact hGD.commutator_mem x y (hL0K_fixed x hx) (hL0K_fixed y hy)
    have hcentN : Subgroup.centralizer (N : Set ↥L) = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have hcomm : ∀ S, θ (D.Ψ S) * a = a * θ (D.Ψ S) := by
        intro S
        have hmem : θ (D.Ψ S) ∈ N :=
          hL0K_le_N (Subgroup.mem_map_of_mem θ (show D.Ψ S ∈ D.Ψ.range from ⟨S, rfl⟩))
        exact Subgroup.mem_centralizer_iff.mp ha _ hmem
      exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.outer_centralizer_bot hθ D hcomm
    exact sigmaFacts_of_fixed_commutator
      (fun n hn => hGD.fixed n hn) hsimpleN hperfectN
      (fun x y hx hy => hGD.commutator_mem x y hx hy) hcentN

end CFSG.LocalAnalysis.WeakClosure81

end
