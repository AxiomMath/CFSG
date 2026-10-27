module

public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsSpComp

public section

namespace CFSG.StandardType.RCKA6

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Dickson.Bal207 CFSG.HardMathSupport.Dickson.Bal207.FamF42
  CFSG.LieType.Steinberg.Adjoint

open scoped MatrixGroups

private theorem rckCS_fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (x : G) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : x * y = y * x := by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h]
    exact h'.symm
  · intro h
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [← h]
      _ = y := by group

theorem rckF4_comp_shape
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (x : ↥(adjointGroup Tag.F4 K)) (hx : orderOf x = 3) :
    (∀ L L' : Subgroup ↥(adjointGroup Tag.F4 K),
      CFSG.Open.IsComponentOf L
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) →
      CFSG.Open.IsComponentOf L'
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) → L = L') ∧
    ∀ L : Subgroup ↥(adjointGroup Tag.F4 K),
      CFSG.Open.IsComponentOf L
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) →
      Subgroup.center ↥L = ⊥ := by
  classical
  refine ⟨?_, ?_⟩
  ·
    intro L L' hL hL'
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    haveI : Finite ↥(adjointGroup Tag.F4 K) := by
      have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
      infer_instance
    have hpK : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      norm_num
    obtain ⟨p₀, S, a, ι, hSq, hT, hap, h1, hinj, hrange, -, hconj, hTame⟩ :=
      exists_langSetup_F4_of_orderOf_eq_three hpK x hx
    have hq2 : S.D.q = 2 := hSq.trans hK
    obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param (L := AlgebraicClosure K) hap
    have hk0 : ∃ i, k i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply h1
      rw [show a = 1 from funext fun i => by rw [hak i, hcon i, pow_zero]; rfl, rootDiagUnit_one]
    have hcomp : ∀ L : Subgroup ↥(adjointGroup Tag.F4 K),
        CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) →
          ∃ i : KernelComponent (rootCharHom a),
            CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
              L.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := fun L hL =>
      components_of_langSetup S Nat.prime_three ι hinj hrange (MulAut.conj x) hconj hT hap h1
        hTame hL
    rcases classify_kernel k hk3 hk0 with he | hA2
    ·
      obtain ⟨hcard, hconn⟩ := kernel_conn_of_orth k hk3 hk0 he
      have huniq : ∀ i j : KernelComponent (rootCharHom a), i = j :=
        eq_of_kernel_conn hω3 hω1 hak hconn
      obtain ⟨i, -, hi⟩ := hcomp L hL
      obtain ⟨j, -, hj⟩ := hcomp L' hL'
      rw [huniq i j] at hi
      exact Subgroup.map_injective hinj (hi.trans hj.symm)
    ·
      obtain ⟨i, hiq, -⟩ := hcomp L hL
      exact absurd
        (isSolvable_rationalComponent_of_a2a2 S hT hap hω3 hω1 hk3 hk0 hak hA2 hq2 i)
        (not_isSolvable_of_isQuasisimple' hiq)
  ·
    intro L hL
    have hcent : CFSG.Open.IsComponentOf L
        (Subgroup.centralizer ({x} : Set ↥(adjointGroup Tag.F4 K))) := by
      rw [← rckCS_fixSubgroup_conj_eq_centralizer (x := x)]
      exact hL
    obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ :=
      CFSG.StandardType.A6Red.ggA6F4_comp_iso_sp (K := K) hK x hx L hcent
    letI : Field F := hFfield
    letI : Finite F := hFfin
    haveI : CharP F 2 := by
      haveI : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 1)
        (by rw [← Nat.card_eq_fintype_card, hFcard]; norm_num)
    have hcenter : Subgroup.center (CFSG.Open.StatedSp 3 F) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := 3) (by norm_num)
    have hmap : (Subgroup.center ↥L).map e.toMonoidHom = ⊥ :=
      (Subgroup.map_center_eq e).trans hcenter
    exact Subgroup.map_injective e.injective (hmap.trans (Subgroup.map_bot _).symm)

end CFSG.StandardType.RCKA6
