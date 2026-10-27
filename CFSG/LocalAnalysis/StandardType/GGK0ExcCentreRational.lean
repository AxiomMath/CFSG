module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import Mathlib.LinearAlgebra.Pi

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem lk0xpa2b_rootChar_zsmul {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (n : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (n • v) = rootChar a v ^ n := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

private theorem lk0xpa2b_node_eq
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (b : Fin ρ.tau.rank → Omegaˣ) (hb : ∀ i, b i ^ p = 1)
    (t : Fin ρ.row.diagram.marks.length → ZMod p)
    (ht : ∀ i, rootChar b (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ (t i).val)
    (hinv : ∀ i, t (ρ.row.nodePerm i) = t i) :
    ∀ j, rootChar (ρ.torusStep b) (ρ.nodeMap (Pi.single j 1)) =
         rootChar b (ρ.nodeMap (Pi.single j 1)) := by
  intro j
  obtain ⟨i, rfl⟩ := ρ.row.nodePerm.surjective j
  have hchar := ρ.torusStep_char b (ρ.nodeMap (Pi.single i 1))
  rw [ρ.frob_nodes i, ht i, ρ.q_eq] at hchar
  have hbnode : rootChar b (ρ.nodeMap (Pi.single (ρ.row.nodePerm i) 1)) =
      ρ.zeta ^ (t i).val := by
    rw [ht (ρ.row.nodePerm i), hinv i]
  by_cases hd : ρ.row.d = 1
  · have heps : ρ.epsilon = 1 := by rw [ρ.epsilon_eq, if_pos hd]
    have hdvd : p ∣ 2 ^ lab.n - 1 := by
      by_contra hc
      have h2 : ρ.row.d = 2 := by rw [ρ.row.d_eq, if_neg hc]
      omega
    have hzq : ρ.zeta ^ (2 ^ lab.n) = ρ.zeta := by
      obtain ⟨k, hk⟩ := hdvd
      have hp : ρ.zeta ^ p = 1 := by
        simpa only [ρ.zeta_order] using pow_orderOf_eq_one ρ.zeta
      have hle : 1 ≤ 2 ^ lab.n := by
        have h : 0 < 2 ^ lab.n := pow_pos (by norm_num) _
        omega
      calc ρ.zeta ^ (2 ^ lab.n) = ρ.zeta ^ ((2 ^ lab.n - 1) + 1) := by
            rw [Nat.sub_add_cancel hle]
        _ = ρ.zeta ^ (2 ^ lab.n - 1) * ρ.zeta := by rw [pow_add, pow_one]
        _ = ρ.zeta ^ (p * k) * ρ.zeta := by rw [hk]
        _ = (ρ.zeta ^ p) ^ k * ρ.zeta := by rw [pow_mul]
        _ = 1 ^ k * ρ.zeta := by rw [hp]
        _ = ρ.zeta := by simp
    have hrhs : (ρ.zeta ^ (t i).val) ^ (2 ^ lab.n) = ρ.zeta ^ (t i).val := by
      calc (ρ.zeta ^ (t i).val) ^ (2 ^ lab.n)
          = (ρ.zeta ^ (2 ^ lab.n)) ^ (t i).val := by rw [← pow_mul, mul_comm, pow_mul]
        _ = ρ.zeta ^ (t i).val := by rw [hzq]
    rw [heps, one_smul] at hchar
    rw [hchar, hrhs, hbnode]
  · have heps : ρ.epsilon = -1 := by rw [ρ.epsilon_eq, if_neg hd]
    have hdvd : p ∣ 2 ^ lab.n + 1 := by
      rcases hpair.2.2.1 with h | h
      · exact absurd (by rw [ρ.row.d_eq, if_pos h]) hd
      · exact h
    have hzq : ρ.zeta ^ (2 ^ lab.n) = ρ.zeta⁻¹ := by
      obtain ⟨k, hk⟩ := hdvd
      have hp : ρ.zeta ^ p = 1 := by
        simpa only [ρ.zeta_order] using pow_orderOf_eq_one ρ.zeta
      have hone : ρ.zeta ^ (2 ^ lab.n + 1) = 1 := by
        calc ρ.zeta ^ (2 ^ lab.n + 1) = (ρ.zeta ^ p) ^ k := by rw [hk, pow_mul]
          _ = 1 ^ k := by rw [hp]
          _ = 1 := by simp
      have hmul : ρ.zeta ^ (2 ^ lab.n) * ρ.zeta = 1 := by
        rw [← pow_succ, hone]
      exact (mul_eq_one_iff_eq_inv).mp hmul
    have hrhs : (((ρ.zeta ^ (t i).val) ^ (2 ^ lab.n)))⁻¹ = ρ.zeta ^ (t i).val := by
      calc (((ρ.zeta ^ (t i).val) ^ (2 ^ lab.n)))⁻¹
          = (((ρ.zeta ^ (2 ^ lab.n)) ^ (t i).val))⁻¹ := by rw [← pow_mul, mul_comm, pow_mul]
        _ = (((ρ.zeta⁻¹) ^ (t i).val))⁻¹ := by rw [hzq]
        _ = ρ.zeta ^ (t i).val := by rw [inv_pow, inv_inv]
    rw [heps, lk0xpa2b_rootChar_zsmul, zpow_neg_one] at hchar
    have hu : rootChar (ρ.torusStep b) (ρ.nodeMap (Pi.single (ρ.row.nodePerm i) 1)) =
        (((ρ.zeta ^ (t i).val) ^ (2 ^ lab.n)))⁻¹ := (inv_eq_iff_eq_inv).mp hchar
    rw [hu, hrhs, hbnode]

private theorem lk0xpa2b_rootChar_all_eq
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (b : Fin ρ.tau.rank → Omegaˣ) (hb : ∀ i, b i ^ p = 1)
    (t : Fin ρ.row.diagram.marks.length → ZMod p)
    (ht : ∀ i, rootChar b (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ (t i).val)
    (hinv : ∀ i, t (ρ.row.nodePerm i) = t i) :
    ∀ v : Fin ρ.tau.rank → ℤ, rootChar (ρ.torusStep b) v = rootChar b v := by
  have hnode := lk0xpa2b_node_eq hpair ρ b hb t ht hinv
  have hspan : Submodule.span ℤ (Set.range (fun j : Fin ρ.row.diagram.marks.length =>
      (Pi.single j 1 : Fin ρ.row.diagram.marks.length → ℤ))) = ⊤ := by
    have h := (Pi.basisFun ℤ (Fin ρ.row.diagram.marks.length)).span_eq
    rw [show Set.range (Pi.basisFun ℤ (Fin ρ.row.diagram.marks.length)) =
        Set.range (fun j : Fin ρ.row.diagram.marks.length =>
          (Pi.single j 1 : Fin ρ.row.diagram.marks.length → ℤ)) by
      ext v
      simp [Pi.basisFun_apply]] at h
    exact h
  have hspanN : Submodule.span ℤ (Set.range (fun j : Fin ρ.row.diagram.marks.length =>
      ρ.nodeMap (Pi.single j 1))) = ⊤ := by
    have h1 : Submodule.span ℤ (Set.range (fun j : Fin ρ.row.diagram.marks.length =>
        ρ.nodeMap (Pi.single j 1)))
        = Submodule.map ρ.nodeMap (Submodule.span ℤ
            (Set.range (fun j : Fin ρ.row.diagram.marks.length =>
              (Pi.single j 1 : Fin ρ.row.diagram.marks.length → ℤ)))) := by
      rw [Submodule.map_span]
      congr 1
      ext v
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨_, ⟨j, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
    rw [h1, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr ρ.nodeMap_surj]
  have hmem : ∀ v, v ∈ Submodule.span ℤ (Set.range (fun j : Fin ρ.row.diagram.marks.length =>
      ρ.nodeMap (Pi.single j 1))) → rootChar (ρ.torusStep b) v = rootChar b v := by
    intro v hv
    exact Submodule.span_induction
      (fun x hx => by obtain ⟨j, rfl⟩ := hx; exact hnode j)
      (by rw [rootChar_zero, rootChar_zero])
      (fun x y _ _ ihx ihy => by rw [rootChar_add, rootChar_add, ihx, ihy])
      (fun c x _ ih => by rw [lk0xpa2b_rootChar_zsmul, lk0xpa2b_rootChar_zsmul, ih])
      hv
  intro v
  exact hmem v (by rw [hspanN]; trivial)

private theorem lk0xpa2b_torusStep_eq
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (b : Fin ρ.tau.rank → Omegaˣ) (hb : ∀ i, b i ^ p = 1)
    (t : Fin ρ.row.diagram.marks.length → ZMod p)
    (ht : ∀ i, rootChar b (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ (t i).val)
    (hinv : ∀ i, t (ρ.row.nodePerm i) = t i) :
    ρ.torusStep b = b := by
  funext j
  have hall := lk0xpa2b_rootChar_all_eq hpair ρ b hb t ht hinv (Pi.single j 1)
  have hxj : rootChar (ρ.torusStep b) (Pi.single j 1 : Fin ρ.tau.rank → ℤ) =
      (ρ.torusStep b) j := by
    have h := rootChar_nsmul_single (ρ.torusStep b) j 1
    simpa using h
  have hbj : rootChar b (Pi.single j 1 : Fin ρ.tau.rank → ℤ) = b j := by
    have h := rootChar_nsmul_single b j 1
    simpa using h
  rwa [hxj, hbj] at hall

theorem PA2b_mem_torus_of_perm_invariant
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (b : Fin ρ.tau.rank → Omegaˣ) (hb : ∀ i, b i ^ p = 1)
    (t : Fin ρ.row.diagram.marks.length → ZMod p)
    (ht : ∀ i, rootChar b (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ (t i).val)
    (hinv : ∀ i, t (ρ.row.nodePerm i) = t i) :
    rootDiagUnit ρ.tau b ∈ ρ.setup.D.torus := by
  have hb_eq : ρ.torusStep b = b := lk0xpa2b_torusStep_eq hpair ρ b hb t ht hinv
  have hfix : ρ.setup.D.step (rootDiagUnit ρ.tau b) = rootDiagUnit ρ.tau b := by
    rw [← ρ.torusStep_diag b, hb_eq]
  rw [show ρ.setup.D.torus =
      CFSG.RankThree.PartOne.KE.twistedTorusOf ρ.setup.D.n ρ.setup.D.Φ from rfl]
  rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
  refine ⟨rootDiagUnit_mem_torusGroup b, ?_⟩
  have hds : ρ.setup.D.step (rootDiagUnit ρ.tau b) =
      ρ.setup.D.n * ρ.setup.D.Φ (rootDiagUnit ρ.tau b) * ρ.setup.D.n⁻¹ := by
    simp [LangDatum.step, MulAut.conj_apply]
  rw [← hds]
  exact hfix

end CFSG.StandardType.GGK0ExcCentreU

end
