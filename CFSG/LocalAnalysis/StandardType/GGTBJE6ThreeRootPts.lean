module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def e6ThreeRootPt (c : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ((∑ k, Tag.cartan .E6 j k * c k : ℤ) : ZMod 3)

private theorem e6c3p_cartan_symm (i j : Fin Tag.E6.rank) :
    Tag.cartan Tag.E6 i j = Tag.cartan Tag.E6 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem e6ThreeRootPt_mem_hypE6 (c : Fin Tag.E6.rank → ℤ) :
    e6ThreeRootPt c ∈ NoOffRest.hypE6 := by
  rw [NoOffRest.mem_hypE6]
  calc NoOffRest.kDotP 3 (e6ThreeRootPt c)
      = ∑ k, (c k : ZMod 3) *
          NoOffRest.kDotP 3 (fun j => ((Tag.E6.cartan k j : ℤ) : ZMod 3)) := by
        simp only [e6ThreeRootPt, NoOffRest.kDotP]
        push_cast
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [e6c3p_cartan_symm i k]
        ring
    _ = 0 := by simp [NoOffRest.kDot_cartan]

private theorem e6c3p_pt_reflect (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ℤ) :
    e6ThreeRootPt (reflect Tag.E6 i v) = adRefl Tag.E6 3 i (e6ThreeRootPt v) := by
  funext k
  have hz : ∑ l, Tag.cartan Tag.E6 k l * (reflect Tag.E6 i v) l =
      ∑ l, Tag.cartan Tag.E6 k l * v l -
        (∑ j, Tag.cartan Tag.E6 i j * v j) * Tag.cartan Tag.E6 i k := by
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      Pi.single_apply]
    rw [e6c3p_cartan_symm i k]
    congr 1
    simp [mul_comm, mul_left_comm]
  simp only [e6ThreeRootPt, adRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hz]
  push_cast
  ring

theorem e6ThreeRootPt_smul (w : WeylGroup Tag.E6) (c : Fin Tag.E6.rank → ℤ) :
    e6ThreeRootPt (w • c) = adAct Tag.E6 3 w (e6ThreeRootPt c) := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem Tag.E6).wordProd_surjective w
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, adAct_one]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, simple_smul, e6c3p_pt_reflect, ih, adAct_mul,
      adAct_simple]

private theorem e6c3p_check : e6Certificate.check = true := by decide +kernel

private theorem e6c3p_length : e6Certificate.roots.length = 72 := by decide

private theorem e6c3p_exists_root {c : Fin Tag.E6.rank → ℤ} (hc : IsRoot Tag.E6 c) :
    ∃ k < 72, e6Certificate.root k = c := by
  obtain ⟨k, hk, h⟩ := RootCertificate.exists_root_eq e6c3p_check hc
  exact ⟨k, e6c3p_length ▸ hk, h⟩

private def e6c3p_ptL (k : ℕ) : List ℕ :=
  List.ofFn fun j : Fin Tag.E6.rank => (e6ThreeRootPt (e6Certificate.root k) j).val

private theorem e6c3p_nodup : ((List.range 72).map e6c3p_ptL).Nodup := by decide +kernel

theorem e6ThreeRootPt_injOn {c c' : Fin Tag.E6.rank → ℤ} (hc : IsRoot Tag.E6 c)
    (hc' : IsRoot Tag.E6 c') (h : e6ThreeRootPt c = e6ThreeRootPt c') :
    ∀ j, (c j : ZMod 3) = (c' j : ZMod 3) := by
  obtain ⟨k, hk, rfl⟩ := e6c3p_exists_root hc
  obtain ⟨k', hk', rfl⟩ := e6c3p_exists_root hc'
  have hpt : e6c3p_ptL k = e6c3p_ptL k' := by
    unfold e6c3p_ptL
    rw [h]
  have hkk : k = k' :=
    (List.nodup_map_iff_inj_on List.nodup_range).mp e6c3p_nodup k (List.mem_range.mpr hk) k'
      (List.mem_range.mpr hk') hpt
  subst hkk
  intro j
  rfl

theorem e6ThreeRootPt_dot (γ c : Fin Tag.E6.rank → ℤ) :
    ∑ j, (γ j : ZMod 3) * e6ThreeRootPt c j =
      ((CFSG.LieType.Steinberg.Adjoint.iform γ c : ℤ) : ZMod 3) := by
  have hS : ∀ i j : Fin Tag.E6.rank,
      Tag.symmetrizedCartan Tag.E6 i j = Tag.cartan Tag.E6 i j := by
    intro i j
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  simp only [CFSG.LieType.Steinberg.Adjoint.iform, e6ThreeRootPt, hS]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem e6Three_dot_adAct (w : WeylGroup Tag.E6) (c : Fin Tag.E6.rank → ℤ)
    (x : Fin Tag.E6.rank → ZMod 3) :
    ∑ j, ((w • c) j : ZMod 3) * adAct Tag.E6 3 w x j = ∑ j, (c j : ZMod 3) * x j := by
  have key : ∀ k : Fin Tag.E6.rank,
      ∑ j, (w • c) j * (w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k = c k := by
    intro k
    have h := congrFun (weyl_smul_eq_sum w⁻¹ (w • c)) k
    rw [inv_smul_smul] at h
    simpa [Finset.sum_apply] using h.symm
  calc ∑ j, ((w • c) j : ZMod 3) * adAct Tag.E6 3 w x j
      = ∑ j, ∑ k, ((w • c) j : ZMod 3) *
          (((w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k : ℤ) : ZMod 3) * x k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [adAct, Finset.mul_sum, mul_assoc]
    _ = ∑ k, (∑ j, ((w • c) j : ZMod 3) *
          (((w⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k : ℤ) : ZMod 3)) * x k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, (c k : ZMod 3) * x k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        have h := congrArg (fun z : ℤ => (z : ZMod 3)) (key k)
        simpa only [Int.cast_sum, Int.cast_mul] using h

end CFSG.StandardType

end
