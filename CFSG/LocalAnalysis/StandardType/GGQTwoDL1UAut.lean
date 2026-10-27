module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U8Semilin
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder
import CFSG.LieType.Steinberg.CentralExt.SUThree
import CFSG.RankThree.PartOne.SEITZ2.SU3Pair

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.SEITZ2

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}

private lemma p9uUAut_bar_map_eq (hdata : UnitaryFieldData 2 1 K)
    (x : Matrix (Fin n) (Fin n) K) :
    x.map hdata.bar = x.map (unitaryInvolution K 2 1) := by
  ext i j
  exact (unitaryInvolution_eq_bar hdata (x i j)).symm

private lemma p9uUAut_mem_primeFormUnitary_iff (hdata : UnitaryFieldData 2 1 K)
    {g : GL (Fin n) K} :
    g ∈ primeFormUnitary hdata
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ↔
      ggIsUnitaryMat (p := 2) (f := 1) g := by
  rw [mem_primeFormUnitary, ggIsUnitaryMat, conjTr,
    CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one,
    Matrix.mul_one, p9uUAut_bar_map_eq hdata]

private lemma p9uUAut_diag_of_mem_center (hK : Nat.card K = 4) {z : Su K 2 1 n}
    (hz : z ∈ Subgroup.center (Su K 2 1 n)) (hn : 4 ≤ n) :
    ∃ c : K, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun _ => c) := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hcomm : ∀ u : Su K 2 1 n,
      ((z : GL (Fin n) K)) * (u : GL (Fin n) K) =
        (u : GL (Fin n) K) * (z : GL (Fin n) K) := by
    intro u
    have h := congrArg (fun w : Su K 2 1 n => (w : GL (Fin n) K))
      (Subgroup.mem_center_iff.mp hz u)
    simpa using h.symm
  obtain ⟨c, hc⟩ :=
    CFSG.StandardType.ggNSPosPF_exists_scalar_of_commute_SUid hF le_rfl
      (by omega : 3 ≤ n) hcomm
  refine ⟨(c : K), ?_⟩
  have hc' : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) :=
    congrArg (fun w : GL (Fin n) K => (w : Matrix (Fin n) (Fin n) K)) hc
  rw [hc', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem qtwoDL1_unitChart_semilin (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ)
    (hrange : ψ.range = X) (α : MulAut ↥X) :
    ∃ (g : GL (Fin n) K) (τ : K ≃+* K), ggIsUnitaryMat (p := 2) (f := 1) g ∧
      ∀ u v : Su K 2 1 n,
        ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (g : Matrix (Fin n) (Fin n) K) *
              (((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ) *
                ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
          ∀ y : ↥X, (y : G) = ψ u → ((α y : ↥X) : G) = ψ v := by
  let hdata : UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  let hSU : SUid (unitaryInvolution K 2 1) n = unitarySU 2 1 K n :=
    SUid_eq_unitarySU hdata n
  let e : Su K 2 1 n ≃* ↥(unitarySU 2 1 K n) := MulEquiv.subgroupCongr hSU
  let φ : ↥(unitarySU 2 1 K n) →* ↥X :=
    { toFun := fun x => ⟨ψ (e.symm x), by
        rw [← hrange]
        exact ⟨e.symm x, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp }
  have hφs : Function.Surjective φ := by
    intro y
    have hy : (y : G) ∈ ψ.range := by rw [hrange]; exact y.2
    obtain ⟨u, hu⟩ := hy
    refine ⟨e u, ?_⟩
    apply Subtype.ext
    change ψ (e.symm (e u)) = (y : G)
    rw [e.symm_apply_apply]
    exact hu
  have hφker : ∀ x : ↥(unitarySU 2 1 K n), φ x = 1 →
      ∃ c : K, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.diagonal (fun _ => c) := by
    intro x hx
    have hψ : ψ (e.symm x) = 1 := by
      have hx' := congrArg Subtype.val hx
      simpa [φ] using hx'
    have hz : e.symm x ∈ Subgroup.center (Su K 2 1 n) :=
      h.ker (by rw [MonoidHom.mem_ker]; exact hψ)
    obtain ⟨c, hc⟩ := p9uUAut_diag_of_mem_center hK hz h.four_le
    refine ⟨c, ?_⟩
    have hcoe : ((e.symm x : Su K 2 1 n) : GL (Fin n) K) = (x : GL (Fin n) K) := rfl
    simpa [hcoe] using hc
  obtain ⟨g, hg, τ, hsl⟩ :=
    CFSG.StandardType.FrameRoute.P9_U8a_exists_isSemilin hdata h.four_le hφs hφker α
  refine ⟨g, τ, (p9uUAut_mem_primeFormUnitary_iff hdata).mp hg, ?_⟩
  intro u v huv y hy
  have hv : ((e v : ↥(unitarySU 2 1 K n)) : GL (Fin n) K) =
      g * glAut τ (e u : GL (Fin n) K) * g⁻¹ := by
    apply Units.ext
    change ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) *
        (((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    simpa [coe_glAut] using huv
  have hα := hsl (e u) (e v) hv
  have hφu : φ (e u) = y := by
    apply Subtype.ext
    change ψ (e.symm (e u)) = (y : G)
    rw [e.symm_apply_apply]
    exact hy.symm
  have hαy : α y = φ (e v) := by rw [← hφu]; exact hα
  calc ((α y : ↥X) : G) = (φ (e v) : G) := congrArg Subtype.val hαy
    _ = ψ (e.symm (e v)) := rfl
    _ = ψ v := by rw [e.symm_apply_apply]

theorem qtwoDL1_unitChart_scalar_of_fix (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ)
    {M : GL (Fin n) K} (hM : ggIsUnitaryMat (p := 2) (f := 1) M)
    (hfix : ∀ u v : Su K 2 1 n,
      ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (M : Matrix (Fin n) (Fin n) K) * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → ψ v = ψ u) :
    ∃ c : K, (M : Matrix (Fin n) (Fin n) K) = c • (1 : Matrix (Fin n) (Fin n) K) := by
  have hn : 4 ≤ n := h.four_le
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let σ : Su K 2 1 n →* Su K 2 1 n :=
    { toFun := fun u => ⟨M * (u : GL (Fin n) K) * M⁻¹,
        CFSG.LieType.Steinberg.conj_mem_SUid
          (unitaryInvolution_involutive hF) hM u.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hc_mem : ∀ u : Su K 2 1 n,
      σ u * u⁻¹ ∈ Subgroup.center (Su K 2 1 n) := by
    intro u
    apply h.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hfix u (σ u) rfl, mul_inv_cancel]
  let c : Su K 2 1 n →* Subgroup.center (Su K 2 1 n) :=
    { toFun := fun u => ⟨σ u * u⁻¹, hc_mem u⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun u v => by
        apply Subtype.ext
        have hcalc : (σ (u * v) * (u * v)⁻¹ : Su K 2 1 n) =
            (σ u * u⁻¹) * (σ v * v⁻¹) := by
          have hcomm : σ v * v⁻¹ * u⁻¹ = u⁻¹ * (σ v * v⁻¹) :=
            (Subgroup.mem_center_iff.mp (hc_mem v) u⁻¹).symm
          calc (σ (u * v) * (u * v)⁻¹ : Su K 2 1 n)
              = (σ u * σ v) * (v⁻¹ * u⁻¹) := by rw [map_mul, mul_inv_rev]
            _ = σ u * ((σ v * v⁻¹) * u⁻¹) := by group
            _ = σ u * (u⁻¹ * (σ v * v⁻¹)) := by rw [hcomm]
            _ = (σ u * u⁻¹) * (σ v * v⁻¹) := by group
        exact hcalc }
  have hperf : Group.IsPerfect (Su K 2 1 n) := isPerfect_Su hK h.four_le
  have hcommle : ⁅(⊤ : Subgroup (Su K 2 1 n)), ⊤⁆ ≤ c.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (c b).2 (c a : Su K 2 1 n))
  have htop : (⊤ : Subgroup (Su K 2 1 n)) ≤ c.ker := by
    rw [← hperf.commutator_eq_top]
    exact hcommle
  have hσfix : ∀ u : Su K 2 1 n, σ u = u := by
    intro u
    have hc1 : c u = 1 := htop (Subgroup.mem_top u)
    have hprod : σ u * u⁻¹ = 1 := by
      have h := congrArg (fun z : Subgroup.center (Su K 2 1 n) => (z : Su K 2 1 n)) hc1
      simpa [c] using h
    calc σ u = σ u * u⁻¹ * u := by group
      _ = 1 * u := by rw [hprod]
      _ = u := by simp
  have hMcomm : ∀ u : Su K 2 1 n,
      M * (u : GL (Fin n) K) = (u : GL (Fin n) K) * M := by
    intro u
    have hval : M * (u : GL (Fin n) K) * M⁻¹ = (u : GL (Fin n) K) :=
      congrArg (fun w : Su K 2 1 n => (w : GL (Fin n) K)) (hσfix u)
    calc M * (u : GL (Fin n) K) = M * (u : GL (Fin n) K) * M⁻¹ * M := by group
      _ = (u : GL (Fin n) K) * M := by rw [hval]
  obtain ⟨c₀, hc₀⟩ :=
    CFSG.StandardType.ggNSPosPF_exists_scalar_of_commute_SUid hF le_rfl
      (by omega : 3 ≤ n) hMcomm
  refine ⟨(c₀ : K), ?_⟩
  have hc₀' : (M : Matrix (Fin n) (Fin n) K) =
      ((Matrix.GeneralLinearGroup.scalar (Fin n) c₀ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) :=
    congrArg (fun w : GL (Fin n) K => (w : Matrix (Fin n) (Fin n) K)) hc₀
  rw [hc₀', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]

end CFSG.StandardType.QTwo

end
