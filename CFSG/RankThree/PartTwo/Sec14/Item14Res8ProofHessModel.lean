module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessTools
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res8Hess

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.RankThree.LocalRank (aschbacherSolvableCore
  solvable_prime_complement_core_characterization)
open CFSG.Assembly.RankThreeEven (projImage)

noncomputable abbrev thetaC {X : Type} [Group X] (b : X) : Subgroup X :=
  inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X))

theorem thetaC_map_equiv {X Y : Type} [Group X] [Group Y] [Finite X] (φ : X ≃* Y) (b : X) :
    (thetaC b).map φ.toMonoidHom = thetaC (φ b) := by
  rw [thetaC, thetaC, Sec6.map_inSubgroup_theta_of_injective φ.toMonoidHom φ.injective,
    CFSG.RankThree.PartTwo.map_centralizer_singleton φ b]

theorem mem_thetaC_iff_conj {X : Type} [Group X] [Finite X] {n b d : X} (hnb : n * b * n⁻¹ = d)
    (y : X) : y ∈ thetaC b ↔ n * y * n⁻¹ ∈ thetaC d := by
  have h := thetaC_map_equiv (MulAut.conj n) b
  rw [MulAut.conj_apply, hnb] at h
  rw [← h, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hy
    simpa [mul_assoc] using hy
  · intro hy
    simpa [mul_assoc] using hy

theorem le_theta_of_normal {G : Type} [Group G] [Finite G] {J V₀ : Subgroup G} (hVJ : V₀ ≤ J)
    (hVn : ∀ x ∈ J, ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀) (hVs : Group.IsSolvable ↥V₀)
    (hVp : ¬ 3 ∣ Nat.card ↥V₀) : V₀ ≤ inSubgroup (aschbacherSolvableCore 3) J := by
  have hn : (V₀.subgroupOf J).Normal := ⟨fun x hx g => by
    have hxV : (x : G) ∈ V₀ := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (hVn g g.2 x hxV)⟩
  have hsol : Group.IsSolvable ↥(V₀.subgroupOf J) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hVJ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hVJ).injective
  have hcard : Nat.card ↥(V₀.subgroupOf J) = Nat.card ↥V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVJ).toEquiv
  have hle := (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).2.2.2.1 _
    hn hsol (by rw [hcard]; exact hVp)
  intro v hv
  exact ⟨⟨v, hVJ hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

theorem not_dvd_card_inSubgroup_theta {G : Type} [Group G] [Finite G] (J : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) J) := by
  rw [inSubgroup, Subgroup.card_map_of_injective J.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).2.2.1

theorem inSubgroup_theta_le {G : Type} [Group G] (J : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) J ≤ J :=
  Subgroup.map_subtype_le _

section Matrices

variable {K : Type} [Field K]

theorem commute_of_mk_commute_of_coprime' {l w : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk l * ProjGenLinGroup.mk w = ProjGenLinGroup.mk w * ProjGenLinGroup.mk l)
    (hn : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk l))) : l * w = w * l := by
  obtain ⟨μ, hμ⟩ := exists_conj_of_mk_comm h
  have hμ3 : μ ^ 3 = 1 := by
    have e := congrArg (fun x : GL (Fin 3) K => GeneralLinearGroup.det x) hμ
    simp only [map_mul, map_inv] at e
    have hs : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) μ) = μ ^ 3 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    rw [hs, mul_comm (GeneralLinearGroup.det l), mul_assoc, mul_inv_cancel, mul_one] at e
    have := congrArg (fun x => x * (GeneralLinearGroup.det w)⁻¹) e
    simpa using this.symm
  set n := orderOf (ProjGenLinGroup.mk l) with hn_def
  have hln : ProjGenLinGroup.mk (l ^ n) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hln
  obtain ⟨s, hs⟩ := hln
  have hpow : ∀ m : ℕ, l ^ m * w * (l ^ m)⁻¹ = GeneralLinearGroup.scalar (Fin 3) (μ ^ m) * w := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc l ^ (m + 1) * w * (l ^ (m + 1))⁻¹ = l * (l ^ m * w * (l ^ m)⁻¹) * l⁻¹ := by
            rw [pow_succ']; group
        _ = l * (GeneralLinearGroup.scalar (Fin 3) (μ ^ m) * w) * l⁻¹ := by rw [ih]
        _ = (l * GeneralLinearGroup.scalar (Fin 3) (μ ^ m)) * w * l⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) (μ ^ m) * l) * w * l⁻¹ := by
            rw [scalar_mul_comm]
        _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ m) * (l * w * l⁻¹) := by group
        _ = GeneralLinearGroup.scalar (Fin 3) (μ ^ (m + 1)) * w := by
            rw [hμ, ← mul_assoc, ← map_mul, ← pow_succ]
  have e2 := hpow n
  have e3 : l ^ n * w * (l ^ n)⁻¹ = w := by
    rw [← hs, ← scalar_mul_comm]
    group
  rw [e3] at e2
  have hμn : μ ^ n = 1 := eq_one_of_scalar_mul_eq e2.symm
  have hμ1 : μ = 1 := by
    have h1 : orderOf μ ∣ 3 := orderOf_dvd_of_pow_eq_one hμ3
    have h2 : orderOf μ ∣ n := orderOf_dvd_of_pow_eq_one hμn
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn h1 h2)
  rw [hμ1, map_one, one_mul] at hμ
  calc l * w = l * w * l⁻¹ * l := by group
    _ = w * l := by rw [hμ]

@[expose] def cycDiag' (a b c : K) : Fin 3 → Fin 3 → K :=
  ![![a, b, c], ![c, a, b], ![b, c, a]]

omit [Field K] in
theorem exists_cycDiag'_ne {a b c : K} (habc : ¬ (a = b ∧ b = c)) {i j : Fin 3} (hij : i ≠ j) :
    ∃ t : Fin 3, cycDiag' a b c t i ≠ cycDiag' a b c t j := by
  by_contra h
  push Not at h
  apply habc
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  fin_cases i <;> fin_cases j <;>
    simp [cycDiag'] at h0 h1 h2 hij ⊢ <;> grind

theorem cyc_mul_diagonal_mul_inv' (a b c : K) :
    ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] *
      ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![c, a, b] := by
  rw [coe_cycThree, coe_cycThree_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

theorem cyc_inv_mul_diagonal_mul' (a b c : K) :
    ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] *
      ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![b, c, a] := by
  rw [coe_cycThree, coe_cycThree_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

end Matrices

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

noncomputable def torusM (hK : PiField π p f K) (hp2 : p ≠ 2) :
    Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
  Subgroup.centralizer {tM hK hp2 _ isTInv_tOne} ⊓ Subgroup.centralizer {tM hK hp2 _ isTInv_tTwo}

variable (hK : PiField π p f K) (hp2 : p ≠ 2)

theorem offDiag_of_mem_torusM {x : projImage (slPi π 3 (p ^ f) K)} (hx : x ∈ torusM hK hp2)
    {A : GL (Fin 3) K} (hA : ProjGenLinGroup.mk A = (x : ProjGenLinGroup (Fin 3) K)) :
    ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
  offDiag_of_comm_t hK hp2 (Subgroup.mem_centralizer_singleton_iff.mp hx.1)
    (Subgroup.mem_centralizer_singleton_iff.mp hx.2) hA

theorem mem_torusM_of_offDiag {x : projImage (slPi π 3 (p ^ f) K)} {A : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (x : ProjGenLinGroup (Fin 3) K))
    (hoff : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    x ∈ torusM hK hp2 :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_offDiag hA hoff (coe_tM hK hp2 _)),
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_offDiag hA hoff (coe_tM hK hp2 _))⟩

theorem torusM_comm {x y : projImage (slPi π 3 (p ^ f) K)} (hx : x ∈ torusM hK hp2)
    (hy : y ∈ torusM hK hp2) : x * y = y * x := by
  obtain ⟨A, -, hA⟩ := exists_lift x
  obtain ⟨B, -, hB⟩ := exists_lift y
  exact comm_of_offDiag_offDiag hA hB (offDiag_of_mem_torusM hK hp2 hx hA)
    (offDiag_of_mem_torusM hK hp2 hy hB)

theorem tM_mem_torusM {t : GL (Fin 3) K} (ht : IsTInv t) : tM hK hp2 t ht ∈ torusM hK hp2 := by
  refine mem_torusM_of_offDiag hK hp2 (coe_tM hK hp2 ht).symm fun i j hij => ?_
  obtain ⟨a, b, c, rfl⟩ := isTInv_diagUnits ht
  rw [coe_diagUnits]
  exact diagonal_apply_ne _ hij

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
variable {dM cM : projImage (slPi π 3 (p ^ f) K)}

theorem commute_dM_of_mem_torusM
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    {x : projImage (slPi π 3 (p ^ f) K)} (hx : x ∈ torusM hK hp2) : x * dM = dM * x := by
  obtain ⟨A, -, hA⟩ := exists_lift x
  exact comm_of_offDiag hA (offDiag_of_mem_torusM hK hp2 hx hA)
    (hdM.trans (by rw [diagTau_eq_diagUnits hτ (tau_ne_zero hτ)]))

include hτ1 in
theorem mem_torusM_of_comm_coprime
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    {x : projImage (slPi π 3 (p ^ f) K)} (hxd : x * dM = dM * x)
    (hx3 : Nat.Coprime 3 (orderOf x)) : x ∈ torusM hK hp2 := by
  obtain ⟨A, -, hA⟩ := exists_lift x
  have hcomm : ProjGenLinGroup.mk A * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk A := by
    rw [hA, ← hdM]
    exact congrArg Subtype.val hxd
  have hord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk A)) := by
    rw [hA, Subgroup.orderOf_coe]
    exact hx3
  exact mem_torusM_of_offDiag hK hp2 hA
    (offDiag_of_comm_diagTau hτ hτ1 (commute_of_mk_commute_of_coprime' hcomm hord))

noncomputable def torus3M : Subgroup (projImage (slPi π 3 (p ^ f) K)) where
  carrier := {x | x ∈ torusM hK hp2 ∧ Nat.Coprime 3 (orderOf x)}
  mul_mem' {x y} hx hy := by
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    have hc : Commute x y := torusM_comm hK hp2 hx.1 hy.1
    have h1 := hc.orderOf_mul_dvd_lcm
    have h2 : Nat.Coprime 3 (orderOf x * orderOf y) := Nat.Coprime.mul_right hx.2 hy.2
    exact Nat.Coprime.coprime_dvd_right (h1.trans (Nat.lcm_dvd_mul _ _)) h2
  one_mem' := ⟨one_mem _, by rw [orderOf_one]; exact Nat.coprime_one_right 3⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by rw [orderOf_inv]; exact hx.2⟩

theorem not_dvd_card_torus3M : ¬ 3 ∣ Nat.card (torus3M hK hp2) := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := torus3M hK hp2) 3 h3
  have hx3 := hx.2
  rw [← Subgroup.orderOf_mk x hx, hxo] at hx3
  norm_num at hx3

include hτ1 in
theorem torus3M_le_thetaC
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ)) :
    torus3M hK hp2 ≤ thetaC dM := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hVC : torus3M hK hp2 ≤ Subgroup.centralizer ({dM} : Set _) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_dM_of_mem_torusM hK hp2 hτ hdM hx.1)
  refine le_theta_of_normal hVC (fun g hg v hv => ?_) ?_ (not_dvd_card_torus3M hK hp2)
  · have hgd : g * dM = dM * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hvd : v * dM = dM * v := Subgroup.mem_centralizer_singleton_iff.mp (hVC hv)
    have hcd : g * v * g⁻¹ * dM = dM * (g * v * g⁻¹) := by
      have hginv : g⁻¹ * dM = dM * g⁻¹ := by
        calc g⁻¹ * dM = g⁻¹ * (dM * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * dM) * g⁻¹ := by rw [hgd]
          _ = dM * g⁻¹ := by group
      calc g * v * g⁻¹ * dM = g * v * (g⁻¹ * dM) := by group
        _ = g * v * (dM * g⁻¹) := by rw [hginv]
        _ = g * (v * dM) * g⁻¹ := by group
        _ = g * (dM * v) * g⁻¹ := by rw [hvd]
        _ = (g * dM) * v * g⁻¹ := by group
        _ = dM * (g * v * g⁻¹) := by rw [hgd]; group
    have hco : Nat.Coprime 3 (orderOf (g * v * g⁻¹)) := by
      rw [orderOf_conj_eq]
      exact hv.2
    exact ⟨mem_torusM_of_comm_coprime hK hp2 hτ hτ1 hdM hcd hco, hco⟩
  · have : IsMulCommutative (torus3M hK hp2) :=
      ⟨⟨fun x y => Subtype.ext (torusM_comm hK hp2 x.2.1 y.2.1)⟩⟩
    infer_instance

include hτ1 in
theorem thetaC_le_torusM
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ)) :
    thetaC dM ≤ torusM hK hp2 := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  intro x hx
  have hxC := inSubgroup_theta_le _ hx
  exact mem_torusM_of_comm_coprime hK hp2 hτ hτ1 hdM
    (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    (coprime_orderOf_of_mem (not_dvd_card_inSubgroup_theta _) hx)

theorem mem_centralizer_conj' {G : Type*} [Group G] {R : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hx : x ∈ Subgroup.centralizer (R : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) r).mp hr
  have h := hx _ hr'
  calc r * (g * x * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * r := by group

theorem normalizer_le_normalizer_centralizer' {G : Type*} [Group G] [Finite G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := fun _ hg =>
  Subgroup.mem_normalizer_fintype fun _ hx => mem_centralizer_conj' hg hx

theorem mem_torusM_of_comm_cyc
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {z : projImage (slPi π 3 (p ^ f) K)} (hzT : z ∈ torusM hK hp2) (hz1 : z ≠ 1)
    (hz3 : Nat.Coprime 3 (orderOf z)) {g : projImage (slPi π 3 (p ^ f) K)}
    (h1 : z * g = g * z) (h2 : cM * z * cM⁻¹ * g = g * (cM * z * cM⁻¹))
    (h3 : cM⁻¹ * z * cM * g = g * (cM⁻¹ * z * cM)) : g ∈ torusM hK hp2 := by
  obtain ⟨Z, -, hZ⟩ := exists_lift z
  obtain ⟨G, -, hG⟩ := exists_lift g
  have hZoff := offDiag_of_mem_torusM hK hp2 hzT hZ
  have hZd := eq_diagonal_of_offDiag hZoff
  set a := (Z : Matrix (Fin 3) (Fin 3) K) 0 0
  set b := (Z : Matrix (Fin 3) (Fin 3) K) 1 1
  set c := (Z : Matrix (Fin 3) (Fin 3) K) 2 2
  have key : ∀ (W : GL (Fin 3) K) (w : projImage (slPi π 3 (p ^ f) K)),
      ProjGenLinGroup.mk W = (w : ProjGenLinGroup (Fin 3) K) → w * g = g * w →
        Nat.Coprime 3 (orderOf w) →
          (W : Matrix (Fin 3) (Fin 3) K) * G = (G : Matrix (Fin 3) (Fin 3) K) * W := by
    intro W w hW hwg hw3
    have hc : ProjGenLinGroup.mk W * ProjGenLinGroup.mk G =
        ProjGenLinGroup.mk G * ProjGenLinGroup.mk W := by
      rw [hW, hG]
      exact congrArg Subtype.val hwg
    have hord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk W)) := by
      rw [hW, Subgroup.orderOf_coe]
      exact hw3
    have := commute_of_mk_commute_of_coprime' hc hord
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) this
  have k1 := key Z z hZ h1 hz3
  have k2 := key (cycThree * Z * cycThree⁻¹) (cM * z * cM⁻¹)
    (by rw [map_mul, map_mul, map_inv, hZ, ← hcM]; rfl) h2 (by rw [orderOf_conj_eq]; exact hz3)
  have k3 := key (cycThree⁻¹ * Z * cycThree) (cM⁻¹ * z * cM)
    (by rw [map_mul, map_mul, map_inv, hZ, ← hcM]; rfl) h3 (by
      rw [show cM⁻¹ * z * cM = cM⁻¹ * z * cM⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq]; exact hz3)
  rw [Units.val_mul, Units.val_mul, hZd, cyc_mul_diagonal_mul_inv'] at k2
  rw [Units.val_mul, Units.val_mul, hZd, cyc_inv_mul_diagonal_mul'] at k3
  rw [hZd] at k1
  have hcyc : ∀ t : Fin 3, (G : Matrix (Fin 3) (Fin 3) K) * diagonal (cycDiag' a b c t) =
      diagonal (cycDiag' a b c t) * G := by
    intro t
    fin_cases t
    · exact k1.symm
    · exact k2.symm
    · exact k3.symm
  have habc : ¬ (a = b ∧ b = c) := by
    rintro ⟨hab, hbc⟩
    apply hz1
    apply Subtype.ext
    rw [← hZ, OneMemClass.coe_one]
    have hZs : (Z : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hZd, hab, hbc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h0 := mk_eq_of_coe_eq_smul (M := Z) (N := 1) (a := c) (by rw [hZs, Units.val_one])
    rw [h0, map_one]
  refine mem_torusM_of_offDiag hK hp2 hG fun i j hij => ?_
  obtain ⟨t, ht⟩ := exists_cycDiag'_ne habc hij
  exact entry_eq_zero_of_commute_diagonal (hcyc t) ht

theorem le_torusM_of_le_normalizer
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {U : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hU3 : ¬ 3 ∣ Nat.card U)
    (hUN : U ≤ Subgroup.normalizer ((torusM hK hp2 : Subgroup _) : Set _))
    (hcU : cM ∈ Subgroup.normalizer (U : Set (projImage (slPi π 3 (p ^ f) K)))) :
    U ≤ torusM hK hp2 := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set t₁ := tM hK hp2 _ isTInv_tOne with ht₁
  set t₂ := tM hK hp2 _ isTInv_tTwo with ht₂
  set t₃ := tM hK hp2 _ isTInv_tThree with ht₃
  have h12 : t₁ * t₂ = t₃ := tM_one_mul_tM_two hK hp2
  obtain ⟨hc1, hc2, hc3⟩ := cM_conj_tM hK hp2 hcM
  have hsq : ∀ (t : GL (Fin 3) K) (ht : IsTInv t), tM hK hp2 t ht * tM hK hp2 t ht = 1 :=
    fun t ht => by rw [← sq]; exact tM_sq hK hp2 ht
  have hc12 : t₁ * t₂ = t₂ * t₁ :=
    torusM_comm hK hp2 (tM_mem_torusM hK hp2 isTInv_tOne) (tM_mem_torusM hK hp2 isTInv_tTwo)
  have hne : t₁ ≠ t₂ := by
    intro h
    apply tM_ne_one hK hp2 isTInv_tThree
    rw [← ht₃, ← h12, h, hsq]
  have key := commute_of_perm_three (hsq _ isTInv_tOne) (hsq _ isTInv_tTwo) hc12 h12
    (tM_ne_one hK hp2 isTInv_tOne) (tM_ne_one hK hp2 isTInv_tTwo) hne hc1 hc2 hc3 hcU
    (fun u hu h3 => hU3 (h3.trans (by
      have := orderOf_dvd_natCard (⟨u, hu⟩ : U)
      rwa [Subgroup.orderOf_mk] at this)))
    (fun u hu t ht => by
      have htT : t ∈ torusM hK hp2 := by
        rcases ht with rfl | rfl | rfl
        · exact tM_mem_torusM hK hp2 isTInv_tOne
        · exact tM_mem_torusM hK hp2 isTInv_tTwo
        · exact tM_mem_torusM hK hp2 isTInv_tThree
      have ht2 : t * t = 1 := by
        rcases ht with rfl | rfl | rfl
        · exact hsq _ isTInv_tOne
        · exact hsq _ isTInv_tTwo
        · exact hsq _ isTInv_tThree
      have ht1 : t ≠ 1 := by
        rcases ht with rfl | rfl | rfl
        · exact tM_ne_one hK hp2 isTInv_tOne
        · exact tM_ne_one hK hp2 isTInv_tTwo
        · exact tM_ne_one hK hp2 isTInv_tThree
      have hcT : u * t * u⁻¹ ∈ torusM hK hp2 :=
        (Subgroup.mem_normalizer_iff.mp (hUN hu) t).mp htT
      obtain ⟨A, -, hA⟩ := exists_lift (u * t * u⁻¹)
      refine isTM_of_offDiag hK hp2 ?_ ?_ hA (offDiag_of_mem_torusM hK hp2 hcT hA)
      · rw [sq, show u * t * u⁻¹ * (u * t * u⁻¹) = u * (t * t) * u⁻¹ by group, ht2]
        group
      · intro h
        apply ht1
        calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
          _ = 1 := by rw [h]; group)
  intro u hu
  obtain ⟨e1, e2⟩ := key u hu
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr e1,
    Subgroup.mem_centralizer_singleton_iff.mpr e2⟩

include hτ1 in
theorem torusM_facts
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {R : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hR3 : ∀ x ∈ R, Nat.Coprime 3 (orderOf x))
    (hcR : cM ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    {z : projImage (slPi π 3 (p ^ f) K)} (hzR : z ∈ R)
    (hzC : z ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    (hzd : z * dM = dM * z) (hz1 : z ≠ 1) :
    Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) = torusM hK hp2 ∧
      ∀ U : Subgroup (projImage (slPi π 3 (p ^ f) K)),
        U ≤ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) →
        ¬ 3 ∣ Nat.card U → cM ∈ Subgroup.normalizer (U : Set (projImage (slPi π 3 (p ^ f) K))) →
          U ≤ torusM hK hp2 := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hzT : z ∈ torusM hK hp2 := mem_torusM_of_comm_coprime hK hp2 hτ hτ1 hdM hzd (hR3 z hzR)
  have hz3 := hR3 z hzR
  have hcR' : cM⁻¹ ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := inv_mem hcR
  have hz'R : cM * z * cM⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcR z).mp hzR
  have hz''R : cM⁻¹ * z * cM ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp hcR' z).mp hzR
    rwa [inv_inv] at this
  have hz'C : cM * z * cM⁻¹ ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) :=
    mem_centralizer_conj' hcR hzC
  have hz''C : cM⁻¹ * z * cM ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := by
    have := mem_centralizer_conj' hcR' hzC
    rwa [inv_inv] at this
  have hCT : Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) ≤ torusM hK hp2 := by
    intro g hg
    have hg' := Subgroup.mem_centralizer_iff.mp hg
    exact mem_torusM_of_comm_cyc hK hp2 hcM hzT hz1 hz3 (hg' z hzR) (hg' _ hz'R) (hg' _ hz''R)
  have hRT : R ≤ torusM hK hp2 := by
    intro r hr
    have e1 := Subgroup.mem_centralizer_iff.mp hzC r hr
    have e2 := Subgroup.mem_centralizer_iff.mp hz'C r hr
    have e3 := Subgroup.mem_centralizer_iff.mp hz''C r hr
    exact mem_torusM_of_comm_cyc hK hp2 hcM hzT hz1 hz3 e1.symm e2.symm e3.symm
  have hCeq : Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) = torusM hK hp2 := by
    refine le_antisymm hCT fun t ht => Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
    exact torusM_comm hK hp2 (hRT hr) ht
  refine ⟨hCeq, fun U hUR hU3 hcU => le_torusM_of_le_normalizer hK hp2 hcM hU3 ?_ hcU⟩
  rw [← hCeq]
  exact hUR.trans (normalizer_le_normalizer_centralizer' R)

include hK hp2 hτ1 in
theorem thetaC_comm (hq : ModThree π (p ^ f))
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hd1 : dM ≠ 1) {b : projImage (slPi π 3 (p ^ f) K)}
    (hbE : b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM) (hb1 : b ≠ 1) :
    ∀ x ∈ thetaC b, ∀ y ∈ thetaC b, x * y = y * x := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hdE : dM ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  set e : (⊤ : Subgroup (projImage (slPi π 3 (p ^ f) K))) ≃* projImage (slPi π 3 (p ^ f) K) :=
    Subgroup.topEquiv with he
  have htr := transitive_of_normal_form hK hq e hτ hτ1 (one_mem (glPi π 3 (p ^ f) K))
    (Subgroup.mem_top dM) (Subgroup.mem_top cM) (by rw [he, Subgroup.topEquiv_apply, hdM]; simp)
    (by rw [he, Subgroup.topEquiv_apply, hcM]; simp)
  obtain ⟨n, -, hnb⟩ := htr b hbE hb1 dM hdE hd1
  intro x hx y hy
  have hx' := (mem_thetaC_iff_conj hnb x).mp hx
  have hy' := (mem_thetaC_iff_conj hnb y).mp hy
  have h := torusM_comm hK hp2 (thetaC_le_torusM hK hp2 hτ hτ1 hdM hx')
    (thetaC_le_torusM hK hp2 hτ hτ1 hdM hy')
  have h' : n * (x * y) * n⁻¹ = n * (y * x) * n⁻¹ := by
    calc n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
      _ = n * y * n⁻¹ * (n * x * n⁻¹) := h
      _ = n * (y * x) * n⁻¹ := by group
  simpa using h'

include hK hp2 hτ1 in
theorem exists_thetaC_of_pGroup (hq : ModThree π (p ^ f))
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hdc : dM * cM = cM * dM) (hdo : orderOf dM = 3) (hco : orderOf cM = 3)
    (hcd : cM ∉ Subgroup.zpowers dM) {r : ℕ} [Fact r.Prime] (hr3 : r ≠ 3)
    {R : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hRr : IsPGroup r R) (hR1 : R ≠ ⊥)
    (hER : Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
      Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K)))) :
    ∃ b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM, b ≠ 1 ∧
      (∀ x ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))),
        Nat.Coprime 3 (orderOf x) → x ∈ thetaC b) ∧
      ∀ U : Subgroup (projImage (slPi π 3 (p ^ f) K)),
        U ≤ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) →
        ¬ 3 ∣ Nat.card U →
        Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
          Subgroup.normalizer (U : Set (projImage (slPi π 3 (p ^ f) K))) →
          U ≤ thetaC b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hdE : dM ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  have hcE : cM ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)
  have hd1 : dM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdo
    omega
  have hRnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  have hZnt := hRr.center_nontrivial
  obtain ⟨⟨z₀, hz₀c⟩, hz₀1⟩ := exists_ne (1 : Subgroup.center R)
  set Z := R ⊓ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) with hZ
  have hz₀Z : (z₀ : projImage (slPi π 3 (p ^ f) K)) ∈ Z := by
    refine ⟨z₀.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.mp hz₀c ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hZ1 : Z ≠ ⊥ := by
    intro hZ0
    rw [hZ0, Subgroup.mem_bot] at hz₀Z
    exact hz₀1 (Subtype.ext (Subtype.ext hz₀Z))
  have hEZ : E ≤ Subgroup.normalizer (Z : Set (projImage (slPi π 3 (p ^ f) K))) :=
    le_normalizer_inf' hER (hER.trans (normalizer_le_normalizer_centralizer' R))
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  have hd3 : dM ^ 3 = 1 := by simpa [hdo] using pow_orderOf_eq_one dM
  have hc3 : cM ^ 3 = 1 := by simpa [hco] using pow_orderOf_eq_one cM
  have hEab : CFSG.Open.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup hdc x.2
      obtain ⟨k, l, hkl⟩ := exists_zpow_mul_of_mem_sup hdc y.2
      change (x : projImage (slPi π 3 (p ^ f) K)) * y = y * x
      rw [hij, hkl]
      have hc := fun a b : ℤ => (Commute.zpow_zpow hdc a b).eq
      calc dM ^ i * cM ^ j * (dM ^ k * cM ^ l) = dM ^ i * (cM ^ j * dM ^ k) * cM ^ l := by group
        _ = dM ^ i * (dM ^ k * cM ^ j) * cM ^ l := by rw [← hc k j]
        _ = dM ^ k * dM ^ i * (cM ^ j * cM ^ l) := by group
        _ = dM ^ k * dM ^ i * (cM ^ l * cM ^ j) := by group
        _ = dM ^ k * (dM ^ i * cM ^ l) * cM ^ j := by group
        _ = dM ^ k * (cM ^ l * dM ^ i) * cM ^ j := by rw [hc i l]
        _ = dM ^ k * cM ^ l * (dM ^ i * cM ^ j) := by group
    · obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hdc hx
      rw [(Commute.zpow_zpow hdc i j).mul_pow, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, mul_comm (j : ℤ),
        _root_.zpow_mul]
      simp [hd3, hc3]
  have hR3 : ∀ x ∈ R, Nat.Coprime 3 (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hRr ⟨x, hx⟩
    have h1 : orderOf x ∣ r ^ k := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right _
      ((Nat.coprime_primes Nat.prime_three Fact.out).mpr (Ne.symm hr3)))
  have hZ2 : IsPGroup r Z := hRr.to_le inf_le_left
  have hcop : Nat.Coprime 3 (Nat.card Z) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three Fact.out).mpr (Ne.symm hr3))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three E Z hEab (by rw [hE9]; norm_num) hEZ hcop
  obtain ⟨U₀, hU₀, hZU₀⟩ : ∃ U₀ ∈ CFSG.Open.signalizerFunctorEk 3 1 E,
      Z ⊓ Subgroup.centralizer (U₀ : Set (projImage (slPi π 3 (p ^ f) K))) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hZ1
    rw [← hgen]
    exact iSup₂_eq_bot.mpr hcon
  obtain ⟨hU₀E, hU₀3⟩ := hU₀
  have hU₀nt : Nontrivial U₀ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU₀3]; norm_num)
  obtain ⟨⟨b, hbU⟩, hb1⟩ := exists_ne (1 : U₀)
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨⟨z, hzZ, hzU⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZU₀
  have hzb : (z : projImage (slPi π 3 (p ^ f) K)) * b = b * z :=
    (Subgroup.mem_centralizer_iff.mp hzU b hbU).symm
  have hz1' : (z : projImage (slPi π 3 (p ^ f) K)) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hbE : b ∈ E := hU₀E hbU
  set e : (⊤ : Subgroup (projImage (slPi π 3 (p ^ f) K))) ≃* projImage (slPi π 3 (p ^ f) K) :=
    Subgroup.topEquiv with he
  have htr := transitive_of_normal_form hK hq e hτ hτ1 (one_mem (glPi π 3 (p ^ f) K))
    (Subgroup.mem_top dM) (Subgroup.mem_top cM) (by rw [he, Subgroup.topEquiv_apply, hdM]; simp)
    (by rw [he, Subgroup.topEquiv_apply, hcM]; simp)
  obtain ⟨n, ⟨-, hnE⟩, hnb⟩ := htr b hbE hb1' dM hdE hd1
  have hnE' : n⁻¹ ∈ Subgroup.normalizer (E : Set (projImage (slPi π 3 (p ^ f) K))) := inv_mem hnE
  have hcE' : n⁻¹ * cM * n⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hnE' cM).mp hcE
  set R' := R.map (MulAut.conj n).toMonoidHom with hR'
  have hmemR' : ∀ x, x ∈ R' ↔ n⁻¹ * x * n ∈ R := by
    intro x
    rw [hR', Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hR'3 : ∀ x ∈ R', Nat.Coprime 3 (orderOf x) := by
    intro x hx
    have h1 := hR3 _ ((hmemR' x).mp hx)
    rwa [show n⁻¹ * x * n = n⁻¹ * x * n⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq] at h1
  have hcR' : cM ∈ Subgroup.normalizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    simp only [SetLike.mem_coe] at hx ⊢
    rw [hmemR'] at hx ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (hER hcE') _).mp hx
    have e1 : n⁻¹ * cM * n⁻¹⁻¹ * (n⁻¹ * x * n) * (n⁻¹ * cM * n⁻¹⁻¹)⁻¹ =
        n⁻¹ * (cM * x * cM⁻¹) * n := by group
    rwa [e1] at h1
  have hz'R : n * z * n⁻¹ ∈ R' := by
    rw [hmemR']
    simpa [mul_assoc] using hzZ.1
  have hz'C : n * z * n⁻¹ ∈
      Subgroup.centralizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := (hmemR' x).mp hx
    have hzr := Subgroup.mem_centralizer_iff.mp hzZ.2 _ hx'
    calc x * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [hzr]
      _ = n * z * n⁻¹ * x := by group
  have hz'd : n * z * n⁻¹ * dM = dM * (n * z * n⁻¹) := by
    rw [← hnb]
    calc n * z * n⁻¹ * (n * b * n⁻¹) = n * (z * b) * n⁻¹ := by group
      _ = n * (b * z) * n⁻¹ := by rw [hzb]
      _ = n * b * n⁻¹ * (n * z * n⁻¹) := by group
  have hz'1 : n * z * n⁻¹ ≠ 1 := by
    intro h
    apply hz1'
    calc (z : projImage (slPi π 3 (p ^ f) K)) = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  obtain ⟨hCR', hNR'⟩ := torusM_facts hK hp2 hτ hτ1 hdM hcM hR'3 hcR' hz'R hz'C hz'd hz'1
  refine ⟨b, hbE, hb1', fun x hx hx3 => ?_, fun U hUR hU3 hEU => ?_⟩
  ·
    rw [mem_thetaC_iff_conj hnb]
    have hxC : n * x * n⁻¹ ∈
        Subgroup.centralizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' := (hmemR' y).mp hy
      have hxy := Subgroup.mem_centralizer_iff.mp hx _ hy'
      calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [hxy]
        _ = n * x * n⁻¹ * y := by group
    rw [hCR'] at hxC
    exact torus3M_le_thetaC hK hp2 hτ hτ1 hdM ⟨hxC, by rw [orderOf_conj_eq]; exact hx3⟩
  ·
    set U' := U.map (MulAut.conj n).toMonoidHom with hU'
    have hmemU' : ∀ x, x ∈ U' ↔ n⁻¹ * x * n ∈ U := by
      intro x
      rw [hU', Subgroup.mem_map_equiv]
      simp [MulAut.conj_symm_apply]
    have hU'3 : ¬ 3 ∣ Nat.card U' := by
      rw [hU', Subgroup.card_map_of_injective (MulAut.conj n).injective]
      exact hU3
    have hU'R : U' ≤ Subgroup.normalizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
      intro u hu
      have hu' := hUR ((hmemU' u).mp hu)
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      simp only [SetLike.mem_coe] at hx ⊢
      rw [hmemR'] at hx ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp hu' _).mp hx
      have e1 : n⁻¹ * u * n * (n⁻¹ * x * n) * (n⁻¹ * u * n)⁻¹ = n⁻¹ * (u * x * u⁻¹) * n := by
        group
      rwa [e1] at h1
    have hcU' : cM ∈ Subgroup.normalizer (U' : Set (projImage (slPi π 3 (p ^ f) K))) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      simp only [SetLike.mem_coe] at hx ⊢
      rw [hmemU'] at hx ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hEU hcE') _).mp hx
      have e1 : n⁻¹ * cM * n⁻¹⁻¹ * (n⁻¹ * x * n) * (n⁻¹ * cM * n⁻¹⁻¹)⁻¹ =
          n⁻¹ * (cM * x * cM⁻¹) * n := by group
      rwa [e1] at h1
    have hU'T := hNR' U' hU'R hU'3 hcU'
    intro u hu
    rw [mem_thetaC_iff_conj hnb]
    have hu' : n * u * n⁻¹ ∈ U' := by
      rw [hmemU']
      simpa [mul_assoc] using hu
    exact torus3M_le_thetaC hK hp2 hτ hτ1 hdM ⟨hU'T hu', coprime_orderOf_of_mem hU'3 hu'⟩

include hK hp2 hτ1 in
theorem le_thetaC_model (hq : ModThree π (p ^ f))
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hdc : dM * cM = cM * dM) (hdo : orderOf dM = 3) (hco : orderOf cM = 3)
    (hcd : cM ∉ Subgroup.zpowers dM) {Y : Subgroup (projImage (slPi π 3 (p ^ f) K))}
    (hY3 : ¬ 3 ∣ Nat.card Y)
    (hEY : Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
      Subgroup.normalizer (Y : Set (projImage (slPi π 3 (p ^ f) K)))) :
    ∃ b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM, b ≠ 1 ∧ Y ≤ thetaC b := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hd1 : dM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdo
    omega
  have hdE : dM ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  have hE9 : Nat.card (Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :
      Subgroup (projImage (slPi π 3 (p ^ f) K))) = 9 := by
    rw [Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  have hE3 : IsPGroup 3 (Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :
      Subgroup (projImage (slPi π 3 (p ^ f) K))) :=
    IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  exact exists_le_of_family hE3 thetaC ⟨dM, hdE, hd1⟩
    (fun b hbE hb1 => thetaC_comm hK hp2 hτ hτ1 hq hdM hcM hd1 hbE hb1)
    (fun r _ hr3 R hRr hR1 hER =>
      exists_thetaC_of_pGroup hK hp2 hτ hτ1 hq hdM hcM hdc hdo hco hcd hr3 hRr hR1 hER) Y hY3 hEY

end CFSG.RankThree.PartTwo.Sec14.Res8Hess
