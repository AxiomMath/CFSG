module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListMat
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.SeitzGeneration (heisC)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open Res8Hess (thetaC)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem coe_cycThree_eq_heisC :
    ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisC 1 := by
  rw [coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisC]

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
variable {dM cM : projImage (slPi π 3 (p ^ f) K)}

include hτ1 in
theorem comm_of_comm_dM
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    {x y : projImage (slPi π 3 (p ^ f) K)} (hx : x * dM = dM * x) (hx3 : Nat.Coprime 3 (orderOf x))
    (hy : y * dM = dM * y) (hy3 : Nat.Coprime 3 (orderOf y)) : x * y = y * x := by
  have key : ∀ w : projImage (slPi π 3 (p ^ f) K), w * dM = dM * w →
      Nat.Coprime 3 (orderOf w) → ∃ W : GL (Fin 3) K,
        ProjGenLinGroup.mk W = (w : ProjGenLinGroup (Fin 3) K) ∧
          ∀ i j : Fin 3, i ≠ j → (W : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro w hw hw3
    obtain ⟨W, hW⟩ := ProjGenLinGroup.mk_surjective (w : ProjGenLinGroup (Fin 3) K)
    refine ⟨W, hW, offDiag_of_comm_d hτ hτ1 ?_ ?_⟩
    · rw [hW, ← hdM]
      exact congrArg Subtype.val hw
    · rw [hW, Subgroup.orderOf_coe]
      exact hw3
  obtain ⟨X, hX, hXo⟩ := key x hx hx3
  obtain ⟨Y, hY, hYo⟩ := key y hy hy3
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hX, ← hY]
  exact mk_comm_of_offDiag hXo hYo

@[expose] noncomputable def torusD (hτ1 : τ ≠ 1)
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ)) :
    Subgroup (projImage (slPi π 3 (p ^ f) K)) where
  carrier := {x | x * dM = dM * x ∧ Nat.Coprime 3 (orderOf x)}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · calc x * y * dM = x * (dM * y) := by rw [mul_assoc, hy.1]
        _ = dM * (x * y) := by rw [← mul_assoc, hx.1, mul_assoc]
    · have hc : Commute x y := comm_of_comm_dM hτ hτ1 hdM hx.1 hx.2 hy.1 hy.2
      exact Nat.Coprime.coprime_dvd_right (hc.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
        (Nat.Coprime.mul_right hx.2 hy.2)
  one_mem' := ⟨by rw [one_mul, mul_one], by rw [orderOf_one]; exact Nat.coprime_one_right 3⟩
  inv_mem' {x} hx := by
    refine ⟨?_, by rw [orderOf_inv]; exact hx.2⟩
    calc x⁻¹ * dM = x⁻¹ * (dM * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * dM) * x⁻¹ := by rw [hx.1]
      _ = dM * x⁻¹ := by group

include hτ1 in
theorem torusD_eq_thetaC [Finite K]
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ)) :
    torusD hτ hτ1 hdM = thetaC dM := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  refine le_antisymm ?_ fun x hx => ?_
  · have hVC : torusD hτ hτ1 hdM ≤ Subgroup.centralizer ({dM} : Set _) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr hx.1
    refine Res8Hess.le_theta_of_normal hVC (fun g hg v hv => ?_) ?_ ?_
    · have hgd : g * dM = dM * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hvd := hv.1
      refine ⟨?_, by rw [Res8Hess.orderOf_conj_eq]; exact hv.2⟩
      have hginv : g⁻¹ * dM = dM * g⁻¹ := by
        calc g⁻¹ * dM = g⁻¹ * (dM * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * dM) * g⁻¹ := by rw [hgd]
          _ = dM * g⁻¹ := by group
      calc g * v * g⁻¹ * dM = g * v * (g⁻¹ * dM) := by group
        _ = g * (v * dM) * g⁻¹ := by rw [hginv]; group
        _ = g * (dM * v) * g⁻¹ := by rw [hvd]
        _ = (g * dM) * v * g⁻¹ := by group
        _ = dM * (g * v * g⁻¹) := by rw [hgd]; group
    · have : IsMulCommutative (torusD hτ hτ1 hdM) :=
        ⟨⟨fun x y => Subtype.ext (comm_of_comm_dM hτ hτ1 hdM x.2.1 x.2.2 y.2.1 y.2.2)⟩⟩
      infer_instance
    · refine not_three_dvd_card_of_pow_three fun v hv hv3 => ?_
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hv.2
        (orderOf_dvd_of_pow_eq_one hv3) (dvd_refl _))
  · exact ⟨Subgroup.mem_centralizer_singleton_iff.mp (Res8Hess.inSubgroup_theta_le _ hx),
      Res8Hess.coprime_orderOf_of_mem (Res8Hess.not_dvd_card_inSubgroup_theta _) hx⟩

include hτ1 in
theorem hess_thetaC_comm (hK : PiField π p f K) (hq : ModThree π (p ^ f))
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
  have hx' := (Res8Hess.mem_thetaC_iff_conj hnb x).mp hx
  have hy' := (Res8Hess.mem_thetaC_iff_conj hnb y).mp hy
  rw [← torusD_eq_thetaC hτ hτ1 hdM] at hx' hy'
  have h := comm_of_comm_dM hτ hτ1 hdM hx'.1 hx'.2 hy'.1 hy'.2
  have h' : n * (x * y) * n⁻¹ = n * (y * x) * n⁻¹ := by
    calc n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
      _ = n * y * n⁻¹ * (n * x * n⁻¹) := h
      _ = n * (y * x) * n⁻¹ := by group
  simpa using h'

include hτ1 in
theorem torus_facts_d
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {R : Subgroup (projImage (slPi π 3 (p ^ f) K))} (hR3 : ∀ x ∈ R, Nat.Coprime 3 (orderOf x))
    (hcR : cM ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    {z : projImage (slPi π 3 (p ^ f) K)} (hzR : z ∈ R)
    (hzC : z ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    (hzd : z * dM = dM * z) (hz1 : z ≠ 1) :
    (∀ x ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))), x * dM = dM * x) ∧
      (∀ x ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))),
        ∀ y ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))), x * y = y * x) ∧
      dM ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := by
  set C := Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) with hC
  have hcR' : cM⁻¹ ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := inv_mem hcR
  have hz'R : cM * z * cM⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcR z).mp hzR
  have hz''R : cM⁻¹ * z * cM ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp hcR' z).mp hzR
    rwa [inv_inv] at this
  have hz'C : cM * z * cM⁻¹ ∈ C := Res8Hess.mem_centralizer_conj' hcR hzC
  have hz''C : cM⁻¹ * z * cM ∈ C := by
    have := Res8Hess.mem_centralizer_conj' hcR' hzC
    rwa [inv_inv] at this
  have hdiag : ∀ g : projImage (slPi π 3 (p ^ f) K), z * g = g * z →
      cM * z * cM⁻¹ * g = g * (cM * z * cM⁻¹) → cM⁻¹ * z * cM * g = g * (cM⁻¹ * z * cM) →
      ∃ G : GL (Fin 3) K, ProjGenLinGroup.mk G = (g : ProjGenLinGroup (Fin 3) K) ∧
        ∀ i j : Fin 3, i ≠ j → (G : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro g h1 h2 h3
    obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective (g : ProjGenLinGroup (Fin 3) K)
    refine ⟨G, hG, offDiag_of_comm_conj hτ hτ1 (coe_cycThree_eq_heisC (K := K))
      (z := (z : ProjGenLinGroup (Fin 3) K)) ?_ ?_ ?_ ?_ ?_ ?_⟩
    · rw [← hdM]
      exact congrArg Subtype.val hzd
    · exact fun h => hz1 (Subtype.ext h)
    · rw [Subgroup.orderOf_coe]
      exact hR3 z hzR
    · rw [hG]
      exact congrArg Subtype.val h1
    · rw [hG, ← hcM]
      exact congrArg Subtype.val h2
    · rw [hG, ← hcM]
      exact congrArg Subtype.val h3
  have hdd : ∀ g : projImage (slPi π 3 (p ^ f) K), (∃ G : GL (Fin 3) K,
      ProjGenLinGroup.mk G = (g : ProjGenLinGroup (Fin 3) K) ∧
        ∀ i j : Fin 3, i ≠ j → (G : Matrix (Fin 3) (Fin 3) K) i j = 0) → g * dM = dM * g := by
    rintro g ⟨G, hG, hGo⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hG, hdM]
    exact mk_comm_of_offDiag hGo (offDiag_diagTau hτ)
  have hcent : ∀ x ∈ C, ∃ G : GL (Fin 3) K,
      ProjGenLinGroup.mk G = (x : ProjGenLinGroup (Fin 3) K) ∧
        ∀ i j : Fin 3, i ≠ j → (G : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro x hx
    have hx' := Subgroup.mem_centralizer_iff.mp hx
    exact hdiag x (hx' z hzR) (hx' _ hz'R) (hx' _ hz''R)
  refine ⟨fun x hx => hdd x (hcent x hx), fun x hx y hy => ?_,
    Subgroup.mem_centralizer_iff.mpr fun r hr => hdd r ?_⟩
  · obtain ⟨X, hX, hXo⟩ := hcent x hx
    obtain ⟨Y, hY, hYo⟩ := hcent y hy
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hX, ← hY]
    exact mk_comm_of_offDiag hXo hYo
  · exact hdiag r (Subgroup.mem_centralizer_iff.mp hzC r hr).symm
      (Subgroup.mem_centralizer_iff.mp hz'C r hr).symm
      (Subgroup.mem_centralizer_iff.mp hz''C r hr).symm

include hτ1 in
theorem le_torusD_of_normalizer [Finite K]
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hd3 : dM ^ 3 = 1) {R : Subgroup (projImage (slPi π 3 (p ^ f) K))}
    (hCab : ∀ x ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))),
      ∀ y ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))), x * y = y * x)
    (hdC : dM ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    {U : Subgroup (projImage (slPi π 3 (p ^ f) K))}
    (hUR : U ≤ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))))
    (hU3 : ¬ 3 ∣ Nat.card U)
    (hdU : dM ∈ Subgroup.normalizer (U : Set (projImage (slPi π 3 (p ^ f) K)))) :
    U ≤ torusD hτ hτ1 hdM := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  intro u hu
  have hu3 : Nat.Coprime 3 (orderOf u) := Res8Hess.coprime_orderOf_of_mem hU3 hu
  have hdu : dM * u * dM⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hdU u).mp hu
  set c := u⁻¹ * (dM * u * dM⁻¹) with hc
  have hcU : c ∈ U := mul_mem (inv_mem hu) hdu
  have huN : u⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) : Subgroup _) :
        Set (projImage (slPi π 3 (p ^ f) K))) :=
    Res8Hess.normalizer_le_normalizer_centralizer' R (inv_mem (hUR hu))
  have hcC : c ∈ Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := by
    have h1 : u⁻¹ * dM * u⁻¹⁻¹ ∈
        Subgroup.centralizer (R : Set (projImage (slPi π 3 (p ^ f) K))) :=
      (Subgroup.mem_normalizer_iff.mp huN dM).mp hdC
    have e : c = u⁻¹ * dM * u⁻¹⁻¹ * dM⁻¹ := by rw [hc]; group
    rw [e]
    exact mul_mem h1 (inv_mem hdC)
  have hcd : c * dM = dM * c := hCab c hcC dM hdC
  have hpow : ∀ n : ℕ, dM ^ n * u * (dM ^ n)⁻¹ = u * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hdc : dM * c ^ n * dM⁻¹ = c ^ n := by
        rw [(Commute.pow_left hcd n).eq.symm, mul_inv_cancel_right]
      calc dM ^ (n + 1) * u * (dM ^ (n + 1))⁻¹ = dM * (dM ^ n * u * (dM ^ n)⁻¹) * dM⁻¹ := by
            rw [pow_succ']; group
        _ = dM * (u * c ^ n) * dM⁻¹ := by rw [ih]
        _ = (dM * u * dM⁻¹) * (dM * c ^ n * dM⁻¹) := by group
        _ = u * c * c ^ n := by rw [hdc, hc, mul_inv_cancel_left]
        _ = u * c ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hc3 : c ^ 3 = 1 := by
    have h := hpow 3
    rw [hd3, one_mul, inv_one, mul_one] at h
    have := congrArg (fun x => u⁻¹ * x) h
    simpa using this.symm
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have h2 : Nat.Coprime 3 (orderOf c) := Res8Hess.coprime_orderOf_of_mem hU3 hcU
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h2 h1 (dvd_refl _))
  refine ⟨?_, hu3⟩
  have e : dM * u * dM⁻¹ = u := by
    have := hc1
    rw [hc] at this
    calc dM * u * dM⁻¹ = u * (u⁻¹ * (dM * u * dM⁻¹)) := by group
      _ = u := by rw [this, mul_one]
  calc u * dM = dM * u * dM⁻¹ * dM := by rw [e]
    _ = dM * u := by group

include hτ1 in
theorem exists_thetaC_of_pGroup' (hK : PiField π p f K) (hq : ModThree π (p ^ f))
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
  have hd3 : dM ^ 3 = 1 := by simpa [hdo] using pow_orderOf_eq_one dM
  have hc3 : cM ^ 3 = 1 := by simpa [hco] using pow_orderOf_eq_one cM
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
    Res8Hess.le_normalizer_inf' hER (hER.trans (Res8Hess.normalizer_le_normalizer_centralizer' R))
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
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
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three Fact.out).mpr
      (Ne.symm hr3))
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
  have hdE' : n⁻¹ * dM * n⁻¹⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hnE' dM).mp hdE
  set R' := R.map (MulAut.conj n).toMonoidHom with hR'
  have hmemR' : ∀ x, x ∈ R' ↔ n⁻¹ * x * n ∈ R := by
    intro x
    rw [hR', Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hR'3 : ∀ x ∈ R', Nat.Coprime 3 (orderOf x) := by
    intro x hx
    have h1 := hR3 _ ((hmemR' x).mp hx)
    rwa [show n⁻¹ * x * n = n⁻¹ * x * n⁻¹⁻¹ by rw [inv_inv], Res8Hess.orderOf_conj_eq] at h1
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
  obtain ⟨hCd, hCab, hdC⟩ := torus_facts_d hτ hτ1 hdM hcM hR'3 hcR' hz'R hz'C hz'd hz'1
  refine ⟨b, hbE, hb1', fun x hx hx3 => ?_, fun U hUR hU3 hEU => ?_⟩
  ·
    rw [Res8Hess.mem_thetaC_iff_conj hnb, ← torusD_eq_thetaC hτ hτ1 hdM]
    have hxC : n * x * n⁻¹ ∈
        Subgroup.centralizer (R' : Set (projImage (slPi π 3 (p ^ f) K))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' := (hmemR' y).mp hy
      have hxy := Subgroup.mem_centralizer_iff.mp hx _ hy'
      calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by rw [hxy]
        _ = n * x * n⁻¹ * y := by group
    exact ⟨hCd _ hxC, by rw [Res8Hess.orderOf_conj_eq]; exact hx3⟩
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
    have hdU' : dM ∈ Subgroup.normalizer (U' : Set (projImage (slPi π 3 (p ^ f) K))) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      simp only [SetLike.mem_coe] at hx ⊢
      rw [hmemU'] at hx ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hEU hdE') _).mp hx
      have e1 : n⁻¹ * dM * n⁻¹⁻¹ * (n⁻¹ * x * n) * (n⁻¹ * dM * n⁻¹⁻¹)⁻¹ =
          n⁻¹ * (dM * x * dM⁻¹) * n := by group
      rwa [e1] at h1
    have hU'T := le_torusD_of_normalizer hτ hτ1 hdM hd3 hCab hdC hU'R hU'3 hdU'
    intro u hu
    rw [Res8Hess.mem_thetaC_iff_conj hnb, ← torusD_eq_thetaC hτ hτ1 hdM]
    have hu' : n * u * n⁻¹ ∈ U' := by
      rw [hmemU']
      simpa [mul_assoc] using hu
    exact hU'T hu'

include hτ1 in
theorem hess_le_thetaC (hK : PiField π p f K) (hq : ModThree π (p ^ f))
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
  exact Res8Hess.exists_le_of_family hE3 thetaC ⟨dM, hdE, hd1⟩
    (fun b hbE hb1 => hess_thetaC_comm hτ hτ1 hK hq hdM hcM hd1 hbE hb1)
    (fun r _ hr3 R hRr hR1 hER =>
      exists_thetaC_of_pGroup' hτ hτ1 hK hq hdM hcM hdc hdo hco hcd hr3 hRr hR1 hER) Y hY3 hEY

include hτ1 in
theorem hess_centralizer_isPGroup [Finite K]
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    IsPGroup 3 (Subgroup.centralizer
      ((Subgroup.zpowers dM ⊔ Subgroup.zpowers cM : Subgroup (projImage (slPi π 3 (p ^ f) K))) :
        Set (projImage (slPi π 3 (p ^ f) K)))) := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  rintro ⟨g, hg⟩
  have hgd : g * dM = dM * g :=
    (Subgroup.mem_centralizer_iff.mp hg dM (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM))).symm
  have hgc : g * cM = cM * g :=
    (Subgroup.mem_centralizer_iff.mp hg cM (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM))).symm
  obtain ⟨k, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  set g' := g ^ (3 ^ k) with hg'
  have hord : Nat.Coprime 3 (orderOf g') := by
    have hdvd : orderOf g' ∣ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [hg', ← pow_mul, ← hnm, pow_orderOf_eq_one]
    exact Nat.Coprime.coprime_dvd_right hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  have hg'd : g' * dM = dM * g' := (Commute.pow_left hgd _).eq
  have hg'c : g' * cM = cM * g' := (Commute.pow_left hgc _).eq
  have h1 := eq_one_of_comm_d_c hτ hτ1 (coe_cycThree_eq_heisC (K := K))
    (x := (g' : ProjGenLinGroup (Fin 3) K))
    (by rw [← hdM]; exact congrArg Subtype.val hg'd)
    (by rw [← hcM]; exact congrArg Subtype.val hg'c)
    (by rw [Subgroup.orderOf_coe]; exact hord)
  exact Subtype.ext h1

end CFSG.RankThree.PartTwo.Sec14.L3PGL
