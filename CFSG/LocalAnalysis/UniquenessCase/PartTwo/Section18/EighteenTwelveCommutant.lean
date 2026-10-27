module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open Multiplicative
open scoped Matrix

theorem k_18_12_commutant_holds :
    ∀ {W : Type} [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut W)) (k : ℕ) (K : Type) [Field K] [Finite K] (b c : K)
        (π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →* ↥H),
        Nat.card K = 2 ^ k → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        SumOfNatVia (CFSG.Quasithin.FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c)))
          H ⊤ ⊥ 2 π →
        Nat.card (centralizer (H : Set (MulAut W))) ≤ 2 ^ (4 * k) := by
  intro W _ _ hW H k K _ _ b c π hcard hirr hS
  classical
  have : Fintype K := Fintype.ofFinite K
  let Γ := StatedOmega (StatedQuadMinus 2 K b c)
  let D := CFSG.Quasithin.FFModel.nat Γ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    refine charP_of_card_eq_prime_pow (p := 2) (f := k) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hHS : CFSG.Quasithin.H.HasScalarCommutant Γ :=
    hasScalarCommutant_statedOmegaMinus2 (K := K) (b := b) (c := c) hirr
  obtain ⟨I, hZI, hind, hsup, hreal⟩ := hS
  have hK0 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
    apply le_antisymm
    · refine iSup_le (fun j => ?_)
      refine iSup_le (fun hj => ?_)
      fin_cases j
      · exact (hj rfl).elim
      · exact le_rfl
    · refine le_iSup_of_le (1 : Fin 2) ?_
      exact le_iSup_of_le (show (1 : Fin 2) ≠ 0 by decide) le_rfl
  have hK1 : (⨆ (j : Fin 2) (_ : j ≠ 1), I j) = I 0 := by
    apply le_antisymm
    · refine iSup_le (fun j => ?_)
      refine iSup_le (fun hj => ?_)
      fin_cases j
      · exact le_rfl
      · exact (hj rfl).elim
    · refine le_iSup_of_le (0 : Fin 2) ?_
      exact le_iSup_of_le (show (0 : Fin 2) ≠ 1 by decide) le_rfl
  have hdisj : I 0 ⊓ I 1 = ⊥ := by
    have h0 := hind 0
    rw [bot_sup_eq, hK0] at h0
    exact le_bot_iff.mp h0
  have htop : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
    apply le_antisymm
    · refine iSup_le (fun i => ?_)
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun i : Fin 2 => I i) 0) (le_iSup _ 1)
  have hsup2 : I 0 ⊔ I 1 = ⊤ := by
    have h := hsup
    rw [bot_sup_eq, htop] at h
    exact h
  have hex : ∀ w : W, ∃ p : ↥(I 0) × ↥(I 1), ((p.1 : W) * (p.2 : W)) = w := by
    intro w
    have hw : w ∈ I 0 ⊔ I 1 := by rw [hsup2]; exact Subgroup.mem_top w
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp hw
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
  let Φ : W → ↥(I 0) × ↥(I 1) := fun w => Classical.choose (hex w)
  have hΦ : ∀ w : W, ((Φ w).1 : W) * ((Φ w).2 : W) = w :=
    fun w => Classical.choose_spec (hex w)
  have huniq : ∀ (w : W) (p q : ↥(I 0) × ↥(I 1)),
      ((p.1 : W) * (p.2 : W) = w) → ((q.1 : W) * (q.2 : W) = w) → p = q := by
    rintro w ⟨p0, p1⟩ ⟨q0, q1⟩ hp hq
    have h : (p0 : W) * (p1 : W) = (q0 : W) * (q1 : W) := hp.trans hq.symm
    have hab : ((p0 : W) * (q0 : W)⁻¹) * ((p1 : W) * (q1 : W)⁻¹) = 1 := by
      calc ((p0 : W) * (q0 : W)⁻¹) * ((p1 : W) * (q1 : W)⁻¹)
          = ((p0 : W) * (p1 : W)) * ((q0 : W) * (q1 : W))⁻¹ := by
            rw [mul_inv_rev]
            ac_rfl
        _ = 1 := by rw [h, mul_inv_cancel]
    have ha : (p0 : W) * (q0 : W)⁻¹ = ((p1 : W) * (q1 : W)⁻¹)⁻¹ := by
      calc (p0 : W) * (q0 : W)⁻¹
          = ((p0 : W) * (q0 : W)⁻¹) *
              (((p1 : W) * (q1 : W)⁻¹) * ((p1 : W) * (q1 : W)⁻¹)⁻¹) := by simp
        _ = (((p0 : W) * (q0 : W)⁻¹) * ((p1 : W) * (q1 : W)⁻¹)) *
              ((p1 : W) * (q1 : W)⁻¹)⁻¹ := by ac_rfl
        _ = ((p1 : W) * (q1 : W)⁻¹)⁻¹ := by rw [hab, one_mul]
    have hmem : (p0 : W) * (q0 : W)⁻¹ ∈ I 0 ⊓ I 1 := by
      refine ⟨Subgroup.mul_mem _ p0.2 (Subgroup.inv_mem _ q0.2), ?_⟩
      rw [ha]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ p1.2 (Subgroup.inv_mem _ q1.2))
    rw [hdisj] at hmem
    have hbot : (p0 : W) * (q0 : W)⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have hp0 : (p0 : W) = (q0 : W) := by
      have h1 : (p0 : W) * (q0 : W)⁻¹ = (q0 : W) * (q0 : W)⁻¹ := by
        rw [hbot, mul_inv_cancel]
      exact mul_right_cancel h1
    have hp1 : (p1 : W) = (q1 : W) := by
      rw [hp0] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext hp0) (Subtype.ext hp1)
  have hΦmul : ∀ a b : W, Φ (a * b) = Φ a * Φ b := by
    intro a b
    refine huniq (a * b) (Φ (a * b)) (Φ a * Φ b) (hΦ (a * b)) ?_
    show ((Φ a).1 : W) * ((Φ b).1 : W) * (((Φ a).2 : W) * ((Φ b).2 : W)) = a * b
    calc ((Φ a).1 : W) * ((Φ b).1 : W) * (((Φ a).2 : W) * ((Φ b).2 : W))
        = (((Φ a).1 : W) * ((Φ a).2 : W)) * (((Φ b).1 : W) * ((Φ b).2 : W)) := by ac_rfl
      _ = a * b := by rw [hΦ a, hΦ b]
  have hΦone : Φ 1 = 1 := by
    refine huniq 1 (Φ 1) (1 : ↥(I 0) × ↥(I 1)) (hΦ 1) ?_
    simp
  let Φhom : W →* ↥(I 0) × ↥(I 1) :=
    { toFun := Φ, map_one' := hΦone, map_mul' := hΦmul }
  have hNat : ∀ i : Fin 2, CFSG.Quasithin.SzN15.NatReal H (I i) ⊥ Γ π :=
    fun i => CFSG.Quasithin.SzN15.NatReal.of_realizesVia (hreal i)
  have hIinv : ∀ (i : Fin 2) (h : ↥H) (x : W), x ∈ I i → (h : MulAut W) x ∈ I i :=
    fun i h x hx => (hNat i).U_inv h x hx
  have hΦπ : ∀ (γ : ↥Γ) (w : W),
      Φ (((π γ : ↥H) : MulAut W) w) =
        (⟨((π γ : ↥H) : MulAut W) ((Φ w).1 : W),
            hIinv 0 (π γ) ((Φ w).1 : W) (Φ w).1.2⟩,
          ⟨((π γ : ↥H) : MulAut W) ((Φ w).2 : W),
            hIinv 1 (π γ) ((Φ w).2 : W) (Φ w).2.2⟩) := by
    intro γ w
    refine huniq (((π γ : ↥H) : MulAut W) w) (Φ (((π γ : ↥H) : MulAut W) w)) _ (hΦ _) ?_
    show ((π γ : ↥H) : MulAut W) ((Φ w).1 : W) *
        ((π γ : ↥H) : MulAut W) ((Φ w).2 : W) = ((π γ : ↥H) : MulAut W) w
    rw [← map_mul, hΦ w]
  let β (i : Fin 2) : ↥(I i) →* Multiplicative (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    Classical.choose (hNat i).exists_β
  have hβs : ∀ i : Fin 2, Function.Surjective (β i) :=
    fun i => (Classical.choose_spec (hNat i).exists_β).1
  have hβk : ∀ (i : Fin 2) (u : ↥(I i)), β i u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W) :=
    fun i => (Classical.choose_spec (hNat i).exists_β).2.1
  have hβe : ∀ (i : Fin 2) (γ : ↥Γ) (u : ↥(I i))
      (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I i),
      β i ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ = natAct Γ γ (β i u) :=
    fun i => (Classical.choose_spec (hNat i).exists_β).2.2
  have hβinj : ∀ i : Fin 2, Function.Injective (β i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro u hu
    have hz : (u : W) ∈ (⊥ : Subgroup W) := (hβk i u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.mp hz)
  let e (i : Fin 2) : ↥(I i) ≃* Multiplicative (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    MulEquiv.ofBijective (β i) ⟨hβinj i, hβs i⟩
  have he : ∀ (i : Fin 2) (γ : ↥Γ) (u : ↥(I i))
      (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ I i),
      e i ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ = natAct Γ γ (e i u) := by
    intro i γ u hu
    exact hβe i γ u hu
  let pr (j : Fin 2) (p : ↥(I 0) × ↥(I 1)) : ↥(I j) :=
    match j with
    | ⟨0, _⟩ => p.1
    | ⟨1, _⟩ => p.2
  have hpr_one : ∀ j : Fin 2, pr j (1 : ↥(I 0) × ↥(I 1)) = 1 := by
    intro j
    fin_cases j <;> rfl
  have hpr_mul : ∀ (j : Fin 2) (p q : ↥(I 0) × ↥(I 1)),
      pr j (p * q) = pr j p * pr j q := by
    intro j p q
    fin_cases j <;> rfl
  let toMat (γ : ↥Γ) : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K :=
    ((γ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
  have component_scalar : ∀ (d : MulAut W), (∀ x ∈ H, d * x = x * d) →
      ∀ i j : Fin 2, ∃ μ : K, ∀ v : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
        Multiplicative.toAdd (β j (pr j (Φ (d ((e i).symm
          (Multiplicative.ofAdd v) : ↥(I i)) : W)))) = μ • v := by
    intro d hd i j
    let g : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) →+
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
      { toFun := fun v => Multiplicative.toAdd (β j (pr j (Φ (d ((e i).symm
          (Multiplicative.ofAdd v) : ↥(I i)) : W))))
        map_zero' := by
          simp only [ofAdd_zero, Subgroup.coe_one, MulEquiv.map_one, hΦone, hpr_one,
            MonoidHom.map_one, toAdd_one]
        map_add' := by
          intro v w
          simp only [ofAdd_add, Subgroup.coe_mul, MulEquiv.map_mul, hΦmul, hpr_mul,
            MonoidHom.map_mul, toAdd_mul] }
    have hcomm : ∀ γ : ↥Γ, ∀ v,
        g (((toMat γ)) *ᵥ v) =
          ((toMat γ)) *ᵥ g v := by
      intro γ v
      let x : ↥(I i) := (e i).symm (Multiplicative.ofAdd v)
      have hA : (e i).symm (Multiplicative.ofAdd
          (((toMat γ)) *ᵥ v)) =
          ⟨((π γ : ↥H) : MulAut W) (x : W), hIinv i (π γ) (x : W) x.2⟩ := by
        apply (e i).injective
        rw [MulEquiv.apply_symm_apply]
        have hx : e i x = Multiplicative.ofAdd v := by
          show e i ((e i).symm (Multiplicative.ofAdd v)) = Multiplicative.ofAdd v
          rw [MulEquiv.apply_symm_apply]
        rw [he i γ x (hIinv i (π γ) (x : W) x.2), hx]
        rfl
      have hB : d (((π γ : ↥H) : MulAut W) (x : W)) =
          ((π γ : ↥H) : MulAut W) (d (x : W)) := by
        have h := congrArg (fun m : MulAut W => m (x : W)) (hd (π γ) (π γ).2)
        simpa [MulAut.mul_apply] using h
      have hC : pr j (Φ (((π γ : ↥H) : MulAut W) (d (x : W)))) =
          ⟨((π γ : ↥H) : MulAut W) ((pr j (Φ (d (x : W))) : ↥(I j)) : W),
            hIinv j (π γ) ((pr j (Φ (d (x : W))) : ↥(I j)) : W)
              (pr j (Φ (d (x : W)))).2⟩ := by
        rw [hΦπ γ (d (x : W))]
        fin_cases j <;> rfl
      have hD : β j ⟨((π γ : ↥H) : MulAut W) ((pr j (Φ (d (x : W))) : ↥(I j)) : W),
            hIinv j (π γ) ((pr j (Φ (d (x : W))) : ↥(I j)) : W)
              (pr j (Φ (d (x : W)))).2⟩ =
          natAct Γ γ (β j (pr j (Φ (d (x : W))))) :=
        hβe j γ (pr j (Φ (d (x : W)))) _
      calc g (((toMat γ)) *ᵥ v)
          = Multiplicative.toAdd (β j (pr j (Φ (d ((e i).symm
              (Multiplicative.ofAdd (((toMat γ)) *ᵥ v)) : ↥(I i)) : W)))) := rfl
        _ = Multiplicative.toAdd (β j (pr j (Φ (d ((⟨((π γ : ↥H) : MulAut W) (x : W),
              hIinv i (π γ) (x : W) x.2⟩ : ↥(I i)) : W))))) := by rw [hA]
        _ = Multiplicative.toAdd (β j (pr j (Φ (d (((π γ : ↥H) : MulAut W) (x : W)))))) := by
          rfl
        _ = Multiplicative.toAdd (β j (pr j (Φ (((π γ : ↥H) : MulAut W) (d (x : W)))))) := by
          rw [hB]
        _ = Multiplicative.toAdd (β j ⟨((π γ : ↥H) : MulAut W)
              ((pr j (Φ (d (x : W))) : ↥(I j)) : W),
              hIinv j (π γ) ((pr j (Φ (d (x : W))) : ↥(I j)) : W)
                (pr j (Φ (d (x : W)))).2⟩) := by rw [hC]
        _ = Multiplicative.toAdd (natAct Γ γ (β j (pr j (Φ (d (x : W)))))) := by rw [hD]
        _ = ((toMat γ)) *ᵥ Multiplicative.toAdd (β j (pr j (Φ (d (x : W))))) := rfl
        _ = ((toMat γ)) *ᵥ g v := rfl
    exact hHS g (fun γ hγ v => hcomm ⟨γ, hγ⟩ v)
  let μ (d : MulAut W) (hd : ∀ x ∈ H, d * x = x * d) (i j : Fin 2) : K :=
    Classical.choose (component_scalar d hd i j)
  have hμspec : ∀ (d : MulAut W) (hd : ∀ x ∈ H, d * x = x * d) (i j : Fin 2) (v : _),
      Multiplicative.toAdd (β j (pr j (Φ (d ((e i).symm
        (Multiplicative.ofAdd v) : ↥(I i)) : W)))) = μ d hd i j • v :=
    fun d hd i j => Classical.choose_spec (component_scalar d hd i j)
  have hμapp : ∀ (d : MulAut W) (hd : ∀ x ∈ H, d * x = x * d) (i j : Fin 2) (u : ↥(I i)),
      β j (pr j (Φ (d (u : W)))) =
        Multiplicative.ofAdd (μ d hd i j • Multiplicative.toAdd (β i u)) := by
    intro d hd i j u
    have h := hμspec d hd i j (Multiplicative.toAdd (β i u))
    have hu : (e i).symm (Multiplicative.ofAdd (Multiplicative.toAdd (β i u))) = u := by
      rw [ofAdd_toAdd]
      exact MulEquiv.symm_apply_apply (e i) u
    rw [hu] at h
    have h' := congrArg Multiplicative.ofAdd h
    simpa using h'
  let mat (q : ↥(centralizer (H : Set (MulAut W)))) : Fin 2 × Fin 2 → K :=
    fun p => μ (q : MulAut W) (fun x hx => (Subgroup.mem_centralizer_iff.mp q.2 x hx).symm)
      p.1 p.2
  have hmat_inj : Function.Injective mat := by
    intro q q' hEq
    have hμeq : ∀ i j : Fin 2,
        μ (q : MulAut W) (fun x hx => (Subgroup.mem_centralizer_iff.mp q.2 x hx).symm) i j =
        μ (q' : MulAut W) (fun x hx => (Subgroup.mem_centralizer_iff.mp q'.2 x hx).symm) i j :=
      fun i j => congrFun hEq (i, j)
    apply Subtype.ext
    ext x
    let x0 : ↥(I 0) := pr 0 (Φ x)
    let x1 : ↥(I 1) := pr 1 (Φ x)
    have hx : (x0 : W) * (x1 : W) = x := by
      have h := hΦ x
      rwa [show ((Φ x).1 : W) = (x0 : W) from rfl, show ((Φ x).2 : W) = (x1 : W) from rfl] at h
    let hdq : ∀ x ∈ H, (q : MulAut W) * x = x * (q : MulAut W) :=
      fun x hx => (Subgroup.mem_centralizer_iff.mp q.2 x hx).symm
    let hdq' : ∀ x ∈ H, (q' : MulAut W) * x = x * (q' : MulAut W) :=
      fun x hx => (Subgroup.mem_centralizer_iff.mp q'.2 x hx).symm
    have hcomp : ∀ (i j : Fin 2) (u : ↥(I i)),
        pr j (Φ ((q : MulAut W) (u : W))) =
          pr j (Φ ((q' : MulAut W) (u : W))) := by
      intro i j u
      apply hβinj j
      rw [hμapp (q : MulAut W) hdq i j u, hμapp (q' : MulAut W) hdq' i j u, hμeq i j]
    have hqxi : ∀ i : Fin 2, ∀ u : ↥(I i), (q : MulAut W) (u : W) = (q' : MulAut W) (u : W) := by
      intro i u
      calc (q : MulAut W) (u : W)
          = ((pr 0 (Φ ((q : MulAut W) (u : W))) : ↥(I 0)) : W) *
              ((pr 1 (Φ ((q : MulAut W) (u : W))) : ↥(I 1)) : W) := (hΦ _).symm
        _ = ((pr 0 (Φ ((q' : MulAut W) (u : W))) : ↥(I 0)) : W) *
              ((pr 1 (Φ ((q' : MulAut W) (u : W))) : ↥(I 1)) : W) := by
          rw [hcomp i 0 u, hcomp i 1 u]
        _ = (q' : MulAut W) (u : W) := hΦ _
    calc (q : MulAut W) x = (q : MulAut W) ((x0 : W) * (x1 : W)) := by rw [hx]
      _ = (q : MulAut W) (x0 : W) * (q : MulAut W) (x1 : W) := map_mul _ _ _
      _ = (q' : MulAut W) (x0 : W) * (q' : MulAut W) (x1 : W) := by
        rw [hqxi 0 x0, hqxi 1 x1]
      _ = (q' : MulAut W) ((x0 : W) * (x1 : W)) := (map_mul _ _ _).symm
      _ = (q' : MulAut W) x := by rw [hx]
  have hcardMat : Nat.card (Fin 2 × Fin 2 → K) = 2 ^ (4 * k) := by
    rw [Nat.card_fun, Nat.card_prod, Nat.card_fin, hcard, ← pow_mul, Nat.mul_comm]
  have hle := Nat.card_le_card_of_injective mat hmat_inj
  rw [hcardMat] at hle
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
