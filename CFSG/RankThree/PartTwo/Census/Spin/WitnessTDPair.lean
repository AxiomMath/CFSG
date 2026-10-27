module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDWeyl
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDTwo

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  {b : Module.Basis ι K P.W}

variable (b) in
noncomputable abbrev gen (s : Bool) (p : ι) : CliffordAlgebra Q := bif s then cr b p else an b p

theorem gen_anti (s t : Bool) {p q : ι} (hpq : p ≠ q) :
    gen b s p * gen b t q = -(gen b t q * gen b s p) := by
  cases s <;> cases t
  exacts [an_an b p q, an_cr b hpq.symm, cr_an b hpq, cr_cr b p q]

theorem commute_gens (s₁ s₂ t₁ t₂ : Bool) {p₁ p₂ q₁ q₂ : ι} (h₁₁ : p₁ ≠ q₁) (h₁₂ : p₁ ≠ q₂)
    (h₂₁ : p₂ ≠ q₁) (h₂₂ : p₂ ≠ q₂) :
    Commute (gen b s₁ p₁ * gen b s₂ p₂) (gen b t₁ q₁ * gen b t₂ q₂) :=
  commute_of_anticomm (gen_anti s₁ t₁ h₁₁) (gen_anti s₁ t₂ h₁₂) (gen_anti s₂ t₁ h₂₁)
    (gen_anti s₂ t₂ h₂₂)

variable {i k m : ι} (hik : i ≠ k) (hmi : m ≠ i) (hmk : m ≠ k)
include hik hmi hmk

omit hik in
theorem commute_cr_weyls :
    Commute (cr b m) (chainWeyl b i k) ∧ Commute (cr b m) (pairWeyl b i k) :=
  let h := commute_weyls (cr_cr b m i) (cr_an b hmi) (cr_cr b m k) (cr_an b hmk)
  ⟨h.1, h.2.1⟩

omit hik in
theorem commute_an_weyls :
    Commute (an b m) (chainWeyl b i k) ∧ Commute (an b m) (pairWeyl b i k) :=
  let h := commute_weyls (an_cr b hmi.symm) (an_an b m i) (an_cr b hmk.symm) (an_an b m k)
  ⟨h.1, h.2.1⟩

theorem chainWeyl_pair_first :
    chainWeyl b i k * (cr b k * cr b m) = cr b i * cr b m * chainWeyl b i k ∧
      chainWeyl b i k * (an b m * an b k) = an b m * an b i * chainWeyl b i k := by
  have hc := (commute_cr_weyls (b := b) hmi hmk).1
  have ha := (commute_an_weyls (b := b) hmi hmk).1
  constructor
  · calc chainWeyl b i k * (cr b k * cr b m) = chainWeyl b i k * cr b k * cr b m :=
          (mul_assoc _ _ _).symm
      _ = cr b i * (chainWeyl b i k * cr b m) := by rw [chainWeyl_mul_cr hik, mul_assoc]
      _ = cr b i * cr b m * chainWeyl b i k := by rw [← hc.eq, mul_assoc]
  · calc chainWeyl b i k * (an b m * an b k) = an b m * (chainWeyl b i k * an b k) := by
          rw [← mul_assoc, ← ha.eq, mul_assoc]
      _ = an b m * an b i * chainWeyl b i k := by rw [chainWeyl_mul_an hik, mul_assoc]

theorem chainWeyl_pair_second :
    chainWeyl b i k * (cr b m * cr b k) = cr b m * cr b i * chainWeyl b i k ∧
      chainWeyl b i k * (an b k * an b m) = an b i * an b m * chainWeyl b i k := by
  have hc := (commute_cr_weyls (b := b) hmi hmk).1
  have ha := (commute_an_weyls (b := b) hmi hmk).1
  constructor
  · calc chainWeyl b i k * (cr b m * cr b k) = cr b m * (chainWeyl b i k * cr b k) := by
          rw [← mul_assoc, ← hc.eq, mul_assoc]
      _ = cr b m * cr b i * chainWeyl b i k := by rw [chainWeyl_mul_cr hik, mul_assoc]
  · calc chainWeyl b i k * (an b k * an b m) = chainWeyl b i k * an b k * an b m :=
          (mul_assoc _ _ _).symm
      _ = an b i * (chainWeyl b i k * an b m) := by rw [chainWeyl_mul_an hik, mul_assoc]
      _ = an b i * an b m * chainWeyl b i k := by rw [← ha.eq, mul_assoc]

theorem signWeyl_chain :
    pairWeyl b i k * (cr b m * an b i) = -(cr b m * cr b k) * pairWeyl b i k ∧
      chainWeyl b i k * -(cr b m * cr b k) = -(cr b m * cr b i) * chainWeyl b i k ∧
      pairWeyl b i k * (cr b i * an b m) = -(an b k * an b m) * pairWeyl b i k ∧
      chainWeyl b i k * -(an b k * an b m) = -(an b i * an b m) * chainWeyl b i k := by
  obtain ⟨hc1, hc2⟩ := commute_cr_weyls (b := b) hmi hmk
  obtain ⟨ha1, ha2⟩ := commute_an_weyls (b := b) hmi hmk
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc pairWeyl b i k * (cr b m * an b i) = cr b m * (pairWeyl b i k * an b i) := by
          rw [← mul_assoc, ← hc2.eq, mul_assoc]
      _ = -(cr b m * cr b k) * pairWeyl b i k := by
          rw [pairWeyl_mul_an hik]; noncomm_ring
  · calc chainWeyl b i k * -(cr b m * cr b k) = -(cr b m * (chainWeyl b i k * cr b k)) := by
          rw [mul_neg, ← mul_assoc, ← hc1.eq, mul_assoc]
      _ = -(cr b m * cr b i) * chainWeyl b i k := by
          rw [chainWeyl_mul_cr hik]; noncomm_ring
  · calc pairWeyl b i k * (cr b i * an b m) = -an b k * (pairWeyl b i k * an b m) := by
          rw [← mul_assoc, pairWeyl_mul_cr hik, mul_assoc]
      _ = -(an b k * an b m) * pairWeyl b i k := by
          rw [← ha2.eq]; noncomm_ring
  · calc chainWeyl b i k * -(an b k * an b m) = -(an b i * (chainWeyl b i k * an b m)) := by
          rw [mul_neg, ← mul_assoc, chainWeyl_mul_an hik, mul_assoc]
      _ = -(an b i * an b m) * chainWeyl b i k := by
          rw [← ha1.eq]; noncomm_ring

end Cliff

namespace CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

variable {n : ℕ} (hn : 4 ≤ n)

theorem isIntOp_chainE {j k : Fin n} (hjk : j.val + 1 = k.val) :
    IsIntOp n (crD n j * anD n k) (rootIntMatrix n hn (.inl j)) := by
  have hj : j.val + 1 < n := hjk ▸ k.isLt
  have e : (⟨j.val + 1, hj⟩ : Fin n) = k := Fin.ext hjk
  have h := (isIntOp_E n hn j).congr (chainE_eq n (by omega) j hj)
  rw [e] at h
  exact h

theorem isIntOp_chainF {j k : Fin n} (hjk : j.val + 1 = k.val) :
    IsIntOp n (crD n k * anD n j) (rootIntMatrix n hn (.inr j)) := by
  have hj : j.val + 1 < n := hjk ▸ k.isLt
  have e : (⟨j.val + 1, hj⟩ : Fin n) = k := Fin.ext hjk
  have h := (isIntOp_F n hn j).congr (chainF_eq n (by omega) j hj)
  rw [e] at h
  exact h

theorem isIntOp_forkE :
    IsIntOp n (crD n (forkA n hn) * crD n (forkB n hn))
      (rootIntMatrix n hn (.inl (forkB n hn))) :=
  (isIntOp_E n hn _).congr (Fork.Eb_eq (polarization n) (polarizationBasis n) (by omega))

theorem isIntOp_forkF :
    IsIntOp n (anD n (forkB n hn) * anD n (forkA n hn))
      (rootIntMatrix n hn (.inr (forkB n hn))) :=
  (isIntOp_F n hn _).congr (Fork.Fb_eq (polarization n) (polarizationBasis n) (by omega))

variable {K : Type} [Field K]

omit hn in
theorem pair_sqZeroPair {i k : Fin n} (hik : i ≠ k)
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crD n i * crD n k) X) (hY : IsIntOp n (anD n k * anD n i) Y)
    (hXsq : intMap K X * intMap K X = 0) (hYsq : intMap K Y * intMap K Y = 0) :
    SqZeroPair (intMap K X) (intMap K Y) where
  ee := hXsq
  ff := hYsq
  efe := intMap_eq_of hX hY hX (P_N_P _ hik)
  fef := intMap_eq_of hY hX hY (N_P_N _ hik)

omit hn in
theorem pair_ne_zero {i k : Fin n} (hik : i < k)
    {X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crD n i * crD n k) X) : intMap K X ≠ 0 := by
  set ik : Fin (dimension n) := Fintype.equivFin (Finset (Fin n)) {i, k}
  have hact : spinAction _ (polarization n) (crD n i * crD n k)
      ((latticeBasis n vac : (lattice n).toAddSubgroup) : ExteriorAlgebra ℚ (polarization n).W) =
      ((latticeBasis n ik : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
    rw [latticeBasis_vac, coe_latticeBasis, signSet, Equiv.symm_apply_apply,
      TauCeti.ExteriorAlgebra.basis_pair _ hik, map_mul, Module.End.mul_apply,
      spinAction_ι_wedge, spinAction_ι_wedge, mul_one]
  have h1 := hX vac
  rw [hact] at h1
  have hM : ∑ r, X r vac • latticeBasis n r = latticeBasis n ik := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_zsmul] using h1.symm
  have h2 := congrArg (fun x => (latticeBasis n).repr x ik) hM
  simp only [map_sum, map_zsmul, Module.Basis.repr_self] at h2
  rw [Finsupp.finsetSum_apply] at h2
  simp [Finsupp.single_apply] at h2
  intro h0
  have h3 := congrFun (congrFun h0 ik) vac
  change ((X ik vac : ℤ) : K) = 0 at h3
  rw [h2, Int.cast_one] at h3
  exact one_ne_zero h3


omit hn in
theorem block_commute {p q : Fin n} (hpq : p ≠ q) :
    Commute (crD n p * anD n q) (crD n p * crD n q) ∧
      Commute (crD n p * anD n q) (anD n q * anD n p) ∧
      Commute (crD n p * crD n q) (crD n q * anD n p) ∧
      Commute (crD n q * anD n p) (anD n q * anD n p) :=
  ⟨(Fork.EE (polarization n) (polarizationBasis n) hpq).trans
      (Fork.EE' (polarization n) (polarizationBasis n)).symm,
    (Fork.EF (polarization n) (polarizationBasis n)).trans
      (Fork.FE (polarization n) (polarizationBasis n) hpq).symm,
    (Fork.EF' (polarization n) (polarizationBasis n)).trans
      (Fork.FE' (polarization n) (polarizationBasis n) hpq).symm,
    (Fork.FF (polarization n) (polarizationBasis n)).trans
      (Fork.FF' (polarization n) (polarizationBasis n) hpq).symm⟩

section Blocks

variable {hn} {F : (rootData n hn K).G →* (rootData n hn K).G} {L : Subfield K}

theorem three_witness_blocks (hchar : (2 : K) = 0) {β : Type*} [Fintype β] [DecidableEq β]
    (i j : β → Fin n) (hij : ∀ b, (i b).val + 1 = (j b).val)
    (hdisj : ∀ b b', b ≠ b' → i b ≠ i b' ∧ i b ≠ j b' ∧ j b ≠ i b' ∧ j b ≠ j b')
    (hD : ∀ b, (rootData n hn K).x (i b) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n hn K).y (i b) 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆)
    (MP NP : β → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ)
    (hMP : ∀ b, IsIntOp n (crD n (i b) * crD n (j b)) (MP b))
    (hNP : ∀ b, IsIntOp n (anD n (j b) * anD n (i b)) (NP b))
    (hMPR : ∀ b, (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ L
      (intMap K (MP b)))
    (hNPR : ∀ b, (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ L
      (intMap K (NP b)))
    {k k' : Fin n} (hkk : k.val + 1 = k'.val) (hkd : ∀ b, k ≠ i b ∧ k ≠ j b ∧ k' ≠ i b ∧ k' ≠ j b)
    (hkD : (rootData n hn K).x k 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n hn K).y k 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 (Fintype.card β * 2) := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact hchar
  have hne : ∀ b, i b ≠ j b := fun b => fin_ne (by have := hij b; omega)
  have hlt : ∀ b, i b < j b := fun b => by rw [Fin.lt_def]; have := hij b; omega
  choose gP hgPD hgP using fun b => (hMPR b).memD 1 L.one_mem
  choose gN hgND hgN using fun b => (hNPR b).memD 1 L.one_mem
  let MX : β × Fin 2 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    fun p => ![rootIntMatrix n hn (.inl (i p.1)), MP p.1] p.2
  let MY : β × Fin 2 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    fun p => ![rootIntMatrix n hn (.inr (i p.1)), NP p.1] p.2
  let sX : Fin 2 → Bool := ![false, true]
  let sY : Fin 2 → Bool := ![true, false]
  let cX : β × Fin 2 → Cl n := fun p =>
    gen (polarizationBasis n) true (i p.1) * gen (polarizationBasis n) (sX p.2) (j p.1)
  let cY : β × Fin 2 → Cl n := fun p =>
    gen (polarizationBasis n) (sY p.2) (j p.1) * gen (polarizationBasis n) false (i p.1)
  let gx : β × Fin 2 → (rootData n hn K).G := fun p => ![(rootData n hn K).x (i p.1) 1, gP p.1] p.2
  let gy : β × Fin 2 → (rootData n hn K).G := fun p => ![(rootData n hn K).y (i p.1) 1, gN p.1] p.2
  have hMX : ∀ p, IsIntOp n (cX p) (MX p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact isIntOp_chainE hn (hij b)
    · exact hMP b
  have hMY : ∀ p, IsIntOp n (cY p) (MY p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact isIntOp_chainF hn (hij b)
    · exact hNP b
  have hgx : ∀ p, (rootData n hn K).mat (gx p) = 1 + (1 : K) • intMap K (MX p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact mat_x' _ _
    · exact hgP b
  have hgy : ∀ p, (rootData n hn K).mat (gy p) = 1 + (1 : K) • intMap K (MY p) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact mat_y' _ _
    · exact hgN b
  have hpair : ∀ p, SqZeroPair (intMap K (MX p)) (intMap K (MY p)) := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact (rootData n hn K).sqZero (i b)
    · exact pair_sqZeroPair (hne b) (hMP b) (hNP b) (hMPR b).sq (hNPR b).sq
  have hX0 : ∀ p, intMap K (MX p) ≠ 0 := by
    rintro ⟨b, s⟩
    fin_cases s
    · exact (rootData n hn K).E_ne_zero (i b)
    · exact pair_ne_zero (hlt b) (hMP b)
  have hXX : ∀ p p', p ≠ p' → Commute (cX p) (cX p') := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ hpp
    by_cases hbb : b = b'
    · subst hbb
      have hc := block_commute (hne b)
      fin_cases s <;> fin_cases s'
      · exact absurd rfl hpp
      · exact hc.1
      · exact hc.1.symm
      · exact absurd rfl hpp
    · obtain ⟨h1, h2, h3, h4⟩ := hdisj b b' hbb
      exact commute_gens _ _ _ _ h1 h2 h3 h4
  have hXY : ∀ p p', p ≠ p' → Commute (cX p) (cY p') := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ hpp
    by_cases hbb : b = b'
    · subst hbb
      have hc := block_commute (hne b)
      fin_cases s <;> fin_cases s'
      · exact absurd rfl hpp
      · exact hc.2.1
      · exact hc.2.2.1
      · exact absurd rfl hpp
    · obtain ⟨h1, h2, h3, h4⟩ := hdisj b b' hbb
      exact commute_gens _ _ _ _ h2 h1 h4 h3
  have hYY : ∀ p p', p ≠ p' → Commute (cY p) (cY p') := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ hpp
    by_cases hbb : b = b'
    · subst hbb
      have hc := block_commute (hne b)
      fin_cases s <;> fin_cases s'
      · exact absurd rfl hpp
      · exact hc.2.2.2
      · exact hc.2.2.2.symm
      · exact absurd rfl hpp
    · obtain ⟨h1, h2, h3, h4⟩ := hdisj b b' hbb
      exact commute_gens _ _ _ _ h4 h3 h2 h1
  have hkE : IsIntOp n (gen (polarizationBasis n) true k * gen (polarizationBasis n) false k')
      (rootIntMatrix n hn (.inl k)) := isIntOp_chainE hn hkk
  have hkc : ∀ p, Commute (gen (polarizationBasis n) true k * gen (polarizationBasis n) false k')
      (cX p) ∧ Commute (gen (polarizationBasis n) true k * gen (polarizationBasis n) false k')
      (cY p) := fun p => by
    obtain ⟨h1, h2, h3, h4⟩ := hkd p.1
    exact ⟨commute_gens _ _ _ _ h1 h2 h3 h4, commute_gens _ _ _ _ h2 h1 h4 h3⟩
  have ht2 : (rootData n hn K).x k 1 ^ 2 = 1 := by
    rw [pow_two, ← x_add, h11, x_zero]
  have htz : ∃ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      (rootData n hn K).x k 1 * g ≠ g * (rootData n hn K).x k 1 := by
    refine ⟨(rootData n hn K).y k 1, hkD.2, fun h => (one_ne_zero : (1 : K) ≠ 0) ?_⟩
    exact (rootData n hn K).eq_zero_of_commute_sqZeroPair ((rootData n hn K).sqZero k)
      ((rootData n hn K).E_ne_zero k) (mat_x' _ _) (by rw [mat_y', one_smul]) h
  have h := RootData.three_witness_pairs (R := rootData n hn K) hchar (F := F)
    (X := fun p => intMap K (MX p)) (Y := fun p => intMap K (MY p)) hpair hX0 gx gy
    (fun p => by rw [hgx, one_smul]) (fun p => by rw [hgy, one_smul])
    (by rintro ⟨b, s⟩; fin_cases s; exacts [(hD b).1, hgPD b])
    (by rintro ⟨b, s⟩; fin_cases s; exacts [(hD b).2, hgND b])
    (fun p p' hpp => intMap_commute_of (hMX p) (hMX p') (hXX p p' hpp).eq)
    (fun p p' hpp => intMap_commute_of (hMX p) (hMY p') (hXY p p' hpp).eq)
    (fun p p' hpp => intMap_commute_of (hMY p) (hMY p') (hYY p p' hpp).eq)
    ((rootData n hn K).x k 1) hkD.1 ht2 htz
    (fun p => (rootData n hn K).commute_of_mat (by
      rw [mat_x', hgx]
      exact commute_one_add_smul (intMap_commute_of hkE (hMX p) (hkc p).1.eq) 1 1))
    (fun p => (rootData n hn K).commute_of_mat (by
      rw [mat_x', hgy]
      exact commute_one_add_smul (intMap_commute_of hkE (hMY p) (hkc p).2.eq) 1 1))
  rwa [Fintype.card_prod, Fintype.card_fin] at h

end Blocks

end CarrierD

namespace CarrierTD

open TauCeti TauCeti.TypeDSpinCarrier CarrierD Cliff RootData
open scoped commutatorElement

section Generic

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K} {π : Equiv.Perm (Fin n)}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem nu_mem_fixed (hF : (rootData n hn K).IsTwistedFrobenius σ π F) {j : Fin n}
    (hj : π j = j) : nu j ∈ fixedSubgroup F := by
  rw [mem_fixedSubgroup]
  simp only [nu, map_mul, hF.map_x, hF.map_y, hj, map_one, map_neg]

theorem nu_fork_mem_fixed (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπA : π (forkA n hn) = forkB n hn) (hπB : π (forkB n hn) = forkA n hn) :
    nu (forkA n hn) * nu (forkB n hn) ∈ fixedSubgroup F := by
  have hAv : (forkA n hn).val = n - 2 := rfl
  have hBv : (forkB n hn).val = n - 1 := rfl
  have hAB : forkA n hn ≠ forkB n hn := fin_ne (by omega)
  have hcm : (rootData n hn K).CM (forkA n hn) (forkB n hn) = 0 := by
    rw [rootData_CM, D_apply']
    split_ifs <;> omega
  have hxx : ∀ u v, Commute ((rootData n hn K).x (forkA n hn) u)
      ((rootData n hn K).x (forkB n hn) v) := (rootData n hn K).commute_x_x hcm
  have hxy : ∀ u v, Commute ((rootData n hn K).x (forkA n hn) u)
      ((rootData n hn K).y (forkB n hn) v) := (rootData n hn K).commute_x_y hAB
  have hyx : ∀ u v, Commute ((rootData n hn K).y (forkA n hn) u)
      ((rootData n hn K).x (forkB n hn) v) := fun u v =>
    ((rootData n hn K).commute_x_y hAB.symm v u).symm
  have hyy : ∀ u v, Commute ((rootData n hn K).y (forkA n hn) u)
      ((rootData n hn K).y (forkB n hn) v) := (rootData n hn K).commute_y_y hcm
  have hxB : ∀ u, Commute ((rootData n hn K).x (forkA n hn) u) (nu (forkB n hn)) := fun u =>
    ((hxx u 1).mul_right (hxy u (-1))).mul_right (hxx u 1)
  have hyB : ∀ u, Commute ((rootData n hn K).y (forkA n hn) u) (nu (forkB n hn)) := fun u =>
    ((hyx u 1).mul_right (hyy u (-1))).mul_right (hyx u 1)
  have hAB' : Commute (nu (forkA n hn)) (nu (forkB n hn)) :=
    ((hxB 1).mul_left (hyB (-1))).mul_left (hxB 1)
  rw [mem_fixedSubgroup, map_mul]
  have hA : F (nu (forkA n hn)) = nu (forkB n hn) := by
    simp only [nu, map_mul, hF.map_x, hF.map_y, hπA, map_one, map_neg]
  have hB : F (nu (forkB n hn)) = nu (forkA n hn) := by
    simp only [nu, map_mul, hF.map_x, hF.map_y, hπB, map_one, map_neg]
  rw [hA, hB]
  exact hAB'.eq.symm

variable {D : Subgroup (rootData n hn K).G} {L : Subfield K}

theorem pairOps_move {j k : Fin n} (hjk : j.val + 1 = k.val)
    (hD : ∀ g ∈ D, nu j * g * (nu j)⁻¹ ∈ D) {p q p' q' : Fin n}
    (h1 : chainWeyl (polarizationBasis n) j k * (crD n p * crD n q) =
      crD n p' * crD n q' * chainWeyl (polarizationBasis n) j k)
    (h2 : chainWeyl (polarizationBasis n) j k * (anD n q * anD n p) =
      anD n q' * anD n p' * chainWeyl (polarizationBasis n) j k)
    (h : ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n p * crD n q) M ∧ IsIntOp n (anD n q * anD n p) N ∧
      (rootData n hn K).RootOpIn D L (intMap K M) ∧ (rootData n hn K).RootOpIn D L (intMap K N)) :
    ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n p' * crD n q') M ∧ IsIntOp n (anD n q' * anD n p') N ∧
      (rootData n hn K).RootOpIn D L (intMap K M) ∧
      (rootData n hn K).RootOpIn D L (intMap K N) := by
  obtain ⟨M, N, hM, hN, hMR, hNR⟩ := h
  have hjk' : j ≠ k := fin_ne (by omega)
  have hE := isIntOp_chainE hn hjk
  have hF := isIntOp_chainF hn hjk
  obtain ⟨hM', hMR'⟩ := rootOpIn_conj hE hF (chain_E_sq hjk') (chain_F_sq hjk') hM h1 hD hMR
  obtain ⟨hN', hNR'⟩ := rootOpIn_conj hE hF (chain_E_sq hjk') (chain_F_sq hjk') hN h2 hD hNR
  exact ⟨_, _, hM', hN', hMR', hNR'⟩

theorem exists_pairOp_fork (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) :
    ∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n ⟨n - 3, by omega⟩ * crD n (forkA n hn)) M ∧
      IsIntOp n (anD n (forkA n hn) * anD n ⟨n - 3, by omega⟩) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N) := by
  set A := forkA n hn with hAd
  set B := forkB n hn with hBd
  set k4 : Fin n := ⟨n - 3, by omega⟩
  have hAv : A.val = n - 2 := rfl
  have hBv : B.val = n - 1 := rfl
  have hk4 : k4.val = n - 3 := rfl
  have hAB : A ≠ B := fin_ne (by omega)
  have h4A : k4 ≠ A := fin_ne (by omega)
  have h4B : k4 ≠ B := fin_ne (by omega)
  have hDs : ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu A * nu B * g * (nu A * nu B)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun g hg =>
    conj_mem_commutator (nu_fork_mem_fixed hF hπA hπB) g hg
  have hk4' : k4.val < n - 2 := by omega
  have hfix : ∀ u : K, σ u = u → (rootData n hn K).x k4 u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (rootData n hn K).y k4 u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun u hu =>
    fixed_mem_commutator hF hπ hc k4 hk4' hu
  have he := isIntOp_chainE hn (j := A) (k := B) (by omega)
  have hf := isIntOp_chainF hn (j := A) (k := B) (by omega)
  obtain ⟨s1, s2, s3, s4⟩ := signWeyl_chain (b := polarizationBasis n) hAB h4A h4B
  have hE4 := isIntOp_chainE hn (j := k4) (k := A) (by omega)
  have hF4 := isIntOp_chainF hn (j := k4) (k := A) (by omega)
  obtain ⟨hX, hXR⟩ := rootOpIn_conj₂ he hf (chain_E_sq hAB) (chain_F_sq hAB) (isIntOp_forkE hn)
    (isIntOp_forkF hn) pair_E_sq pair_F_sq hE4 s1 s2 hDs
    (RootOpIn.of_x (R := rootData n hn K) (L := RootData.fixedField σ) k4
      fun u hu => (hfix u hu).1)
  obtain ⟨hY, hYR⟩ := rootOpIn_conj₂ he hf (chain_E_sq hAB) (chain_F_sq hAB) (isIntOp_forkE hn)
    (isIntOp_forkF hn) pair_E_sq pair_F_sq hF4 s3 s4 hDs
    (RootOpIn.of_y (R := rootData n hn K) (L := RootData.fixedField σ) k4
      fun u hu => (hfix u hu).2)
  have hXR' := hXR.neg
  have hYR' := hYR.neg
  rw [← intMap_neg'] at hXR' hYR'
  exact ⟨_, _, hX.neg.congr (neg_neg _), hY.neg.congr (neg_neg _), hXR', hYR'⟩

theorem exists_pairOps (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (h5 : 5 ≤ n) :
    (∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n ⟨n - 3, by omega⟩ * crD n (forkA n hn)) M ∧
      IsIntOp n (anD n (forkA n hn) * anD n ⟨n - 3, by omega⟩) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N)) ∧
    (∃ M N : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crD n ⟨n - 5, by omega⟩ * crD n ⟨n - 4, by omega⟩) M ∧
      IsIntOp n (anD n ⟨n - 4, by omega⟩ * anD n ⟨n - 5, by omega⟩) N ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M) ∧
      (rootData n hn K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K N)) := by
  set A := forkA n hn with hAd
  set B := forkB n hn with hBd
  set k2 : Fin n := ⟨n - 5, by omega⟩
  set k3 : Fin n := ⟨n - 4, by omega⟩
  set k4 : Fin n := ⟨n - 3, by omega⟩
  have hAv : A.val = n - 2 := rfl
  have hBv : B.val = n - 1 := rfl
  have hk2 : k2.val = n - 5 := rfl
  have hk3 : k3.val = n - 4 := rfl
  have hk4 : k4.val = n - 3 := rfl
  have hAB : A ≠ B := fin_ne (by omega)
  have h4A : k4 ≠ A := fin_ne (by omega)
  have h4B : k4 ≠ B := fin_ne (by omega)
  have hDj : ∀ j : Fin n, j.val < n - 2 → ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu j * g * (nu j)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j hj g hg =>
    conj_mem_commutator (nu_mem_fixed hF (hπ j hj)) g hg
  have hk4' : k4.val < n - 2 := by omega
  have base := exists_pairOp_fork hF hπ hπA hπB hc
  refine ⟨base, ?_⟩
  have h34 : k3.val + 1 = k4.val := by omega
  have h23 : k2.val + 1 = k3.val := by omega
  have h4A' : k4.val + 1 = A.val := by omega
  have m1 := chainWeyl_pair_first (b := polarizationBasis n) (fin_ne (by omega) : k3 ≠ k4)
    (fin_ne (by omega) : A ≠ k3) h4A.symm
  have q1 := pairOps_move h34 (hDj k3 (by omega)) m1.1 m1.2 base
  have m2 := chainWeyl_pair_first (b := polarizationBasis n) (fin_ne (by omega) : k2 ≠ k3)
    (fin_ne (by omega) : A ≠ k2) (fin_ne (by omega) : A ≠ k3)
  have q2 := pairOps_move h23 (hDj k2 (by omega)) m2.1 m2.2 q1
  have m3 := chainWeyl_pair_second (b := polarizationBasis n) h4A
    (fin_ne (by omega) : k2 ≠ k4) (fin_ne (by omega) : k2 ≠ A)
  have q3 := pairOps_move h4A' (hDj k4 hk4') m3.1 m3.2 q2
  have m4 := chainWeyl_pair_second (b := polarizationBasis n) (fin_ne (by omega) : k3 ≠ k4)
    (fin_ne (by omega) : k2 ≠ k3) (fin_ne (by omega) : k2 ≠ k4)
  exact pairOps_move h34 (hDj k3 (by omega)) m4.1 m4.2 q3

theorem hasWitness_pair_gen (hF : (rootData n hn K).IsTwistedFrobenius σ π F)
    (hπ : ∀ i : Fin n, i.val < n - 2 → π i = i) (hπA : π (forkA n hn) = forkB n hn)
    (hπB : π (forkB n hn) = forkA n hn) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hchar : (2 : K) = 0) (h7 : 7 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  obtain ⟨⟨M45, N45, hM45, hN45, hM45R, hN45R⟩, ⟨M23, N23, hM23, hN23, hM23R, hN23R⟩⟩ :=
    exists_pairOps hF hπ hπA hπB hc (by omega)
  have h1 : σ 1 = 1 := map_one σ
  have hfix : ∀ i : Fin n, i.val < n - 2 →
      (rootData n hn K).x i 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
        (rootData n hn K).y i 1 ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun i hi =>
    fixed_mem_commutator hF hπ hc i hi h1
  let I : Fin 2 → Fin n := ![⟨n - 5, by omega⟩, ⟨n - 3, by omega⟩]
  let J : Fin 2 → Fin n := ![⟨n - 4, by omega⟩, forkA n hn]
  have hIv : ∀ b, (I b).val = n - 5 + 2 * b.val := fun b => by
    fin_cases b <;> simp [I]
    omega
  have hJv : ∀ b, (J b).val = n - 4 + 2 * b.val := fun b => by
    fin_cases b <;> simp [J, forkA]
    omega
  have h := three_witness_blocks hchar I J (fun b => by rw [hIv, hJv]; omega)
    (fun b b' hbb => by
      have hv : b.val ≠ b'.val := fun h => hbb (Fin.ext h)
      have hb := b.isLt
      have hb' := b'.isLt
      exact ⟨fin_ne (by simp only [hIv]; omega), fin_ne (by simp only [hIv, hJv]; omega),
        fin_ne (by simp only [hIv, hJv]; omega), fin_ne (by simp only [hJv]; omega)⟩)
    (fun b => hfix (I b) (by rw [hIv]; have := b.isLt; omega))
    ![M23, M45] ![N23, N45] (fun b => by fin_cases b; exacts [hM23, hM45])
    (fun b => by fin_cases b; exacts [hN23, hN45]) (fun b => by fin_cases b; exacts [hM23R, hM45R])
    (fun b => by fin_cases b; exacts [hN23R, hN45R]) (k := ⟨n - 7, by omega⟩)
    (k' := ⟨n - 6, by omega⟩) (by simp only; omega)
    (fun b => by
      have := b.isLt
      exact ⟨fin_ne (by simp only [hIv]; omega), fin_ne (by simp only [hJv]; omega),
        fin_ne (by simp only [hIv]; omega), fin_ne (by simp only [hJv]; omega)⟩)
    (hfix _ (by simp only; omega))
  rwa [Fintype.card_fin] at h

end Generic

variable (d : TypeTwistedDLieIndex)

theorem hasWitness_pair (h2 : d.1.characteristic = 2) (h7 : 7 ≤ d.1.rank) :
    HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  obtain ⟨c, hc⟩ := CarrierD.exists_unit_order_seven d.1 h2
  exact hasWitness_pair_gen (isTwistedFrobenius d) (fun i hi => perm_of_lt d hi) (perm_forkA d)
    (perm_forkB d) hc hchar h7

end CarrierTD

end CFSG.RankThree.PartTwo.Census.Spin
