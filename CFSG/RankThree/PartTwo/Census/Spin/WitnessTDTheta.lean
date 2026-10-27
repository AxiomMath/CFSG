module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTD

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData
open scoped commutatorElement

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {R : RootData K N ι}

theorem RootOp.of_conj {H₀ : Subgroup R.G} {L₀ : Subfield K} {X : Matrix N N K} {w : ι → ℤ}
    (hX : R.RootOp H₀ L₀ X w) {H : Subgroup R.G} {L : Subfield K}
    (hfix : ∀ u ∈ L, ∀ g : R.G, R.mat g = 1 + u • X → g ∈ H) (s : ι → Kˣ)
    (hs : R.torus s ∈ H) (hχ : ((∏ j, s j ^ w j : Kˣ) : K) ≠ 1)
    (hχL : ((∏ j, s j ^ w j : Kˣ) : K) ∈ L) : R.RootOp H L X w where
  sq := hX.sq
  mem := hX.mem
  torus := hX.torus
  memD u hu := by
    set c : K := ((∏ j, s j ^ w j : Kˣ) : K)
    have hc1 : c - 1 ≠ 0 := sub_ne_zero.mpr hχ
    set v := u / (c - 1) with hv
    have key : c * v - v = u := by rw [hv, ← sub_one_mul, mul_div_cancel₀ u hc1]
    obtain ⟨g, hg⟩ := hX.mem v
    have hgH := hfix _ (L.div_mem hu (L.sub_mem hχL L.one_mem)) g hg
    refine ⟨⁅R.torus s, g⁆, Subgroup.commutator_mem_commutator hs hgH, ?_⟩
    rw [commutatorElement_def, mat_mul, hX.mat_conj s hg, mat_inv_one_add_smul R hX.sq hg,
      add_mul, one_mul, mul_sub, mul_one, smul_mul_smul, hX.sq, smul_zero, sub_zero, ← key,
      sub_smul]
    abel

end RootData

namespace CarrierD

variable (n : ℕ) (hn : 4 ≤ n)

noncomputable abbrev gvec : Cl n := crD n ⟨n - 1, by omega⟩ - anD n ⟨n - 1, by omega⟩

@[expose] noncomputable def graphInt : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  Matrix.of fun i j => if i = graphBasisPerm n (by omega) j then graphBasisScale n (by omega) j
    else 0

theorem isIntOp_gvec : IsIntOp n (gvec n hn) (graphInt n hn) := fun s => by
  have h := graphOperator_latticeBasis n (by omega) s
  have e : graphOperator n (by omega) ((latticeBasis n s : (lattice n).toAddSubgroup) :
      ExteriorAlgebra ℚ (polarization n).W) = spinAction _ (polarization n) (gvec n hn)
        ((latticeBasis n s : (lattice n).toAddSubgroup) :
          ExteriorAlgebra ℚ (polarization n).W) := by
    rw [SpinPolarizationData.typeDGraphOperator_apply,
      SpinPolarizationData.typeDGraphVector_def, map_sub]
  rw [← e, h, AddSubgroup.coe_zsmul]
  simp only [graphInt, Matrix.of_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

variable {n}

theorem gvec_cr (i : Fin n) (hi : i ≠ ⟨n - 1, by omega⟩) :
    gvec n hn * crD n i = -(crD n i * gvec n hn) := by
  rw [sub_mul, mul_sub, cr_cr (polarizationBasis n) _ i, an_cr (polarizationBasis n) hi]
  abel

theorem gvec_an (i : Fin n) (hi : i ≠ ⟨n - 1, by omega⟩) :
    gvec n hn * anD n i = -(anD n i * gvec n hn) := by
  rw [sub_mul, mul_sub, cr_an (polarizationBasis n) hi.symm, an_an (polarizationBasis n) _ i]
  abel

theorem comm_mul_of_anticomm {A : Type*} [Ring A] {g x y : A} (hx : g * x = -(x * g))
    (hy : g * y = -(y * g)) : g * (x * y) = x * y * g := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, mul_assoc]

theorem graph_commute_theta {K : Type} [Field K]
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crD n ⟨0, by omega⟩ * crD n ⟨1, by omega⟩) X)
    (hY : IsIntOp n (anD n ⟨1, by omega⟩ * anD n ⟨0, by omega⟩) Y) :
    Commute (intMap K (graphInt n hn)) (intMap K X) ∧
      Commute (intMap K (graphInt n hn)) (intMap K Y) := by
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := fin_ne (by simp only; omega)
  have h1 : (⟨1, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := fin_ne (by simp only; omega)
  exact ⟨intMap_commute_of (isIntOp_gvec n hn) hX
      (comm_mul_of_anticomm (gvec_cr hn _ h0) (gvec_cr hn _ h1)),
    intMap_commute_of (isIntOp_gvec n hn) hY
      (comm_mul_of_anticomm (gvec_an hn _ h1) (gvec_an hn _ h0))⟩

theorem graphAutMatrix_eq (K : Type) [Field K] :
    ((graphAutMatrix n hn K : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) = intMap K (graphInt n hn) := by
  ext i j
  rw [coe_graphAutMatrix_apply]
  simp only [intMap, graphInt, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_one_add_smul_intMap {K : Type} [Field K] (σ : K →+* K) (u : K)
    (X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    (1 + u • intMap K X).map σ = 1 + σ u • intMap K X := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, intMap,
    smul_eq_mul, map_add, map_mul, map_intCast]
  split_ifs <;> simp

end CarrierD

namespace CarrierTD

open CarrierD

variable (d : TypeTwistedDLieIndex)

theorem coe_steinberg (g : d.toTypeDDiagramLieIndex.AmbientGroup) :
    (((d.steinberg g : d.toTypeDDiagramLieIndex.AmbientGroup) :
        Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure) =
      ((graphAutMatrix d.1.rank (four_le d) d.1.Closure :
          Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure) *
        (((g : Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
          Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure).map
            (frob d)) *
      (((graphAutMatrix d.1.rank (four_le d) d.1.Closure)⁻¹ :
          Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure) := by
  rw [TypeTwistedDLieIndex.steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    TypeTwistedDLieIndex.graphAut_def, coe_graphAutPoints, Units.val_mul, Units.val_mul]
  congr 2
  ext r c
  rw [TypeDDiagramLieIndex.coe_frobenius_apply, Matrix.map_apply, frob_apply]

variable {d}

theorem steinberg_eq_of_commute
    {X : Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) ℤ}
    (hX : Commute (intMap d.1.Closure (graphInt d.1.rank (four_le d))) (intMap d.1.Closure X))
    {g : d.toTypeDDiagramLieIndex.AmbientGroup} {u : d.1.Closure} (hu : frob d u = u)
    (hg : ((g : Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
      Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure) =
        1 + u • intMap d.1.Closure X) :
    d.steinberg g = g := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_steinberg, hg, map_one_add_smul_intMap, hu]
  set Pm : Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure :=
    ((graphAutMatrix d.1.rank (four_le d) d.1.Closure :
      Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure) with hPm
  set Pi : Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure :=
    (((graphAutMatrix d.1.rank (four_le d) d.1.Closure)⁻¹ :
      Matrix.GeneralLinearGroup (Fin (dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) d.1.Closure) with hPi
  have hPP : Pm * Pi = 1 := Units.mul_inv _
  have hP : Commute Pm (intMap d.1.Closure X) := by
    rw [hPm, graphAutMatrix_eq]
    exact hX
  calc Pm * (1 + u • intMap d.1.Closure X) * Pi
      = Pm * Pi + u • (Pm * intMap d.1.Closure X * Pi) := by
        rw [mul_add, mul_one, add_mul, mul_smul_comm, smul_mul_assoc]
    _ = 1 + u • intMap d.1.Closure X := by rw [hPP, hP.eq, mul_assoc, hPP, mul_one]

variable (d)

theorem hasWitness_theta (hodd : d.1.characteristic ≠ 2) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * 4) := by
  have h4 := four_le d
  have h2 := two_ne_zero_closure d hodd
  set R := rootData d.1.rank h4 d.1.Closure with hR
  have hCM : R.CM = CartanMatrix.D d.1.rank := rfl
  let H : Subgroup R.G := fixedSubgroup d.steinberg
  have hF := isTwistedFrobenius d
  set σ := frob d
  set fa := forkA d.1.rank h4
  set fb := forkB d.1.rank h4
  set z : Fin d.1.rank := ⟨0, by omega⟩
  set o : Fin d.1.rank := ⟨1, by omega⟩
  have hp : R.IsDisjointPair fa fb := isDisjointPair_fork d.1.rank h4 d.1.Closure
  have hm1F : σ ((-1 : d.1.Closureˣ) : d.1.Closure) = ((-1 : d.1.Closureˣ) : d.1.Closure) := by
    simp
  have hneg : (-1 : d.1.Closure) ≠ 1 := fun h => h2 (by
    rw [← one_add_one_eq_two]
    nth_rewrite 1 [← h]
    exact neg_add_cancel 1)
  have hm1 : (-1 : d.1.Closureˣ) ≠ 1 := fun h => hneg (by
    have := congrArg (fun v : d.1.Closureˣ => (v : d.1.Closure)) h
    simpa using this)
  obtain ⟨hxy, hXY⟩ := mem_commutator_of_unit hm1F hm1
  have hz : z.val < d.1.rank - 2 := by simp only [z]; omega
  have ho : o.val < d.1.rank - 2 := by simp only [o]; omega
  have hzo : z ≠ o := fin_ne (by simp [z, o])
  have hzfa : z ≠ fa := fin_ne (show 0 ≠ d.1.rank - 2 by omega)
  have hzfb : z ≠ fb := fin_ne (show 0 ≠ d.1.rank - 1 by omega)
  have hzv : z.val = 0 := rfl
  have hov : o.val = 1 := rfl
  have hfav : fa.val = d.1.rank - 2 := rfl
  have hfbv : fb.val = d.1.rank - 1 := rfl
  have hCMza : R.CM z fa = 0 := by
    rw [hCM, D_apply, hzv, hfav]
    d_entry
  have hCMzb : R.CM z fb = 0 := by
    rw [hCM, D_apply, hzv, hfbv]
    d_entry
  have hF0 : R.IsFrobenius (RingHom.id d.1.Closure) (MonoidHom.id R.G) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun s => by
      simp only [MonoidHom.id_apply]
      congr 1⟩
  have hfin : Finite (fixedField2 d) := Nat.finite_of_card_ne_zero (by
    rw [card_fixedField2]
    exact pow_ne_zero _ d.1.characteristic_prime.ne_zero)
  obtain ⟨μ, hμL, hμ2⟩ := exists_unit_sq_ne_one (fixedField2 d) (by
    rw [card_fixedField2]
    have h3 : 3 ≤ d.1.characteristic := by
      have := d.1.characteristic_prime.two_le
      omega
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ d.1.characteristic ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ d.1.characteristic ^ (2 * d.1.fieldExponent) :=
        Nat.pow_le_pow_right (by omega) (by
          have : 0 < d.1.fieldExponent := d.1.1.fieldExponent_pos
          omega))
  have hR0 := R.rootsInCommutator_of_unit hF0 (fun j => CartanMatrix.D_diag _ j)
    (show (μ : d.1.Closure) ∈ RootData.fixedField (RingHom.id d.1.Closure) from rfl) hμ2
  obtain ⟨Xt, hXt, hXt0⟩ := exists_rootOp_theta (hn := h4) (H := fixedSubgroup (MonoidHom.id R.G))
    fun i u hu => (hR0 i u hu).1
  obtain ⟨Yt, hYt, hYt0⟩ := exists_rootOp_thetaY (hn := h4) (H := fixedSubgroup (MonoidHom.id R.G))
    fun i u hu => (hR0 i u hu).2
  obtain ⟨hgX, hgY⟩ := graph_commute_theta (K := d.1.Closure) h4 hXt hYt
  set s : Fin d.1.rank → d.1.Closureˣ := Pi.mulSingle o (-1)
  have hsH : R.torus s ∈ H := by
    refine torus_mem_fixed_tw hF fun j => ?_
    simp only [s]
    by_cases hj : j = o
    · rw [hj, perm_of_lt d ho, Pi.mulSingle_eq_same]
      exact hm1F
    · have hj' : perm d j ≠ o := fun h => hj (by
        rw [← perm_of_lt d ho] at h
        exact (perm d).injective h)
      rw [Pi.mulSingle_eq_of_ne hj', Pi.mulSingle_eq_of_ne hj, Units.val_one, map_one]
  have hprod : ∀ (t : Fin d.1.rank) (v : Fin d.1.rank → ℤ),
      (∏ j, (Pi.mulSingle t (-1 : d.1.Closureˣ)) j ^ v j) = (-1 : d.1.Closureˣ) ^ v t :=
    fun t v => by
      rw [Finset.prod_eq_single t (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
        (fun h => absurd (Finset.mem_univ _) h), Pi.mulSingle_eq_same]
  have hwo : epsW d.1.rank 0 o + epsW d.1.rank 1 o = 1 := by
    simp only [epsW, o]
    split_ifs <;> omega
  have hwz : epsW d.1.rank 0 z + epsW d.1.rank 1 z = 0 := by
    simp only [epsW, z]
    split_ifs <;> omega
  have hm1L : ((-1 : d.1.Closureˣ) : d.1.Closure) ∈ RootData.fixedField σ := hm1F
  have hXtR : R.RootOp H (RootData.fixedField σ) (intMap d.1.Closure Xt)
      (fun j => epsW d.1.rank 0 j + epsW d.1.rank 1 j) := by
    refine hXt0.of_conj (fun u hu g hg => steinberg_eq_of_commute hgX hu hg) s hsH ?_ ?_
    · rw [hprod, hwo, zpow_one]
      exact fun h => hm1 (Units.ext h)
    · rw [hprod, hwo, zpow_one]
      exact hm1L
  have hYtR : R.RootOp H (RootData.fixedField σ) (intMap d.1.Closure Yt)
      (fun j => -(epsW d.1.rank 0 j + epsW d.1.rank 1 j)) := by
    refine hYt0.of_conj (fun u hu g hg => steinberg_eq_of_commute hgY hu hg) s hsH ?_ ?_
    · rw [hprod, hwo, zpow_neg_one, inv_neg_one]
      exact fun h => hm1 (Units.ext h)
    · rw [hprod, hwo, zpow_neg_one, inv_neg_one]
      exact hm1L
  have hmx : ∀ i u, R.mat (R.x i u) = 1 + u • R.E i := fun i u => by
    rw [mat_x, SqZeroPair.φ_upper]
  have hmy : ∀ i u, R.mat (R.y i u) = 1 + u • R.F i := fun i u => by
    rw [mat_y, SqZeroPair.φ_lower]
  have hE0 := (isIntOp_E d.1.rank h4 z).congr (chainE_eq d.1.rank (by omega) z (by simp [z]; omega))
  have hF0 := (isIntOp_F d.1.rank h4 z).congr (chainF_eq d.1.rank (by omega) z (by simp [z]; omega))
  have c1 : Commute (intMap d.1.Closure Xt) (R.E z) :=
    intMap_commute_of hXt hE0 ((P_E _).trans (E_P _ hzo).symm)
  have c2 : Commute (intMap d.1.Closure Xt) (R.F z) :=
    intMap_commute_of hXt hF0 ((P_F _).trans (F_P _ hzo).symm)
  have c3 : Commute (intMap d.1.Closure Yt) (R.E z) :=
    intMap_commute_of hYt hE0 ((N_E _ hzo).trans (E_N _).symm)
  have hfa2 : 2 ≤ fa.val := show 2 ≤ d.1.rank - 2 by omega
  have hfb2 : 2 ≤ fb.val := show 2 ≤ d.1.rank - 1 by omega
  obtain ⟨a1, a2, -, -⟩ := commute_simple_of_two_le h4 fa hfa2 z o (by simp [z]) (by simp [o])
  obtain ⟨-, -, a3, -⟩ := commute_simple_of_two_le h4 fa hfa2 o z (by simp [o]) (by simp [z])
  obtain ⟨b1, b2, -, -⟩ := commute_simple_of_two_le h4 fb hfb2 z o (by simp [z]) (by simp [o])
  obtain ⟨-, -, b3, -⟩ := commute_simple_of_two_le h4 fb hfb2 o z (by simp [o]) (by simp [z])
  have da1 : Commute (intMap d.1.Closure Xt) (R.E fa) :=
    intMap_commute_of hXt (isIntOp_E _ h4 fa) a1.eq
  have da2 : Commute (intMap d.1.Closure Xt) (R.F fa) :=
    intMap_commute_of hXt (isIntOp_F _ h4 fa) a2.eq
  have da3 : Commute (intMap d.1.Closure Yt) (R.E fa) :=
    intMap_commute_of hYt (isIntOp_E _ h4 fa) a3.eq
  have db1 : Commute (intMap d.1.Closure Xt) (R.E fb) :=
    intMap_commute_of hXt (isIntOp_E _ h4 fb) b1.eq
  have db2 : Commute (intMap d.1.Closure Xt) (R.F fb) :=
    intMap_commute_of hXt (isIntOp_F _ h4 fb) b2.eq
  have db3 : Commute (intMap d.1.Closure Yt) (R.E fb) :=
    intMap_commute_of hYt (isIntOp_E _ h4 fb) b3.eq
  set Fq := RootData.fixedField σ
  set L2 := fixedField2 d
  let L : Unit ⊕ Unit ⊕ Unit → Subfield d.1.Closure :=
    Sum.elim (fun _ => Fq) (Sum.elim (fun _ => Fq) (fun _ => L2))
  let g : Unit ⊕ Unit ⊕ Unit → d.1.Closure → R.G :=
    Sum.elim (fun _ => R.x z) (Sum.elim (fun _ => hXtR.elt) (fun _ => R.pairX σ fa fb))
  have hg : ∀ c u v, g c (u + v) = g c u * g c v := by
    rintro (_ | _ | _) u v
    · exact R.x_add _ u v
    · exact hXtR.elt_add u v
    · exact pairX_add (D_forkA_forkB d) u v
  have hg0 : ∀ c, g c 0 = 1 := by
    rintro (_ | _ | _)
    · exact R.x_zero _
    · exact hXtR.elt_zero
    · change R.x fa 0 * R.x fb (σ 0) = 1
      rw [map_zero, x_zero, x_zero, mul_one]
  let ϕ : ∀ c, Multiplicative (L c) →* R.G := fun c =>
    { toFun := fun u => g c ((Multiplicative.toAdd u : L c) : d.1.Closure)
      map_one' := hg0 c
      map_mul' := fun u v => hg c _ _ }
  have cx : ∀ u v, Commute (R.x z u) (hXtR.elt v) := fun u v =>
    R.commute_of_mat (by rw [hmx, hXtR.mat_elt]; exact commute_one_add_smul c1.symm u v)
  have cp : ∀ u v, Commute (hXtR.elt u) (R.pairX σ fa fb v) := fun u v =>
    (R.commute_of_mat (by rw [hXtR.mat_elt, hmx]; exact commute_one_add_smul da1 _ _)).mul_right
      (R.commute_of_mat (by rw [hXtR.mat_elt, hmx]; exact commute_one_add_smul db1 _ _))
  have cz : ∀ u v, Commute (R.x z u) (R.pairX σ fa fb v) := fun u v =>
    (R.commute_x_x hCMza _ _).mul_right (R.commute_x_x hCMzb _ _)
  have hcomm : Pairwise fun c c' => ∀ u v, Commute (ϕ c u) (ϕ c' v) := by
    rintro (_ | _ | _) (_ | _ | _) hne u v
    · exact absurd rfl hne
    · exact cx _ _
    · exact cz _ _
    · exact (cx _ _).symm
    · exact absurd rfl hne
    · exact cp _ _
    · exact (cz _ _).symm
    · exact (cp _ _).symm
    · exact absurd rfl hne
  have hD : ∀ c u, ϕ c u ∈ ⁅H, H⁆ := by
    rintro (_ | _ | _) u
    · exact (hxy z hz _ (Multiplicative.toAdd u).2).1
    · exact hXtR.elt_mem (Multiplicative.toAdd u).2
    · exact (hXY _ (Multiplicative.toAdd u).2).1
  have hpc : ∀ c (u : L c), d.1.characteristic • u = 0 := fun c u => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rfl)
  have hcard : Nat.card (∀ c, Multiplicative (L c)) =
      d.1.characteristic ^ (d.1.fieldExponent * 4) := by
    have e1 : ∀ c, Nat.card (Multiplicative (L c)) = Nat.card (L c) := fun c =>
      Nat.card_congr Multiplicative.toAdd
    rw [Nat.card_pi, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [e1]
    change (∏ _a : Unit, Nat.card Fq) * ((∏ _a : Unit, Nat.card Fq) * (∏ _u : Unit, Nat.card L2))
      = _
    rw [card_fixedField_frob, card_fixedField2]
    simp only [Finset.univ_unique, Finset.prod_singleton, ← pow_add]
    congr 1
    ring
  let y : Unit ⊕ Unit ⊕ Unit → R.G :=
    Sum.elim (fun _ => R.y z 1) (Sum.elim (fun _ => hYtR.elt 1) (fun _ => R.pairY σ fa fb 1))
  have hy : ∀ c, y c ∈ ⁅H, H⁆ := by
    rintro (_ | _ | _)
    · exact (hxy z hz 1 (map_one _)).2
    · exact hYtR.elt_mem (RootData.fixedField σ).one_mem
    · exact (hXY 1 (by simp)).2
  have hdet : ∀ c u, Commute (ϕ c u) (y c) → u = 1 := by
    rintro (_ | _ | _) u h
    · exact Multiplicative.toAdd.injective (Subtype.ext (R.eq_zero_of_commute_x_y h))
    · exact Multiplicative.toAdd.injective (Subtype.ext (R.eq_zero_of_commute_sqZeroPair
        (theta_sqZeroPair h4 hXt hYt hXtR.sq hYtR.sq) (theta_ne_zero h4 hXt) (hXtR.mat_elt _)
        (show R.mat (hYtR.elt 1) = 1 + intMap d.1.Closure Yt by rw [hYtR.mat_elt, one_smul]) h))
    · exact Multiplicative.toAdd.injective (Subtype.ext (eq_zero_of_commute_pairX_pairY hp h))
  have ty : ∀ u, Commute (hXtR.elt u) (R.y z 1) := fun u =>
    R.commute_of_mat (by rw [hXtR.mat_elt, hmy]; exact commute_one_add_smul c2 _ _)
  have tx : ∀ i u, Commute (R.E i) (intMap d.1.Closure Yt) →
      Commute (R.x i u) (hYtR.elt 1) := fun i u hc =>
    R.commute_of_mat (by rw [hmx, hYtR.mat_elt]; exact commute_one_add_smul hc _ _)
  have tyf : ∀ i u, Commute (intMap d.1.Closure Xt) (R.F i) →
      Commute (hXtR.elt u) (R.y i 1) := fun i u hc =>
    R.commute_of_mat (by rw [hXtR.mat_elt, hmy]; exact commute_one_add_smul hc _ _)
  have hoff : ∀ c c', c ≠ c' → ∀ u, Commute (ϕ c' u) (y c) := by
    rintro (_ | _ | _) (_ | _ | _) hne u
    · exact absurd rfl hne
    · exact ty _
    · exact (R.commute_x_y (Ne.symm hzfa) _ _).mul_left (R.commute_x_y (Ne.symm hzfb) _ _)
    · exact tx z _ c3.symm
    · exact absurd rfl hne
    · exact (tx fa _ da3.symm).mul_left (tx fb _ db3.symm)
    · exact (R.commute_x_y hzfa _ _).mul_right (R.commute_x_y hzfb _ _)
    · have e1 := tyf fa ((Multiplicative.toAdd u : L (Sum.inr (Sum.inl ()))) : _) da2
      have e2 := tyf fb ((Multiplicative.toAdd u : L (Sum.inr (Sum.inl ()))) : _) db2
      rw [← map_one σ] at e2
      exact e1.mul_right e2
    · exact absurd rfl hne
  have htD : R.h z (-1) ∈ ⁅H, H⁆ :=
    h_mem_of_xy (R := R) (fun u hu => (hxy z hz u hu).1) (fun u hu => (hxy z hz u hu).2) hm1F
  have ht2 : R.h z (-1) ^ 2 = 1 := by
    rw [RootData.h, ← map_pow, ← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one, map_one]
  have hzo' : Odd (CartanMatrix.D d.1.rank z o) := by
    rw [Int.odd_iff, D_apply, hzv, hov]
    d_entry
  have htz : ∃ g ∈ ⁅H, H⁆, R.h z (-1) * g ≠ g * R.h z (-1) := by
    refine ⟨R.x o 1, (hxy o ho 1 (map_one _)).1, fun hc => ?_⟩
    have h1 := R.h_conj_x z o (-1) 1
    rw [hc, mul_inv_cancel_right, hCM, hzo'.neg_one_zpow, Units.val_neg, Units.val_one,
      mul_one] at h1
    exact hneg (R.x_injective o h1).symm
  have hEz : ∀ j : Fin d.1.rank, CartanMatrix.D d.1.rank z j = 0 →
      Even (CartanMatrix.D d.1.rank z j) := fun j h => by rw [h]; exact ⟨0, rfl⟩
  have ht : ∀ c u, Commute (R.h z (-1)) (ϕ c u) := by
    rintro (_ | _ | _) u
    · have h1 := R.h_conj_x z z (-1) ((Multiplicative.toAdd u : L (Sum.inl ())) : _)
      rw [hCM, CartanMatrix.D_diag, even_two.neg_one_zpow, Units.val_one, one_mul] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    · exact hXtR.commute_torus (by rw [hprod, hwz, zpow_zero]) _
    · have h1 := R.h_conj_x z fa (-1) ((Multiplicative.toAdd u : L (Sum.inr (Sum.inr ()))) : _)
      have h1' := R.h_conj_x z fb (-1)
        (σ ((Multiplicative.toAdd u : L (Sum.inr (Sum.inr ()))) : _))
      rw [hCM, (hEz fa hCMza).neg_one_zpow, Units.val_one, one_mul] at h1
      rw [hCM, (hEz fb hCMzb).neg_one_zpow, Units.val_one, one_mul] at h1'
      have e1 : Commute (R.h z (-1)) (R.x fa _) := mul_inv_eq_iff_eq_mul.mp h1
      have e2 : Commute (R.h z (-1)) (R.x fb _) := mul_inv_eq_iff_eq_mul.mp h1'
      exact e1.mul_right e2
  exact family_witness ϕ hcomm hD hpc hcard y hy hdet hoff _ htD ht2 htz ht

end CarrierTD

end CFSG.RankThree.PartTwo.Census.Spin
