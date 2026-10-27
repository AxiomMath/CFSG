module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Three
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigRank
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.H13.L3321

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.Lift

abbrev P2 : Subgroup SL4 := FLc.QI 4 {2}

theorem mem_P2_iff (g : SL4) : g ∈ P2 ↔
    ∀ k l : Fin 4, (l : ℕ) < 2 → 2 ≤ (k : ℕ) → (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) k l = 0 := by
  constructor
  · intro hg k l hl hk
    exact stabilizer_entries (mem_flagStabilizer.1 hg 2 rfl) hl hk
  · intro h
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact h k l hl hk

theorem P2_stab : ∀ g ∈ P2, g ∈ stabilizer (flagSpace 4 (ZMod 2) 2) :=
  fun _ hg => mem_flagStabilizer.1 hg 2 rfl

theorem blockRight_A : BlockRight P2 0 2 := blockRight_of_stabilizer P2_stab

theorem blockLeft_C : BlockLeft P2 2 2 := blockLeft_of_stabilizer P2_stab

@[expose] noncomputable def blkAM : ↥P2 →* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  blkMon P2 0 2 (by norm_num) (blockLeft_zero P2 2) blockRight_A

@[expose] noncomputable def blkCM : ↥P2 →* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  blkMon P2 2 2 (by norm_num) blockLeft_C (blockRight_top P2 (by norm_num))

theorem blkAM_apply (g : ↥P2) (i j : Fin 2) :
    blkAM g i j = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  rw [blkAM, blkMon_apply, blkAt_apply]
  simp only [zero_add]

theorem blkCM_apply (g : ↥P2) (i j : Fin 2) :
    blkCM g i j = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨2 + i, by omega⟩ ⟨2 + j, by omega⟩ :=
  rfl

theorem det_eq_one_of_mul {M N : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : M * N = 1) : M.det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h1
  have h2 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one h1
  revert h2
  generalize M.det = x
  revert x
  decide

@[expose] noncomputable def blkA : ↥P2 →* SL2F2 where
  toFun g := ⟨blkAM g, det_eq_one_of_mul (N := blkAM g⁻¹)
    (by rw [← map_mul, mul_inv_cancel, map_one])⟩
  map_one' := Subtype.ext (map_one blkAM)
  map_mul' g h := Subtype.ext (map_mul blkAM g h)

@[expose] noncomputable def blkC : ↥P2 →* SL2F2 where
  toFun g := ⟨blkCM g, det_eq_one_of_mul (N := blkCM g⁻¹)
    (by rw [← map_mul, mul_inv_cancel, map_one])⟩
  map_one' := Subtype.ext (map_one blkCM)
  map_mul' g h := Subtype.ext (map_mul blkCM g h)

theorem coe_blkA (g : ↥P2) : ((blkA g : SL2F2) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = blkAM g := rfl

theorem coe_blkC (g : ↥P2) : ((blkC g : SL2F2) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = blkCM g := rfl

noncomputable abbrev gam : MulAut SL4 := BinaryParabolic.graphAut 4

theorem gam_apply_coe (g : SL4) (k l : Fin 4) :
    ((gam g : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) k l =
      ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) (Fin.rev l) (Fin.rev k) := by
  rw [BinaryParabolic.graphAut_apply, BinaryParabolic.coe_graphFun]
  rfl

theorem gam_gam (g : SL4) : gam (gam g) = g := BinaryParabolic.graphFun_graphFun g

theorem gam_mul_gam : gam * gam = 1 := MulEquiv.ext gam_gam

theorem gam_mem {g : SL4} (hg : g ∈ P2) : gam g ∈ P2 := by
  have hg' := (mem_P2_iff g⁻¹).1 (P2.inv_mem hg)
  refine (mem_P2_iff _).2 fun k l hl hk => ?_
  rw [gam_apply_coe]
  refine hg' (Fin.rev l) (Fin.rev k) ?_ ?_
  · rw [Fin.val_rev]
    omega
  · rw [Fin.val_rev]
    omega

theorem map_gam_P2 : P2.map gam.toMonoidHom = P2 := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact gam_mem hg
  · intro g hg
    exact ⟨gam g, gam_mem hg, gam_gam g⟩

@[expose] noncomputable def gamP : MulAut ↥P2 :=
  (gam.subgroupMap P2).trans (MulEquiv.subgroupCongr map_gam_P2)

theorem coe_gamP (g : ↥P2) : ((gamP g : ↥P2) : SL4) = gam g := rfl

theorem gamP_mul_gamP : gamP * gamP = 1 :=
  MulEquiv.ext fun g => Subtype.ext (gam_gam (g : SL4))

theorem rev_transpose_eq : ∀ N N' : Matrix (Fin 2) (Fin 2) (ZMod 2), N' * N = 1 →
    Matrix.of (fun i j => N' (Fin.rev j) (Fin.rev i)) = N := by
  decide +kernel

theorem rev_four_lo (j : Fin 2) :
    Fin.rev (⟨j, by omega⟩ : Fin 4) = ⟨2 + (Fin.rev j : ℕ), by have := (Fin.rev j).isLt; omega⟩ :=
  Fin.ext (by simp only [Fin.val_rev]; omega)

theorem rev_four_hi (j : Fin 2) :
    Fin.rev (⟨2 + j, by omega⟩ : Fin 4) = ⟨(Fin.rev j : ℕ), by have := (Fin.rev j).isLt; omega⟩ :=
  Fin.ext (by simp only [Fin.val_rev]; omega)

theorem blkAM_gamP (g : ↥P2) : blkAM (gamP g) = blkCM g := by
  have hinv : blkCM g⁻¹ * blkCM g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have key := rev_transpose_eq (blkCM g) (blkCM g⁻¹) hinv
  funext i j
  have hij := congrFun (congrFun key i) j
  rw [Matrix.of_apply] at hij
  rw [← hij, blkAM_apply, coe_gamP, gam_apply_coe, blkCM_apply, rev_four_lo, rev_four_lo]
  rfl

theorem blkCM_gamP (g : ↥P2) : blkCM (gamP g) = blkAM g := by
  have hinv : blkAM g⁻¹ * blkAM g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have key := rev_transpose_eq (blkAM g) (blkAM g⁻¹) hinv
  funext i j
  have hij := congrFun (congrFun key i) j
  rw [Matrix.of_apply] at hij
  rw [← hij, blkCM_apply, coe_gamP, gam_apply_coe, blkAM_apply, rev_four_hi, rev_four_hi]
  rfl

@[expose] def homZ2 {X : Type*} [Group X] (x : X) (hx : x * x = 1) :
    Multiplicative (ZMod 2) →* X where
  toFun k := x ^ (Multiplicative.toAdd k).val
  map_one' := by
    show x ^ (0 : ZMod 2).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' a b := by
    have hx2 : ∀ n : ℕ, x ^ (n % 2) = x ^ n := fun n => by
      conv_rhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, sq, hx, one_pow, mul_one]
    show x ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val = _
    rw [ZMod.val_add, hx2, pow_add]

theorem homZ2_one' {X : Type*} [Group X] (x : X) (hx : x * x = 1) :
    homZ2 x hx (Multiplicative.ofAdd 1) = x := by
  show x ^ (1 : ZMod 2).val = x
  rw [ZMod.val_one, pow_one]

theorem mult_z2_cases (k : Multiplicative (ZMod 2)) : k = 1 ∨ k = Multiplicative.ofAdd 1 := by
  revert k
  decide

@[expose] noncomputable def thetaG : Multiplicative (ZMod 2) →* MulAut ↥P2 :=
  homZ2 gamP gamP_mul_gamP

abbrev Pgam : Type := ↥P2 ⋊[thetaG] Multiplicative (ZMod 2)

@[expose] noncomputable def xiHom : Pgam →* MulAut SL4 :=
  SemidirectProduct.lift (MulAut.conj.comp P2.subtype) (homZ2 gam gam_mul_gam) (by
    intro k
    rcases mult_z2_cases k with rfl | rfl
    · rw [map_one, map_one]
      ext g x
      simp
    · ext g x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [thetaG, homZ2_one', homZ2_one', coe_gamP, ← SteinbergCD.mulAut_mul_conj_mul_inv]
      rfl)

theorem xiHom_mk (g : ↥P2) (k : Multiplicative (ZMod 2)) :
    xiHom ⟨g, k⟩ = MulAut.conj (g : SL4) * homZ2 gam gam_mul_gam k := rfl

theorem xiHom_injective : Function.Injective xiHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨g, k⟩ hgk
  rw [MonoidHom.mem_ker, xiHom_mk] at hgk
  rcases mult_z2_cases k with rfl | rfl
  · rw [map_one, mul_one] at hgk
    have h1 : (g : SL4) = 1 := by
      apply SteinbergCD.injective_conj_binarySL 4
      rw [hgk, map_one]
    rw [Subgroup.mem_bot]
    exact SemidirectProduct.ext (Subtype.ext h1) rfl
  · exfalso
    rw [homZ2_one'] at hgk
    apply SteinbergCD.graphAut_ne_conj (n := 4) (by norm_num) (g : SL4)⁻¹
    calc BinaryParabolic.graphAut 4 = (MulAut.conj (g : SL4))⁻¹ * (MulAut.conj (g : SL4) * gam) :=
          by group
      _ = MulAut.conj (g : SL4)⁻¹ := by rw [hgk, mul_one, map_inv]

open CFSG.Quasithin.S152N

@[expose] def baseW : (Multiplicative (ZMod 2) → Equiv.Perm (Fin 3)) →* W3 where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by
    show (⟨f * g, 1⟩ : W3) = ⟨f * fun x => g (1⁻¹ * x), 1 * 1⟩
    simp

@[expose] noncomputable def betaB : ↥P2 →* (Multiplicative (ZMod 2) → Equiv.Perm (Fin 3)) where
  toFun g q := if q = 1 then sl2F2EquivPerm3 (blkA g) else sl2F2EquivPerm3 (blkC g)
  map_one' := by
    funext q
    simp
  map_mul' g h := by
    funext q
    by_cases hq : q = 1 <;> simp [hq]

theorem betaB_gamP (g : ↥P2) (x : Multiplicative (ZMod 2)) :
    betaB (gamP g) x = betaB g ((Multiplicative.ofAdd 1)⁻¹ * x) := by
  have hA : blkA (gamP g) = blkC g := Subtype.ext (blkAM_gamP g)
  have hC : blkC (gamP g) = blkA g := Subtype.ext (blkCM_gamP g)
  show (if x = 1 then sl2F2EquivPerm3 (blkA (gamP g)) else sl2F2EquivPerm3 (blkC (gamP g))) =
    (if (Multiplicative.ofAdd 1)⁻¹ * x = 1 then sl2F2EquivPerm3 (blkA g)
      else sl2F2EquivPerm3 (blkC g))
  rcases mult_z2_cases x with rfl | rfl
  · have : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ * 1 ≠ 1 := by decide
    rw [ite_eq_left rfl, ite_eq_right this, hA]
  · have h1 : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ * Multiplicative.ofAdd 1 = 1 := by decide
    have h2 : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    rw [ite_eq_right h2, ite_eq_left h1, hC]

theorem inl_conj_baseW (k : Multiplicative (ZMod 2))
    (f : Multiplicative (ZMod 2) → Equiv.Perm (Fin 3)) :
    RegularWreathProduct.inl k * baseW f * (RegularWreathProduct.inl k)⁻¹ =
      baseW (fun x => f (k⁻¹ * x)) := by
  apply RegularWreathProduct.ext
  · funext x
    simp [baseW, RegularWreathProduct.mul_def, RegularWreathProduct.inv_left,
      RegularWreathProduct.left_inl, RegularWreathProduct.right_inl]
  · simp [baseW, RegularWreathProduct.mul_def, RegularWreathProduct.inv_right,
      RegularWreathProduct.right_inl]

@[expose] noncomputable def chiHom : Pgam →* W3 :=
  SemidirectProduct.lift (baseW.comp betaB) RegularWreathProduct.inl (by
    intro k
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inl_conj_baseW]
    congr 1
    funext x
    rcases mult_z2_cases k with rfl | rfl
    · rw [map_one, inv_one, one_mul]
      rfl
    · rw [thetaG, homZ2_one']
      exact betaB_gamP g x)

theorem chiHom_mk (g : ↥P2) (k : Multiplicative (ZMod 2)) :
    chiHom ⟨g, k⟩ = baseW (betaB g) * RegularWreathProduct.inl k := rfl

@[expose] def diagM (A C : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, C 0 0, C 0 1; 0, 0, C 1 0, C 1 1]

theorem det_diagM : ∀ A C : SL2F2,
    (diagM (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (C : Matrix (Fin 2) (Fin 2) (ZMod 2))).det =
      1 := by
  decide +kernel

@[expose] def diagSL (A C : SL2F2) : SL4 := ⟨diagM A C, det_diagM A C⟩

theorem diagSL_mem (A C : SL2F2) : diagSL A C ∈ P2 := by
  rw [mem_P2_iff]
  intro k l hl hk
  have hk' : k = 2 ∨ k = 3 := by omega
  have hl' : l = 0 ∨ l = 1 := by omega
  rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl <;> rfl

theorem blkA_diagSL (A C : SL2F2) : blkA ⟨diagSL A C, diagSL_mem A C⟩ = A := by
  apply Subtype.ext
  funext i j
  rw [coe_blkA, blkAM_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem blkC_diagSL (A C : SL2F2) : blkC ⟨diagSL A C, diagSL_mem A C⟩ = C := by
  apply Subtype.ext
  funext i j
  rw [coe_blkC, blkCM_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem chiHom_surjective : Function.Surjective chiHom := by
  rintro ⟨f, k⟩
  set A := sl2F2EquivPerm3.symm (f 1)
  set C := sl2F2EquivPerm3.symm (f (Multiplicative.ofAdd 1))
  refine ⟨⟨⟨diagSL A C, diagSL_mem A C⟩, k⟩, ?_⟩
  rw [chiHom_mk]
  apply RegularWreathProduct.ext
  · funext x
    simp only [baseW, RegularWreathProduct.mul_def, RegularWreathProduct.left_inl,
      MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply]
    show (if x = 1 then sl2F2EquivPerm3 (blkA ⟨diagSL A C, diagSL_mem A C⟩)
      else sl2F2EquivPerm3 (blkC ⟨diagSL A C, diagSL_mem A C⟩)) = f x
    rw [blkA_diagSL, blkC_diagSL]
    rcases mult_z2_cases x with rfl | rfl
    · rw [ite_eq_left rfl, MulEquiv.apply_symm_apply]
    · rw [ite_eq_right (by decide), MulEquiv.apply_symm_apply]
  · show 1 * k = k
    rw [one_mul]

theorem chiHom_eq_one {g : ↥P2} {k : Multiplicative (ZMod 2)} (h : chiHom ⟨g, k⟩ = 1) :
    k = 1 ∧ (g : SL4) ∈ FLc.Ut 4 := by
  rw [chiHom_mk] at h
  have hk : k = 1 := by
    have := congrArg RegularWreathProduct.right h
    simpa [baseW, RegularWreathProduct.mul_def] using this
  refine ⟨hk, ?_⟩
  subst hk
  rw [map_one, mul_one] at h
  have hb : betaB g = 1 := by
    have := congrArg RegularWreathProduct.left h
    exact this
  have hA : blkA g = 1 := by
    have h1 := congrFun hb 1
    have h2 : sl2F2EquivPerm3 (blkA g) = 1 := by
      simpa [betaB] using h1
    simpa using h2
  have hC : blkC g = 1 := by
    have h1 := congrFun hb (Multiplicative.ofAdd 1)
    have h2 : sl2F2EquivPerm3 (blkC g) = 1 := by
      have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
      simpa [betaB, hne] using h1
    simpa using h2
  have hAe : ∀ i j : Fin 2, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨i, by omega⟩ ⟨j, by omega⟩ =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := fun i j => by
    rw [← blkAM_apply, ← coe_blkA, hA]
    rfl
  have hCe : ∀ i j : Fin 2,
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨2 + i, by omega⟩ ⟨2 + j, by omega⟩ =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := fun i j => by
    rw [← blkCM_apply, ← coe_blkC, hC]
    rfl
  have hP := (mem_P2_iff (g : SL4)).1 g.2
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | exact hP _ _ (by decide) (by decide)
      | exact hAe 1 0
      | exact hCe 1 0
  · fin_cases i
    · exact hAe 0 0
    · exact hAe 1 1
    · exact hCe 0 0
    · exact hCe 1 1

theorem Ut_le_P2 : FLc.Ut 4 ≤ P2 := BinaryParabolic.unitriangular_le_flagStabilizer {2}

theorem exists_xiHom_of_map_Ut (φ : MulAut SL4) (hφ : (FLc.Ut 4).map φ.toMonoidHom = FLc.Ut 4) :
    ∃ (u : SL4) (hu : u ∈ FLc.Ut 4) (k : Multiplicative (ZMod 2)),
      φ = xiHom ⟨⟨u, Ut_le_P2 hu⟩, k⟩ := by
  have hU : ∀ h : SL4, (FLc.Ut 4).map (MulAut.conj h).toMonoidHom = FLc.Ut 4 → h ∈ FLc.Ut 4 := by
    intro h hh
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.2 hh
    rwa [normalizer_unitriangular, BinaryParabolic.upperTriangular_eq_unitriangular] at h1
  rcases SteinbergCD.aut_eq_conj_or_conj_mul_graphAut (n := 4) (by norm_num) φ with ⟨h, rfl⟩ |
    ⟨h, rfl⟩
  · have hu := hU h hφ
    refine ⟨h, hu, 1, ?_⟩
    rw [xiHom_mk, map_one, mul_one]
  · have hu : h ∈ FLc.Ut 4 := by
      apply hU h
      calc (FLc.Ut 4).map (MulAut.conj h).toMonoidHom
          = ((FLc.Ut 4).map gam.toMonoidHom).map (MulAut.conj h).toMonoidHom := by
            rw [BinaryParabolic.map_graphAut_unitriangular]
        _ = (FLc.Ut 4).map (MulAut.conj h * gam).toMonoidHom := by
            rw [Subgroup.map_map]
            rfl
        _ = FLc.Ut 4 := hφ
    refine ⟨h, hu, Multiplicative.ofAdd 1, ?_⟩
    rw [xiHom_mk, homZ2_one']

end CFSG.Quasithin.H13.L3321
