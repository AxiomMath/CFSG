module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSU
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Coker
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Cyc
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LieType.Chevalley.E6EvenRootTorus
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal

public section

namespace CFSG.StandardType.KGTwE6

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)


variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

section Realize

variable {σ : K →+* K}

theorem realize_mem_su6Levi (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (B : ↥(E6GraphLevi.unitarySL σ)) :
    E6GraphLevi.realize (CharP.cast_eq_zero K 2)
        (B : Matrix.SpecialLinearGroup (Fin 6) K) ∈ su6Levi σ := by
  have h := Subgroup.mem_map_of_mem (E6GraphLevi.realize (CharP.cast_eq_zero K 2)) B.2
  rw [su6Levi, (E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ
    (CharP.cast_eq_zero K 2)).1]
  exact h

theorem realize_mem_graphFixedRootGroup (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (B : ↥(E6GraphLevi.unitarySL σ)) :
    E6GraphLevi.realize (CharP.cast_eq_zero K 2)
        (B : Matrix.SpecialLinearGroup (Fin 6) K) ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
  (E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ
      (CharP.cast_eq_zero K 2)).2.2 (Subgroup.mem_map_of_mem _ B.2)

@[expose] noncomputable def su6LeviHom (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ↥(SU (unitaryInvolution K 2 f) 6) →*
      ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) where
  toFun B :=
    ⟨⟨E6GraphLevi.realize (CharP.cast_eq_zero K 2)
        (((E6GraphLevi.unitarySLEquiv hσ).symm B : ↥(E6GraphLevi.unitarySL σ)) :
          Matrix.SpecialLinearGroup (Fin 6) K),
      realize_mem_graphFixedRootGroup hK hσ _⟩,
      Subgroup.mem_subgroupOf.2 (realize_mem_su6Levi hK hσ _)⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    show E6GraphLevi.realize (CharP.cast_eq_zero K 2)
        (((E6GraphLevi.unitarySLEquiv hσ).symm 1 : ↥(E6GraphLevi.unitarySL σ)) :
          Matrix.SpecialLinearGroup (Fin 6) K) = 1
    simp
  map_mul' B₁ B₂ := by
    refine Subtype.ext (Subtype.ext ?_)
    show E6GraphLevi.realize (CharP.cast_eq_zero K 2)
        (((E6GraphLevi.unitarySLEquiv hσ).symm (B₁ * B₂) :
          ↥(E6GraphLevi.unitarySL σ)) : Matrix.SpecialLinearGroup (Fin 6) K) =
      E6GraphLevi.realize (CharP.cast_eq_zero K 2)
          (((E6GraphLevi.unitarySLEquiv hσ).symm B₁ : ↥(E6GraphLevi.unitarySL σ)) :
            Matrix.SpecialLinearGroup (Fin 6) K) *
        E6GraphLevi.realize (CharP.cast_eq_zero K 2)
          (((E6GraphLevi.unitarySLEquiv hσ).symm B₂ : ↥(E6GraphLevi.unitarySL σ)) :
            Matrix.SpecialLinearGroup (Fin 6) K)
    have h : (((E6GraphLevi.unitarySLEquiv hσ).symm (B₁ * B₂) :
        ↥(E6GraphLevi.unitarySL σ)) : Matrix.SpecialLinearGroup (Fin 6) K) =
        (((E6GraphLevi.unitarySLEquiv hσ).symm B₁ : ↥(E6GraphLevi.unitarySL σ)) :
          Matrix.SpecialLinearGroup (Fin 6) K) *
        (((E6GraphLevi.unitarySLEquiv hσ).symm B₂ : ↥(E6GraphLevi.unitarySL σ)) :
          Matrix.SpecialLinearGroup (Fin 6) K) := by
      rw [map_mul]
      rfl
    rw [h, map_mul]

theorem coe_su6LeviHom (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (B : ↥(SU (unitaryInvolution K 2 f) 6)) :
    ((su6LeviHom hK hσ B : ↥((su6Levi σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ))) : ModGL TwistTag.E6.tag K) =
      E6GraphLevi.realize (CharP.cast_eq_zero K 2)
        (((E6GraphLevi.unitarySLEquiv hσ).symm B : ↥(E6GraphLevi.unitarySL σ)) :
          Matrix.SpecialLinearGroup (Fin 6) K) :=
  rfl

theorem su6LeviHom_surjective (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : Function.Surjective (su6LeviHom hK hσ) := by
  intro y
  have hy : (y : ModGL TwistTag.E6.tag K) ∈
      Subgroup.map (E6GraphLevi.realize (CharP.cast_eq_zero K 2))
        (E6GraphLevi.unitarySL σ) := by
    rw [← (E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ
      (CharP.cast_eq_zero K 2)).1]
    exact Subgroup.mem_subgroupOf.1 y.2
  obtain ⟨B, hB, hreal⟩ := Subgroup.mem_map.1 hy
  refine ⟨E6GraphLevi.unitarySLEquiv hσ ⟨B, hB⟩, ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  show E6GraphLevi.realize (CharP.cast_eq_zero K 2)
      (((E6GraphLevi.unitarySLEquiv hσ).symm (E6GraphLevi.unitarySLEquiv hσ ⟨B, hB⟩) :
        ↥(E6GraphLevi.unitarySL σ)) : Matrix.SpecialLinearGroup (Fin 6) K) =
    (y : ModGL TwistTag.E6.tag K)
  rw [MulEquiv.symm_apply_apply]
  exact hreal

theorem ker_su6LeviHom_le_center (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (su6LeviHom hK hσ).ker ≤ Subgroup.center ↥(SU (unitaryInvolution K 2 f) 6) := by
  intro B hB
  rw [MonoidHom.mem_ker] at hB
  have hcoe : E6GraphLevi.realize (CharP.cast_eq_zero K 2)
      (((E6GraphLevi.unitarySLEquiv hσ).symm B : ↥(E6GraphLevi.unitarySL σ)) :
        Matrix.SpecialLinearGroup (Fin 6) K) = 1 := by
    have h := congrArg (fun z : ↥((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) => (z : ModGL TwistTag.E6.tag K)) hB
    rw [coe_su6LeviHom] at h
    simpa using h
  obtain ⟨l, -, hl⟩ := (E6GraphLevi.mem_ker_realize (E := K)
    (CharP.cast_eq_zero K 2) _).1 hcoe
  have hB' : (E6GraphLevi.unitarySLEquiv hσ).symm B ∈
      Subgroup.center ↥(E6GraphLevi.unitarySL σ) :=
    (E6GraphLevi.mem_center_unitarySL_iff hK hσ _).2 ⟨l, hl⟩
  have hmem := hB'
  rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv
    (E6GraphLevi.unitarySLEquiv hσ).symm] at hmem
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hmem
  rw [← (E6GraphLevi.unitarySLEquiv hσ).symm.injective hxy]
  exact hy

theorem largeEvenMarking_su6Levi (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LargeEvenMarking ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))
      (fun lab R _ I _ θ => GGChevStTag lab ∧
        ∀ α ∈ KGND.suConjSet (su6LeviHom hK hσ),
          ∃ φ ∈ I,
            ∀ y : ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)),
              φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) :=
  KGND.largeEvenMarking_suConjSet (F := K) hK hf (k := 6) (by norm_num)
    (fun h => absurd h (by norm_num)) _ (su6LeviHom_surjective hK hσ)
    (ker_su6LeviHom_le_center hK hσ)

section Tau

variable {σ : K →+* K}

private def beta (b : Fin TwistTag.E6.tag.rank → Kˣ) (t : Fin 5) : Kˣ := b (E6GraphLevi.pathIdx t)

private def tau (b : Fin TwistTag.E6.tag.rank → Kˣ) : Fin 6 → Kˣ :=
  ![1, (beta b 0)⁻¹, (beta b 0 * beta b 1)⁻¹,
    (beta b 0 * beta b 1 * beta b 2)⁻¹,
    (beta b 0 * beta b 1 * beta b 2 * beta b 3)⁻¹,
    (beta b 0 * beta b 1 * beta b 2 * beta b 3 * beta b 4)⁻¹]

private theorem tau_zero (b : Fin TwistTag.E6.tag.rank → Kˣ) : tau b 0 = 1 := rfl

private theorem tau_one (b : Fin TwistTag.E6.tag.rank → Kˣ) : tau b 1 = (beta b 0)⁻¹ :=
  rfl

private theorem tau_two (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    tau b 2 = (beta b 0 * beta b 1)⁻¹ :=
  rfl

private theorem tau_three (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    tau b 3 = (beta b 0 * beta b 1 * beta b 2)⁻¹ := rfl

private theorem tau_four (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    tau b 4 = (beta b 0 * beta b 1 * beta b 2 * beta b 3)⁻¹ := rfl

private theorem tau_five (b : Fin TwistTag.E6.tag.rank → Kˣ) :
    tau b 5 = (beta b 0 * beta b 1 * beta b 2 * beta b 3 * beta b 4)⁻¹ := rfl

private theorem tau_succ (b : Fin TwistTag.E6.tag.rank → Kˣ) (t : Fin 5) :
    tau b t.succ = tau b t.castSucc * (beta b t)⁻¹ := by
  fin_cases t <;> simp [tau] <;> ac_rfl

private theorem tau_coeff (b : Fin TwistTag.E6.tag.rank → Kˣ) (t : Fin 5) :
    tau b t.castSucc * (tau b t.succ)⁻¹ = b (E6GraphLevi.pathIdx t) := by
  have h := tau_succ b t
  rw [h, mul_inv_rev, inv_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel, one_mul]
  rfl

private theorem map_beta_zero (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    Units.map σ.toMonoidHom (beta b 0) = beta b 4 := by
  have hidx : TwistTag.E6.perm (E6GraphLevi.pathIdx 0) = E6GraphLevi.pathIdx 4 := by
    decide
  have h := hb (E6GraphLevi.pathIdx 0)
  rw [hidx] at h
  simpa only [beta] using h.symm

private theorem map_beta_one (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    Units.map σ.toMonoidHom (beta b 1) = beta b 3 := by
  have hidx : TwistTag.E6.perm (E6GraphLevi.pathIdx 1) = E6GraphLevi.pathIdx 3 := by
    decide
  have h := hb (E6GraphLevi.pathIdx 1)
  rw [hidx] at h
  simpa only [beta] using h.symm

private theorem map_beta_two (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    Units.map σ.toMonoidHom (beta b 2) = beta b 2 := by
  have hidx : TwistTag.E6.perm (E6GraphLevi.pathIdx 2) = E6GraphLevi.pathIdx 2 := by
    decide
  have h := hb (E6GraphLevi.pathIdx 2)
  rw [hidx] at h
  simpa only [beta] using h.symm

private theorem map_beta_three (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    Units.map σ.toMonoidHom (beta b 3) = beta b 1 := by
  have hidx : TwistTag.E6.perm (E6GraphLevi.pathIdx 3) = E6GraphLevi.pathIdx 1 := by
    decide
  have h := hb (E6GraphLevi.pathIdx 3)
  rw [hidx] at h
  simpa only [beta] using h.symm

private theorem map_beta_four (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    Units.map σ.toMonoidHom (beta b 4) = beta b 0 := by
  have hidx : TwistTag.E6.perm (E6GraphLevi.pathIdx 4) = E6GraphLevi.pathIdx 0 := by
    decide
  have h := hb (E6GraphLevi.pathIdx 4)
  rw [hidx] at h
  simpa only [beta] using h.symm

private theorem tau_mul_rev (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) (i : Fin 6) :
    Units.map σ.toMonoidHom (tau b i) * tau b (Fin.rev i) = tau b 5 := by
  have h0 := map_beta_zero b hb
  have h1 := map_beta_one b hb
  have h2 := map_beta_two b hb
  have h3 := map_beta_three b hb
  have h4 := map_beta_four b hb
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    fin_cases i <;> simp
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : tau b (Fin.rev (0 : Fin 6)) = tau b 5 := rfl
    rw [tau_zero, e, tau_five, map_one, one_mul]
  · have e : tau b (Fin.rev (1 : Fin 6)) = tau b 4 := rfl
    rw [tau_one, e, tau_four, tau_five]
    simp only [map_mul, map_inv, map_one, mul_inv_rev, h0, h1, h2, h3, h4,
      mul_comm, mul_left_comm, mul_assoc]
  · have e : tau b (Fin.rev (2 : Fin 6)) = tau b 3 := rfl
    rw [tau_two, e, tau_three, tau_five]
    simp only [map_mul, map_inv, map_one, mul_inv_rev, h0, h1, h2, h3, h4,
      mul_comm, mul_left_comm, mul_assoc]
  · have e : tau b (Fin.rev (3 : Fin 6)) = tau b 2 := rfl
    rw [tau_three, e, tau_two, tau_five]
    simp only [map_mul, map_inv, map_one, mul_inv_rev, h0, h1, h2, h3, h4,
      mul_comm, mul_left_comm, mul_assoc]
  · have e : tau b (Fin.rev (4 : Fin 6)) = tau b 1 := rfl
    rw [tau_four, e, tau_one, tau_five]
    simp only [map_mul, map_inv, map_one, mul_inv_rev, h0, h1, h2, h3, h4,
      mul_comm, mul_left_comm, mul_assoc]
  · have e : tau b (Fin.rev (5 : Fin 6)) = tau b 0 := rfl
    rw [tau_five, e, tau_zero]
    simp only [map_mul, map_inv, map_one, mul_inv_rev, h0, h1, h2, h3, h4,
      mul_comm, mul_left_comm, mul_assoc, one_mul]

private theorem map_tau_five (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    Units.map σ.toMonoidHom (tau b 5) = tau b 5 := by
  rw [tau_five]
  simp only [map_inv, map_mul, mul_inv_rev, map_beta_zero b hb, map_beta_one b hb,
    map_beta_two b hb, map_beta_three b hb, map_beta_four b hb,
    mul_comm, mul_left_comm, mul_assoc]

end Tau

section TorusAction

private theorem rootDiagUnit_conj_xUnit (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag b * xUnit TwistTag.E6.tag K i c *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      xUnit TwistTag.E6.tag K i (b i * c) := by
  rw [← pinnedX_single TwistTag.E6.tag K i c,
    ← pinnedX_single TwistTag.E6.tag K i (b i * c),
    rootDiagUnit_conj_pinnedX b (isRoot_single TwistTag.E6.tag i) c]
  congr 1
  have h : rootChar b (Pi.single i 1) = b i := by
    simpa using rootChar_nsmul_single b i 1
  rw [h]

private theorem rootDiagUnit_conj_yUnit (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    rootDiagUnit TwistTag.E6.tag b * yUnit TwistTag.E6.tag K i c *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      yUnit TwistTag.E6.tag K i ((b i)⁻¹ * c) := by
  rw [← pinnedX_neg_single TwistTag.E6.tag K i c,
    ← pinnedX_neg_single TwistTag.E6.tag K i ((b i)⁻¹ * c),
    rootDiagUnit_conj_pinnedX b (isRoot_neg_single TwistTag.E6.tag i) c]
  congr 1
  have h : rootChar b (-Pi.single i 1) = (b i)⁻¹ := by
    have h1 : rootChar b (-Pi.single i 1) =
        (rootChar b (Pi.single i 1))⁻¹ := by
      have := rootChar_sub b 0 (Pi.single i 1)
      simpa [rootChar_zero] using this
    rw [h1]
    have h2 : rootChar b (Pi.single i 1) = b i := by
      simpa using rootChar_nsmul_single b i 1
    rw [h2]
  rw [h]

private theorem rootDiagUnit_conj_realize (h2 : (2 : K) = 0) (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (B : Matrix.SpecialLinearGroup (Fin 6) K) :
    rootDiagUnit TwistTag.E6.tag b * E6GraphLevi.realize h2 B *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      E6GraphLevi.realize h2
        (InnerDiagA.conjSL (InnerDiagA.diagGL (tau b)) B) := by
  have key : (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom.comp
        (E6GraphLevi.realize h2) =
      (E6GraphLevi.realize h2).comp
        (InnerDiagA.conjSL (InnerDiagA.diagGL (tau b))) := by
    refine MonoidHom.eq_of_eqOn_dense (E6GraphLevi.closure_adjacentSet) ?_
    rintro _ ⟨t, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        E6GraphLevi.realize_x h2 t c, InnerDiagA.conjSL_diagGL_transvection,
        E6GraphLevi.realize_x h2, rootDiagUnit_conj_xUnit]
      congr 1
      rw [← tau_coeff b t]
      simp only [mul_comm, mul_left_comm, mul_assoc, Units.val_mul, Units.val_inv_eq_inv_val]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        E6GraphLevi.realize_y h2 t c, InnerDiagA.conjSL_diagGL_transvection,
        E6GraphLevi.realize_y h2, rootDiagUnit_conj_yUnit]
      congr 1
      rw [← tau_coeff b t, mul_inv_rev, inv_inv]
      simp only [mul_comm, mul_left_comm, mul_assoc, Units.val_mul, Units.val_inv_eq_inv_val]
  exact congrArg (fun φ : Matrix.SpecialLinearGroup (Fin 6) K →* ModGL TwistTag.E6.tag K =>
    φ B) key

end TorusAction

section Unitary

private theorem conjGL_diagGL_smul (lam : Kˣ) (d : Fin 6 → Kˣ) (X : GL (Fin 6) K) :
    InnerDiagA.diagGL (fun i => lam * d i) * X * (InnerDiagA.diagGL (fun i => lam * d i))⁻¹ =
      InnerDiagA.diagGL d * X * (InnerDiagA.diagGL d)⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

private theorem isJUnitary_diagGL_smul (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) (lam : Kˣ)
    (hlam : Units.map (unitaryInvolution K 2 f).toMonoidHom lam * lam = (tau b 5)⁻¹) :
    InnerDiagSU.IsJUnitary (unitaryInvolution K 2 f)
      (InnerDiagA.diagGL (fun i => lam * tau b i)) := by
  have hσu : ∀ s : Fin 6, Units.map (unitaryInvolution K 2 f).toMonoidHom (tau b s) =
      Units.map σ.toMonoidHom (tau b s) := by
    intro s
    apply Units.ext
    show (unitaryInvolution K 2 f) ((tau b s : Kˣ) : K) = σ ((tau b s : Kˣ) : K)
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hσ]
  have hdU : ∀ s : Fin 6,
      Units.map (unitaryInvolution K 2 f).toMonoidHom ((fun i => lam * tau b i) s) *
        (fun i => lam * tau b i) s.rev = 1 := by
    intro s
    show Units.map (unitaryInvolution K 2 f).toMonoidHom (lam * tau b s) *
      (lam * tau b s.rev) = 1
    rw [map_mul, hσu s]
    calc Units.map (unitaryInvolution K 2 f).toMonoidHom lam *
          Units.map σ.toMonoidHom (tau b s) * (lam * tau b s.rev)
        = (Units.map (unitaryInvolution K 2 f).toMonoidHom lam * lam) *
            (Units.map σ.toMonoidHom (tau b s) * tau b s.rev) := by ac_rfl
      _ = (tau b 5)⁻¹ * tau b 5 := by rw [hlam, tau_mul_rev b hb s]
      _ = 1 := inv_mul_cancel _
  have hd : ∀ s : Fin 6,
      unitaryInvolution K 2 f ((fun i => ((lam * tau b i : Kˣ) : K)) s) *
        ((fun i => ((lam * tau b i : Kˣ) : K)) s.rev) = 1 := by
    intro s
    have := congrArg (fun u : Kˣ => (u : K)) (hdU s)
    simpa using this
  have hdiag : InnerDiagA.diagGL (fun i => lam * tau b i) =
      InnerDiagSU.diagJ (fun i => ((lam * tau b i : Kˣ) : K)) hd := by
    apply Units.ext
    rw [InnerDiagA.coe_diagGL, InnerDiagSU.coe_diagJ]
  rw [hdiag]
  exact InnerDiagSU.isJUnitary_diagJ _ hd

private theorem exists_smul_tau_isJUnitary (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)) :
    ∃ lam : Kˣ, InnerDiagSU.IsJUnitary (unitaryInvolution K 2 f)
      (InnerDiagA.diagGL (fun i => lam * tau b i)) := by
  have hμ : Units.map (unitaryInvolution K 2 f).toMonoidHom (tau b 5) = tau b 5 := by
    have h1 : Units.map (unitaryInvolution K 2 f).toMonoidHom (tau b 5) =
        Units.map σ.toMonoidHom (tau b 5) := by
      apply Units.ext
      simp only [Units.coe_map]
      show (unitaryInvolution K 2 f) ((tau b 5 : Kˣ) : K) = σ ((tau b 5 : Kˣ) : K)
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hσ]
    rw [h1]
    exact map_tau_five b hb
  have hfix : unitaryInvolution K 2 f ((tau b 5 : Kˣ) : K) = ((tau b 5 : Kˣ) : K) := by
    have := congrArg (fun u : Kˣ => (u : K)) hμ
    simpa using this
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed (p := 2) (f := f)
    hK (d := ((tau b 5 : Kˣ) : K)) hfix (Units.ne_zero (tau b 5))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact Units.ne_zero (tau b 5) (by rw [← hc, mul_zero])
  have hcU : Units.map (unitaryInvolution K 2 f).toMonoidHom (Units.mk0 c hc0) *
      Units.mk0 c hc0 = tau b 5 := by
    apply Units.ext
    simpa [Units.coe_map, Units.val_mk0] using hc
  refine ⟨(Units.mk0 c hc0)⁻¹, isJUnitary_diagGL_smul hσ b hb (Units.mk0 c hc0)⁻¹ ?_⟩
  rw [map_inv (Units.map (unitaryInvolution K 2 f).toMonoidHom) (Units.mk0 c hc0),
    ← mul_inv, hcU]

end Unitary

section Levi

private theorem conj_rootDiagUnit_mem_su6Levi {σ : K →+* K} {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i))
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ su6Levi σ) :
    rootDiagUnit TwistTag.E6.tag b * x * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈ su6Levi σ := by
  rw [su6Levi] at hx ⊢
  refine ⟨?_, ?_⟩
  · exact RootTorus.conj_rootDiagUnit_mem_subsystemGroup E6GraphLevi.setA b hx.1
  · have hN := rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) (σ := σ) hb
    exact (Subgroup.mem_normalizer_iff.1 hN x).1 hx.2

private noncomputable def compatParamAutLevi (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (b : ↥(TableB.TwE6.compat σ)) :
    MulAut ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) where
  toFun l :=
    ⟨RootCentExc.compatParamAut σ b l.1, Subgroup.mem_subgroupOf.2 (by
      rw [RootCentExc.coe_compatParamAut_apply]
      exact conj_rootDiagUnit_mem_su6Levi ((TableB.TwE6.mem_compat σ).1 b.2)
        (Subgroup.mem_subgroupOf.1 l.2))⟩
  invFun l :=
    ⟨RootCentExc.compatParamAut σ b⁻¹ l.1, Subgroup.mem_subgroupOf.2 (by
      have hbinv : ∀ i : Fin TwistTag.E6.tag.rank,
          (fun j : Fin TwistTag.E6.tag.rank => ((↑b : Fin 6 → Kˣ) j)⁻¹)
              (TwistTag.E6.perm i) =
            Units.map σ.toMonoidHom ((fun j : Fin TwistTag.E6.tag.rank =>
              ((↑b : Fin 6 → Kˣ) j)⁻¹) i) := by
        intro i
        show ((↑b : Fin 6 → Kˣ) (TwistTag.E6.perm i))⁻¹ =
          ((Units.map σ.toMonoidHom) ((↑b : Fin 6 → Kˣ) i))⁻¹
        rw [show TwistTag.E6.perm i = LargeEvenRhoE6 i from rfl,
          (TableB.TwE6.mem_compat σ).1 b.2 i]
      rw [RootCentExc.coe_compatParamAut_apply]
      exact conj_rootDiagUnit_mem_su6Levi hbinv (Subgroup.mem_subgroupOf.1 l.2))⟩
  left_inv l := by
    refine Subtype.ext (Subtype.ext ?_)
    show ((RootCentExc.compatParamAut σ b⁻¹
      (RootCentExc.compatParamAut σ b l.1) : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) = (l.1 : ModGL TwistTag.E6.tag K)
    rw [show RootCentExc.compatParamAut σ b⁻¹ = (RootCentExc.compatParamAut σ b)⁻¹ from
      map_inv _ b, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  right_inv l := by
    refine Subtype.ext (Subtype.ext ?_)
    show ((RootCentExc.compatParamAut σ b
      (RootCentExc.compatParamAut σ b⁻¹ l.1) : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) = (l.1 : ModGL TwistTag.E6.tag K)
    rw [show RootCentExc.compatParamAut σ b = (RootCentExc.compatParamAut σ b⁻¹)⁻¹ from by
      rw [map_inv, inv_inv], MulAut.inv_apply, MulEquiv.symm_apply_apply]
  map_mul' l₁ l₂ := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, map_mul]

private theorem coe_compatParamAutLevi (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (b : ↥(TableB.TwE6.compat σ))
    (l : ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))) :
    ((compatParamAutLevi hK hσ b l :
        ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))) :
      ↥(graphFixedRootGroup TwistTag.E6 K σ)) =
      RootCentExc.compatParamAut σ b
        (l : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :=
  rfl

theorem exists_suConjSet_compatParamAut (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (b : ↥(TableB.TwE6.compat σ)) :
    ∃ α ∈ KGND.suConjSet (su6LeviHom hK hσ),
      ∀ l : ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)),
        ((α l : ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))) :
          ↥(graphFixedRootGroup TwistTag.E6 K σ)) =
          RootCentExc.compatParamAut σ b
            (l : ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by
  classical
  let h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let b' : Fin 6 → Kˣ := b
  have hb' : ∀ i, b' (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b' i) :=
    (TableB.TwE6.mem_compat σ).1 b.2
  obtain ⟨lam, hA⟩ := exists_smul_tau_isJUnitary hK hσ b' hb'
  refine ⟨compatParamAutLevi hK hσ b, ?_, fun l => coe_compatParamAutLevi hK hσ b l⟩
  refine ⟨InnerDiagA.diagGL (fun i => lam * tau b' i), hA, fun B => ?_⟩
  set B' : ↥(E6GraphLevi.unitarySL σ) := (E6GraphLevi.unitarySLEquiv hσ).symm B with hB'
  have hBcoe : ((B : ↥(SU (unitaryInvolution K 2 f) 6)) : GL (Fin 6) K) =
      Matrix.SpecialLinearGroup.toGL (B' : Matrix.SpecialLinearGroup (Fin 6) K) := by
    rw [show B = E6GraphLevi.unitarySLEquiv hσ B' from
      (MulEquiv.apply_symm_apply (E6GraphLevi.unitarySLEquiv hσ) B).symm]
    exact E6GraphLevi.coe_unitarySLEquiv hσ B'
  set X : ↥(SU (unitaryInvolution K 2 f) 6) :=
    InnerDiagSU.conjSU (InnerDiagA.diagGL (fun i => lam * tau b' i)) hA B with hX
  have hGL : Matrix.SpecialLinearGroup.toGL ((E6GraphLevi.unitarySLEquiv hσ).symm X :
        ↥(E6GraphLevi.unitarySL σ)) =
      InnerDiagA.diagGL (tau b') * Matrix.SpecialLinearGroup.toGL B' *
        (InnerDiagA.diagGL (tau b'))⁻¹ := by
    have h1 : Matrix.SpecialLinearGroup.toGL
        ((E6GraphLevi.unitarySLEquiv hσ).symm X : ↥(E6GraphLevi.unitarySL σ)) =
        (X : GL (Fin 6) K) := by
      have h := E6GraphLevi.coe_unitarySLEquiv hσ ((E6GraphLevi.unitarySLEquiv hσ).symm X)
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    rw [h1, hX, InnerDiagSU.coe_conjSU, hBcoe]
    exact conjGL_diagGL_smul lam (tau b') (Matrix.SpecialLinearGroup.toGL B')
  have hY : Matrix.SpecialLinearGroup.toGL
      (InnerDiagA.conjSL (InnerDiagA.diagGL (tau b')) B') =
      InnerDiagA.diagGL (tau b') * Matrix.SpecialLinearGroup.toGL B' *
        (InnerDiagA.diagGL (tau b'))⁻¹ := by
    apply Units.ext
    change (((InnerDiagA.conjSL (InnerDiagA.diagGL (tau b')) B' :
      Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      (((InnerDiagA.diagGL (tau b') * Matrix.SpecialLinearGroup.toGL B' *
        (InnerDiagA.diagGL (tau b'))⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    rw [InnerDiagA.coe_conjSL]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hSL : InnerDiagA.conjSL (InnerDiagA.diagGL (tau b')) B' =
      (((E6GraphLevi.unitarySLEquiv hσ).symm X : ↥(E6GraphLevi.unitarySL σ)) :
        Matrix.SpecialLinearGroup (Fin 6) K) :=
    (Matrix.SpecialLinearGroup.toGL_injective (hGL.trans hY.symm)).symm
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_compatParamAutLevi, RootCentExc.coe_compatParamAut_apply, coe_su6LeviHom,
    coe_su6LeviHom, rootDiagUnit_conj_realize h2 b', hSL]

end Levi

end Realize

end CFSG.StandardType.KGTwE6

end
