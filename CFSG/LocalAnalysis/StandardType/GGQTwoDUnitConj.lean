module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoord
import CFSG.LocalAnalysis.StandardType.GGQTwoDTransport

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G} {L : Subgroup G}
  {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
  {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ} {e' : Fin m ≃ ι} {F0 : Type} [Field F0]
  [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G} {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}
  {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

private lemma qtwoDB10_perm_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ((TauCeti.permutationGL (k := F0) σ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
        Pi.single i 1 = Pi.single (σ i) 1 := by
  rw [TauCeti.permutationGL_coe, Matrix.permMatrix_mulVec]
  ext j
  simp only [Function.comp_apply, Pi.single_apply]
  by_cases h : σ⁻¹ j = i
  · rw [if_pos h, if_pos ((Equiv.symm_apply_eq σ).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((Equiv.symm_apply_eq σ).mpr hh))]

private lemma qtwoDB10_diag_inv (c : Fin m → F0ˣ) :
    (qTwoChartTwoThree_diag c)⁻¹ = qTwoChartTwoThree_diag (fun i => (c i)⁻¹) :=
  Units.ext rfl

private lemma qtwoDB10_diag_mulVec (c : Fin m → F0ˣ) (i : Fin m) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
        Pi.single i 1 = (c i : F0) • Pi.single i 1 := by
  change Matrix.diagonal (fun j => ((c j : F0ˣ) : F0)) *ᵥ Pi.single i 1 =
    (c i : F0) • Pi.single i 1
  rw [Matrix.diagonal_mulVec_single, mul_one, ← Pi.single_smul', smul_eq_mul, mul_one]

private theorem qtwoDB10_perm_mem (σ : Equiv.Perm (Fin m)) :
    TauCeti.permutationGL (k := F0) σ ∈ SUid (unitaryInvolution F0 2 1) m := by
  rw [mem_SUid]
  constructor
  · rw [TauCeti.permutationGL_coe, Matrix.det_permutation]
    have hs : ((Equiv.Perm.sign σ⁻¹ : ℤˣ) : F0) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
      · rw [h]; simp
      · rw [h]
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
        exact CharTwo.neg_eq (1 : F0)
    rw [hs]
  · rw [conjTr]
    have hmap : (Equiv.Perm.permMatrix F0 σ⁻¹).map (unitaryInvolution F0 2 1) =
        Equiv.Perm.permMatrix F0 σ⁻¹ := by
      ext a b
      have hP : Equiv.Perm.permMatrix F0 σ⁻¹ a b = if σ⁻¹ a = b then 1 else 0 := by
        simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      rw [Matrix.map_apply, hP]
      by_cases h : σ⁻¹ a = b
      · rw [if_pos h, unitaryInvolution_apply]
        simp
      · rw [if_neg h, unitaryInvolution_apply]
        simp
    rw [TauCeti.permutationGL_coe, hmap, Matrix.transpose_permMatrix, inv_inv,
      ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

private lemma qtwoDB10_perm_inv_self (σ : Equiv.Perm (Fin m)) (hσ : σ * σ = 1) :
    (TauCeti.permutationGL (k := F0) σ)⁻¹ = TauCeti.permutationGL (k := F0) σ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul (TauCeti.permutationGL (k := F0)) σ σ, hσ, map_one]

private lemma qtwoDB10_conj_diag_mulVec (c : Fin m → F0ˣ) (σ : Equiv.Perm (Fin m))
    (hσ : σ * σ = 1) (i : Fin m) :
    (((qTwoChartTwoThree_diag c * TauCeti.permutationGL (k := F0) σ *
        (qTwoChartTwoThree_diag c)⁻¹ * TauCeti.permutationGL (k := F0) σ : GL (Fin m) F0)) :
        Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      ((c (σ i))⁻¹ * c i) • Pi.single i 1 := by
  have hσσ : σ (σ i) = i := by
    have h := congrArg (fun e : Equiv.Perm (Fin m) => e i) hσ
    simpa using h
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [qtwoDB10_perm_mulVec σ i]
  rw [qtwoDB10_diag_inv, qtwoDB10_diag_mulVec]
  rw [Matrix.mulVec_smul, qtwoDB10_perm_mulVec σ (σ i), hσσ]
  rw [Matrix.mulVec_smul, qtwoDB10_diag_mulVec, smul_smul, ← Units.val_mul]
  rfl

theorem ggQTwoDUnit_conj (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {a b : Fin m}
    (hab : a ≠ b) :
    ∃ α ∈ ggAutomizerJoin L Bs 𝒦,
      (∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) ∧
      ∃ g ∈ L ⊔ ⨆ K ∈ 𝒦, K, g ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹ := by
  have hmem : dSign m a b ∈ dEven m := by
    have hd : dSign m a b = (dPerm m (Equiv.swap a b))⁻¹ * dTau m true a b := by
      rw [dTau]
      simp only [if_true]
      group
    rw [hd]
    exact (dEven m).mul_mem ((dEven m).inv_mem (dPerm_mem_dEven m (Equiv.swap a b)))
      (dTau_mem_dEven m true hab)
  obtain ⟨α, hα, hαact⟩ := hcoords.join_onto (dSign m a b) hmem
  exact ⟨α, hα, hαact, exists_lift_of_mem_ggAutomizerJoin hα⟩

theorem ggQTwoDUnit_shape_coords (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hψ : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) (hm : 3 ≤ m) {a b : Fin m} (s : ↥Bs) :
    (∀ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ (s : G) c → c a = c b) ↔
      βL (Additive.ofMul s) a = βL (Additive.ofMul s) b := by
  classical
  constructor
  · intro h
    let v : Fin m → ZMod 3 := βL (Additive.ofMul s)
    let c₀ : Fin m → F0ˣ := fun i => ω ^ (v i).val
    have hc0 : qTwoChartTwoThree_induces ψ (s : G) c₀ := hcoords.induces s
    have hab : c₀ a = c₀ b := h c₀ hc0
    have hmod : (v a).val % orderOf ω = (v b).val % orderOf ω :=
      (pow_inj_mod (x := ω)).mp hab
    rw [hcoords.ω_order] at hmod
    have hva : (v a).val < 3 := ZMod.val_lt (v a)
    have hvb : (v b).val < 3 := ZMod.val_lt (v b)
    have hval : (v a).val = (v b).val := by
      rwa [Nat.mod_eq_of_lt hva, Nat.mod_eq_of_lt hvb] at hmod
    exact ZMod.val_injective 3 hval
  · intro hvab c hc
    by_cases hab : a = b
    · subst hab
      rfl
    let v : Fin m → ZMod 3 := βL (Additive.ofMul s)
    let c₀ : Fin m → F0ˣ := fun i => ω ^ (v i).val
    have hc0 : qTwoChartTwoThree_induces ψ (s : G) c₀ := hcoords.induces s
    have hc0ab : c₀ a = c₀ b := congrArg (fun z : ZMod 3 => ω ^ z.val) hvab
    set σ : Equiv.Perm (Fin m) := Equiv.swap a b with hσdef
    have hσ2 : σ * σ = 1 := by
      rw [hσdef]
      refine Equiv.ext fun z => ?_
      simpa using Equiv.swap_apply_self a b z
    let P : GL (Fin m) F0 := TauCeti.permutationGL (k := F0) σ
    have hPmem : P ∈ SUid (unitaryInvolution F0 2 1) m := qtwoDB10_perm_mem σ
    let uP : Su F0 2 1 m := ⟨P, hPmem⟩
    have huP : (uP : GL (Fin m) F0) = P := rfl
    have huPvec : ∀ i : Fin m,
        ((uP : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
          Pi.single (σ i) 1 := by
      intro i
      rw [huP]
      exact qtwoDB10_perm_mulVec σ i
    have hσsymm : σ.symm = σ := inv_eq_of_mul_eq_one_right hσ2
    have hcomp : (fun i => c₀ (σ.symm i)) = c₀ := by
      rw [hσsymm]
      funext i
      rw [hσdef]
      rcases eq_or_ne i a with hia | hia
      · rw [hia, Equiv.swap_apply_left a b]
        exact hc0ab.symm
      · rcases eq_or_ne i b with hib | hib
        · rw [hib, Equiv.swap_apply_right a b]
          exact hc0ab
        · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
    have hPc0 : P * qTwoChartTwoThree_diag c₀ * P⁻¹ = qTwoChartTwoThree_diag c₀ := by
      have h := qTwoChartTwoThree_perm_conj_diag (u := uP) huPvec c₀
      rw [huP] at h
      simpa [hcomp] using h
    have hDc0P : qTwoChartTwoThree_diag c₀ * P * (qTwoChartTwoThree_diag c₀)⁻¹ = P := by
      have hcomm : qTwoChartTwoThree_diag c₀ * P = P * qTwoChartTwoThree_diag c₀ := by
        calc qTwoChartTwoThree_diag c₀ * P
            = (P * qTwoChartTwoThree_diag c₀ * P⁻¹) * P := by rw [hPc0]
          _ = P * qTwoChartTwoThree_diag c₀ := by group
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨u₁, hu1mat, hu1ψ⟩ := hc uP
    obtain ⟨u₂, hu2mat, hu2ψ⟩ := hc0 uP
    have hu2GL : (u₂ : GL (Fin m) F0) = P := by
      rw [hu2mat, huP, hDc0P]
    let z : Su F0 2 1 m := u₁ * u₂⁻¹
    have hzmem : z ∈ Subgroup.center (Su F0 2 1 m) := by
      apply hψ
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu1ψ, hu2ψ, mul_inv_cancel]
    obtain ⟨k, hka, hkb⟩ : ∃ k : Fin m, k ≠ a ∧ k ≠ b := by
      have hcard : ({a, b} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        have h2 : ({a, b} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      exact ⟨k, fun h => hk (by rw [h]; simp), fun h => hk (by rw [h]; simp)⟩
    set τ : Equiv.Perm (Fin m) := Equiv.swap b k with hτdef
    have hτ2 : τ * τ = 1 := by
      rw [hτdef]
      refine Equiv.ext fun z => ?_
      simpa using Equiv.swap_apply_self b k z
    let Q : GL (Fin m) F0 := TauCeti.permutationGL (k := F0) τ
    have hQmem : Q ∈ SUid (unitaryInvolution F0 2 1) m := qtwoDB10_perm_mem τ
    let uQ : Su F0 2 1 m := ⟨Q, hQmem⟩
    have huQ : (uQ : GL (Fin m) F0) = Q := rfl
    have hτb : τ b = k := by rw [hτdef]; exact Equiv.swap_apply_left b k
    have hτk : τ k = b := by rw [hτdef]; exact Equiv.swap_apply_right b k
    have huQb : ((uQ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 =
        Pi.single k 1 := by
      rw [huQ, qtwoDB10_perm_mulVec τ b, hτb]
    have huQk : ((uQ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1 =
        Pi.single b 1 := by
      rw [huQ, qtwoDB10_perm_mulVec τ k, hτk]
    have hzGL : (z : GL (Fin m) F0) =
        qTwoChartTwoThree_diag c * P * (qTwoChartTwoThree_diag c)⁻¹ * P := by
      change ((u₁ * u₂⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) = _
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hu1mat, huP, hu2GL,
        qtwoDB10_perm_inv_self σ hσ2]
    have hzB : ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 =
        ((c a)⁻¹ * c b) • Pi.single b 1 := by
      rw [hzGL, qtwoDB10_conj_diag_mulVec c σ hσ2 b, hσdef]
      rw [Equiv.swap_apply_right]
    have hzK : ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single k 1 =
        Pi.single k 1 := by
      rw [hzGL, qtwoDB10_conj_diag_mulVec c σ hσ2 k, hσdef]
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb, inv_mul_cancel, one_smul]
    have hzcomm : z * uQ = uQ * z := ((Subgroup.mem_center_iff.mp hzmem) uQ).symm
    have hL : (((z * uQ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 = Pi.single k 1 := by
      have hcoe : (((z * uQ : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
          ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
            ((uQ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
        rw [Subgroup.coe_mul, Units.val_mul]
      rw [hcoe, ← Matrix.mulVec_mulVec, huQb, hzK]
    have hR : (((uQ * z : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 = ((c a)⁻¹ * c b) • Pi.single k 1 := by
      have hcoe : (((uQ * z : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
          ((uQ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
            ((z : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
        rw [Subgroup.coe_mul, Units.val_mul]
      rw [hcoe, ← Matrix.mulVec_mulVec, hzB, Matrix.mulVec_smul, huQb]
    have h1 : ((c a)⁻¹ * c b : F0ˣ) = 1 := by
      have hEq : (Pi.single k (1 : F0) : Fin m → F0) =
          ((c a)⁻¹ * c b : F0ˣ) • (Pi.single k (1 : F0) : Fin m → F0) := by
        calc (Pi.single k (1 : F0) : Fin m → F0)
            = (((z * uQ : Su F0 2 1 m) : GL (Fin m) F0) :
                Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 := hL.symm
          _ = (((uQ * z : Su F0 2 1 m) : GL (Fin m) F0) :
                Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single b 1 := by rw [hzcomm]
          _ = ((c a)⁻¹ * c b : F0ˣ) • (Pi.single k (1 : F0) : Fin m → F0) := hR
      have hk := congrFun hEq k
      rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same] at hk
      exact Units.ext (by simpa [Units.smul_def] using hk.symm)
    have h2 : c a = c b := by
      have hc := congrArg (fun y : F0ˣ => c a * y) h1
      simpa [mul_assoc] using hc.symm
    exact h2

end CFSG.StandardType.QTwo

end
