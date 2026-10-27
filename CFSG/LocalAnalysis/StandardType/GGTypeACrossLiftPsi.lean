module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueCtx
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftCoord
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftRot

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.StandardType.TypeAReflOver

private theorem rotCtx_eq_one_of_centralizes {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {n : ℕ} {F : Type} [Field F] {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* G}
    {x y y₃ : G} (hX : GGFarCtx p Bs φ₁ φ₂ x y) (hX₃ : GGFarCtx p Bs φ₁ φ₃ x y₃)
    (j : Fin n) (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs, κ (Additive.ofMul (hX.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kRefl p n (κ (Additive.ofMul b)))
    (hκ₃ : ∀ b : ↥Bs, κ (Additive.ofMul (hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kThreeRefl p n (κ (Additive.ofMul b)))
    {w : G} (hw : w ∈ Bs) (h₂w : ∀ s, w * φ₂ s = φ₂ s * w)
    (hψw : ∀ s, w * ggRotLift hX.two φ₂ φ₃ s = ggRotLift hX.two φ₂ φ₃ s * w) :
    w = 1 := by
  classical
  set c : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1) with hc
  have hgw : w * φ₂ (slPerm hX.two c) = φ₂ (slPerm hX.two c) * w := h₂w (slPerm hX.two c)
  have hconj : (φ₂ (slPerm hX.two c))⁻¹ * w * φ₂ (slPerm hX.two c) = w := by
    rw [mul_assoc, hgw, ← mul_assoc, inv_mul_cancel, one_mul]
  have h₃w : ∀ s, w * φ₃ s = φ₃ s * w := by
    intro s
    have h := hψw s
    rw [ggRotLift_apply] at h
    have h' := congrArg (fun t => (φ₂ (slPerm hX.two c))⁻¹ * t * φ₂ (slPerm hX.two c)) h
    have e1 : (φ₂ (slPerm hX.two c))⁻¹ *
        (w * (φ₂ (slPerm hX.two c) * φ₃ s * (φ₂ (slPerm hX.two c))⁻¹)) *
          φ₂ (slPerm hX.two c) = w * φ₃ s := by
      calc (φ₂ (slPerm hX.two c))⁻¹ *
          (w * (φ₂ (slPerm hX.two c) * φ₃ s * (φ₂ (slPerm hX.two c))⁻¹)) *
            φ₂ (slPerm hX.two c) =
          ((φ₂ (slPerm hX.two c))⁻¹ * w * φ₂ (slPerm hX.two c)) * φ₃ s := by group
        _ = w * φ₃ s := by rw [hconj]
    have e2 : (φ₂ (slPerm hX.two c))⁻¹ *
        ((φ₂ (slPerm hX.two c) * φ₃ s * (φ₂ (slPerm hX.two c))⁻¹) * w) *
          φ₂ (slPerm hX.two c) = φ₃ s * w := by
      calc (φ₂ (slPerm hX.two c))⁻¹ *
          ((φ₂ (slPerm hX.two c) * φ₃ s * (φ₂ (slPerm hX.two c))⁻¹) * w) *
            φ₂ (slPerm hX.two c) =
          φ₃ s * ((φ₂ (slPerm hX.two c))⁻¹ * w * φ₂ (slPerm hX.two c)) := by group
        _ = φ₃ s * w := by rw [hconj]
    rwa [e1, e2] at h'
  have hfix₂ : ∀ σ : Equiv.Perm (Fin (n + 1)), hX.permAut₂ σ ⟨w, hw⟩ = ⟨w, hw⟩ := by
    intro σ
    apply Subtype.ext
    rw [GGFarCtx.permAut₂_apply]
    rw [← h₂w (slPerm hX.two σ), mul_assoc, mul_inv_cancel, mul_one]
  have hfix₃ : hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) ⟨w, hw⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [GGFarCtx.permAut₂_apply]
    rw [← h₃w (slPerm hX₃.two (Equiv.swap j.castSucc j.succ)), mul_assoc, mul_inv_cancel,
      mul_one]
  have hc₁ : ∀ a b : Fin n,
      coordPerm p n (Equiv.swap a.succ b.succ) (κ (Additive.ofMul ⟨w, hw⟩)) =
        κ (Additive.ofMul ⟨w, hw⟩) := by
    intro a b
    have h := hκ₁ (Equiv.swap a.succ b.succ) ⟨w, hw⟩
    rw [hX.permAut_compat a b, hfix₂ (Equiv.swap a.castSucc b.castSucc)] at h
    exact h.symm
  have hc₂ : kRefl p n (κ (Additive.ofMul ⟨w, hw⟩)) = κ (Additive.ofMul ⟨w, hw⟩) := by
    have h := hκ₂ ⟨w, hw⟩
    rw [hfix₂ (Equiv.swap j.castSucc j.succ)] at h
    exact h.symm
  have hc₃ : kThreeRefl p n (κ (Additive.ofMul ⟨w, hw⟩)) = κ (Additive.ofMul ⟨w, hw⟩) := by
    have h := hκ₃ ⟨w, hw⟩
    rw [hfix₃] at h
    exact h.symm
  have hsingle := eq_single_zero_of_fixed (κ (Additive.ofMul ⟨w, hw⟩)) hc₁ hc₂
  have hn : 3 ≤ n := hX.three_le
  have ht : (κ (Additive.ofMul ⟨w, hw⟩)) 0 = 0 := by
    refine eq_zero_of_kThreeRefl_single (p := p) (n := n) (by omega) ?_
    rw [← hsingle]
    exact hc₃
  have hzero : κ (Additive.ofMul ⟨w, hw⟩) = 0 := by
    rw [hsingle, ht, Pi.single_zero]
  have h1 : (⟨w, hw⟩ : ↥Bs) = 1 :=
    ofMul_eq_zero.mp (κ.injective (by rw [hzero, map_zero]))
  simpa using congrArg Subtype.val h1

theorem GGFarCtx.rotCtx {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type}
    [Field F] {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y y₃ : G}
    (hX : GGFarCtx p Bs φ₁ φ₂ x y) (hX₃ : GGFarCtx p Bs φ₁ φ₃ x y₃) (j : Fin n)
    (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs, κ (Additive.ofMul (hX.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kRefl p n (κ (Additive.ofMul b)))
    (hκ₃ : ∀ b : ↥Bs, κ (Additive.ofMul (hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kThreeRefl p n (κ (Additive.ofMul b))) :
    GGFarCtx p Bs φ₂ (ggRotLift hX.two φ₂ φ₃) y
      (φ₂ (slPerm hX.two (finRotate (n + 1))) * y₃ *
        (φ₂ (slPerm hX.two (finRotate (n + 1))))⁻¹) := by
  classical
  set c : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1) with hc
  have hgN : φ₂ (slPerm hX.two c) ∈ Subgroup.normalizer (Bs : Set G) :=
    hX.perm_mem_normalizer₂ c
  have hker₂ : (ggRotLift hX.two φ₂ φ₃).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := by
    rw [ggRotLift_ker hX.two φ₂ φ₃]
    exact hX₃.lifts.ker₂
  have hdiag₂ : ∀ b ∈ Bs, GGActsDiag (ggRotLift hX.two φ₂ φ₃) b := by
    intro b hb
    have hb' : (φ₂ (slPerm hX.two c))⁻¹ * b * φ₂ (slPerm hX.two c) ∈ Bs :=
      (Subgroup.mem_normalizer_iff''.mp hgN b).mp hb
    obtain ⟨h, hh⟩ :=
      hX₃.lifts.diag₂ ((φ₂ (slPerm hX.two c))⁻¹ * b * φ₂ (slPerm hX.two c)) hb'
    refine ⟨h, fun s => ?_⟩
    calc b * ggRotLift hX.two φ₂ φ₃ s * b⁻¹
        = b * (φ₂ (slPerm hX.two c) * φ₃ s * (φ₂ (slPerm hX.two c))⁻¹) * b⁻¹ := by
          rw [ggRotLift_apply]
      _ = φ₂ (slPerm hX.two c) *
            (((φ₂ (slPerm hX.two c))⁻¹ * b * φ₂ (slPerm hX.two c)) * φ₃ s *
              ((φ₂ (slPerm hX.two c))⁻¹ * b * φ₂ (slPerm hX.two c))⁻¹) *
            (φ₂ (slPerm hX.two c))⁻¹ := by group
      _ = φ₂ (slPerm hX.two c) * φ₃ (ggDiagConj h s) * (φ₂ (slPerm hX.two c))⁻¹ := by
          rw [hh s]
      _ = ggRotLift hX.two φ₂ φ₃ (ggDiagConj h s) := by rw [ggRotLift_apply]
  have hy'_mem : φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hgN y₃).mp hX₃.y_mem
  have hy'_ne : φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹ ≠ 1 := by
    intro h
    apply hX₃.y_ne
    have h' : (φ₂ (slPerm hX.two c))⁻¹ *
        (φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹) * φ₂ (slPerm hX.two c) =
          (φ₂ (slPerm hX.two c))⁻¹ * (1 : G) * φ₂ (slPerm hX.two c) := by rw [h]
    rwa [show (φ₂ (slPerm hX.two c))⁻¹ *
          (φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹) * φ₂ (slPerm hX.two c) =
        y₃ by group,
      show (φ₂ (slPerm hX.two c))⁻¹ * (1 : G) * φ₂ (slPerm hX.two c) = 1 by group] at h'
  have hinj : ∀ w ∈ Bs, (∀ s, w * φ₂ s = φ₂ s * w) →
      (∀ s, w * ggRotLift hX.two φ₂ φ₃ s = ggRotLift hX.two φ₂ φ₃ s * w) → w = 1 :=
    fun w hw h₁ h₂ => rotCtx_eq_one_of_centralizes hX hX₃ j κ hκ₁ hκ₂ hκ₃ hw h₁ h₂
  have hx_ncomm : ¬ ∀ s, y * ggRotLift hX.two φ₂ φ₃ s =
      ggRotLift hX.two φ₂ φ₃ s * y := by
    intro h
    exact hX.y_ne (hinj y hX.y_mem hX.y_comm h)
  exact
    { prime := hX.prime
      odd := hX.odd
      two := hX.two
      three_le := hX.three_le
      lifts :=
        { ker₁ := hX.lifts.ker₂
          ker₂ := hker₂
          compat := ggRotLift_compat hX.two hX.lifts.compat hX₃.lifts.compat
          diag₁ := hX.lifts.diag₂
          diag₂ := hdiag₂ }
      exp := hX.exp
      cent := hX.cent
      x_mem := hX.y_mem
      y_mem := hy'_mem
      y_ne := hy'_ne
      x_comm := hX.y_comm
      x_ncomm := hx_ncomm
      y_comm := by
        intro s
        calc (φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹) *
              ggRotLift hX.two φ₂ φ₃ s
            = (φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹) *
                (φ₂ (slPerm hX.two c) * φ₃ s * (φ₂ (slPerm hX.two c))⁻¹) := by
              rw [ggRotLift_apply]
          _ = φ₂ (slPerm hX.two c) * (y₃ * φ₃ s) * (φ₂ (slPerm hX.two c))⁻¹ := by group
          _ = φ₂ (slPerm hX.two c) * (φ₃ s * y₃) * (φ₂ (slPerm hX.two c))⁻¹ := by
              rw [hX₃.y_comm s]
          _ = ggRotLift hX.two φ₂ φ₃ s *
                (φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹) := by
              rw [ggRotLift_apply, ← hc]
              group
      inj := hinj }

theorem GGFarCtx.rot_abab_mem_centralizer {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ}
    {F : Type} [Field F] {φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y y₃ : G}
    (hX : GGFarCtx p Bs φ₁ φ₂ x y) (hX₃ : GGFarCtx p Bs φ₁ φ₃ x y₃) (hp : p ∣ n + 3)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (κ : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p))
    (hκ₁ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (b : ↥Bs),
      κ (Additive.ofMul (hX.permAut₁ σ b)) = coordPerm p n σ (κ (Additive.ofMul b)))
    (hκ₂ : ∀ b : ↥Bs, κ (Additive.ofMul (hX.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kRefl p n (κ (Additive.ofMul b)))
    (hκ₃ : ∀ b : ↥Bs, κ (Additive.ofMul (hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) b)) =
      kThreeRefl p n (κ (Additive.ofMul b))) :
    φ₂ (weylRep n F i) * ggRotLift hX.two φ₂ φ₃ (weylRep n F j) * φ₂ (weylRep n F i) *
        ggRotLift hX.two φ₂ φ₃ (weylRep n F j) ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  set c : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1) with hc
  set gb : MulAut ↥Bs := hX.permAut₂ c with hgb
  set Q : MulAut ↥Bs := hX.permAut₂ (Equiv.swap (0 : Fin (n + 1)) j.castSucc) with hQ
  set Kr : MulAut ↥Bs := hX.permAut₂ (Equiv.swap j.castSucc j.succ) with hKr
  set K3 : MulAut ↥Bs := hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) with hK3
  have hY : GGFarCtx p Bs φ₂ (ggRotLift hX.two φ₂ φ₃) y
      (φ₂ (slPerm hX.two c) * y₃ * (φ₂ (slPerm hX.two c))⁻¹) :=
    hX.rotCtx hX₃ j κ hκ₁ hκ₂ hκ₃
  have hYtwo : hY.two = hX.two := Subsingleton.elim _ _
  have hX₃two : hX₃.two = hX.two := Subsingleton.elim _ _
  have hi0 : i.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simpa using hi)
  have hi1 : i.succ = (1 : Fin (n + 1)) := by
    apply Fin.ext
    rw [Fin.val_succ, hi, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hjs : j.succ = Fin.last n := Fin.ext (by rw [Fin.val_succ, Fin.val_last]; exact hj)
  have hn : 3 ≤ n := hX.three_le
  let z : Fin n := ⟨0, by omega⟩
  have ha_ne_last : z.succ ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_succ, Fin.val_last] at hv
    have hz : (z : ℕ) = 0 := rfl
    omega
  have hA : hY.permAut₁ (Equiv.swap i.castSucc i.succ) =
      hX.permAut₂ (Equiv.swap (0 : Fin (n + 1)) 1) := by
    rw [hi0, hi1]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    simp only [GGFarCtx.permAut₁_apply, GGFarCtx.permAut₂_apply]
  have hgb_inv : ∀ b : ↥Bs,
      (((hX.permAut₂ c)⁻¹ b : ↥Bs) : G) = (φ₂ (slPerm hX.two c))⁻¹ * (b : G) *
        φ₂ (slPerm hX.two c) := by
    intro b
    exact inv_apply_of_forall (GGFarCtx.permAut₂_apply hX c) b
  have hB' : hY.permAut₂ (Equiv.swap j.castSucc j.succ) = gb * K3 * gb⁻¹ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [GGFarCtx.permAut₂_apply, ggRotLift_apply, hYtwo, ← hc]
    rw [MulAut.mul_apply, MulAut.mul_apply, hgb, hK3]
    rw [GGFarCtx.permAut₂_apply hX c]
    rw [GGFarCtx.permAut₂_apply hX₃ (Equiv.swap j.castSucc j.succ), hX₃two]
    rw [hgb_inv]
    group
  have hconj_perm : c⁻¹ * Equiv.swap (0 : Fin (n + 1)) 1 * c =
      Equiv.swap (0 : Fin (n + 1)) j.castSucc * Equiv.swap j.castSucc j.succ *
        Equiv.swap (0 : Fin (n + 1)) j.castSucc := by
    have hc0 : c⁻¹ 0 = Fin.last n := by
      rw [Equiv.Perm.inv_eq_iff_eq, hc]
      exact (finRotate_last (n := n)).symm
    have hc1 : c⁻¹ 1 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq, hc]
      exact (finRotate_apply_zero (n := n)).symm
    have h1 : c⁻¹ * Equiv.swap (0 : Fin (n + 1)) 1 * c =
        Equiv.swap (Fin.last n) (0 : Fin (n + 1)) := by
      simpa [hc0, hc1] using (Equiv.swap_apply_apply c⁻¹ (0 : Fin (n + 1)) 1).symm
    have hj0 : j.succ ≠ (0 : Fin (n + 1)) := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hjcs : j.succ ≠ j.castSucc := (Fin.castSucc_lt_succ (i := j)).ne.symm
    have h2 : Equiv.swap (0 : Fin (n + 1)) j.succ =
        Equiv.swap (0 : Fin (n + 1)) j.castSucc * Equiv.swap j.castSucc j.succ *
          Equiv.swap (0 : Fin (n + 1)) j.castSucc := by
      have h := Equiv.swap_apply_apply (Equiv.swap (0 : Fin (n + 1)) j.castSucc)
        j.castSucc j.succ
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hj0 hjcs,
        Equiv.swap_inv] at h
      exact h
    rw [h1, Equiv.swap_comm, ← hjs]
    exact h2
  have hconjA : gb⁻¹ * hX.permAut₂ (Equiv.swap (0 : Fin (n + 1)) 1) * gb = Q * Kr * Q := by
    rw [hgb, hKr, ← map_inv, ← map_mul, ← map_mul, hconj_perm, map_mul, map_mul]
  have hQ₁ : Q = hX.permAut₁ (Equiv.swap z.succ j.succ) := by
    rw [hQ]
    exact (hX.permAut_compat z j).symm
  have hLeft : ∀ b : ↥Bs,
      κ (Additive.ofMul (((Q * Kr * Q) * K3) b)) =
        coordPerm p n (Equiv.swap z.succ j.succ)
          (kRefl p n (coordPerm p n (Equiv.swap z.succ j.succ)
            (kThreeRefl p n (κ (Additive.ofMul b))))) := by
    intro b
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hQ₁, hKr, hK3]
    rw [hκ₁, hκ₂, hκ₁, hκ₃]
  have hRight : ∀ b : ↥Bs,
      κ (Additive.ofMul ((K3 * (Q * Kr * Q)) b)) =
        kThreeRefl p n (coordPerm p n (Equiv.swap z.succ j.succ)
          (kRefl p n (coordPerm p n (Equiv.swap z.succ j.succ)
            (κ (Additive.ofMul b))))) := by
    intro b
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hK3, hQ₁, hKr]
    rw [hκ₃, hκ₁, hκ₂, hκ₁]
  have hcomm' : (Q * Kr * Q) * K3 = K3 * (Q * Kr * Q) := by
    refine MulEquiv.ext fun b => ?_
    apply Additive.ofMul.injective
    apply κ.injective
    rw [hLeft b, hRight b, hjs]
    exact (kThreeRefl_commute_swap_kRefl hp ha_ne_last (κ (Additive.ofMul b))).symm
  have hA0 : hX.permAut₂ (Equiv.swap (0 : Fin (n + 1)) 1) =
      gb * (Q * Kr * Q) * gb⁻¹ := by
    rw [← hconjA]
    group
  have hcommA : hX.permAut₂ (Equiv.swap (0 : Fin (n + 1)) 1) * (gb * K3 * gb⁻¹) =
      (gb * K3 * gb⁻¹) * hX.permAut₂ (Equiv.swap (0 : Fin (n + 1)) 1) := by
    rw [hA0]
    calc gb * (Q * Kr * Q) * gb⁻¹ * (gb * K3 * gb⁻¹)
        = gb * ((Q * Kr * Q) * K3) * gb⁻¹ := by group
      _ = gb * (K3 * (Q * Kr * Q)) * gb⁻¹ := by rw [hcomm']
      _ = gb * K3 * gb⁻¹ * (gb * (Q * Kr * Q) * gb⁻¹) := by group
  refine hY.abab_mem_centralizer ?_
  rw [hA, hB']
  exact hcommA

end CFSG.StandardType

end
