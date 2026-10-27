module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwoAux1
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9LinearTorus
import CFSG.Mathlib.GroupTheory.AutomorphismNormalFactors

public section

namespace CFSG.StandardType.CommonJRowLinTwo

open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf
open CFSG.StandardType.LinTwoTB
open CFSG.StandardType.LinTwoTv
open Multiplicative

theorem ggCommonJRowLinTwo_hsign {d m : ℕ} (hd : d = 2 * m ∨ d = 2 * m + 1) (hm : 3 ≤ m)
    (ε : Fin d ≃ (Fin (rootPB phi3).dim × Fin m) ⊕ Fin (d - 2 * m)) :
    ∀ g : Matrix.SpecialLinearGroup (Fin d) F2,
      (∀ s ∈ (ggCommonJRowLinTwo_torus ε).range, g * s * g⁻¹ ∈
        (ggCommonJRowLinTwo_torus ε).range) →
      ∃ u : (Fin m → Multiplicative (ZMod 3)) → (Fin m → Multiplicative (ZMod 3)),
        SpCoord.IsSignedPerm u ∧
          ∀ f, g * ggCommonJRowLinTwo_torus ε f * g⁻¹ = ggCommonJRowLinTwo_torus ε (u f) := by
  classical
  have hK : Nat.card F2 = 2 := by
    rw [GaloisField.card 2 1 (by omega)]
    norm_num
  have hp3 : ((3 : ℕ) : F2) ≠ 0 := natCast_three_ne_zero
  have hgd : phi3 ∣ Polynomial.cyclotomic 3 F2 := phi3_dvd_cyclotomic
  have hC : (rootMat phi3).det = 1 := det_rootMat_phi3
  have hCp : rootMat phi3 ^ 3 = 1 := rootMat_phi3_pow_three
  have hζ : AdjoinRoot.root phi3 ^ 3 = 1 := root_phi3_pow_three
  have hd3 : 3 ≤ d := by omega
  have hcomp : ∀ t, Matrix.SpecialLinearGroup.toGL (ggCommonJRowLinTwo_torus ε t) =
      frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp t := by
    intro t
    rfl
  have h_toGL_glEquivSL : ∀ A : GL (Fin d) F2,
      Matrix.SpecialLinearGroup.toGL ((glEquivSL (d := d) hK) A) = A := by
    intro A
    exact TwoThree.toGL_toSLHom hK A
  have h_gl_toGL : ∀ x : Matrix.SpecialLinearGroup (Fin d) F2,
      (glEquivSL (d := d) hK) (Matrix.SpecialLinearGroup.toGL x) = x := by
    intro x
    exact Subtype.ext rfl
  have h_symm_toGL : ∀ x : Matrix.SpecialLinearGroup (Fin d) F2,
      (glEquivSL (d := d) hK).symm x = Matrix.SpecialLinearGroup.toGL x := by
    intro x
    apply (glEquivSL (d := d) hK).injective
    rw [MulEquiv.apply_symm_apply, h_gl_toGL x]
  have hlift : ∀ (π : Equiv.Perm (Fin m))
      (σ : Fin m → (AdjoinRoot phi3 ≃ₐ[F2] AdjoinRoot phi3)),
      (∀ i, π (π i) = i) → (∀ i x, σ i (σ (π i) x) = x) →
      ∃ L : GL (Fin d) F2, L * L = 1 ∧ ∀ t t' : Fin m → ZMod 3,
        (∀ i, AdjoinRoot.root phi3 ^ (t i).val =
          σ i (AdjoinRoot.root phi3) ^ (t' (π i)).val) →
        L * frameHom (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) * L⁻¹ =
          frameHom (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t') := by
    intro π σ hπ hσ
    obtain ⟨M, hMM, hM⟩ := exists_move_invol phi3 ε π σ hπ hσ
    let L : GL (Fin d) F2 := ⟨M, M, hMM, hMM⟩
    refine ⟨L, Units.ext hMM, fun t t' ht => ?_⟩
    have hLsq : L * L = 1 := Units.ext hMM
    have hLinv : L⁻¹ = L := inv_eq_of_mul_eq_one_right hLsq
    rw [hLinv]
    apply Units.ext
    have hιt : ((frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) :
          GL (Fin d) F2) : Matrix (Fin d) (Fin d) F2) =
        SLNS.nsMat ε (rootMat phi3) (fun i => (t i).val) := by
      rw [coe_frameHom_toGL]
      simp
    have hιt' : ((frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t') :
          GL (Fin d) F2) : Matrix (Fin d) (Fin d) F2) =
        SLNS.nsMat ε (rootMat phi3) (fun i => (t' i).val) := by
      rw [coe_frameHom_toGL]
      simp
    change M * (frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t)).val * M =
      (frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t')).val
    rw [hιt, hιt']
    have hMN : SLNS.nsMat ε (rootMat phi3) (fun i => (t i).val) * M =
        M * SLNS.nsMat ε (rootMat phi3) (fun i => (t' i).val) := hM _ _ ht
    calc M * SLNS.nsMat ε (rootMat phi3) (fun i => (t i).val) * M
        = M * (SLNS.nsMat ε (rootMat phi3) (fun i => (t i).val) * M) := by
          rw [Matrix.mul_assoc]
      _ = M * (M * SLNS.nsMat ε (rootMat phi3) (fun i => (t' i).val)) := by rw [hMN]
      _ = (M * M) * SLNS.nsMat ε (rootMat phi3) (fun i => (t' i).val) := by
          rw [Matrix.mul_assoc]
      _ = SLNS.nsMat ε (rootMat phi3) (fun i => (t' i).val) := by
          rw [hMM, Matrix.one_mul]
  obtain ⟨frob, hfrob, hfrob2⟩ := exists_frob (K := F2) (g := phi3) hK hζ
  have hsg : ∀ i : Fin m, ∃ L : GL (Fin d) F2, L * L = 1 ∧ ∀ t : Fin m → ZMod 3,
      L * frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) * L⁻¹ =
        frameHom (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp
            (ofAdd (signV i t)) := by
    intro i
    obtain ⟨L, hL, hLt⟩ := hlift 1 (fun j => if j = i then frob else AlgEquiv.refl)
      (fun _ => rfl) (fun j x => by
        by_cases hj : j = i
        · subst hj
          simp only [if_true, Equiv.Perm.coe_one, id_eq]
          exact hfrob2 x
        · simp [hj])
    refine ⟨L, hL, fun t => hLt t _ (fun j => ?_)⟩
    by_cases hj : j = i
    · subst hj
      simp only [if_true, Equiv.Perm.coe_one, id_eq, hfrob, signV_self]
      exact root_pow_neg hζ (t j)
    · simp [hj, signV_of_ne hj]
  have hsw : ∀ i j : Fin m, ∃ L : GL (Fin d) F2, L * L = 1 ∧ ∀ t : Fin m → ZMod 3,
      L * frameHom (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) * L⁻¹ =
        frameHom (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp
            (ofAdd (swapV i j t)) := by
    intro i j
    obtain ⟨L, hL, hLt⟩ := hlift (Equiv.swap i j) (fun _ => AlgEquiv.refl)
      (fun k => Equiv.swap_apply_self i j k) (fun _ _ => rfl)
    refine ⟨L, hL, fun t => hLt t _ (fun k => ?_)⟩
    simp [swapV, Equiv.swap_apply_self]
  choose Lg hLg2 hLg using hsg
  choose Lw hLw2 hLw using hsw
  let D : LinTwoTB.TorusData (Matrix.SpecialLinearGroup (Fin d) F2) m :=
    { ι := ggCommonJRowLinTwo_torus ε
      inj := ggCommonJRowLinTwo_hτ ε
      sg := fun i => (glEquivSL (d := d) hK) (Lg i)
      sg_sq := fun i => by
        change (glEquivSL (d := d) hK) (Lg i) * (glEquivSL (d := d) hK) (Lg i) = 1
        rw [← map_mul, hLg2 i, map_one]
      sg_act := fun i t => by
        apply Matrix.SpecialLinearGroup.toGL_injective
        have h1 : Matrix.SpecialLinearGroup.toGL
            ((glEquivSL (d := d) hK) (Lg i) * ggCommonJRowLinTwo_torus ε (ofAdd t) *
              ((glEquivSL (d := d) hK) (Lg i))⁻¹) =
            Lg i * frameHom (Matrix.SpecialLinearGroup.toGL :
              Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) *
              (Lg i)⁻¹ := by
          rw [map_mul, map_mul, map_inv, h_toGL_glEquivSL (Lg i), hcomp (ofAdd t)]
        have h2 : Lg i * frameHom (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) *
            (Lg i)⁻¹ =
            frameHom (Matrix.SpecialLinearGroup.toGL :
              Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp
              (ofAdd (signV i t)) := hLg i t
        rw [h1, h2, ← hcomp (ofAdd (signV i t))]
      sw := fun i j => (glEquivSL (d := d) hK) (Lw i j)
      sw_sq := fun i j => by
        change (glEquivSL (d := d) hK) (Lw i j) * (glEquivSL (d := d) hK) (Lw i j) = 1
        rw [← map_mul, hLw2 i j, map_one]
      sw_act := fun i j t => by
        apply Matrix.SpecialLinearGroup.toGL_injective
        have h1 : Matrix.SpecialLinearGroup.toGL
            ((glEquivSL (d := d) hK) (Lw i j) * ggCommonJRowLinTwo_torus ε (ofAdd t) *
              ((glEquivSL (d := d) hK) (Lw i j))⁻¹) =
            Lw i j * frameHom (Matrix.SpecialLinearGroup.toGL :
              Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) *
              (Lw i j)⁻¹ := by
          rw [map_mul, map_mul, map_inv, h_toGL_glEquivSL (Lw i j), hcomp (ofAdd t)]
        have h2 : Lw i j * frameHom (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp (ofAdd t) *
            (Lw i j)⁻¹ =
            frameHom (Matrix.SpecialLinearGroup.toGL :
              Matrix.SpecialLinearGroup (Fin d) F2 →* GL (Fin d) F2) 1 ε hC hCp
              (ofAdd (swapV i j t)) := hLw i j t
        rw [h1, h2, ← hcomp (ofAdd (swapV i j t))] }
  let wt : Matrix.SpecialLinearGroup (Fin d) F2 → ℕ :=
    fun x => wtGL (Matrix.SpecialLinearGroup.toGL x)
  have hw : ∀ v, wt (D.el v) = 2 * hamWt v := by
    intro v
    change wtGL (Matrix.SpecialLinearGroup.toGL
      (ggCommonJRowLinTwo_torus ε (Multiplicative.ofAdd v))) = 2 * hamWt v
    rw [hcomp (Multiplicative.ofAdd v)]
    rw [wtGL_frameHom (K := F2) (g := phi3) (s := m) (r := d - 2 * m)
      (d := d) hK hp3 hgd ε 1 hC hCp v, rootPB_phi3_dim]
  have hwt : ∀ (α : MulAut (Matrix.SpecialLinearGroup (Fin d) F2)) x,
      wt (α x) = wt x := by
    intro α x
    let Φ : MulAut (GL (Fin d) F2) := MulAut.congr (glEquivSL (d := d) hK).symm α
    have hΦ : Φ (Matrix.SpecialLinearGroup.toGL x) =
        Matrix.SpecialLinearGroup.toGL (α x) := by
      simp only [Φ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]
      rw [h_gl_toGL x, h_symm_toGL (α x)]
    have h := wtGL_mulAut (K := F2) (d := d) hK hd3 Φ
      (Matrix.SpecialLinearGroup.toGL x)
    rw [hΦ] at h
    exact h
  intro g hg
  let α : MulAut (Matrix.SpecialLinearGroup (Fin d) F2) := MulAut.conj g
  have hα_mem : ∀ s ∈ D.tor, α s ∈ D.tor := by
    intro s hs
    exact hg s (by simpa [D, LinTwoTB.TorusData.tor] using hs)
  have hNmap : D.tor.map α.toMonoidHom = D.tor := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact hα_mem s hs
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective α)]
  let αD : MulAut D.tor := CFSG.GroupTheory.MulAut.restrictNormal α D.tor hNmap
  let F : (Fin m → Multiplicative (ZMod 3)) → D.tor :=
    fun f => ⟨D.el (fun i => toAdd (f i)), D.mem_tor.mpr ⟨_, rfl⟩⟩
  have hF_inj : Function.Injective F := by
    intro f g h
    have h' : (fun i => toAdd (f i)) = (fun i => toAdd (g i)) :=
      D.el_inj (congrArg Subtype.val h)
    funext i
    exact toAdd.injective (congrFun h' i)
  have hF_surj : Function.Surjective F := by
    intro t
    obtain ⟨v, hv⟩ := D.mem_tor.mp t.prop
    refine ⟨fun i => ofAdd (v i), ?_⟩
    apply Subtype.ext
    change D.el (fun i => toAdd (ofAdd (v i))) = t.val
    simpa using hv.symm
  let eHom : (Fin m → Multiplicative (ZMod 3)) →* D.tor :=
    { toFun := F,
      map_one' := by
        apply Subtype.ext
        dsimp [F]
        change D.el (0 : Fin m → ZMod 3) = 1
        rw [D.el_zero],
      map_mul' := fun f g => by
        apply Subtype.ext
        dsimp [F]
        change D.el ((fun i => toAdd (f i)) + (fun i => toAdd (g i))) =
          D.el (fun i => toAdd (f i)) * D.el (fun i => toAdd (g i))
        rw [D.el_add] }
  let e : (Fin m → Multiplicative (ZMod 3)) ≃* D.tor :=
    MulEquiv.ofBijective eHom ⟨hF_inj, hF_surj⟩
  let u : MulAut (Fin m → Multiplicative (ZMod 3)) := (MulAut.congr e.symm) αD
  have hφ : ∀ f, α (D.el (fun i => toAdd (f i))) =
      D.el (fun i => toAdd (u f i)) := by
    intro f
    have h1 : ((αD (e f) : D.tor) : Matrix.SpecialLinearGroup (Fin d) F2) =
        α (D.el (fun i => toAdd (f i))) := by
      rw [CFSG.GroupTheory.MulAut.restrictNormal_apply]
      rfl
    have h2 : ((αD (e f) : D.tor) : Matrix.SpecialLinearGroup (Fin d) F2) =
        D.el (fun i => toAdd (u f i)) := by
      change ((αD (e f) : D.tor) : Matrix.SpecialLinearGroup (Fin d) F2) =
        ((e (u f) : D.tor) : Matrix.SpecialLinearGroup (Fin d) F2)
      have hu : u f = e.symm (αD (e f)) := rfl
      rw [hu, MulEquiv.apply_symm_apply]
    rw [← h1, h2]
  have hsign : SpCoord.IsSignedPerm u :=
    FrameRoute.isSignedPerm_of_torus_weight_action D wt (by norm_num : 0 < 2) hw hwt α u hφ
  refine ⟨u, hsign, fun f => ?_⟩
  have hof : ∀ g : Fin m → Multiplicative (ZMod 3),
      (Multiplicative.ofAdd (fun i => toAdd (g i))) = g := by
    intro g
    rfl
  have h := hφ f
  dsimp [D, LinTwoTB.TorusData.el] at h
  rw [hof f, hof (u f)] at h
  simpa only [D, LinTwoTB.TorusData.el, ggCommonJRowLinTwo_torus, α,
    MulAut.conj_apply] using h

end CFSG.StandardType.CommonJRowLinTwo

end
