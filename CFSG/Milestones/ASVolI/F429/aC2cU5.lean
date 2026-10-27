module

public import CFSG.Milestones.ASVolI.F429.aU5Psi
public import CFSG.Milestones.ASVolI.F429.aC2cU4
public import CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F429.aU5Chart

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ASVolI.ChF.ClassicalRoots CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
  CFSG.Quasithin.H13.U4Par

section Frob

theorem burnsideF429a_matrix_frob_gen {K ι κ : Type} [Field K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (σ : K →+* K) (Bm Bi : Matrix κ κ K) (hBiBm : Bi * Bm = 1)
    (P : Matrix κ ι K) (Q : Matrix ι κ K) (hPs : P.map σ = P) (hQs : Q.map σ = Q)
    (g : Matrix ι ι K) :
    Bm * (Bi * (Bm * P * g * (Q * Bi)) * Bm).map σ * Bi = Bm * P * g.map σ * (Q * Bi) := by
  have e1 : Bi * (Bm * P * g * (Q * Bi)) * Bm = P * g * Q := by
    rw [show Bi * (Bm * P * g * (Q * Bi)) * Bm = (Bi * Bm) * P * g * Q * (Bi * Bm) by
      simp only [Matrix.mul_assoc], hBiBm, Matrix.one_mul, Matrix.mul_one]
  rw [e1, Matrix.map_mul, Matrix.map_mul, hPs, hQs]
  simp only [Matrix.mul_assoc]

variable {f : ℕ} {H : Type} [Group H] (mk : Marking .U5 2 f H)

theorem burnsideF429a_U5_coe_T (g : hypSU (burnsideF429a_U5_fieldData mk) 2 1) :
    (((burnsideF429a_U5_T mk g : nativeGroup .U5 (2 ^ f) mk.field) : GL (Coord .U5) mk.field) :
      Matrix (Fin 5) (Fin 5) mk.field) =
      burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        ((g : GL (HypIndex 2 1) mk.field) : Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) *
        transportInv (burnsideF429a_U5_fieldData mk)
          (burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) := by
  rw [burnsideF429a_U5_T]
  exact coe_hypTransport _ _

theorem burnsideF429a_U5_T_frob (sigma : mk.field →+* mk.field)
    (hsig : ∀ p, sigma p = p ^ (2 ^ f)) (g : hypSU (burnsideF429a_U5_fieldData mk) 2 1) :
    mk.basis * Matrix.GeneralLinearGroup.map sigma
        (mk.basis⁻¹ * ((burnsideF429a_U5_T mk g : nativeGroup .U5 (2 ^ f) mk.field) :
          GL (Coord .U5) mk.field) * mk.basis) * mk.basis⁻¹ =
      ((burnsideF429a_U5_T mk (act (burnsideF429a_U5_fieldData mk)
        (fieldElt (burnsideF429a_U5_fieldData mk) (barEquiv (burnsideF429a_U5_fieldData mk))) g) :
        nativeGroup .U5 (2 ^ f) mk.field) : GL (Coord .U5) mk.field) := by
  have hBiBm : ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) *
      (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBmBi : (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
      ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hR := burnsideF429a_U5_isHypTransport mk
  have h1 := transportInv_mul hR
  have hRP : burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) =
      (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id (fullPosEquiv (r := 2) (ε := 1)) := by
    ext i a
    simp only [burnsideF429a_hypR, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.one_apply, id,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hPQ : (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id (fullPosEquiv (r := 2) (ε := 1)) *
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix (fullPosEquiv (r := 2) (ε := 1)) id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]
    ext i j
    simp [Matrix.one_apply]
  have hRinv : transportInv (burnsideF429a_U5_fieldData mk)
      (burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) =
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix (fullPosEquiv (r := 2) (ε := 1)) id *
        ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) := by
    set Rinv := transportInv (burnsideF429a_U5_fieldData mk)
      (burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field))
    have hq : Rinv * (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) =
        (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix (fullPosEquiv (r := 2) (ε := 1)) id := by
      calc Rinv * (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)
          = Rinv * (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
              ((1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id (fullPosEquiv (r := 2) (ε := 1)) *
                (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
                  (fullPosEquiv (r := 2) (ε := 1)) id) := by
            rw [hPQ, Matrix.mul_one]
        _ = Rinv * ((mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
              (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id (fullPosEquiv (r := 2) (ε := 1))) *
              (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
                (fullPosEquiv (r := 2) (ε := 1)) id := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hRP, h1, Matrix.one_mul]
    calc Rinv = Rinv * ((mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
          ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field)) := by
          rw [hBmBi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hq]
  have hPs : ((1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id
      (fullPosEquiv (r := 2) (ε := 1))).map sigma =
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix id (fullPosEquiv (r := 2) (ε := 1)) := by
    ext i a
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hQs : ((1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix
      (fullPosEquiv (r := 2) (ε := 1)) id).map sigma =
      (1 : Matrix (Fin 5) (Fin 5) mk.field).submatrix (fullPosEquiv (r := 2) (ε := 1)) id := by
    ext a i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hbar : ((g : GL (HypIndex 2 1) mk.field) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field).map sigma =
      (((act (burnsideF429a_U5_fieldData mk) (fieldElt (burnsideF429a_U5_fieldData mk)
        (barEquiv (burnsideF429a_U5_fieldData mk))) g : hypSU _ 2 1) : GL (HypIndex 2 1) mk.field) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) := by
    have e := mat_act_fieldElt (barEquiv (burnsideF429a_U5_fieldData mk)) g
    unfold mat at e
    rw [e]
    ext a b
    simp only [Matrix.map_apply, hsig, barEquiv_apply, (burnsideF429a_U5_fieldData mk).bar_apply]
  apply Units.ext
  change (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
      ((((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) *
        (((burnsideF429a_U5_T mk g : nativeGroup .U5 (2 ^ f) mk.field) : GL (Coord .U5) mk.field) :
          Matrix (Fin 5) (Fin 5) mk.field) *
        (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)).map sigma) *
      ((mk.basis⁻¹ : GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) = _
  rw [burnsideF429a_U5_coe_T, burnsideF429a_U5_coe_T, ← hbar, hRinv, hRP]
  exact burnsideF429a_matrix_frob_gen sigma _ _ hBiBm _ _ hPs hQs _

end Frob

section Classify

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem burnsideF429a_U5_inv_classify {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (Ψ : hypPSU h 2 1 ≃* ↥Gp) {t : E}
    (htG : t ∉ Gp) (ht2 : t * t = 1) :
    ∃ y : Gam h, y.1.right = 1 ∧ ∀ g : hypSU h 2 1,
      ((Ψ (hypProj h 2 1 (act h y (act h (fieldElt h (barEquiv h)) g))) : ↥Gp) : E) =
        t * ((Ψ (hypProj h 2 1 (act h y g)) : ↥Gp) : E) * t⁻¹ := by
  let α : MulAut (hypPSU h 2 1) := (MulAut.congr Ψ.symm) (burnsideF4d_rho Gp t)
  have hα : ∀ x, ((Ψ (α x) : ↥Gp) : E) = t * ((Ψ x : ↥Gp) : E) * t⁻¹ := by
    intro x
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp t (Ψ x))) : ↥Gp) : E) = t * ((Ψ x : ↥Gp) : E) * t⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply t (Ψ x)
  have hαα : α * α = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    apply Ψ.injective
    apply Subtype.ext
    rw [hα, hα]
    calc t * (t * ((Ψ x : ↥Gp) : E) * t⁻¹) * t⁻¹ = (t * t) * ((Ψ x : ↥Gp) : E) * (t * t)⁻¹ := by
          group
      _ = ((Ψ x : ↥Gp) : E) := by rw [ht2]; group
  have hαP : α ∉ Pi h := by
    rintro ⟨z, hz⟩
    apply htG
    have e : t = ((Ψ z : ↥Gp) : E) := by
      refine burnsideF429a_eq_of_conj hc Ψ fun x => ?_
      rw [← hα]
      congr 2
      rw [← hz]
      rfl
    rw [e]
    exact (Ψ z).2
  obtain ⟨σ, hσ, β, hβ, hαβ⟩ := exists_eq_conj_fieldElt hαα hαP
  obtain ⟨y, hy, rfl⟩ := hβ
  have hy1 : y.1.right = 1 := mem_Gam1.mp hy
  have hσb : σ = barEquiv h := RingEquiv.ext fun c => by rw [hσ, barEquiv_apply]
  refine ⟨y, hy1, fun g => ?_⟩
  have e1 : α (Phi h y (hypProj h 2 1 g)) =
      Phi h y (Phi h (fieldElt h σ) (hypProj h 2 1 g)) := by
    rw [hαβ]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  rw [Phi_apply, Phi_apply, Phi_apply] at e1
  rw [← hσb, ← e1, hα]

end Classify

section Chart

variable {f : ℕ} {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF429a_U5_coe_act {K : Type} [Field K] {h : UnitaryFieldData 2 f K} (y : Gam h)
    (hy : y.1.right = 1) (g : hypSU h 2 1) :
    ((act h y g : hypSU h 2 1) : GL (HypIndex 2 1) K) =
      y.1.left * (g : GL (HypIndex 2 1) K) * y.1.left⁻¹ := by
  show y.1.left * glAut y.1.right (g : GL (HypIndex 2 1) K) * y.1.left⁻¹ = _
  rw [hy, map_one, MulAut.one_apply]

theorem burnsideF429a_U5_transportGL_conj (mk : Marking .U5 2 f ↥Gp)
    (y : Gam (burnsideF429a_U5_fieldData mk)) (hy : y.1.right = 1)
    (g : hypSU (burnsideF429a_U5_fieldData mk) 2 1) :
    transportGL (burnsideF429a_U5_isHypTransport mk) y.1.left *
        ((burnsideF429a_U5_T mk g : nativeGroup .U5 (2 ^ f) mk.field) : GL (Coord .U5) mk.field) *
        (transportGL (burnsideF429a_U5_isHypTransport mk) y.1.left)⁻¹ =
      ((burnsideF429a_U5_T mk (act _ y g) : nativeGroup .U5 (2 ^ f) mk.field) :
        GL (Coord .U5) mk.field) := by
  apply Units.ext
  have hR := burnsideF429a_U5_isHypTransport mk
  change (transportGL hR y.1.left : Matrix (Fin 5) (Fin 5) mk.field) *
      (((burnsideF429a_U5_T mk g : nativeGroup .U5 (2 ^ f) mk.field) : GL (Coord .U5) mk.field) :
        Matrix (Fin 5) (Fin 5) mk.field) *
      ((transportGL hR y.1.left)⁻¹ : GL (Fin 5) mk.field) = _
  have hinv : (((transportGL hR y.1.left)⁻¹ : GL (Fin 5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) =
      burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        ((y.1.left⁻¹ : GL (HypIndex 2 1) mk.field) :
          Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) *
        transportInv (burnsideF429a_U5_fieldData mk)
          (burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) :=
    rfl
  rw [hinv, coe_transportGL, burnsideF429a_U5_coe_T, burnsideF429a_U5_coe_T,
    burnsideF429a_U5_coe_act y hy, transport_mul_mul hR, transport_mul_mul hR, Units.val_mul,
    Units.val_mul]

theorem burnsideF429a_U5_graphAction (mk : Marking .U5 2 f ↥Gp) {t : E}
    (y : Gam (burnsideF429a_U5_fieldData mk)) (hy : y.1.right = 1)
    (ht : ∀ g : hypSU (burnsideF429a_U5_fieldData mk) 2 1,
      ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y (act _ (fieldElt _
        (barEquiv (burnsideF429a_U5_fieldData mk))) g))) : ↥Gp) : E) =
        t * ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y g)) : ↥Gp) : E) * t⁻¹) :
    (NativeCoordinates.classical .U5 rfl mk : NativeCoordinates .U5 2 f ↥Gp).GraphAction t := by
  haveI := (burnsideF429a_U5_fieldData mk).finite
  have hR := burnsideF429a_U5_isHypTransport mk
  let conj : MulAut ↥Gp := (MulAut.congr (burnsideF429a_U5_Psi mk))
    (Phi (burnsideF429a_U5_fieldData mk) y)
  have hconj : ∀ x, conj (burnsideF429a_U5_Psi mk x) =
      burnsideF429a_U5_Psi mk (Phi (burnsideF429a_U5_fieldData mk) y x) := fun x => by
    show burnsideF429a_U5_Psi mk (Phi (burnsideF429a_U5_fieldData mk) y
      ((burnsideF429a_U5_Psi mk).symm (burnsideF429a_U5_Psi mk x))) = _
    rw [MulEquiv.symm_apply_apply]
  have htrans : ∀ g, conj (mk.transport (burnsideF429a_U5_T mk g)) =
      burnsideF429a_U5_Psi mk (hypProj _ 2 1 (act _ y g)) := fun g => by
    rw [← burnsideF429a_U5_Psi_hypProj, hconj, Phi_apply]
  have hmemN : ∀ A : nativeGroup .U5 (2 ^ f) mk.field,
      ∃ g, burnsideF429a_U5_T mk g = A := fun A => (burnsideF429a_U5_T mk).surjective A
  refine ⟨conj, ⟨transportGL hR y.1.left, ?_, fun rep => ?_⟩, Or.inr rfl,
    (burnsideF429a_U5_fieldData mk).bar, (burnsideF429a_U5_fieldData mk).bar_apply,
    fun source => ?_⟩
  ·
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨A, hA, rfl⟩
      obtain ⟨g, hg⟩ := hmemN ⟨A, hA⟩
      have e := burnsideF429a_U5_transportGL_conj mk y hy g
      rw [hg] at e
      show (MulAut.conj (transportGL hR y.1.left)) A ∈ nativeGroup .U5 (2 ^ f) mk.field
      rw [MulAut.conj_apply]
      change transportGL hR y.1.left *
        ((⟨A, hA⟩ : nativeGroup .U5 (2 ^ f) mk.field) : GL (Coord .U5) mk.field) *
        (transportGL hR y.1.left)⁻¹ ∈ nativeGroup .U5 (2 ^ f) mk.field
      rw [e]
      exact (burnsideF429a_U5_T mk (act _ y g)).2
    · rw [Subgroup.card_map_of_injective (MulAut.conj (transportGL hR y.1.left)).injective]
  ·
    obtain ⟨g, rfl⟩ := hmemN rep
    exact ⟨burnsideF429a_U5_T mk (act _ y g),
      (burnsideF429a_U5_transportGL_conj mk y hy g).symm,
      by rw [htrans, burnsideF429a_U5_Psi_hypProj]⟩
  ·
    obtain ⟨g, rfl⟩ := hmemN source
    refine ⟨burnsideF429a_U5_T mk (act _ (fieldElt _ (barEquiv (burnsideF429a_U5_fieldData mk))) g),
      (burnsideF429a_U5_T_frob mk _ (burnsideF429a_U5_fieldData mk).bar_apply g).symm, ?_⟩
    show ((conj (mk.transport (burnsideF429a_U5_T mk (act _ (fieldElt _
      (barEquiv (burnsideF429a_U5_fieldData mk))) g))) : ↥Gp) : E) =
      t * ((conj (mk.transport (burnsideF429a_U5_T mk g)) : ↥Gp) : E) * t⁻¹
    rw [htrans, htrans]
    exact ht g

theorem burnsideF429a_U5_rankInv_iff (chart : NativeChart .U5 2 f Gp) {mk : Marking .U5 2 f ↥Gp}
    (hcp : chart.coordinatePayload = NativeCoordinates.classical .U5 rfl mk)
    (w : hypSU (burnsideF429a_U5_fieldData mk) 2 1) (hw : w * w = 1) :
    chart.coordinatePayload.RankInvolution 1
        ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 w) : ↥Gp) : E) ↔
      ((burnsideF429a_U5_Psi mk (hypProj _ 2 1 w) : ↥Gp) : E) ≠ 1 ∧
        Matrix.rank (((w : GL (HypIndex 2 1) mk.field) :
          Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) - 1) = 1 := by
  have := (burnsideF429a_U5_fieldData mk).charP
  have hR := burnsideF429a_U5_isHypTransport mk
  have hrank : Matrix.rank ((((burnsideF429a_U5_T mk w : nativeGroup .U5 (2 ^ f) mk.field) :
      GL (Coord .U5) mk.field) : Matrix (Fin 5) (Fin 5) mk.field) - 1) =
      Matrix.rank (((w : GL (HypIndex 2 1) mk.field) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) - 1) := by
    rw [burnsideF429a_U5_coe_T]
    have e : burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        ((w : GL (HypIndex 2 1) mk.field) : Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) *
        transportInv (burnsideF429a_U5_fieldData mk)
          (burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) - 1 =
        burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field) *
        (((w : GL (HypIndex 2 1) mk.field) : Matrix (HypIndex 2 1) (HypIndex 2 1) mk.field) - 1) *
        transportInv (burnsideF429a_U5_fieldData mk)
          (burnsideF429a_hypR (r := 2) (ε := 1) (mk.basis : Matrix (Fin 5) (Fin 5) mk.field)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_transportInv hR]
    rw [e]
    exact burnsideF429a_rank_conj_rect (transportInv_mul hR) _
  have hTw2 : burnsideF429a_U5_T mk w * burnsideF429a_U5_T mk w = 1 := by
    rw [← map_mul, hw, map_one]
  constructor
  · intro hri
    rw [hcp] at hri
    obtain ⟨-, hne, -, rep, hrep, hrep2, hrk⟩ := hri
    refine ⟨hne, ?_⟩
    have hker : mk.transport ((burnsideF429a_U5_T mk w)⁻¹ * rep) = 1 := by
      rw [map_mul, map_inv, ← burnsideF429a_U5_Psi_hypProj]
      have hrep' : mk.transport rep = burnsideF429a_U5_Psi mk (hypProj _ 2 1 w) :=
        Subtype.ext hrep
      rw [hrep', inv_mul_cancel]
    rw [burnsideF4f_transport_eq_one_iff] at hker
    obtain ⟨c, hc⟩ := hker
    have hrepc : (rep : GL (Coord .U5) mk.field) =
        (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
          Matrix.GeneralLinearGroup.scalar (Coord .U5) c := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hc2 : c * c = 1 := by
      have e1 := congrArg (fun x : nativeGroup .U5 (2 ^ f) mk.field =>
        (x : GL (Coord .U5) mk.field)) hrep2
      simp only [Subgroup.coe_mul, OneMemClass.coe_one] at e1
      rw [hrepc] at e1
      have hcomm : Matrix.GeneralLinearGroup.scalar (Coord .U5) c *
          (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) =
          (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
            Matrix.GeneralLinearGroup.scalar (Coord .U5) c := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
        exact (Matrix.scalar_commute (c : mk.field) (fun r => Commute.all (c : mk.field) r) _).eq
      have e2 : (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
          Matrix.GeneralLinearGroup.scalar (Coord .U5) c *
          ((burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
            Matrix.GeneralLinearGroup.scalar (Coord .U5) c) =
          Matrix.GeneralLinearGroup.scalar (Coord .U5) (c * c) := by
        have hTT : (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
            (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) = 1 := by
          rw [← Subgroup.coe_mul, hTw2]
          rfl
        calc (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
              Matrix.GeneralLinearGroup.scalar (Coord .U5) c *
              ((burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
                Matrix.GeneralLinearGroup.scalar (Coord .U5) c) =
            (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
              (Matrix.GeneralLinearGroup.scalar (Coord .U5) c *
                (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field)) *
              Matrix.GeneralLinearGroup.scalar (Coord .U5) c := by group
          _ = (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
              (burnsideF429a_U5_T mk w : GL (Coord .U5) mk.field) *
              (Matrix.GeneralLinearGroup.scalar (Coord .U5) c *
                Matrix.GeneralLinearGroup.scalar (Coord .U5) c) := by rw [hcomm]; group
          _ = _ := by rw [hTT, one_mul, ← map_mul]
      rw [e2] at e1
      have e3 := congrArg (fun x : GL (Coord .U5) mk.field =>
        (x : Matrix (Coord .U5) (Coord .U5) mk.field) 0 0) e1
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at e3
      exact Units.ext (by rw [Units.val_mul, Units.val_one]; exact e3)
    have hc1 : c = 1 := by
      have h2 : (2 : mk.field) = 0 := CharTwo.two_eq_zero
      have e : ((c : mk.field) - 1) ^ 2 = 0 := by
        have hcc : (c : mk.field) * c = 1 := by rw [← Units.val_mul, hc2, Units.val_one]
        linear_combination hcc - (c : mk.field) * h2 + h2
      exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp e))
    have hrepT : rep = burnsideF429a_U5_T mk w := by
      apply Subtype.ext
      rw [hrepc, hc1, map_one, mul_one]
    rw [hrepT] at hrk
    rw [← hrank]
    exact hrk
  · rintro ⟨hne, hrk⟩
    rw [hcp]
    refine ⟨(burnsideF429a_U5_Psi mk (hypProj _ 2 1 w)).2, hne, ?_,
      burnsideF429a_U5_T mk w, ?_, hTw2, ?_⟩
    · rw [← Subgroup.coe_mul, ← map_mul, ← map_mul, hw, map_one, map_one]
      rfl
    · rw [← burnsideF429a_U5_Psi_hypProj]
    · rw [hrank]
      exact hrk

end Chart

end CFSG.ASVolI
