module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OParA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OOutR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix
open CFSG.LocalAnalysis.RankThreeUC
open OutLin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

@[expose] def radShift (g : OutLin.GL6 F) : F := gv g (fV F idx0) (Sum.inl idx1)

theorem radM_n_coord {g : OutLin.GL6 F} (hg : RadHyp b c g) (z : OW F) (k : Fin 2) :
    gv g z (Sum.inr (Sum.inr k)) = z (Sum.inr (Sum.inr k)) +
      z (Sum.inr (Sum.inl idx0)) * OutLin.mcol g idx0 k +
      z (Sum.inr (Sum.inl idx1)) * OutLin.mcol g idx1 k := by
  have hk : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rw [gv_apply_decomp, hg.fixE idx0, hg.fixE idx1, hg.n_coord_nVec 0 k, hg.n_coord_nVec 1 k]
  rcases hk k with rfl | rfl <;>
    simp only [OutLin.mcol, eV_inr, nVec_00, nVec_01, nVec_10, nVec_11, mul_zero, add_zero,
      zero_mul, mul_one] <;> ring

theorem radM_e1_coord {g : OutLin.GL6 F} (hg : RadHyp b c g) (z : OW F) :
    gv g z (Sum.inl idx1) = z (Sum.inl idx1) + z (Sum.inr (Sum.inl idx0)) * radShift g +
      z (Sum.inr (Sum.inl idx1)) *
        (OutLin.mcol g idx1 0 ^ 2 + b * OutLin.mcol g idx1 0 * OutLin.mcol g idx1 1 +
          c * OutLin.mcol g idx1 1 ^ 2) +
      z (Sum.inr (Sum.inr 0)) * (b * OutLin.mcol g idx1 1) +
      z (Sum.inr (Sum.inr 1)) * (b * OutLin.mcol g idx1 0) := by
  obtain ⟨-, A2, -, -, -, A6, A7⟩ := OutLin.RadHyp.e_coords hg
  rw [gv_apply_decomp, hg.fixE idx0, hg.fixE idx1, A2, A6, A7]
  simp only [radShift, OutLin.mcol, eV_self idx1, eV_ne (i := idx0) (k := idx1) (by decide), eV_inr]
  ring

theorem radM_additive {g h : OutLin.GL6 F} (hg : RadHyp b c g) (hh : RadHyp b c h) :
    OutLin.mcol (g * h) = OutLin.mcol g + OutLin.mcol h := by
  have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
  ext i k
  rw [OutLin.mcol, gv_mul, radM_n_coord hg (gv h (fV F i)) k]
  rw [hh.f_coord (fV F i) idx0, hh.f_coord (fV F i) idx1]
  rcases hi i with rfl | rfl
  · simp only [OutLin.mcol, fV_self idx0, fV_ne (i := idx0) (k := idx1) (by decide),
      Pi.add_apply]
    ring
  · simp only [OutLin.mcol, fV_self idx1, fV_ne (i := idx1) (k := idx0) (by decide),
      Pi.add_apply]
    ring

theorem radShift_mul {g h : OutLin.GL6 F} (hg : RadHyp b c g) (hh : RadHyp b c h) :
    radShift (g * h) = radShift g + radShift h +
      b * (OutLin.mcol h idx0 0 * OutLin.mcol g idx1 1 +
        OutLin.mcol h idx0 1 * OutLin.mcol g idx1 0) := by
  rw [radShift, gv_mul, radM_e1_coord hg (gv h (fV F idx0)),
    hh.f_coord (fV F idx0) idx0, hh.f_coord (fV F idx0) idx1]
  simp only [radShift, OutLin.mcol, fV_self idx0, fV_ne (i := idx0) (k := idx1) (by decide),
    mul_one, mul_zero, add_zero, zero_mul]
  ring

@[expose] def radBeta (b : F) (M N : Matrix (Fin (3 - 1)) (Fin 2) F) : F :=
  b * (M idx0 0 * N idx1 1 + M idx0 1 * N idx1 0 + M idx1 0 * N idx0 1 +
    M idx1 1 * N idx0 0)

theorem radBeta_add_left (M M' N : Matrix (Fin (3 - 1)) (Fin 2) F) :
    radBeta b (M + M') N = radBeta b M N + radBeta b M' N := by
  simp only [radBeta, Matrix.add_apply]
  ring

theorem radBeta_smul_left (a : F) (M N : Matrix (Fin (3 - 1)) (Fin 2) F) :
    radBeta b (a • M) N = a * radBeta b M N := by
  simp only [radBeta, Matrix.smul_apply, smul_eq_mul]
  ring

theorem radBeta_add_right (M N N' : Matrix (Fin (3 - 1)) (Fin 2) F) :
    radBeta b M (N + N') = radBeta b M N + radBeta b M N' := by
  simp only [radBeta, Matrix.add_apply]
  ring

theorem radBeta_smul_right (a : F) (M N : Matrix (Fin (3 - 1)) (Fin 2) F) :
    radBeta b M (a • N) = a * radBeta b M N := by
  simp only [radBeta, Matrix.smul_apply, smul_eq_mul]
  ring

theorem radBeta_zero_left (N : Matrix (Fin (3 - 1)) (Fin 2) F) : radBeta b 0 N = 0 := by
  simp [radBeta]

theorem radBeta_zero_right (M : Matrix (Fin (3 - 1)) (Fin 2) F) : radBeta b M 0 = 0 := by
  simp [radBeta]

@[expose] def radBilin (b : F) :
    LinearMap.BilinForm F (Matrix (Fin (3 - 1)) (Fin 2) F) :=
  LinearMap.mk₂ F (radBeta b) (fun M M' N => radBeta_add_left M M' N)
    (fun a M N => radBeta_smul_left a M N) (fun M N N' => radBeta_add_right M N N')
    (fun a M N => radBeta_smul_right a M N)

theorem radBilin_apply (M N : Matrix (Fin (3 - 1)) (Fin 2) F) :
    radBilin b M N = radBeta b M N := by
  rw [radBilin, LinearMap.mk₂_apply]

theorem radBilin_isAlt : (radBilin (b := b)).IsAlt := by
  intro M
  rw [radBilin_apply]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [radBeta]
  linear_combination (b * (M idx0 0 * M idx1 1 + M idx0 1 * M idx1 0)) * h2

theorem radBilin_nondegenerate (hb : b ≠ 0) : (radBilin (b := b)).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl (radBilin_isAlt (b := b))).nondegenerate_iff_separatingLeft.2
    fun M hM => ?_
  ext i k
  have hi : ∀ i : Fin (3 - 1), i = idx0 ∨ i = idx1 := by decide
  have hk : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  rcases hi i with rfl | rfl <;> rcases hk k with rfl | rfl
  · have h := hM (Matrix.single idx1 1 (1 : F))
    rw [radBilin_apply, radBeta] at h
    simp [Matrix.single_apply, idx0, idx1] at h
    rcases h with h0 | h0
    · exact absurd h0 hb
    · exact h0
  · have h := hM (Matrix.single idx1 0 (1 : F))
    rw [radBilin_apply, radBeta] at h
    simp [Matrix.single_apply, idx0, idx1] at h
    rcases h with h0 | h0
    · exact absurd h0 hb
    · exact h0
  · have h := hM (Matrix.single idx0 1 (1 : F))
    rw [radBilin_apply, radBeta] at h
    simp [Matrix.single_apply, idx0, idx1] at h
    rcases h with h0 | h0
    · exact absurd h0 hb
    · exact h0
  · have h := hM (Matrix.single idx0 0 (1 : F))
    rw [radBilin_apply, radBeta] at h
    simp [Matrix.single_apply, idx0, idx1] at h
    rcases h with h0 | h0
    · exact absurd h0 hb
    · exact h0

theorem commute_iff_radBeta {g h : OutLin.GL6 F} (hg : RadHyp b c g) (hh : RadHyp b c h) :
    g * h = h * g ↔ radBeta b (OutLin.mcol g) (OutLin.mcol h) = 0 := by
  have key : radBeta b (OutLin.mcol g) (OutLin.mcol h) =
      radShift (g * h) + radShift (h * g) := by
    rw [radShift_mul hg hh, radShift_mul hh hg]
    simp only [radBeta]
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination - (radShift g + radShift h) * h2
  constructor
  · intro hc
    rw [key, hc]
    exact CharTwo.add_self_eq_zero (radShift (h * g))
  · intro hβ
    refine OutLin.RadHyp.ext_params (radHyp_mul hg hh) (radHyp_mul hh hg) ?_ ?_
    · intro i k
      have hm : OutLin.mcol (g * h) = OutLin.mcol (h * g) := by
        rw [radM_additive hg hh, radM_additive hh hg, add_comm]
      exact congrFun (congrFun hm i) k
    · have h0 : radShift (g * h) + radShift (h * g) = 0 := by
        rw [← key]
        exact hβ
      exact OutLin.eq_of_add_eq_zero_char_two h0

theorem finrank_le_two_of_isTotallyIsotropic (hb : b ≠ 0)
    {W : Submodule F (Matrix (Fin (3 - 1)) (Fin 2) F)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, radBeta b x y = 0) : Module.finrank F W ≤ 2 := by
  have hB := radBilin_nondegenerate (b := b) hb
  have hle : W ≤ (radBilin (b := b)).orthogonal W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [radBilin_apply]
    exact hW y hy x hx
  have hmono : Module.finrank F W ≤
      Module.finrank F ((radBilin (b := b)).orthogonal W) := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB W] at hmono
  have hdim : Module.finrank F (Matrix (Fin (3 - 1)) (Fin 2) F) = 4 := by
    rw [Module.finrank_matrix]
    norm_num
  rw [hdim] at hmono
  omega

def radMHom {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hE : E ≤ RadGrp b c) : E →* Multiplicative (Matrix (Fin (3 - 1)) (Fin 2) F) where
  toFun g := Multiplicative.ofAdd (OutLin.mcol (g : OutLin.GL6 F))
  map_one' := by
    change Multiplicative.ofAdd (OutLin.mcol (1 : OutLin.GL6 F)) = 1
    have h1 : OutLin.mcol (1 : OutLin.GL6 F) = 0 := by
      ext i k
      simp [OutLin.mcol, gv_one]
    rw [h1]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (OutLin.mcol ((g : OutLin.GL6 F) * (h : OutLin.GL6 F))) =
      Multiplicative.ofAdd (OutLin.mcol (g : OutLin.GL6 F)) *
        Multiplicative.ofAdd (OutLin.mcol (h : OutLin.GL6 F))
    rw [radM_additive (hE g.2) (hE h.2)]
    rfl

theorem card_radM_ker_le {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hE : E ≤ RadGrp b c) : Nat.card (radMHom hE).ker ≤ Nat.card F := by
  have hmem : ∀ g : (radMHom hE).ker, ∀ (i : Fin (3 - 1)) (k : Fin 2),
      gv (g.1.1) (fV F i) (Sum.inr (Sum.inr k)) = 0 := by
    intro g i k
    have h1 : radMHom hE g.1 = 1 := MonoidHom.mem_ker.mp g.2
    have h2 : (radMHom hE g.1).toAdd = 0 := by rw [h1]; rfl
    exact congrFun (congrFun h2 i) k
  refine Nat.card_le_card_of_injective (fun g : (radMHom hE).ker => radShift g.1.1) ?_
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  exact OutLin.RadHyp.ext_params (hE g.1.2) (hE h.1.2)
    (fun i k => by rw [hmem g i k, hmem h i k]) hgh

theorem card_le_of_le_radGrp_of_isMulCommutative (hb : b ≠ 0)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hE : E ≤ RadGrp b c) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    Nat.card E ≤ Nat.card F ^ 3 := by
  classical
  let mHom : E →* Multiplicative (Matrix (Fin (3 - 1)) (Fin 2) F) := radMHom hE
  let S : Set (Matrix (Fin (3 - 1)) (Fin 2) F) :=
    Set.range fun g : E => OutLin.mcol (g : OutLin.GL6 F)
  let W : Submodule F (Matrix (Fin (3 - 1)) (Fin 2) F) := Submodule.span F S
  have hS : ∀ x ∈ S, ∀ y ∈ S, radBeta b x y = 0 := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    exact (commute_iff_radBeta (hE g.2) (hE h.2)).1 (hcomm g g.2 h h.2)
  have hleft : ∀ y ∈ S, ∀ x ∈ W, radBeta b x y = 0 := by
    intro y hy x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hS x hx y hy
    | zero => exact radBeta_zero_left (b := b) y
    | add x x' hx hx' ih ih' => rw [radBeta_add_left, ih, ih', add_zero]
    | smul a x hx ih => rw [radBeta_smul_left, ih, mul_zero]
  have hiso : ∀ x ∈ W, ∀ y ∈ W, radBeta b x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hleft y hy x hx
    | zero => exact radBeta_zero_right (b := b) x
    | add y y' hy hy' ih ih' => rw [radBeta_add_right, ih, ih', add_zero]
    | smul a y hy ih => rw [radBeta_smul_right, ih, mul_zero]
  have hdimW : Module.finrank F W ≤ 2 := finrank_le_two_of_isTotallyIsotropic hb hiso
  have hWcard : Nat.card W ≤ Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := W)]
    exact pow_le_pow_right₀ (by have := Nat.card_pos (α := F); omega) hdimW
  have hScard : Nat.card S ≤ Nat.card F ^ 2 := by
    have hinj : Function.Injective fun x : S => (⟨x.1, Submodule.subset_span x.2⟩ : W) := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : W => z.1) hxy)
    exact (Nat.card_le_card_of_injective _ hinj).trans hWcard
  let e : mHom.range ≃ S :=
    { toFun := fun x =>
        ⟨Multiplicative.toAdd (x : Multiplicative (Matrix (Fin (3 - 1)) (Fin 2) F)),
          by
            obtain ⟨g, hg⟩ := x.2
            exact ⟨g, by rw [← hg]; rfl⟩⟩
      invFun := fun x =>
        ⟨Multiplicative.ofAdd (x : Matrix (Fin (3 - 1)) (Fin 2) F),
          by
            obtain ⟨g, hg⟩ := x.2
            exact ⟨g, by rw [← hg]; rfl⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        rfl }
  have hrange : Nat.card mHom.range ≤ Nat.card F ^ 2 := by
    rw [Nat.card_congr e]
    exact hScard
  have hker : Nat.card mHom.ker ≤ Nat.card F := card_radM_ker_le hE
  calc Nat.card E = Nat.card mHom.ker * Nat.card mHom.range :=
        (Subgroup.card_ker_mul_card_range mHom).symm
    _ ≤ Nat.card F * Nat.card F ^ 2 := Nat.mul_le_mul hker hrange
    _ = Nat.card F ^ 3 := by ring

theorem card_le_of_le_radGrp_of_isMulCommutative_of_irreducible
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hE : E ≤ RadGrp b c) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    Nat.card E ≤ Nat.card F ^ 3 :=
  card_le_of_le_radGrp_of_isMulCommutative (OutLin.b_ne_zero hirr) hE hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
