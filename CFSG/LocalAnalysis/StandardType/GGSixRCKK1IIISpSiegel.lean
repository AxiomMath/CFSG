module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.LieType.BorelTits
open scoped Matrix

@[expose] noncomputable def spB (m : ℕ) (x y : Fin m ⊕ Fin m → GaloisField 2 1) : GaloisField 2 1 :=
  x ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 1)) *ᵥ y)

@[expose] noncomputable def spAct {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (v : Fin m ⊕ Fin m → GaloisField 2 1) : Fin m ⊕ Fin m → GaloisField 2 1 :=
  ((g : GL (Fin m ⊕ Fin m) (GaloisField 2 1)) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (GaloisField 2 1)) *ᵥ v

@[expose] def SpSiegel {m : ℕ} (x y : Fin m ⊕ Fin m → GaloisField 2 1)
    (s : ↥(StatedSp m (GaloisField 2 1))) : Prop :=
  ∀ v, spAct s v = v + spB m y v • x + spB m x v • y

theorem spAct_eq_natRep {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct g v = natRep (StatedSp m (GaloisField 2 1)) g v := by
  rw [natRep_apply]
  rfl

theorem spB_eq_spForm {m : ℕ} (x y : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m x y = (spForm m (GaloisField 2 1)).β x y := by
  rw [spForm_β]
  rfl

theorem spB_add_left {m : ℕ} (u u' v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m (u + u') v = spB m u v + spB m u' v := by
  simp only [spB_eq_spForm]
  exact (spForm m (GaloisField 2 1)).add_left u u' v

theorem spB_add_right {m : ℕ} (u v v' : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m u (v + v') = spB m u v + spB m u v' := by
  simp only [spB_eq_spForm]
  exact (spForm m (GaloisField 2 1)).add_right u v v'

theorem spB_smul_right {m : ℕ} (c : GaloisField 2 1)
    (u v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m u (c • v) = c * spB m u v := by
  simp only [spB_eq_spForm]
  exact (spForm m (GaloisField 2 1)).smul_right c u v

theorem spB_self {m : ℕ} (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m v v = 0 := by
  simp only [spB_eq_spForm]
  exact spForm_self m (GaloisField 2 1) v

theorem spB_refl {m : ℕ} {u v : Fin m ⊕ Fin m → GaloisField 2 1}
    (h : spB m u v = 0) : spB m v u = 0 := by
  simp only [spB_eq_spForm] at h ⊢
  exact (spForm m (GaloisField 2 1)).refl u v h

private theorem rckSpS_spB_zero_left (m : ℕ) (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m 0 v = 0 := by
  simp only [spB_eq_spForm]
  exact (spForm m (GaloisField 2 1)).β_zero_left v

private theorem rckSpS_spAct_one {m : ℕ} (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct (1 : ↥(StatedSp m (GaloisField 2 1))) v = v := by
  rw [spAct_eq_natRep, map_one, Module.End.one_apply]

theorem spAct_add {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (u w : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct g (u + w) = spAct g u + spAct g w := by
  simp only [spAct_eq_natRep]
  exact map_add (natRep (StatedSp m (GaloisField 2 1)) g) u w

theorem spAct_smul {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (c : GaloisField 2 1) (w : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct g (c • w) = c • spAct g w := by
  simp only [spAct_eq_natRep]
  exact map_smul (natRep (StatedSp m (GaloisField 2 1)) g) c w

private theorem rckSpS_spAct_mul {m : ℕ} (s t : ↥(StatedSp m (GaloisField 2 1)))
    (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct (s * t) v = spAct s (spAct t v) := by
  simp only [spAct_eq_natRep, map_mul, Module.End.mul_apply]

theorem spAct_inv_apply {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct g (spAct g⁻¹ v) = v := by
  simp only [spAct_eq_natRep]
  exact rep_apply_inv_apply (natRep (StatedSp m (GaloisField 2 1))) g v

private theorem rckSpS_spAct_conj {m : ℕ} (g s : ↥(StatedSp m (GaloisField 2 1)))
    (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct (g * s * g⁻¹) v = spAct g (spAct s (spAct g⁻¹ v)) := by
  rw [rckSpS_spAct_mul, rckSpS_spAct_mul]

private theorem rckSpS_spAct_beta {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (u v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m (spAct g u) (spAct g v) = spB m u v := by
  simp only [spB_eq_spForm, spAct_eq_natRep]
  exact isIsometric_natRep_statedSp m (GaloisField 2 1) g u v

private theorem rckSpS_beta_conj {m : ℕ} (g : ↥(StatedSp m (GaloisField 2 1)))
    (y v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spB m (spAct g y) v = spB m y (spAct g⁻¹ v) := by
  calc spB m (spAct g y) v
      = spB m (spAct g y) (spAct g (spAct g⁻¹ v)) := by rw [spAct_inv_apply]
    _ = spB m y (spAct g⁻¹ v) := rckSpS_spAct_beta g y (spAct g⁻¹ v)

private theorem rckSpS_siegel_form_left (m : ℕ) {x y z v : Fin m ⊕ Fin m → GaloisField 2 1}
    (hxy : spB m x y = 0) (hyz : spB m y z = 0) :
    spB m y (v + spB m z v • x + spB m x v • z) = spB m y v := by
  rw [spB_add_right, spB_add_right, spB_smul_right,
    spB_smul_right, spB_refl hxy, hyz]
  simp

private theorem rckSpS_siegel_form_second (m : ℕ) {x z v : Fin m ⊕ Fin m → GaloisField 2 1}
    (hxz : spB m x z = 0) :
    spB m x (v + spB m z v • x + spB m x v • z) = spB m x v := by
  rw [spB_add_right, spB_add_right, spB_smul_right,
    spB_smul_right, spB_self, hxz]
  simp

private theorem rckSpS_siegel_mul_apply (m : ℕ) {x y z v : Fin m ⊕ Fin m → GaloisField 2 1}
    (hxy : spB m x y = 0) (hxz : spB m x z = 0) (hyz : spB m y z = 0) :
    (v + spB m z v • x + spB m x v • z) +
        spB m y (v + spB m z v • x + spB m x v • z) • x +
        spB m x (v + spB m z v • x + spB m x v • z) • y =
      v + spB m (y + z) v • x + spB m x v • (y + z) := by
  rw [rckSpS_siegel_form_left m hxy hyz, rckSpS_siegel_form_second m hxz,
    spB_add_left, add_smul, smul_add]
  abel

private theorem rckSpS_siegel_form_conj {m : ℕ} {x y : Fin m ⊕ Fin m → GaloisField 2 1}
    (g : ↥(StatedSp m (GaloisField 2 1))) (v : Fin m ⊕ Fin m → GaloisField 2 1) :
    spAct g (spAct g⁻¹ v + spB m y (spAct g⁻¹ v) • x + spB m x (spAct g⁻¹ v) • y) =
      v + spB m (spAct g y) v • spAct g x + spB m (spAct g x) v • spAct g y := by
  rw [spAct_add, spAct_add, spAct_smul, spAct_smul,
    spAct_inv_apply, rckSpS_beta_conj g y v, rckSpS_beta_conj g x v]

private theorem rckSpS_spSiegel_zero_left {m : ℕ} (y : Fin m ⊕ Fin m → GaloisField 2 1) :
    SpSiegel (0 : Fin m ⊕ Fin m → GaloisField 2 1) y
      (1 : ↥(StatedSp m (GaloisField 2 1))) := by
  intro v
  rw [rckSpS_spAct_one, rckSpS_spB_zero_left]
  simp

theorem spSiegel_exists {m : ℕ} {x y : Fin m ⊕ Fin m → GaloisField 2 1} (h : spB m x y = 0) :
    ∃ s : ↥(StatedSp m (GaloisField 2 1)), SpSiegel x y s := by
  have hxy : (spForm m (GaloisField 2 1)).β x y = 0 := by
    rw [← spB_eq_spForm]
    exact h
  obtain ⟨s, hs⟩ := CFSG.QuasithinUnique.B113Lie.Sp.exists_siegel
    (K := GaloisField 2 1) (r := m) x y hxy
  refine ⟨s, fun v => ?_⟩
  simp only [spAct_eq_natRep, spB_eq_spForm]
  rw [hs v]
  abel

theorem spSiegel_ext {m : ℕ} {x y : Fin m ⊕ Fin m → GaloisField 2 1}
    {s t : ↥(StatedSp m (GaloisField 2 1))} (hs : SpSiegel x y s) (ht : SpSiegel x y t) :
    s = t := by
  apply natRep_injective (StatedSp m (GaloisField 2 1))
  apply LinearMap.ext
  intro v
  rw [show natRep (StatedSp m (GaloisField 2 1)) s v = spAct s v from
        (spAct_eq_natRep s v).symm,
      show natRep (StatedSp m (GaloisField 2 1)) t v = spAct t v from
        (spAct_eq_natRep t v).symm,
      hs v, ht v]

theorem spSiegel_zero_right {m : ℕ} (x : Fin m ⊕ Fin m → GaloisField 2 1) :
    SpSiegel x 0 (1 : ↥(StatedSp m (GaloisField 2 1))) := by
  intro v
  rw [rckSpS_spAct_one, rckSpS_spB_zero_left]
  simp

theorem spSiegel_self {m : ℕ} (x : Fin m ⊕ Fin m → GaloisField 2 1) :
    SpSiegel x x (1 : ↥(StatedSp m (GaloisField 2 1))) := by
  intro v
  rw [rckSpS_spAct_one]
  have hcc : spB m x v • x + spB m x v • x = 0 := by
    rw [← two_smul (GaloisField 2 1) (spB m x v • x),
      show (2 : GaloisField 2 1) = 0 from CharP.cast_eq_zero (GaloisField 2 1) 2, zero_smul]
  rw [add_assoc, hcc, add_zero]

theorem spSiegel_mul {m : ℕ} {x y z : Fin m ⊕ Fin m → GaloisField 2 1}
    {s t : ↥(StatedSp m (GaloisField 2 1))} (hxy : spB m x y = 0) (hxz : spB m x z = 0)
    (hyz : spB m y z = 0) (hs : SpSiegel x y s) (ht : SpSiegel x z t) :
    SpSiegel x (y + z) (s * t) := by
  intro v
  rw [rckSpS_spAct_mul, ht v]
  rw [hs (v + spB m z v • x + spB m x v • z)]
  exact rckSpS_siegel_mul_apply m hxy hxz hyz

theorem spSiegel_conj {m : ℕ} {x y : Fin m ⊕ Fin m → GaloisField 2 1}
    {s : ↥(StatedSp m (GaloisField 2 1))} (hs : SpSiegel x y s)
    (g : ↥(StatedSp m (GaloisField 2 1))) :
    SpSiegel (spAct g x) (spAct g y) (g * s * g⁻¹) := by
  intro v
  rw [rckSpS_spAct_conj, hs (spAct g⁻¹ v)]
  exact rckSpS_siegel_form_conj g v

theorem spSiegel_eq_one_iff {m : ℕ} {x y : Fin m ⊕ Fin m → GaloisField 2 1}
    {s : ↥(StatedSp m (GaloisField 2 1))} (hs : SpSiegel x y s) :
    s = 1 ↔ (x = 0 ∨ y = 0 ∨ x = y) := by
  constructor
  · intro h1
    by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hy0, hxne⟩ := hcon
    obtain ⟨v, hv⟩ := CFSG.QuasithinUnique.B113Lie.Sp.exists_β_eq_one
      (F := spForm m (GaloisField 2 1)) (u := y) hy0
    have hsv := hs v
    rw [h1, rckSpS_spAct_one] at hsv
    have ht : spB m y v • x + spB m x v • y = 0 := by
      apply add_left_cancel (a := v)
      rw [add_zero, ← add_assoc]
      exact hsv.symm
    rw [spB_eq_spForm, hv, one_smul] at ht
    by_cases hc : spB m x v = 0
    · rw [hc, zero_smul, add_zero] at ht
      exact hx0 ht
    · have hxcy : x = spB m x v • y := by
        have hcc0 : spB m x v • y + spB m x v • y = 0 := by
          rw [← two_smul (GaloisField 2 1) (spB m x v • y),
            show (2 : GaloisField 2 1) = 0 from CharP.cast_eq_zero (GaloisField 2 1) 2,
            zero_smul]
        exact (eq_neg_of_add_eq_zero_left ht).trans
          (eq_neg_of_add_eq_zero_left hcc0).symm
      have hc1 : spB m x v = 1 := by
        haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
        have hcard : Nat.card (GaloisField 2 1) = 2 := by
          rw [GaloisField.card 2 1 one_ne_zero]
          norm_num
        have hpow := FiniteField.pow_card_sub_one_eq_one (K := GaloisField 2 1)
          (spB m x v) hc
        rw [← Nat.card_eq_fintype_card, hcard] at hpow
        simpa using hpow
      exact hxne (by rw [hxcy, hc1, one_smul])
  · intro h
    rcases h with hx | hy | hxy
    · subst hx
      exact spSiegel_ext hs (rckSpS_spSiegel_zero_left y)
    · subst hy
      exact spSiegel_ext hs (spSiegel_zero_right x)
    · subst hxy
      exact spSiegel_ext hs (spSiegel_self x)

end CFSG.StandardType.RCKK1IIISp
