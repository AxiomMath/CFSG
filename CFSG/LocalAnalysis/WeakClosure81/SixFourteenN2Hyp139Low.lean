module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

variable {W : Type*} [CommGroup W] [Finite W]

theorem one_le_n_of_hyp139_data {W : Type} [CommGroup W] [Finite W]
    {n : ℕ} (hW : Nat.card W = 4 ^ n)
    {G X : Subgroup (MulAut W)} (hXG : X ≤ G) (hXcard : Nat.card X = 3) : 1 ≤ n := by
  by_contra hlt
  have hn : n = 0 := by omega
  rw [hn, pow_zero] at hW
  haveI : Subsingleton W := (Nat.card_eq_one_iff_unique.mp hW).1
  haveI : Subsingleton (MulAut W) :=
    ⟨fun a b => MulEquiv.ext fun w => Subsingleton.elim _ _⟩
  have hle : Nat.card X ≤ Nat.card (MulAut W) := X.card_le_card_group
  have hcardAut : Nat.card (MulAut W) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨‹Subsingleton (MulAut W)›, ⟨1⟩⟩
  omega

section FinOne

theorem finrank_galoisModule_one (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hW : Nat.card W = 4) :
    letI := galoisModule hw2 x hx3 hfix
    Module.finrank (GaloisField 2 2) (Additive W) = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  have hcard : Nat.card (Additive W) = 4 := hW
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Additive W)
  rw [hcard, hK] at h
  apply Nat.pow_right_injective (by norm_num : 2 ≤ (4 : ℕ))
  show 4 ^ Module.finrank (GaloisField 2 2) (Additive W) = 4 ^ 1
  rw [pow_one]
  exact h.symm

noncomputable def galoisBasis1 (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hW : Nat.card W = 4) :
    letI := galoisModule hw2 x hx3 hfix
    Module.Basis (Fin 1) (GaloisField 2 2) (Additive W) := by
  letI := galoisModule hw2 x hx3 hfix
  exact (Module.finBasis (GaloisField 2 2) (Additive W)).reindex
    (finCongr (finrank_galoisModule_one hw2 x hx3 hfix hW))

noncomputable def galoisEquivFun1 (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hW : Nat.card W = 4) :
    letI := galoisModule hw2 x hx3 hfix
    Additive W ≃ₗ[GaloisField 2 2] (Fin 1 → GaloisField 2 2) := by
  letI := galoisModule hw2 x hx3 hfix
  exact (galoisBasis1 hw2 x hx3 hfix hW).equivFun

noncomputable def psiMul1 (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hW : Nat.card W = 4) :
    W ≃* Multiplicative (Fin 1 → GaloisField 2 2) where
  toFun w := Multiplicative.ofAdd (galoisEquivFun1 hw2 x hx3 hfix hW (Additive.ofMul w))
  invFun v :=
    Additive.toMul (galoisEquivFun1 hw2 x hx3 hfix hW |>.symm (Multiplicative.toAdd v))
  left_inv w := by simp
  right_inv v := by simp
  map_mul' a b := by simp only [ofMul_mul, map_add, ofAdd_add]

noncomputable def hGL1 (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (h : MulAut W) (hcomm : h * x = x * h) (hW : Nat.card W = 4) :
    Matrix.GeneralLinearGroup (Fin 1) (GaloisField 2 2) := by
  letI := galoisModule hw2 x hx3 hfix
  exact matrixOfLinearEquiv
    ((galoisEquivFun1 hw2 x hx3 hfix hW).symm.trans
      ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm).trans
        (galoisEquivFun1 hw2 x hx3 hfix hW)))

theorem hGL1_mul (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (h₁ h₂ : MulAut W) (hc₁ : h₁ * x = x * h₁) (hc₂ : h₂ * x = x * h₂)
    (hc : (h₁ * h₂) * x = x * (h₁ * h₂)) (hW : Nat.card W = 4) :
    letI := galoisModule hw2 x hx3 hfix
    hGL1 hw2 x hx3 hfix (h₁ * h₂) hc hW =
      hGL1 hw2 x hx3 hfix h₁ hc₁ hW * hGL1 hw2 x hx3 hfix h₂ hc₂ hW := by
  letI := galoisModule hw2 x hx3 hfix
  dsimp only [hGL1]
  rw [hGaloisLinearEquiv_mul hw2 x hx3 hfix h₁ h₂ hc₁ hc₂ hc]
  rw [← conj_mul (galoisEquivFun1 hw2 x hx3 hfix hW)
    (hGaloisLinearEquiv hw2 x hx3 hfix h₁ hc₁)
    (hGaloisLinearEquiv hw2 x hx3 hfix h₂ hc₂)]
  exact matrixOfLinearEquiv_mul _ _

theorem hGL1_one (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (hc : (1 : MulAut W) * x = x * 1) (hW : Nat.card W = 4) :
    letI := galoisModule hw2 x hx3 hfix
    hGL1 hw2 x hx3 hfix 1 hc hW = 1 := by
  letI := galoisModule hw2 x hx3 hfix
  dsimp only [hGL1]
  rw [hGaloisLinearEquiv_one, LinearEquiv.refl_trans, LinearEquiv.symm_trans_self,
    matrixOfLinearEquiv_refl]

theorem galoisEquivFun1_hGL1_apply (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (h : MulAut W) (hcomm : h * x = x * h) (hW : Nat.card W = 4) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    galoisEquivFun1 hw2 x hx3 hfix hW
        (hGaloisLinearEquiv hw2 x hx3 hfix h hcomm v) =
      Matrix.mulVec (hGL1 hw2 x hx3 hfix h hcomm hW)
        (galoisEquivFun1 hw2 x hx3 hfix hW v) := by
  letI := galoisModule hw2 x hx3 hfix
  let e := galoisEquivFun1 hw2 x hx3 hfix hW
  let C := e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm).trans e)
  have hC : hGL1 hw2 x hx3 hfix h hcomm hW = matrixOfLinearEquiv C := rfl
  have h1 : e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) v) = C (e v) := by
    change e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) v) =
      e ((hGaloisLinearEquiv hw2 x hx3 hfix h hcomm) (e.symm (e v)))
    rw [e.symm_apply_apply]
  rw [h1, hC, matrixOfLinearEquiv_apply]

noncomputable def hGL1OnCentralizer (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 4)
    (h : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W)))) :
    Matrix.GeneralLinearGroup (Fin 1) (GaloisField 2 2) :=
  hGL1 hw2 x hx3 hfix (h : MulAut W) (hcommOf x G X hxgen h) hW

noncomputable def hGL1Hom (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 4) :
    ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) →*
      Matrix.GeneralLinearGroup (Fin 1) (GaloisField 2 2) where
  toFun := hGL1OnCentralizer hw2 x hx3 hfix G X hxgen hW
  map_one' := by
    change hGL1 hw2 x hx3 hfix (1 : MulAut W) (hcommOf x G X hxgen 1) hW = 1
    exact hGL1_one hw2 x hx3 hfix (hcommOf x G X hxgen 1) hW
  map_mul' := by
    intro h₁ h₂
    change hGL1 hw2 x hx3 hfix
        ((h₁ * h₂ : ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W)))) : MulAut W)
        (hcommOf x G X hxgen (h₁ * h₂)) hW =
      hGL1 hw2 x hx3 hfix (h₁ : MulAut W) (hcommOf x G X hxgen h₁) hW *
        hGL1 hw2 x hx3 hfix (h₂ : MulAut W) (hcommOf x G X hxgen h₂) hW
    exact hGL1_mul hw2 x hx3 hfix (h₁ : MulAut W) (h₂ : MulAut W)
      (hcommOf x G X hxgen h₁) (hcommOf x G X hxgen h₂)
      (hcommOf x G X hxgen (h₁ * h₂)) hW

theorem hGL1Hom_injective (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W)
    (hx3 : x ^ 3 = 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 4) :
    Function.Injective (hGL1Hom hw2 x hx3 hfix G X hxgen hW) := by
  intro h₁ h₂ hEq
  letI := galoisModule hw2 x hx3 hfix
  let e := galoisEquivFun1 hw2 x hx3 hfix hW
  have hM : matrixOfLinearEquiv
      (e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W)
        (hcommOf x G X hxgen h₁)).trans e)) =
      matrixOfLinearEquiv
      (e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W)
        (hcommOf x G X hxgen h₂)).trans e)) := by
    simpa [hGL1Hom, hGL1OnCentralizer, hGL1] using hEq
  have hC := matrixOfLinearEquiv_injective hM
  have hcomp : ∀ L : Additive W ≃ₗ[GaloisField 2 2] Additive W,
      e.trans ((e.symm.trans (L.trans e)).trans e.symm) = L := by
    intro L
    ext v
    simp [LinearEquiv.trans_apply]
  have hL : hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W)
        (hcommOf x G X hxgen h₁) =
      hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W)
        (hcommOf x G X hxgen h₂) := by
    calc hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W)
          (hcommOf x G X hxgen h₁)
        = e.trans ((e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₁ : MulAut W)
            (hcommOf x G X hxgen h₁)).trans e)).trans e.symm) := (hcomp _).symm
      _ = e.trans ((e.symm.trans ((hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W)
            (hcommOf x G X hxgen h₂)).trans e)).trans e.symm) := by rw [hC]
      _ = hGaloisLinearEquiv hw2 x hx3 hfix (h₂ : MulAut W)
            (hcommOf x G X hxgen h₂) := hcomp _
  apply Subtype.ext
  ext w
  have hv := congrArg (fun (g : Additive W ≃ₗ[GaloisField 2 2] Additive W) =>
    g (Additive.ofMul w)) hL
  rw [hGaloisLinearEquiv_apply, hGaloisLinearEquiv_apply] at hv
  simpa using hv

end FinOne

theorem concl139_one_of_hyp139_n1 {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hK : CFSG.Open.IsKGroup ↥G) (hpCore : pCoreOf 2 G = ⊥)
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (ht2 : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hXcard : Nat.card X = 3)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYrk : rkIdx Y = 2)
    (hW : Nat.card W = 4 ^ 1)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2 ^ (1 - 1))
    (hYD : Y ≤ fixV D) :
    Concl139Printed W G X 1 := by
  have hW4 : Nat.card W = 4 := by
    rw [hW]
    norm_num
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    omega
  have hfixX : fixV X = ⊥ := fixV_eq_bot_of_irreducible hirr hXG hXnorm hXne
  have hXcard' : Nat.card ↥X = 3 := hXcard
  letI : Fintype ↥X := Fintype.ofFinite _
  have hXcardF : Fintype.card ↥X = 3 := by
    rw [← Nat.card_eq_fintype_card, hXcard']
  obtain ⟨xX, hxXne⟩ : ∃ xX : ↥X, xX ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : ↥X)
    rw [hXcardF]
    norm_num
  let x : MulAut W := xX
  have hxX : x ∈ X := xX.2
  have hx_ne : x ≠ 1 := by
    intro h
    exact hxXne (Subtype.ext h)
  have hx_ord_dvd : orderOf x ∣ 3 := by
    have h : orderOf xX ∣ 3 := by
      have h2 := orderOf_dvd_natCard xX
      rwa [Nat.card_eq_fintype_card, hXcardF] at h2
    rwa [← Subgroup.orderOf_coe xX] at h
  have hx_ord3 : orderOf x = 3 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf x) hx_ord_dvd with
      h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
    · exact h3
  have hx3 : x ^ 3 = 1 := by
    rw [← hx_ord3]
    exact pow_orderOf_eq_one x
  have hxgen : X = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_
    rw [Nat.card_zpowers, hx_ord3, hXcard]
  have hfix : fixV (Subgroup.zpowers x) = ⊥ := by
    rw [← hxgen]
    exact hfixX
  let H : Subgroup (MulAut W) := G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  have hXleH : X ≤ H := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨hXG hy, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hxgen] at hy hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hm, ← hk, ← zpow_add, ← zpow_add]
    congr 1
    omega
  have hHge : 3 ≤ Nat.card ↥H := by
    have hle : Nat.card X ≤ Nat.card ↥H := Subgroup.card_le_of_le hXleH
    rw [hXcard] at hle
    exact hle
  have hGLcard : Nat.card (Matrix.GeneralLinearGroup (Fin 1) (GaloisField 2 2)) = 3 := by
    letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    rw [Matrix.card_GL_field (n := 1)]
    have hq : Fintype.card (GaloisField 2 2) = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    simp [Fin.prod_univ_one, hq]
  have hφinj : Function.Injective (hGL1Hom hw2 x hx3 hfix G X hxgen hW4) :=
    hGL1Hom_injective hw2 x hx3 hfix G X hxgen hW4
  have hHle : Nat.card ↥H ≤ 3 := by
    have h := Nat.card_le_card_of_injective (hGL1Hom hw2 x hx3 hfix G X hxgen hW4) hφinj
    rwa [hGLcard] at h
  have hHcard : Nat.card ↥H = 3 := le_antisymm hHle hHge
  have hφbij : Function.Bijective (hGL1Hom hw2 x hx3 hfix G X hxgen hW4) :=
    hφinj.bijective_of_nat_card_le (by rw [hHcard, hGLcard])
  let φ : ↥H ≃* Matrix.GeneralLinearGroup (Fin 1) (GaloisField 2 2) :=
    MulEquiv.ofBijective (hGL1Hom hw2 x hx3 hfix G X hxgen hW4) hφbij
  let ψ : W ≃* Multiplicative (Fin 1 → GaloisField 2 2) :=
    psiMul1 hw2 x hx3 hfix hW4
  refine Or.inl ⟨φ, ψ, ?_⟩
  intro a w
  have hv := galoisEquivFun1_hGL1_apply hw2 x hx3 hfix (a : MulAut W)
    (hcommOf x G X hxgen a) hW4 (Additive.ofMul w)
  change Multiplicative.ofAdd
      (galoisEquivFun1 hw2 x hx3 hfix hW4 (Additive.ofMul ((a : MulAut W) w))) =
    Multiplicative.ofAdd
      ((hGL1 hw2 x hx3 hfix (a : MulAut W) (hcommOf x G X hxgen a) hW4 :
          Matrix (Fin 1) (Fin 1) (GaloisField 2 2)).mulVec
        (galoisEquivFun1 hw2 x hx3 hfix hW4 (Additive.ofMul w)))
  have hL : Additive.ofMul ((a : MulAut W) w) =
      hGaloisLinearEquiv hw2 x hx3 hfix (a : MulAut W)
        (hcommOf x G X hxgen a) (Additive.ofMul w) := by
    rw [hGaloisLinearEquiv_apply]
    simp
  rw [hL, hv]

end CFSG.LocalAnalysis.WeakClosure81
