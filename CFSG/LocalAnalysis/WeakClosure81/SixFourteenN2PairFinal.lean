module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2PairBasis
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2PairGroups
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2PairTensor

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.G11.Canon.F2Tensor

open scoped Pointwise TensorProduct

private lemma permActLin_mul' : ∀ (σ τ : Equiv.Perm (Fin 3)),
    permActLin 3 (σ * τ) = permActLin 3 σ * permActLin 3 τ := by
  intro σ τ
  ext x
  rw [LinearEquiv.mul_apply, permActLin_apply, permActLin_apply, permActLin_apply,
    permActCore_mul]

private lemma tensorAction_one' : tensorAction (1 : Equiv.Perm (Fin 3))
    (1 : GL (Fin 2) (ZMod 2)) = LinearEquiv.refl _ _ := by
  rw [tensorAction]
  convert TensorProduct.congr_refl_refl using 2
  · ext x
    rw [permActLin_apply, permActCore_one]
    rfl
  · exact map_one (s16c1610_glAction 2)

private lemma tensorAction_mul' : ∀ (σ τ : Equiv.Perm (Fin 3))
    (A B : GL (Fin 2) (ZMod 2)),
    tensorAction σ A * tensorAction τ B = tensorAction (σ * τ) (A * B) := by
  intro σ τ A B
  rw [tensorAction, tensorAction, tensorAction, ← TensorProduct.congr_mul,
    ← permActLin_mul', ← map_mul]

private lemma tensorAction_inv' : ∀ (σ : Equiv.Perm (Fin 3)) (A : GL (Fin 2) (ZMod 2)),
    (tensorAction σ A).symm = tensorAction σ⁻¹ A⁻¹ := by
  intro σ A
  rw [tensorAction, tensorAction, TensorProduct.congr_symm, map_inv,
    show (permActLin 3 σ).symm = permActLin 3 σ⁻¹ from rfl]
  rfl

private theorem compat_of_surjective_generators {W : Type} [CommGroup W] [Finite W]
    [Module (ZMod 2) (Additive W)]
    {G : Subgroup (MulAut W)} {x s0 v0 d0 : MulAut W}
    (R S : GL (Fin 2) (ZMod 2))
    (hAG : Subgroup.closure ({x, s0} : Set (MulAut W)) ≤ G)
    (hBG : Subgroup.closure ({v0, d0} : Set (MulAut W)) ≤ G)
    (hdecomp : ∀ g ∈ G,
      ∃ a ∈ Subgroup.closure ({x, s0} : Set (MulAut W)),
      ∃ b ∈ Subgroup.closure ({v0, d0} : Set (MulAut W)), a * b = g)
    {φ : ↥G ≃* (Equiv.Perm (Fin 3) × GL (Fin 2) (ZMod 2))}
    {e : Additive W ≃ₗ[ZMod 2]
      ((↥(CFSG.Quasithin.permCore 3)) ⊗[ZMod 2] (Fin 2 → ZMod 2))}
    (hφx : ∀ (hx : x ∈ G), φ ⟨x, hx⟩ = (finRotate 3, 1))
    (hφs : ∀ (hs : s0 ∈ G), φ ⟨s0, hs⟩ = (Equiv.swap 0 1, 1))
    (hφv : ∀ (hv : v0 ∈ G), φ ⟨v0, hv⟩ = (1, R))
    (hφd : ∀ (hd : d0 ∈ G), φ ⟨d0, hd⟩ = (1, S))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (f : M →ₗ[ZMod 2] Additive W) (hf : Function.Surjective f)
    (hgenx : ∀ t : M,
      e (autAddHom x (f t)) = tensorAction (finRotate 3) 1 (e (f t)))
    (hgens : ∀ t : M,
      e (autAddHom s0 (f t)) = tensorAction (Equiv.swap 0 1) 1 (e (f t)))
    (hgenv : ∀ t : M,
      e (autAddHom v0 (f t)) = tensorAction 1 R (e (f t)))
    (hgend : ∀ t : M,
      e (autAddHom d0 (f t)) = tensorAction 1 S (e (f t))) :
    ∀ γ : ↥G, ∀ v : Additive W,
      e (autAddHom (γ : MulAut W) v) =
        tensorAction (φ γ).1 (φ γ).2 (e v) := by
  have autAddHom_one : ∀ v : Additive W, autAddHom (1 : MulAut W) v = v := by
    intro v
    rw [autAddHom_apply]
    rfl
  have autAddHom_mul : ∀ (g h : MulAut W) (v : Additive W),
      autAddHom (g * h) v = autAddHom g (autAddHom h v) := by
    intro g h v
    rw [autAddHom_apply, autAddHom_apply, autAddHom_apply]
    rfl
  have autAddHom_inv : ∀ (g : MulAut W) (v : Additive W),
      autAddHom g (autAddHom g⁻¹ v) = v := by
    intro g v
    rw [← autAddHom_mul, mul_inv_cancel, autAddHom_one]
  let A : Subgroup (MulAut W) := Subgroup.closure ({x, s0} : Set (MulAut W))
  let B : Subgroup (MulAut W) := Subgroup.closure ({v0, d0} : Set (MulAut W))
  let P : ↥G → Prop := fun γ => ∀ v : Additive W,
    e (autAddHom (γ : MulAut W) v) = tensorAction (φ γ).1 (φ γ).2 (e v)
  have P_x : P ⟨x, hAG (Subgroup.subset_closure (by simp))⟩ := by
    intro v
    obtain ⟨t, ht⟩ := hf v
    rw [← ht, hφx]
    exact hgenx t
  have P_s0 : P ⟨s0, hAG (Subgroup.subset_closure (by simp))⟩ := by
    intro v
    obtain ⟨t, ht⟩ := hf v
    rw [← ht, hφs]
    exact hgens t
  have P_v0 : P ⟨v0, hBG (Subgroup.subset_closure (by simp))⟩ := by
    intro v
    obtain ⟨t, ht⟩ := hf v
    rw [← ht, hφv]
    exact hgenv t
  have P_d0 : P ⟨d0, hBG (Subgroup.subset_closure (by simp))⟩ := by
    intro v
    obtain ⟨t, ht⟩ := hf v
    rw [← ht, hφd]
    exact hgend t
  have P_one : P 1 := by
    intro v
    change e (autAddHom (1 : MulAut W) v) =
      tensorAction (φ (1 : ↥G)).1 (φ (1 : ↥G)).2 (e v)
    rw [autAddHom_one, map_one]
    change e v = tensorAction (1 : Equiv.Perm (Fin 3))
      (1 : GL (Fin 2) (ZMod 2)) (e v)
    rw [tensorAction_one']
    rfl
  have P_mul : ∀ {a b : ↥G}, P a → P b → P (a * b) := by
    intro a b ha hb v
    change e (autAddHom ((a : MulAut W) * (b : MulAut W)) v) =
      tensorAction (φ (a * b)).1 (φ (a * b)).2 (e v)
    rw [autAddHom_mul, ha (autAddHom (b : MulAut W) v), hb v, ← LinearEquiv.mul_apply,
      tensorAction_mul', map_mul]
    rfl
  have P_inv : ∀ a : ↥G, P a → P a⁻¹ := by
    intro a ha v
    have hinv : ((a⁻¹ : ↥G) : MulAut W) = (a : MulAut W)⁻¹ := rfl
    have h1 := ha (autAddHom (a⁻¹ : ↥G) v)
    rw [hinv, autAddHom_inv] at h1
    change e (autAddHom (a : MulAut W)⁻¹ v) =
      tensorAction (φ (a⁻¹)).1 (φ (a⁻¹)).2 (e v)
    calc e (autAddHom (a : MulAut W)⁻¹ v)
        = (tensorAction (φ a).1 (φ a).2).symm (e v) := by
            rw [h1]
            simp
      _ = tensorAction (φ a).1⁻¹ (φ a).2⁻¹ (e v) := by rw [tensorAction_inv']
      _ = tensorAction (φ a⁻¹).1 (φ a⁻¹).2 (e v) := by
            rw [map_inv]
            rfl
  have hPA : ∀ a : ↥A, P ⟨a, hAG (a : ↥A).property⟩ := by
    intro a
    refine Subgroup.closure_induction (p := fun a ha => P ⟨a, hAG ha⟩) ?_ ?_ ?_ ?_
      (a : ↥A).property
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact P_x
      · exact P_s0
    · exact P_one
    · intro y z hy hz hy' hz'
      exact P_mul hy' hz'
    · intro y hy hy'
      exact P_inv _ hy'
  have hPB : ∀ b : ↥B, P ⟨b, hBG (b : ↥B).property⟩ := by
    intro b
    refine Subgroup.closure_induction (p := fun b hb => P ⟨b, hBG hb⟩) ?_ ?_ ?_ ?_
      (b : ↥B).property
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact P_v0
      · exact P_d0
    · exact P_one
    · intro y z hy hz hy' hz'
      exact P_mul hy' hz'
    · intro y hy hy'
      exact P_inv _ hy'
  intro γ
  obtain ⟨a, ha, b, hb, hab⟩ := hdecomp (γ : MulAut W) γ.property
  have hγ : γ = ⟨a * b, G.mul_mem (hAG ha) (hBG hb)⟩ := by
    apply Subtype.ext
    exact hab.symm
  rw [hγ]
  exact P_mul (hPA ⟨a, ha⟩) (hPB ⟨b, hb⟩)


theorem sixfourteen_n2_isTensorS3L2 {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hx_ord3 : orderOf x = 3)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hW : Nat.card W = 16)
    {G X H D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W}
    (hH : H = G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hxgen : X = Subgroup.zpowers x)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ y ∈ X, d * y = y * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2)
    (hYD : Y ≤ fixV D)
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYcard : Nat.card Y = 4)
    (hcommH : ∀ h ∈ H, h * x = x * h)
    (hpair : letI := galoisModule hw2 x hx3 hfix;
      ∃ S : Set (LineOf (K := GaloisField 2 2) (V := Additive W)),
        S.ncard = 2 ∧ S.Nonempty ∧ S ≠ Set.univ ∧
        (∀ h : ↥H, S.image (fun L => lineMap (HLinHom hw2 x hx3 hfix H hcommH h) L) = S)) :
    letI := galoisModule hw2 x hx3 hfix
    IsTensorS3L2 W G 2 := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨L, M, H0, v, d, s0, l, m, a, U, hS3, hBasis⟩ :=
    pair_basis_and_U_full hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  obtain ⟨hLM, hXleH0, hH0card, hsupV, hdisj, hvnotX, hvord, hdD, hd2, hdnot, hcover, hdv,
    hs0cases, hs0G, hs0sq, hs0notH, hs0x, hs0v, hs0d, hs0comm⟩ := hS3
  obtain ⟨ha3, ha1, hli_lm, hv0_l, hv0_m, hd_l, hd_m, hs0_l, hs0_m, hv0_ord', hd0sq',
    hs0sq'', hs0x'', hs0v'', hs0d'', hUfix, hUcard, hUinv, hUspan⟩ := hBasis
  let v0 : MulAut W := (((v : ↥H0) : ↥H) : MulAut W)
  let d0 : MulAut W := (d : MulAut W)
  have hv0_l' : autAddHom v0 l = a • l := by simpa [v0] using hv0_l
  have hv0_m' : autAddHom v0 m = a ^ 2 • m := by simpa [v0] using hv0_m
  have hd_l' : autAddHom d0 l = m := by simpa [d0] using hd_l
  have hd_m' : autAddHom d0 m = l := by simpa [d0] using hd_m
  have hs0_l' : autAddHom s0 l = m := hs0_l
  have hs0_m' : autAddHom s0 m = l := hs0_m
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  have hxG : x ∈ G := hXG hxX
  have hHleG : H ≤ G := by rw [hH]; exact inf_le_left
  have hx_ne : x ≠ 1 := by
    intro h
    rw [h] at hx_ord3
    simp at hx_ord3
  have hxH : x ∈ H := by
    rw [hH]
    refine Subgroup.mem_inf.mpr ⟨hxG, ?_⟩
    rw [hxgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hXH : X ≤ H := by
    intro y hy
    rw [hxgen] at hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact H.zpow_mem hxH n
  have hv0H : v0 ∈ H := ((v : ↥H0) : ↥H).2
  have hd0H : d0 ∈ H := d.2
  have hv0G : v0 ∈ G := hHleG hv0H
  have hd0G : d0 ∈ G := hHleG hd0H
  have hv0commx : v0 * x = x * v0 := by
    have hmemH : v0 ∈ G ⊓ Subgroup.centralizer (X : Set (MulAut W)) := by
      rwa [← hH]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmemH).2) x hxX).symm
  have hd0commx : d0 * x = x * d0 := by
    have hmemH : d0 ∈ G ⊓ Subgroup.centralizer (X : Set (MulAut W)) := by
      rwa [← hH]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmemH).2) x hxX).symm
  have hv0_ord : orderOf v0 = 3 := by
    have h1 : orderOf v = orderOf ((v : ↥H0) : ↥H) :=
      Subgroup.orderOf_mk ((v : ↥H0) : ↥H) v.2
    have h2 : orderOf ((v : ↥H0) : ↥H) = orderOf v0 :=
      Subgroup.orderOf_mk v0 ((v : ↥H0) : ↥H).2
    rw [← h2, ← h1]
    exact hvord
  have hv0_3 : v0 ^ 3 = 1 := by
    have := pow_orderOf_eq_one v0
    rwa [hv0_ord] at this
  have hv0_ne : v0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv0_ord
    omega
  have hd0sq : d0 * d0 = 1 := by
    have := congrArg (fun z : ↥H => (z : MulAut W)) hd2
    simpa [d0] using this
  have hd0_ne : d0 ≠ 1 := by
    intro h
    apply hdnot
    have h' : d = 1 := Subtype.ext (by simpa [d0] using h)
    rw [h']
    exact H0.one_mem
  have hdv0 : d0 * v0 * d0⁻¹ = v0 ^ 2 := by
    have h := hdv
    simpa [v0, d0, Subgroup.coe_pow] using h
  have hs0_ne : s0 ≠ 1 := by
    intro h
    apply hs0notH
    rw [h]
    exact H.one_mem
  let A : Subgroup (MulAut W) := Subgroup.closure ({x, s0} : Set (MulAut W))
  let B : Subgroup (MulAut W) := Subgroup.closure ({v0, d0} : Set (MulAut W))
  have hAG : A ≤ G := by
    dsimp [A]
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hxG
    · exact hs0G
  have hBH : B ≤ H := by
    dsimp [B]
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hv0H
    · exact hd0H
  have hBG : B ≤ G := fun y hy => hHleG (hBH hy)
  have hXA : X ≤ A := by
    rw [hxgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hA_inter_H : A ⊓ H = X := by
    dsimp [A]
    rw [hxgen]
    exact closure_pair_inf_eq_zpowers_of_notMem hx3 hx_ne hs0sq hs0x hxH hs0notH
  have hXH0 : X ≤ H0.map H.subtype := by
    intro y hy
    have hyH : y ∈ H := hXH hy
    have hy0 : (⟨y, hyH⟩ : ↥H) ∈ H0 := by
      apply hXleH0
      simpa [Subgroup.mem_subgroupOf] using hy
    simpa using Subgroup.mem_map_of_mem H.subtype hy0
  have hv0H0 : v0 ∈ H0.map H.subtype := by
    simp [v0]
  have hd0H0 : d0 ∉ H0.map H.subtype := by
    intro hmem
    rw [Subgroup.mem_map] at hmem
    obtain ⟨h0, hh0, hEq⟩ := hmem
    apply hdnot
    have h' : h0 = d := Subtype.ext (by simpa [d0] using hEq)
    rwa [h'] at hh0
  have hv0_notX : v0 ∉ X := by
    intro h
    apply hvnotX
    simpa [v0, Subgroup.mem_subgroupOf] using h
  have hX_inter_B : X ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyX : y ∈ X := hy.1
    have hyB : y ∈ B := hy.2
    obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_closure hv0_3 hv0_ne hd0sq hdv0 y hyB
    have hyH0 : y ∈ H0.map H.subtype := hXH0 hyX
    have hv0iH0 : v0 ^ (i : ℕ) ∈ H0.map H.subtype :=
      (H0.map H.subtype).pow_mem hv0H0 i
    have hdjH0 : d0 ^ (j : ℕ) ∈ H0.map H.subtype := by
      have h1 : d0 ^ (j : ℕ) = (v0 ^ (i : ℕ))⁻¹ * y := by rw [← hij]; group
      rw [h1]
      exact (H0.map H.subtype).mul_mem ((H0.map H.subtype).inv_mem hv0iH0) hyH0
    have hj : (j : ℕ) = 0 := by
      have hjlt : (j : ℕ) < 2 := j.2
      rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1) with h | h
      · exact h
      · exfalso
        apply hd0H0
        simpa [h] using hdjH0
    have hy_eq : y = v0 ^ (i : ℕ) := by
      have h1 : d0 ^ (j : ℕ) = 1 := by rw [hj]; simp
      rw [← hij, h1, mul_one]
    rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2) with hi | hi | hi
    · rw [hy_eq, hi]; simp
    · exfalso
      apply hv0_notX
      rw [hi] at hy_eq
      simp only [pow_one] at hy_eq
      rw [← hy_eq]
      exact hyX
    · exfalso
      apply hv0_notX
      rw [hi] at hy_eq
      have hsq : v0 ^ 2 ∈ X := by
        rw [← hy_eq]
        exact hyX
      have hvm : v0 = (v0 ^ 2) ^ 2 := by
        rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num,
          show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hv0_3, one_mul, pow_one]
      rw [hvm]
      exact X.pow_mem hsq 2
  have hA_inter_B : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyA : y ∈ A := hy.1
    have hyB : y ∈ B := hy.2
    have hyH : y ∈ H := hBH hyB
    have hyX : y ∈ X := by
      have hmem : y ∈ A ⊓ H := ⟨hyA, hyH⟩
      rwa [hA_inter_H] at hmem
    have hmem : y ∈ X ⊓ B := ⟨hyX, hyB⟩
    rwa [hX_inter_B] at hmem
  have hXcen : X.subgroupOf H ≤ Subgroup.center ↥H := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro h
    have haX : ((a : ↥H) : MulAut W) ∈ X := by
      simpa [Subgroup.mem_subgroupOf] using ha
    rw [hxgen] at haX
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp haX
    apply Subtype.ext
    change (h : MulAut W) * (a : MulAut W) = (a : MulAut W) * (h : MulAut W)
    rw [← hn]
    exact (Commute.zpow_right (hcommH h h.2) n).eq
  haveI hXHnorm : (X.subgroupOf H).Normal := Subgroup.normal_of_le_center hXcen
  haveI hXH0norm : ((X.subgroupOf H).subgroupOf H0).Normal := inferInstance
  have hH0_le : H0.map H.subtype ≤ A ⊔ B := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨h0, hh0, rfl⟩ := hy
    let h0' : ↥H0 := ⟨h0, hh0⟩
    have hsup_mem : h0' ∈ ((X.subgroupOf H).subgroupOf H0) ⊔ Subgroup.zpowers v := by
      rw [hsupV]
      exact Subgroup.mem_top h0'
    rw [Subgroup.mem_sup_of_normal_left] at hsup_mem
    obtain ⟨a, ha, b, hb, hab⟩ := hsup_mem
    have haA : (((a : ↥H0) : ↥H) : MulAut W) ∈ A := by
      apply hXA
      simpa [Subgroup.mem_subgroupOf] using ha
    obtain ⟨k, hbk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbB : (((v ^ k : ↥H0) : ↥H) : MulAut W) ∈ B := by
      have h1 : (((v ^ k : ↥H0) : ↥H) : MulAut W) = v0 ^ k := by
        simp [v0]
      rw [h1]
      exact B.zpow_mem (Subgroup.subset_closure (by simp)) k
    have hab' : a * (v ^ k) = h0' := by rw [hbk]; exact hab
    have hy_eq : H.subtype h0 = (((a : ↥H0) : ↥H) : MulAut W) *
        (((v ^ k : ↥H0) : ↥H) : MulAut W) := by
      have hval : h0 = ((a * (v ^ k) : ↥H0) : ↥H) := (congrArg Subtype.val hab').symm
      rw [hval]
      rfl
    rw [hy_eq]
    exact Subgroup.mul_mem_sup haA hbB
  have hH_le : H ≤ A ⊔ B := by
    intro h hh
    have hc := hcover (⟨h, hh⟩ : ↥H)
    rcases hc with h0 | h0
    · exact hH0_le (Subgroup.mem_map_of_mem H.subtype h0)
    · have heq : (⟨h, hh⟩ : ↥H) = (⟨h, hh⟩ * d⁻¹) * d := by group
      have hval : h = ((((⟨h, hh⟩ * d⁻¹) : ↥H)) : MulAut W) * d0 := by
        have := congrArg Subtype.val heq
        simp [d0, Subgroup.coe_mul]
      rw [hval]
      exact (A ⊔ B).mul_mem (hH0_le (Subgroup.mem_map_of_mem H.subtype h0))
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hG_le : G ≤ A ⊔ B := by
    intro g hg
    have hgx_mem : g * x * g⁻¹ ∈ X := hXnorm g hg x hxX
    have hgx_ne : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx_ne
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rw [hxgen] at hgx_mem
    rcases mem_zpowers_of_orderOf_three hx_ord3 hgx_mem with h1 | h1 | h1
    · exact absurd h1 hgx_ne
    · have hgH : g ∈ H := by
        rw [hH]
        refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
        have hgcomm : g * x = x * g := by
          calc g * x = (g * x * g⁻¹) * g := by group
            _ = x * g := by rw [h1]
        rw [hxgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hgcomm
      exact hH_le hgH
    · let u : MulAut W := s0⁻¹ * g
      have huG : u ∈ G := G.mul_mem (G.inv_mem hs0G) hg
      have hux : u * x * u⁻¹ = x := by
        dsimp [u]
        calc s0⁻¹ * g * x * (s0⁻¹ * g)⁻¹ = s0⁻¹ * (g * x * g⁻¹) * s0 := by group
          _ = s0⁻¹ * x ^ 2 * s0 := by rw [h1]
          _ = x := by rw [← hs0x]; group
      have hucomm : u * x = x * u := by
        calc u * x = (u * x * u⁻¹) * u := by group
          _ = x * u := by rw [hux]
      have huH : u ∈ H := by
        rw [hH]
        refine Subgroup.mem_inf.mpr ⟨huG, ?_⟩
        rw [hxgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hucomm
      have hg_eq : g = s0 * u := by dsimp [u]; group
      rw [hg_eq]
      exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
        (hH_le huH)
  have hAsupB : A ⊔ B = G := le_antisymm (sup_le hAG hBG) hG_le
  have hcommAB : ∀ {a b : MulAut W}, a ∈ A → b ∈ B → Commute a b := by
    have hxv : Commute x v0 :=
      (hcommH ((v : ↥H0) : ↥H) ((v : ↥H0) : ↥H).2).symm
    have hxd : Commute x d0 := (hDCX d hdD x hxX).symm
    have hsv : Commute s0 v0 := by
      calc s0 * v0 = (s0 * v0 * s0⁻¹) * s0 := by group
        _ = v0 * s0 := by rw [hs0v]
    have hsd : Commute s0 d0 := by
      calc s0 * d0 = (s0 * d0 * s0⁻¹) * s0 := by group
        _ = d0 * s0 := by rw [hs0d]
    have hxB : ∀ b ∈ B, Commute x b := by
      intro b hb
      dsimp [B] at hb
      refine Subgroup.closure_induction (p := fun b _ => Commute x b) ?_ ?_ ?_ ?_ hb
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hxv
        · exact hxd
      · exact Commute.one_right x
      · intro y z hy hz h1 h2
        exact h1.mul_right h2
      · intro y hy h1
        exact h1.inv_right
    have hsB : ∀ b ∈ B, Commute s0 b := by
      intro b hb
      dsimp [B] at hb
      refine Subgroup.closure_induction (p := fun b _ => Commute s0 b) ?_ ?_ ?_ ?_ hb
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hsv
        · exact hsd
      · exact Commute.one_right s0
      · intro y z hy hz h1 h2
        exact h1.mul_right h2
      · intro y hy h1
        exact h1.inv_right
    intro a b ha hb
    dsimp [A] at ha
    refine Subgroup.closure_induction (p := fun a _ => Commute a b) ?_ ?_ ?_ ?_ ha
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hxB b hb
      · exact hsB b hb
    · exact Commute.one_left b
    · intro y z hy hz h1 h2
      exact h1.mul_left h2
    · intro y hy h1
      exact h1.inv_left
  have hAB_set : (↑(A ⊔ B) : Set (MulAut W)) = (A : Set (MulAut W)) * B := by
    apply Subgroup.coe_mul_of_left_le_normalizer_right
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have hc : Commute a b := hcommAB ha hb
    have heq : a * b * a⁻¹ = b := by
      calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [hc.eq]
        _ = b := by group
    rw [heq]
    exact hb
  have hdecomp : ∀ {g : MulAut W}, g ∈ G → ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
    intro g hg
    have hgAB : g ∈ A ⊔ B := by rw [hAsupB]; exact hg
    have hgset : g ∈ (A : Set (MulAut W)) * B := by
      rw [← hAB_set]
      exact hgAB
    rwa [Set.mem_mul] at hgset
  obtain ⟨α, hαx, hαs⟩ := exists_mulEquiv_perm3_closure hx3 hx_ne hs0sq hs0_ne hs0x
  obtain ⟨β, hβv, hβd⟩ := exists_mulEquiv_perm3_closure hv0_3 hv0_ne hd0sq hd0_ne hdv0
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_prod_of_internal_direct hAG hBG hcommAB hA_inter_B hdecomp α β
  have hφx : φ ⟨x, hAG (Subgroup.subset_closure (by simp))⟩ = (finRotate 3, 1) := by
    have h := hφ ⟨x, Subgroup.subset_closure (by simp)⟩ (1 : ↥B)
    have h1 : Subgroup.inclusion hAG ⟨x, Subgroup.subset_closure (by simp)⟩ *
        Subgroup.inclusion hBG (1 : ↥B) =
        (⟨x, hAG (Subgroup.subset_closure (by simp))⟩ : ↥G) := by
      apply Subtype.ext
      simp
    rw [h1] at h
    simpa [hαx] using h
  have hφs : φ ⟨s0, hAG (Subgroup.subset_closure (by simp))⟩ = (Equiv.swap 0 1, 1) := by
    have h := hφ ⟨s0, Subgroup.subset_closure (by simp)⟩ (1 : ↥B)
    have h1 : Subgroup.inclusion hAG ⟨s0, Subgroup.subset_closure (by simp)⟩ *
        Subgroup.inclusion hBG (1 : ↥B) =
        (⟨s0, hAG (Subgroup.subset_closure (by simp))⟩ : ↥G) := by
      apply Subtype.ext
      simp
    rw [h1] at h
    simpa [hαs] using h
  have hφv : φ ⟨v0, hBG (Subgroup.subset_closure (by simp))⟩ = (1, finRotate 3) := by
    have h := hφ (1 : ↥A) ⟨v0, Subgroup.subset_closure (by simp)⟩
    have h1 : Subgroup.inclusion hAG (1 : ↥A) *
        Subgroup.inclusion hBG ⟨v0, Subgroup.subset_closure (by simp)⟩ =
        (⟨v0, hBG (Subgroup.subset_closure (by simp))⟩ : ↥G) := by
      apply Subtype.ext
      simp
    rw [h1] at h
    simpa [hβv] using h
  have hφd : φ ⟨d0, hBG (Subgroup.subset_closure (by simp))⟩ = (1, Equiv.swap 0 1) := by
    have h := hφ (1 : ↥A) ⟨d0, Subgroup.subset_closure (by simp)⟩
    have h1 : Subgroup.inclusion hAG (1 : ↥A) *
        Subgroup.inclusion hBG ⟨d0, Subgroup.subset_closure (by simp)⟩ =
        (⟨d0, hBG (Subgroup.subset_closure (by simp))⟩ : ↥G) := by
      apply Subtype.ext
      simp
    rw [h1] at h
    simpa [hβd] using h
  let R : GL (Fin 2) (ZMod 2) := s16c1610_permGL (finRotate 3)
  let S : GL (Fin 2) (ZMod 2) := s16c1610_permGL (Equiv.swap 0 1)
  let φ' : ↥G ≃* (Equiv.Perm (Fin 3) × GL (Fin 2) (ZMod 2)) :=
    φ.trans (MulEquiv.prodCongr (MulEquiv.refl (Equiv.Perm (Fin 3))) s16c1610_permGL)
  have hprodCongr_apply : ∀ (σ τ : Equiv.Perm (Fin 3)),
      ((MulEquiv.refl (Equiv.Perm (Fin 3))).prodCongr s16c1610_permGL) (σ, τ) =
        (σ, s16c1610_permGL τ) := by
    intro σ τ
    change (Prod.map (id : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) s16c1610_permGL)
      (σ, τ) = (σ, s16c1610_permGL τ)
    simp
  have hφ'x : φ' ⟨x, hAG (Subgroup.subset_closure (by simp))⟩ = (finRotate 3, 1) := by
    change ((MulEquiv.refl (Equiv.Perm (Fin 3))).prodCongr s16c1610_permGL)
      (φ ⟨x, hAG (Subgroup.subset_closure (by simp))⟩) = (finRotate 3, 1)
    rw [hφx, hprodCongr_apply]
    simp
  have hφ's : φ' ⟨s0, hAG (Subgroup.subset_closure (by simp))⟩ = (Equiv.swap 0 1, 1) := by
    change ((MulEquiv.refl (Equiv.Perm (Fin 3))).prodCongr s16c1610_permGL)
      (φ ⟨s0, hAG (Subgroup.subset_closure (by simp))⟩) = (Equiv.swap 0 1, 1)
    rw [hφs, hprodCongr_apply]
    simp
  have hφ'v : φ' ⟨v0, hBG (Subgroup.subset_closure (by simp))⟩ = (1, R) := by
    change ((MulEquiv.refl (Equiv.Perm (Fin 3))).prodCongr s16c1610_permGL)
      (φ ⟨v0, hBG (Subgroup.subset_closure (by simp))⟩) = (1, R)
    rw [hφv, hprodCongr_apply]
  have hφ'd : φ' ⟨d0, hBG (Subgroup.subset_closure (by simp))⟩ = (1, S) := by
    change ((MulEquiv.refl (Equiv.Perm (Fin 3))).prodCongr s16c1610_permGL)
      (φ ⟨d0, hBG (Subgroup.subset_closure (by simp))⟩) = (1, S)
    rw [hφd, hprodCongr_apply]
  obtain ⟨_, _, _, _, _, _, _, _, hxscalar⟩ :=
    sixfourteen_n2_pair_X_scalar hw2 x hx3 hx_ord3 hfix hW hH hXG hXnorm hxgen hsG hs_ord2
      hs_not_cent hirr hD hDCX hDs hElem hDcard hYD hYinv hYcard hcommH hpair
  have hx_mem_sub : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hxX
  obtain ⟨c, hc0, hc⟩ := hxscalar ⟨x, hxH⟩ hx_mem_sub
  have hxc : ∀ v : Additive W, autAddHom x v = c • v := by
    intro v
    rw [← hGaloisLinearEquiv_apply hw2 x hx3 hfix x (hcommH x hxH) v, hc v]
  have hc1 : c ≠ 1 := by
    intro hc1
    have hLin : hGaloisLinearEquiv hw2 x hx3 hfix x (hcommH x hxH) =
        LinearEquiv.refl (GaloisField 2 2) (Additive W) := by
      ext v
      rw [hGaloisLinearEquiv_apply hw2 x hx3 hfix x (hcommH x hxH) v, hxc v, hc1, one_smul]
      rfl
    have hHL_one : HLinHom hw2 x hx3 hfix H hcommH ⟨x, hxH⟩ = 1 := by
      rw [HLinHom_apply, hLin]
      rfl
    have hxH_one : (⟨x, hxH⟩ : ↥H) = 1 :=
      hLinHom_injective hw2 x hx3 hfix H hcommH (by rw [hHL_one, map_one])
    have hx_eq : x = 1 := congrArg (fun z : ↥H => (z : MulAut W)) hxH_one
    rw [hx_eq, orderOf_one] at hx_ord3
    omega
  have hc3 : c ^ 3 = 1 := by
    haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have h := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [show Fintype.card (GaloisField 2 2) = 4 by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num, show 4 - 1 = 3 by norm_num] at h
  obtain ⟨eF, heF_c, heF_sq⟩ := exists_eF_of_scalar c hc3 hc1
  letI : Module (ZMod 2) (Additive U) :=
    CFSG.Quasithin.H13.Mult.zmodModuleW (W := U) (fun u : U => by
      apply Subtype.ext
      simpa [pow_two] using hw2 (u : W))
  letI : Module (ZMod 2) (Additive W) := addModTwo hw2
  let u1 : Additive W := a ^ 2 • l + a • m
  let u2 : Additive W := a • l + a ^ 2 • m
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha3
    norm_num at ha3
  have ha_poly : a ^ 2 + a + 1 = 0 := by
    have h : (a + 1) * (a ^ 2 + a + 1) = 0 := by
      calc (a + 1) * (a ^ 2 + a + 1)
          = a ^ 3 + 2 * a ^ 2 + 2 * a + 1 := by ring
        _ = a ^ 3 + 1 := by
            rw [show (2 : GaloisField 2 2) = 0 from CharTwo.two_eq_zero]; ring
        _ = 1 + 1 := by rw [ha3]
        _ = 0 := CharTwo.add_self_eq_zero 1
    have ha1' : a + 1 ≠ 0 := by
      intro h0
      exact ha1 (CharTwo.add_eq_zero.mp h0)
    exact (mul_eq_zero.mp h).resolve_left ha1'
  have ha_add : a ^ 2 + a = 1 :=
    CharTwo.add_eq_zero.mp ha_poly
  have ha4 : a ^ 4 = a := by
    calc a ^ 4 = a ^ 3 * a := by ring
      _ = a := by rw [ha3, one_mul]
  have hs0_smulW : ∀ (c : GaloisField 2 2) (v : Additive W),
      s0 (Additive.toMul (c • v)) =
        Additive.toMul ((c ^ 2) • autAddHom s0 v) := by
    intro c v
    have h := autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x c v
    rw [autAddHom_apply] at h
    exact Additive.ofMul.injective h
  have hv0_smulW : ∀ (c : GaloisField 2 2) (v : Additive W),
      v0 (Additive.toMul (c • v)) =
        Additive.toMul (c • autAddHom v0 v) := by
    intro c v
    have h := autAddHom_smul_eq_of_comm hw2 x hx3 hfix hv0commx c v
    rw [autAddHom_apply] at h
    exact Additive.ofMul.injective h
  have hd0_smulW : ∀ (c : GaloisField 2 2) (v : Additive W),
      d0 (Additive.toMul (c • v)) =
        Additive.toMul (c • autAddHom d0 v) := by
    intro c v
    have h := autAddHom_smul_eq_of_comm hw2 x hx3 hfix hd0commx c v
    rw [autAddHom_apply] at h
    exact Additive.ofMul.injective h
  have hs0_u1 : autAddHom s0 u1 = u1 := by
    rw [autAddHom_apply]
    apply Additive.ofMul.injective
    change s0 (Additive.toMul (a ^ 2 • l) * Additive.toMul (a • m)) =
      Additive.toMul (a ^ 2 • l) * Additive.toMul (a • m)
    rw [map_mul, hs0_smulW, hs0_smulW, hs0_l, hs0_m]
    rw [show (a ^ 2) ^ 2 = a by
      rw [show (a ^ 2) ^ 2 = a ^ 4 by ring, ha4], mul_comm]
  have hs0_u2 : autAddHom s0 u2 = u2 := by
    rw [autAddHom_apply]
    apply Additive.ofMul.injective
    change s0 (Additive.toMul (a • l) * Additive.toMul (a ^ 2 • m)) =
      Additive.toMul (a • l) * Additive.toMul (a ^ 2 • m)
    rw [map_mul, hs0_smulW, hs0_smulW, hs0_l, hs0_m]
    rw [show (a ^ 2) ^ 2 = a by
      rw [show (a ^ 2) ^ 2 = a ^ 4 by ring, ha4], mul_comm]
  have hu1U : u1.toMul ∈ U := by
    change u1.toMul ∈ (U : Set W)
    rw [hUfix]
    exact Additive.ofMul.injective hs0_u1
  have hu2U : u2.toMul ∈ U := by
    change u2.toMul ∈ (U : Set W)
    rw [hUfix]
    exact Additive.ofMul.injective hs0_u2
  let u1U : Additive U := Additive.ofMul ⟨u1.toMul, hu1U⟩
  let u2U : Additive U := Additive.ofMul ⟨u2.toMul, hu2U⟩
  have hu12 : u1 + u2 = (a ^ 2 + a) • l + (a + a ^ 2) • m := by
    dsimp [u1, u2]
    calc a ^ 2 • l + a • m + (a • l + a ^ 2 • m)
        = (a ^ 2 • l + a • l) + (a • m + a ^ 2 • m) := by abel
      _ = (a ^ 2 + a) • l + (a + a ^ 2) • m := by rw [← add_smul, ← add_smul]
  have hu1_ne : u1 ≠ 0 := by
    intro h
    change a ^ 2 • l + a • m = 0 at h
    have hp := (LinearIndependent.pair_iff.mp hli_lm) (a ^ 2) a h
    exact ha0 hp.2
  have hu2_ne : u2 ≠ 0 := by
    intro h
    change a • l + a ^ 2 • m = 0 at h
    have hp := (LinearIndependent.pair_iff.mp hli_lm) a (a ^ 2) h
    exact ha0 hp.1
  have hu12_ne : u1 + u2 ≠ 0 := by
    intro h
    rw [hu12] at h
    have hp := (LinearIndependent.pair_iff.mp hli_lm) (a ^ 2 + a) (a + a ^ 2) h
    have hzero : a ^ 2 + a = 0 := hp.1
    have hfac : a * (a + 1) = 0 := by
      calc a * (a + 1) = a ^ 2 + a := by ring
        _ = 0 := hzero
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact ha0 h0
    · exact ha1 (CharTwo.add_eq_zero.mp h1)
  have hli_uW : LinearIndependent (ZMod 2) ![u1, u2] := by
    rw [LinearIndependent.pair_iff]
    intro c1 c2 h
    rcases zmod_two_eq_zero_or_one c1 with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one c2 with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      apply hu2_ne
      simpa using h
    · exfalso
      apply hu1_ne
      simpa using h
    · exfalso
      apply hu12_ne
      simpa using h
  let ι_add : Additive U →+ Additive W :=
  { toFun := fun x => Additive.ofMul (x.toMul : W)
    map_zero' := by simp
    map_add' := by
      intro x y
      change Additive.ofMul ((x.toMul : U) * (y.toMul : U) : W) =
        Additive.ofMul (x.toMul : W) + Additive.ofMul (y.toMul : W)
      rfl }
  let ι : Additive U →ₗ[ZMod 2] Additive W := ι_add.toZModLinearMap 2
  have hli_uU : LinearIndependent (ZMod 2) ![u1U, u2U] := by
    apply LinearIndependent.of_comp ι
    have hcomp : (ι ∘ ![u1U, u2U]) = ![u1, u2] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact hli_uW
  have hcardU : Nat.card (Additive U) = 2 ^ 2 := by
    rw [Nat.card_congr Additive.toMul, hUcard]
    norm_num
  have hfinU : Module.finrank (ZMod 2) (Additive U) = 2 := by
    haveI : Module.Finite (ZMod 2) (Additive U) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    rw [Nat.card_zmod] at h
    rw [hcardU] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hcard_eq : Fintype.card (Fin 2) = Module.finrank (ZMod 2) (Additive U) := by
    rw [hfinU]
    rfl
  let bU : Module.Basis (Fin 2) (ZMod 2) (Additive U) :=
    basisOfLinearIndependentOfCardEqFinrank (K := ZMod 2) (b := ![u1U, u2U])
      hli_uU hcard_eq
  let eU : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := bU.equivFun
  have hbU0 : bU 0 = u1U := by
    simp [bU, basisOfLinearIndependentOfCardEqFinrank]
  have hbU1 : bU 1 = u2U := by
    simp [bU, basisOfLinearIndependentOfCardEqFinrank]
  have heU0 : eU u1U = ![1, 0] := by
    rw [← hbU0]
    funext j
    fin_cases j <;> simp [eU, Module.Basis.equivFun_self]
  have heU1 : eU u2U = ![0, 1] := by
    rw [← hbU1]
    funext j
    fin_cases j <;> simp [eU, Module.Basis.equivFun_self]
  let v0U_add : Additive U →+ Additive U :=
  { toFun := fun x => Additive.ofMul
      ⟨(autAddHom v0 (Additive.ofMul (x.toMul : W))).toMul,
        (hUinv (x.toMul : W) x.toMul.2).1⟩
    map_zero' := by
      apply Additive.ofMul.injective
      apply Subtype.ext
      change (autAddHom v0 (Additive.ofMul ((0 : Additive U).toMul : W))).toMul = 1
      simp
    map_add' := by
      intro x y
      apply Additive.ofMul.injective
      apply Subtype.ext
      change autAddHom v0 (Additive.ofMul ((x + y).toMul : W)) =
        autAddHom v0 (Additive.ofMul (x.toMul : W)) +
          autAddHom v0 (Additive.ofMul (y.toMul : W))
      rw [show Additive.ofMul ((x + y).toMul : W) =
        Additive.ofMul (x.toMul : W) + Additive.ofMul (y.toMul : W) from rfl, map_add] }
  let v0U : Additive U →ₗ[ZMod 2] Additive U := v0U_add.toZModLinearMap 2
  let d0U_add : Additive U →+ Additive U :=
  { toFun := fun x => Additive.ofMul
      ⟨(autAddHom d0 (Additive.ofMul (x.toMul : W))).toMul,
        (hUinv (x.toMul : W) x.toMul.2).2⟩
    map_zero' := by
      apply Additive.ofMul.injective
      apply Subtype.ext
      change (autAddHom d0 (Additive.ofMul ((0 : Additive U).toMul : W))).toMul = 1
      simp
    map_add' := by
      intro x y
      apply Additive.ofMul.injective
      apply Subtype.ext
      change autAddHom d0 (Additive.ofMul ((x + y).toMul : W)) =
        autAddHom d0 (Additive.ofMul (x.toMul : W)) +
          autAddHom d0 (Additive.ofMul (y.toMul : W))
      rw [show Additive.ofMul ((x + y).toMul : W) =
        Additive.ofMul (x.toMul : W) + Additive.ofMul (y.toMul : W) from rfl, map_add] }
  let d0U : Additive U →ₗ[ZMod 2] Additive U := d0U_add.toZModLinearMap 2
  have hu1u2_lm : u1 + u2 = l + m := by
    rw [hu12, ha_add]
    rw [show a + a ^ 2 = 1 by rw [add_comm, ha_add]]
    simp
  have hv0u1W : autAddHom v0 u1 = u1 + u2 := by
    rw [autAddHom_apply]
    apply Additive.ofMul.injective
    rw [hu1u2_lm]
    change v0 (Additive.toMul (a ^ 2 • l) * Additive.toMul (a • m)) =
      Additive.toMul l * Additive.toMul m
    rw [map_mul, hv0_smulW, hv0_smulW, hv0_l', hv0_m', smul_smul, smul_smul]
    rw [show a ^ 2 * a = 1 by
      calc a ^ 2 * a = a ^ 3 := by ring
        _ = 1 := ha3,
      show a * a ^ 2 = 1 by
      calc a * a ^ 2 = a ^ 3 := by ring
        _ = 1 := ha3]
    simp
  have hv0u2W : autAddHom v0 u2 = u1 := by
    rw [autAddHom_apply]
    apply Additive.ofMul.injective
    change v0 (Additive.toMul (a • l) * Additive.toMul (a ^ 2 • m)) =
      Additive.toMul (a ^ 2 • l) * Additive.toMul (a • m)
    rw [map_mul, hv0_smulW, hv0_smulW, hv0_l', hv0_m', smul_smul, smul_smul]
    rw [show a * a = a ^ 2 by ring,
      show a ^ 2 * a ^ 2 = a by
        calc a ^ 2 * a ^ 2 = a ^ 4 := by ring
          _ = a := ha4]
  have hd0u1W : autAddHom d0 u1 = u2 := by
    rw [autAddHom_apply]
    apply Additive.ofMul.injective
    change d0 (Additive.toMul (a ^ 2 • l) * Additive.toMul (a • m)) =
      Additive.toMul (a • l) * Additive.toMul (a ^ 2 • m)
    rw [map_mul, hd0_smulW, hd0_smulW, hd_l', hd_m', mul_comm]
  have hd0u2W : autAddHom d0 u2 = u1 := by
    rw [autAddHom_apply]
    apply Additive.ofMul.injective
    change d0 (Additive.toMul (a • l) * Additive.toMul (a ^ 2 • m)) =
      Additive.toMul (a ^ 2 • l) * Additive.toMul (a • m)
    rw [map_mul, hd0_smulW, hd0_smulW, hd_l', hd_m', mul_comm]
  have hv0U_u1 : v0U u1U = u1U + u2U := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    change (autAddHom v0 u1).toMul = (u1 + u2).toMul
    rw [hv0u1W]
  have hv0U_u2 : v0U u2U = u1U := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    change (autAddHom v0 u2).toMul = u1.toMul
    rw [hv0u2W]
  have hd0U_u1 : d0U u1U = u2U := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    change (autAddHom d0 u1).toMul = u2.toMul
    rw [hd0u1W]
  have hd0U_u2 : d0U u2U = u1U := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    change (autAddHom d0 u2).toMul = u1.toMul
    rw [hd0u2W]
  have hadd01 : (![1, 0] : Fin 2 → ZMod 2) + ![0, 1] = ![1, 1] := by
    ext j
    fin_cases j <;> rfl
  have hR1 : s16c1610_glAction 2 R ![1, 0] = ![1, 1] := by
    rw [s16c1610_glAction_apply]
    ext j
    fin_cases j <;> simp [R, s16c1610_permGL_coe, s16c1610_permMat]
  have hR2 : s16c1610_glAction 2 R ![0, 1] = ![1, 0] := by
    rw [s16c1610_glAction_apply]
    ext j
    fin_cases j <;> simp [R, s16c1610_permGL_coe, s16c1610_permMat]
  have hS1 : s16c1610_glAction 2 S ![1, 0] = ![0, 1] := by
    rw [s16c1610_glAction_apply]
    ext j
    fin_cases j <;> simp [S, s16c1610_permGL_coe, s16c1610_permMat]
  have hS2 : s16c1610_glAction 2 S ![0, 1] = ![1, 0] := by
    rw [s16c1610_glAction_apply]
    ext j
    fin_cases j <;> simp [S, s16c1610_permGL_coe, s16c1610_permMat]
  have heU_v0_map : eU.toLinearMap.comp v0U =
      (s16c1610_glAction 2 R).toLinearMap.comp eU.toLinearMap := by
    apply bU.ext
    intro i
    fin_cases i
    · change eU (v0U (bU 0)) = s16c1610_glAction 2 R (eU (bU 0))
      rw [hbU0, hv0U_u1, map_add, heU0, heU1, hadd01, hR1]
    · change eU (v0U (bU 1)) = s16c1610_glAction 2 R (eU (bU 1))
      rw [hbU1, hv0U_u2, heU0, heU1, hR2]
  have heU_v0 : ∀ u : Additive U,
      eU (v0U u) = s16c1610_glAction 2 R (eU u) :=
    fun u => LinearMap.congr_fun heU_v0_map u
  have heU_d0_map : eU.toLinearMap.comp d0U =
      (s16c1610_glAction 2 S).toLinearMap.comp eU.toLinearMap := by
    apply bU.ext
    intro i
    fin_cases i
    · change eU (d0U (bU 0)) = s16c1610_glAction 2 S (eU (bU 0))
      rw [hbU0, hd0U_u1, heU1, heU0, hS1]
    · change eU (d0U (bU 1)) = s16c1610_glAction 2 S (eU (bU 1))
      rw [hbU1, hd0U_u2, heU0, heU1, hS2]
  have heU_d0 : ∀ u : Additive U,
      eU (d0U u) = s16c1610_glAction 2 S (eU u) :=
    fun u => LinearMap.congr_fun heU_d0_map u
  let mulE : (GaloisField 2 2) ⊗[ZMod 2] Additive U →ₗ[ZMod 2] Additive W :=
    TensorProduct.lift
      { toFun := fun c => c • ι
        map_add' := by
          intro c1 c2
          ext u
          simp [add_smul]
        map_smul' := by
          intro r c
          rcases zmod_two_eq_zero_or_one r with rfl | rfl <;> ext u <;> simp }
  have mulE_tmul : ∀ (c : GaloisField 2 2) (u : Additive U),
      mulE (c ⊗ₜ[ZMod 2] u) = c • ι u := by
    intro c u
    rw [TensorProduct.lift.tmul]
    rfl
  have mulE_smul : ∀ (c : GaloisField 2 2)
      (t : (GaloisField 2 2) ⊗[ZMod 2] Additive U),
      mulE (c • t) = c • mulE t := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
        rw [TensorProduct.smul_tmul', mulE_tmul, mulE_tmul, smul_smul]
        simp
    | add x y hx hy => simp [smul_add, map_add, hx, hy]
  have hsurj_mulE : Function.Surjective mulE := by
    intro w
    have hw : w ∈ Submodule.span (GaloisField 2 2) (Additive.ofMul '' (U : Set W)) := by
      rw [hUspan]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun w _ => ∃ t, mulE t = w) ?_ ?_ ?_ ?_ hw
    · rintro x ⟨u, hu, rfl⟩
      exact ⟨1 ⊗ₜ[ZMod 2] Additive.ofMul ⟨u, hu⟩, by
        rw [mulE_tmul, one_smul]
        rfl⟩
    · exact ⟨0, map_zero mulE⟩
    · intro x y hx hy hex hey
      obtain ⟨tx, rfl⟩ := hex
      obtain ⟨ty, rfl⟩ := hey
      exact ⟨tx + ty, map_add mulE tx ty⟩
    · intro c x hx hex
      obtain ⟨t, rfl⟩ := hex
      exact ⟨c • t, mulE_smul c t⟩
  have hfinW_z2 : Module.finrank (ZMod 2) (Additive W) = 4 := by
    haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at h
    have hcard : Nat.card (Additive W) = 2 ^ 4 := by
      rw [Nat.card_congr Additive.toMul, hW]
      norm_num
    rw [hcard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hfin_tensor : Module.finrank (ZMod 2)
      ((GaloisField 2 2) ⊗[ZMod 2] Additive U) = 4 := by
    rw [Module.finrank_tensorProduct, galoisField_two_two_finrank, hfinU]
  haveI : Module.Finite (ZMod 2) ((GaloisField 2 2) ⊗[ZMod 2] Additive U) := by
    haveI : Module.Finite (ZMod 2) (GaloisField 2 2) := Module.Finite.of_finite
    let bF : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
      (Module.finBasis (ZMod 2) (GaloisField 2 2)).reindex
        (finCongr galoisField_two_two_finrank)
    exact Module.Finite.of_basis (bF.tensorProduct bU)
  have hfinrank_eq : Module.finrank (ZMod 2) ((GaloisField 2 2) ⊗[ZMod 2] Additive U) =
      Module.finrank (ZMod 2) (Additive W) := by
    rw [hfin_tensor, hfinW_z2]
  have hbij : Function.Bijective mulE :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank_eq).mpr hsurj_mulE,
      hsurj_mulE⟩
  let mulE_equiv : (GaloisField 2 2) ⊗[ZMod 2] Additive U ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective mulE hbij
  let e : Additive W ≃ₗ[ZMod 2]
      ((↥(CFSG.Quasithin.permCore 3)) ⊗[ZMod 2] (Fin 2 → ZMod 2)) :=
    mulE_equiv.symm.trans (TensorProduct.congr eF eU)
  have e_mulE : ∀ t : (GaloisField 2 2) ⊗[ZMod 2] Additive U,
      e (mulE t) = TensorProduct.congr eF eU t := by
    intro t
    change (TensorProduct.congr eF eU) (mulE_equiv.symm (mulE_equiv t)) =
      TensorProduct.congr eF eU t
    rw [LinearEquiv.symm_apply_apply]
  have e_tmul : ∀ (c : GaloisField 2 2) (u : Additive U),
      e (c • ι u) = eF c ⊗ₜ[ZMod 2] eU u := by
    intro c u
    rw [← mulE_tmul c u, e_mulE, TensorProduct.congr_tmul]
  have hs0_ι : ∀ x : Additive U, autAddHom s0 (ι x) = ι x := by
    intro x
    have hx : (x.toMul : W) ∈ (U : Set W) := x.toMul.2
    rw [hUfix] at hx
    simpa [ι, ι_add] using hx
  have hgen_x : ∀ (b : GaloisField 2 2) (u : Additive U),
      e (autAddHom x (b • ι u)) = tensorAction (finRotate 3) 1 (e (b • ι u)) := by
    intro b u
    have h1 : autAddHom x (b • ι u) = (c * b) • ι u := by
      rw [hxc, smul_smul]
    rw [h1, e_tmul, e_tmul, heF_c b, tensorAction_tmul]
    simp
  have hgen_s0 : ∀ (b : GaloisField 2 2) (u : Additive U),
      e (autAddHom s0 (b • ι u)) = tensorAction (Equiv.swap 0 1) 1 (e (b • ι u)) := by
    intro b u
    have h1 : autAddHom s0 (b • ι u) = (b ^ 2) • ι u := by
      rw [autAddHom_smul_eq_sq hw2 x hx3 hfix hs0x b (ι u), hs0_ι u]
    rw [h1, e_tmul, e_tmul, heF_sq b, tensorAction_tmul]
    simp
  have hgen_v0 : ∀ (b : GaloisField 2 2) (u : Additive U),
      e (autAddHom v0 (b • ι u)) = tensorAction 1 R (e (b • ι u)) := by
    intro b u
    have h1 : autAddHom v0 (b • ι u) = b • autAddHom v0 (ι u) :=
      autAddHom_smul_eq_of_comm hw2 x hx3 hfix hv0commx b (ι u)
    have h2 : autAddHom v0 (ι u) = ι (v0U u) := rfl
    rw [h1, h2, e_tmul, e_tmul, heU_v0 u, tensorAction_tmul]
    simp [permActLin, permActCore_one]
  have hgen_d0 : ∀ (b : GaloisField 2 2) (u : Additive U),
      e (autAddHom d0 (b • ι u)) = tensorAction 1 S (e (b • ι u)) := by
    intro b u
    have h1 : autAddHom d0 (b • ι u) = b • autAddHom d0 (ι u) :=
      autAddHom_smul_eq_of_comm hw2 x hx3 hfix hd0commx b (ι u)
    have h2 : autAddHom d0 (ι u) = ι (d0U u) := rfl
    rw [h1, h2, e_tmul, e_tmul, heU_d0 u, tensorAction_tmul]
    simp [permActLin, permActCore_one]
  have hact : ∀ (g : MulAut W) (v : Additive W),
      autAddHom g v = Additive.ofMul (g v.toMul) := by
    intro g v
    exact autAddHom_apply (x := g) v
  have hact_zero : ∀ g : MulAut W, autAddHom g (0 : Additive W) = 0 := by
    intro g
    rw [autAddHom_apply]
    simp
  have hspan : Submodule.span (ZMod 2)
      (Set.range (fun p : (GaloisField 2 2) × Additive U => p.1 ⊗ₜ[ZMod 2] p.2)) = ⊤ := by
    simpa [Set.range] using TensorProduct.span_tmul_eq_top (R := ZMod 2)
      (M := GaloisField 2 2) (N := Additive U)
  have hgen_all_of_pure : ∀ (g : MulAut W)
      (T : ((↥(CFSG.Quasithin.permCore 3)) ⊗[ZMod 2] (Fin 2 → ZMod 2)) ≃ₗ[ZMod 2]
        ((↥(CFSG.Quasithin.permCore 3)) ⊗[ZMod 2] (Fin 2 → ZMod 2))),
      (∀ (b : GaloisField 2 2) (u : Additive U),
        e (autAddHom g (b • ι u)) = T (e (b • ι u))) →
      ∀ t : (GaloisField 2 2) ⊗[ZMod 2] Additive U,
        e (autAddHom g (mulE t)) = T (e (mulE t)) := by
    intro g T hpure
    let L : (GaloisField 2 2) ⊗[ZMod 2] Additive U →ₗ[ZMod 2]
        ((↥(CFSG.Quasithin.permCore 3)) ⊗[ZMod 2] (Fin 2 → ZMod 2)) :=
      e.toLinearMap.comp (((autAddHom g).toZModLinearMap 2).comp mulE)
    let R : (GaloisField 2 2) ⊗[ZMod 2] Additive U →ₗ[ZMod 2]
        ((↥(CFSG.Quasithin.permCore 3)) ⊗[ZMod 2] (Fin 2 → ZMod 2)) :=
      T.toLinearMap.comp (e.toLinearMap.comp mulE)
    have hLR : L = R := by
      apply LinearMap.ext_on_range
        (v := fun p : (GaloisField 2 2) × Additive U => p.1 ⊗ₜ[ZMod 2] p.2) hspan
      rintro ⟨b, u⟩
      change e (autAddHom g (mulE (b ⊗ₜ[ZMod 2] u))) =
        T (e (mulE (b ⊗ₜ[ZMod 2] u)))
      rw [mulE_tmul]
      exact hpure b u
    intro t
    exact LinearMap.congr_fun hLR t

  have hgen_x_all : ∀ t : (GaloisField 2 2) ⊗[ZMod 2] Additive U,
      e (autAddHom x (mulE t)) = tensorAction (finRotate 3) 1 (e (mulE t)) :=
    hgen_all_of_pure x (tensorAction (finRotate 3) 1) hgen_x
  have hgen_s0_all : ∀ t : (GaloisField 2 2) ⊗[ZMod 2] Additive U,
      e (autAddHom s0 (mulE t)) = tensorAction (Equiv.swap 0 1) 1 (e (mulE t)) :=
    hgen_all_of_pure s0 (tensorAction (Equiv.swap 0 1) 1) hgen_s0
  have hgen_v0_all : ∀ t : (GaloisField 2 2) ⊗[ZMod 2] Additive U,
      e (autAddHom v0 (mulE t)) = tensorAction 1 R (e (mulE t)) :=
    hgen_all_of_pure v0 (tensorAction 1 R) hgen_v0
  have hgen_d0_all : ∀ t : (GaloisField 2 2) ⊗[ZMod 2] Additive U,
      e (autAddHom d0 (mulE t)) = tensorAction 1 S (e (mulE t)) :=
    hgen_all_of_pure d0 (tensorAction 1 S) hgen_d0
  let xG : ↥G := ⟨x, hAG (Subgroup.subset_closure (by simp))⟩
  let s0G : ↥G := ⟨s0, hAG (Subgroup.subset_closure (by simp))⟩
  let v0G : ↥G := ⟨v0, hBG (Subgroup.subset_closure (by simp))⟩
  let d0G : ↥G := ⟨d0, hBG (Subgroup.subset_closure (by simp))⟩
  have hPG := compat_of_surjective_generators (W := W) (G := G) (x := x) (s0 := s0)
    (v0 := v0) (d0 := d0) R S hAG hBG (fun g hg => hdecomp (g := g) hg)
      (φ := φ') (e := e)
    (fun hx => by
      rw [show (⟨x, hx⟩ : ↥G) = xG from Subtype.ext rfl]
      exact hφ'x)
    (fun hx => by
      rw [show (⟨s0, hx⟩ : ↥G) = s0G from Subtype.ext rfl]
      exact hφ's)
    (fun hx => by
      rw [show (⟨v0, hx⟩ : ↥G) = v0G from Subtype.ext rfl]
      exact hφ'v)
    (fun hx => by
      rw [show (⟨d0, hx⟩ : ↥G) = d0G from Subtype.ext rfl]
      exact hφ'd)
    (M := (GaloisField 2 2) ⊗[ZMod 2] Additive U) (f := mulE) (hf := hsurj_mulE)
    hgen_x_all hgen_s0_all hgen_v0_all hgen_d0_all
  have hcompat : ∀ (γ : ↥G) (v : Additive W),
      e (Additive.ofMul ((γ : MulAut W) (Additive.toMul v))) =
        tensorAction (φ' γ).1 (φ' γ).2 (e v) := by
    intro γ v
    rw [← autAddHom_apply (x := (γ : MulAut W)) v]
    exact hPG γ v
  exact isTensorS3L2_of_tensorModel φ' e hcompat


end CFSG.LocalAnalysis.WeakClosure81
