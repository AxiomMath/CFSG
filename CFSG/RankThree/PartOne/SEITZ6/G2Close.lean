module

public import CFSG.RankThree.PartOne.SEITZ3.LongRoot

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

variable {K : Type} [Field K]

theorem weylElement_conj_xp [CharP K 2] (i : Fin (Tag.rank .G2)) {p q : ℕ}
    (hp : p < 12) (h : reflect .G2 i (rt p) = rt q) (c : K) :
    weylElement .G2 K i * xp p c * (weylElement .G2 K i)⁻¹ = xp q c := by
  have hγ : IsRoot .G2 (rt p) := isRoot_rt hp
  have hq : IsRoot .G2 (rt q) := h ▸ IsRoot.reflect i hγ
  have hF := (rootOperatorFamily .G2).weylElement_mul_eltElement_mul_inv (K := K) i ⟨rt p, hγ⟩ c
  have hsign : (((rootOperatorFamily .G2).sign i ⟨rt p, hγ⟩ : ℤ) : K) = 1 := by
    rcases (rootOperatorFamily .G2).sign_eq i ⟨rt p, hγ⟩ with h1 | h1 <;> rw [h1] <;>
      simp [CharTwo.neg_eq]
  rw [hsign, one_mul] at hF
  have e : simple .G2 i • (⟨rt p, hγ⟩ : Root .G2) = ⟨rt q, hq⟩ := by
    rw [simple_smul_eq_sRoot]
    exact Subtype.ext h
  rw [e] at hF
  simpa [xp, xPar_of_isRoot hγ, xPar_of_isRoot hq] using hF

@[expose] def Full (H : Subgroup (adjointGroup .G2 K)) (p : ℕ) : Prop :=
  ∀ c : K, xp p c ∈ H

theorem Full.conj [CharP K 2] {H : Subgroup (adjointGroup .G2 K)}
    (i : Fin (Tag.rank .G2)) {p q : ℕ} (hp : p < 12) (h : reflect .G2 i (rt p) = rt q)
    (hw : weylElement .G2 K i ∈ H) (hF : Full H p) : Full H q := fun c => by
  have := H.mul_mem (H.mul_mem hw (hF c)) (H.inv_mem hw)
  rwa [weylElement_conj_xp i hp h] at this

theorem reflect_7 : reflect .G2 e0 (rt 7) = rt 3 := by decide +kernel
theorem reflect_3 : reflect .G2 e1 (rt 3) = rt 0 := by decide +kernel
theorem reflect_0 : reflect .G2 e0 (rt 0) = rt 2 := by decide +kernel
theorem reflect_2 : reflect .G2 e1 (rt 2) = rt 6 := by decide +kernel
theorem reflect_6 : reflect .G2 e0 (rt 6) = rt 10 := by decide +kernel
theorem reflect_5 : reflect .G2 e1 (rt 5) = rt 1 := by decide +kernel
theorem reflect_1 : reflect .G2 e0 (rt 1) = rt 4 := by decide +kernel
theorem reflect_4 : reflect .G2 e1 (rt 4) = rt 8 := by decide +kernel
theorem comm_xp_11_7 [CharP K 2] (s t : K) :
    ⁅xp 11 s, xp 7 t⁆ = xp 4 (s * t) * xp 5 (s ^ 2 * t) * xp 6 (s ^ 3 * t) := by
  have h : RootOps.repCheck .G2 11 7 [(1, 1, 4, -1), (2, 1, 5, -1), (3, 1, 6, -1), (3, 2, 0, -2)] =
      true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  have h2 : ((-2 : ℤ) : K) = 0 := by simp [CharTwo.two_eq_zero]
  have h1 : ((-1 : ℤ) : K) = 1 := by simp [CharTwo.neg_eq]
  simp only [h1, h2, zero_mul, one_mul] at this
  show _ = _
  rw [this]
  have h0 : xPar (rootOperatorFamily .G2) ((Tag.rootCertificate .G2).root 0) (0 : K) = 1 :=
    xp_zero 0
  rw [h0, mul_one, pow_one, pow_one, mul_assoc]

theorem Full.five_of_long [CharP K 2] {H : Subgroup (adjointGroup .G2 K)}
    (h6 : Full H 6) (h7 : Full H 7) (h11 : xp 11 (1 : K) ∈ H) {τ : adjointGroup .G2 K}
    (hτ : τ ∈ H) {a₁ a₂ : K} (h12 : a₁ ≠ a₂) (ha₁ : ∀ c, τ * xp 4 c * τ⁻¹ = xp 4 (a₁ * c))
    (ha₂ : ∀ c, τ * xp 5 c * τ⁻¹ = xp 5 (a₂ * c)) : Full H 5 := by
  have hz : ∀ t : K, xp 4 t * xp 5 t ∈ H := fun t => by
    have hy : ⁅xp 11 (1 : K), xp 7 t⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h11 (h7 t)) (H.inv_mem h11)) (H.inv_mem (h7 t))
    rw [comm_xp_11_7] at hy
    simp only [one_mul, one_pow] at hy
    have := H.mul_mem hy (H.inv_mem (h6 t))
    rwa [mul_assoc (xp 4 t * xp 5 t) (xp 6 t), mul_inv_cancel, mul_one] at this
  have hinv : ∀ (p : ℕ) (c : K), (xp p c)⁻¹ = xp p c := fun p c =>
    inv_eq_of_mul_eq_one_right (xp_mul_self p c)
  intro c
  have hs : a₁ + a₂ ≠ 0 := fun h => h12 (by
    have := CharTwo.add_eq_zero.1 h
    exact this)
  set t := c / (a₁ + a₂)
  have key : xp 5 ((a₁ + a₂) * t) ∈ H := by
    have h1 := hz t
    have h2 := hz (a₁ * t)
    have h3 := H.mul_mem (H.inv_mem h2) (H.mul_mem (H.mul_mem hτ h1) (H.inv_mem hτ))
    have e : τ * (xp 4 t * xp 5 t) * τ⁻¹ = xp 4 (a₁ * t) * xp 5 (a₂ * t) := by
      rw [show τ * (xp 4 t * xp 5 t) * τ⁻¹ = (τ * xp 4 t * τ⁻¹) * (τ * xp 5 t * τ⁻¹) by group,
        ha₁, ha₂]
    rw [e, mul_inv_rev, hinv, hinv] at h3
    rw [add_mul, xp_add]
    convert h3 using 1
    calc xp 5 (a₁ * t) * xp 5 (a₂ * t)
        = xp 5 (a₁ * t) * (xp 4 (a₁ * t) * xp 4 (a₁ * t)) * xp 5 (a₂ * t) := by
          rw [xp_mul_self, mul_one]
      _ = _ := by group
  rwa [show (a₁ + a₂) * t = c from mul_div_cancel₀ _ hs] at key

theorem rt1_eq : rt 1 = Pi.single e1 1 := by
  ext i; fin_cases i <;> decide

theorem rt5_eq : rt 5 = -Pi.single e1 1 := by
  ext i; fin_cases i <;> decide

theorem eq_top_of_full {H : Subgroup (adjointGroup .G2 K)}
    (h0 : Full H 0) (h1 : Full H 1) (h2 : Full H 2) (h5 : Full H 5) : H = ⊤ := by
  set F := rootOperatorFamily .G2
  set S : Set (ModGL .G2 K) := {g | ∃ (i : Fin (Tag.rank .G2)) (c : K),
    (g : Module.End K (RootModule .G2 K)) = xOp .G2 K i c ∨
      (g : Module.End K (RootModule .G2 K)) = yOp .G2 K i c}
  have hcl : Subgroup.closure (((↑) : adjointGroup .G2 K → ModGL .G2 K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have e : g = xPar F (Pi.single i 1) c := endHom_injective (by
      rw [xPar_simple, endHom_eltElement, F.elt_simple]
      exact hg)
    rw [e]
    fin_cases i
    · have : xPar F (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) c = xp 0 c := by
        rw [xp, rt0_eq]; rfl
      exact this ▸ h0 c
    · have : xPar F (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .G2)) 1) c = xp 1 c := by
        rw [xp, rt1_eq]; rfl
      exact this ▸ h1 c
  · have e : g = xPar F (-Pi.single i 1) c := endHom_injective (by
      rw [xPar_neg_simple, endHom_eltElement, F.elt_neg_simple]
      exact hg)
    rw [e]
    fin_cases i
    · have : xPar F (-Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) c = xp 2 c := by
        rw [xp, rt2_eq]; rfl
      exact this ▸ h2 c
    · have : xPar F (-Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .G2)) 1) c = xp 5 c := by
        rw [xp, rt5_eq]; rfl
      exact this ▸ h5 c

theorem reflect_10 : reflect .G2 e0 (rt 10) = rt 6 := by decide +kernel

theorem eq_top_of_full_seven_of_weyl [CharP K 2]
    {H : Subgroup (adjointGroup .G2 K)} (hw0 : weylElement .G2 K e0 ∈ H)
    (hw1 : weylElement .G2 K e1 ∈ H) (h7 : Full H 7) (h11 : xp 11 (1 : K) ∈ H)
    {τ : adjointGroup .G2 K} (hτ : τ ∈ H) {a₁ a₂ : K} (h12 : a₁ ≠ a₂)
    (ha₁ : ∀ c, τ * xp 4 c * τ⁻¹ = xp 4 (a₁ * c))
    (ha₂ : ∀ c, τ * xp 5 c * τ⁻¹ = xp 5 (a₂ * c)) : H = ⊤ := by
  have h3 : Full H 3 := h7.conj e0 (by norm_num) reflect_7 hw0
  have h0 : Full H 0 := h3.conj e1 (by norm_num) reflect_3 hw1
  have h2 : Full H 2 := h0.conj e0 (by norm_num) reflect_0 hw0
  have h6 : Full H 6 := h2.conj e1 (by norm_num) reflect_2 hw1
  have h5 : Full H 5 := Full.five_of_long h6 h7 h11 hτ h12 ha₁ ha₂
  have h1 : Full H 1 := h5.conj e1 (by norm_num) reflect_5 hw1
  exact eq_top_of_full h0 h1 h2 h5

theorem weylElement_e0_eq :
    weylElement .G2 K e0 = xp 0 (1 : K) * xp 2 (-1) * xp 0 1 := by
  rw [weylElement_eq_xPar (rootOperatorFamily .G2) e0, CFSG.LieType.Steinberg.weylElement]
  simp only [Units.val_one, inv_one, xp, rt0_eq, rt2_eq]

theorem weylElement_e1_eq :
    weylElement .G2 K e1 = xp 1 (1 : K) * xp 5 (-1) * xp 1 1 := by
  rw [weylElement_eq_xPar (rootOperatorFamily .G2) e1, CFSG.LieType.Steinberg.weylElement]
  simp only [Units.val_one, inv_one, xp, rt1_eq, rt5_eq]

theorem torusElement_e1_eq (t : Kˣ) :
    torusElement .G2 K e1 t =
      xp 1 (t : K) * xp 5 (-((t⁻¹ : Kˣ) : K)) * xp 1 (t : K) * (weylElement .G2 K e1)⁻¹ := by
  have h := weylElement_xPar (F := rootOperatorFamily .G2) (K := K) e1 t
  rw [CFSG.LieType.Steinberg.weylElement] at h
  simp only [xp, rt1_eq, rt5_eq]
  rw [h, mul_inv_cancel_right]

theorem torusElement_e1_conj_xp {p : ℕ} (hp : p < 12) (t : Kˣ) (c : K) :
    torusElement .G2 K e1 t * xp p c * (torusElement .G2 K e1 t)⁻¹ =
      xp p (((t ^ (∑ j, (Tag.G2).cartan e1 j * (rt p) j) : Kˣ) : K) * c) := by
  have hγ : IsRoot .G2 (rt p) := isRoot_rt hp
  have := (rootOperatorFamily .G2).torusElement_mul_eltElement_mul_inv (K := K) e1 t
    ⟨rt p, hγ⟩ c
  rw [← xPar_of_isRoot hγ] at this
  rw [← xPar_of_isRoot hγ] at this
  exact this

theorem cartan_e1_rt4 : (∑ j, (Tag.G2).cartan e1 j * (rt 4) j) = -1 := by decide +kernel
theorem cartan_e1_rt5 : (∑ j, (Tag.G2).cartan e1 j * (rt 5) j) = -2 := by decide +kernel

theorem eq_top_of_subfield [CharP K 2] (k : Subfield K) {t : K} (htk : t ∈ k)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) {H : Subgroup (adjointGroup .G2 K)}
    (hH : ∀ p < 12, ∀ c ∈ k, xp p c ∈ H) (h7 : Full H 7) : H = ⊤ := by
  have hneg : ∀ {c : K}, c ∈ k → -c ∈ k := fun hc => k.neg_mem hc
  have hw0 : weylElement .G2 K e0 ∈ H := by
    rw [weylElement_e0_eq]
    exact H.mul_mem (H.mul_mem (hH 0 (by norm_num) 1 k.one_mem)
      (hH 2 (by norm_num) (-1) (hneg k.one_mem))) (hH 0 (by norm_num) 1 k.one_mem)
  have hw1 : weylElement .G2 K e1 ∈ H := by
    rw [weylElement_e1_eq]
    exact H.mul_mem (H.mul_mem (hH 1 (by norm_num) 1 k.one_mem)
      (hH 5 (by norm_num) (-1) (hneg k.one_mem))) (hH 1 (by norm_num) 1 k.one_mem)
  set u : Kˣ := Units.mk0 t ht0 with hu
  have hτ : torusElement .G2 K e1 u ∈ H := by
    rw [torusElement_e1_eq]
    refine H.mul_mem (H.mul_mem (H.mul_mem (hH 1 (by norm_num) _ htk)
      (hH 5 (by norm_num) _ (hneg ?_))) (hH 1 (by norm_num) _ htk)) (H.inv_mem hw1)
    simpa [hu] using k.inv_mem htk
  have ha₁ := fun c : K => torusElement_e1_conj_xp (K := K) (p := 4) (by norm_num) u c
  have ha₂ := fun c : K => torusElement_e1_conj_xp (K := K) (p := 5) (by norm_num) u c
  rw [cartan_e1_rt4] at ha₁
  rw [cartan_e1_rt5] at ha₂
  refine eq_top_of_full_seven_of_weyl hw0 hw1 h7 (hH 11 (by norm_num) 1 k.one_mem) hτ
    (a₁ := ((u ^ (-1 : ℤ) : Kˣ) : K)) (a₂ := ((u ^ (-2 : ℤ) : Kˣ) : K)) ?_ ha₁ ha₂
  intro h
  have h' : u ^ (-1 : ℤ) = u ^ (-2 : ℤ) := Units.ext h
  have h'' : u = 1 := by
    have : u ^ (-1 : ℤ) * u ^ (-1 : ℤ) = u ^ (-1 : ℤ) * 1 := by
      rw [mul_one, ← zpow_add, show (-1 : ℤ) + -1 = -2 by norm_num, ← h']
    have := mul_left_cancel this
    simpa using this
  exact ht1 (by simpa [hu] using congrArg Units.val h'')

end CFSG.RankThree.PartOne.SEITZ6
