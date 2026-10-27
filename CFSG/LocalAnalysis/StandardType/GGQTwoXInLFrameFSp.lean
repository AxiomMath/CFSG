module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSp2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSp3
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFSU
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.ComponentInitial Polynomial Multiplicative
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQTwoUFrame_of_cfg_sp {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {m : ℕ} {E : Subgroup ↥(CFSG.Open.StatedSp m K)} {x : ↥(CFSG.Open.StatedSp m K)}
    {L D J : Subgroup ↥(CFSG.Open.StatedSp m K)} (hC : GGQTwoFRCfg E x L D J) :
    ∃ (n : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ y, τ (τ y) = y)
      (ρ : ↥(heldGU n M τ hτ) →* ↥(CFSG.Open.StatedSp m K)),
      Nat.card M = 4 ∧ (∀ y, τ y = y ^ 2) ∧ GGQTwoUFrame ρ E x L := by
  classical
  obtain ⟨n, M, hMfield, hMfinite, hMalgebra, τ, U, hUadd, hUmod, Φ, c, hM, hτ2,
    hc, hB, hx, hEact, hEback⟩ := exists_traceFrame_of_cfg_sp hK hC
  have hτ : ∀ y, τ (τ y) = y := by
    intro y
    rw [hτ2, hτ2, ← pow_mul]
    have h4 : y ^ 4 = y := by
      have h := @FiniteField.pow_card M _ (Fintype.ofFinite M) y
      rw [Fintype.card_eq_nat_card, hM] at h
      exact h
    simpa using h4
  have hxE : x ∈ E := hC.2.2.2.1
  have hx1 : x ≠ 1 := hC.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hC.1.2 x hxE
  let V := Fin m ⊕ Fin m → K
  let B : LinearMap.BilinForm K V := CFSG.RankThree.Classical.spForm m K
  let e₂ : ↥(CFSG.Open.StatedSp m K) ≃* ↥(sesqUnitaryGroup B) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin)
  obtain ⟨ρ', hρ'inj, hρ'act, hf, hcentral⟩ :=
    exists_heldGU_rep_of_traceFrame hK hM hτ Φ hB
  let ρ : ↥(heldGU n M τ hτ) →* ↥(CFSG.Open.StatedSp m K) :=
    e₂.symm.toMonoidHom.comp ρ'
  have hρinj : Function.Injective ρ := e₂.symm.injective.comp hρ'inj
  have hc0 : c ≠ 0 := by
    intro h
    apply hc
    rw [h]
    ring
  have hc3 : c ^ 3 = 1 := by
    have h4 : c ^ 4 = c := by
      have h := @FiniteField.pow_card M _ (Fintype.ofFinite M) c
      rw [Fintype.card_eq_nat_card, hM] at h
      exact h
    have h5 : c * c ^ 3 = c * 1 := by rw [← pow_succ', h4, mul_one]
    exact mul_left_cancel₀ hc0 h5
  have hc1 : c ≠ 1 := by
    intro h
    apply hc
    rw [h]
    ring
  let d₀ : Fin n → Mˣ := fun _ => Units.mk0 c hc0
  have hd₀ : ∀ i, τ (d₀ i) * d₀ i = 1 := by
    intro i
    change τ c * c = 1
    calc τ c * c = c ^ 2 * c := by rw [hτ2]
      _ = c ^ 3 := by ring
      _ = 1 := hc3
  let A₀ : ↥(heldGU n M τ hτ) :=
    ⟨QTwoFrameTorus.frameDiagGL d₀, QTwoFrameTorus.frameDiagGL_mem_heldGU hd₀⟩
  have hA₀mat : ((A₀ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun _ => c) := by
    dsimp [A₀]
    rw [QTwoFrameTorus.frameDiagGL_val]
    rfl
  have hs_act : ∀ d w, (((ρ' A₀ : ↥(sesqUnitaryGroup B)) :
      LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ (d, w)) = Φ (c • d, w) := by
    intro d w
    rw [hρ'act, QTwoFrameTorus.frameDiagGL_val]
    congr 1
    apply Prod.ext
    · funext i
      change ((Matrix.diagonal (fun _ => c)).mulVec d) i = c * d i
      rw [Matrix.mulVec_diagonal]
    · rfl
  have hxAx : ρ A₀ = x := by
    dsimp [ρ]
    have h : ρ' A₀ = e₂ x := by
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro v
      obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
      rw [hs_act]
      change Φ (c • d, w) = CFSG.RankThree.Classical.spEnd x (Φ (d, w))
      rw [hx]
    rw [h, e₂.symm_apply_apply]
  have hE : ∀ g : ↥(CFSG.Open.StatedSp m K), g ∈ E ↔
      ∃ A : ↥(heldGU n M τ hτ),
        (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) ∧
          ρ A = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨a, ha3, hact⟩ := hEact g hg
      have ha0 : ∀ i, a i ≠ 0 := by
        intro i h
        have h1 := ha3 i
        rw [h] at h1
        norm_num at h1
      let d : Fin n → Mˣ := fun i => Units.mk0 (a i) (ha0 i)
      have hd : ∀ i, τ (d i) * d i = 1 := by
        intro i
        change τ (a i) * a i = 1
        calc τ (a i) * a i = a i ^ 2 * a i := by rw [hτ2]
          _ = a i ^ 3 := by ring
          _ = 1 := ha3 i
      let A : ↥(heldGU n M τ hτ) :=
        ⟨QTwoFrameTorus.frameDiagGL d, QTwoFrameTorus.frameDiagGL_mem_heldGU hd⟩
      have hAdiag : ∀ i j, i ≠ j →
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0 := by
        intro i j hij
        dsimp [A]
        rw [QTwoFrameTorus.frameDiagGL_val]
        simp [Matrix.diagonal, hij]
      have hρA : ρ A = g := by
        dsimp [ρ]
        have h : ρ' A = e₂ g := by
          apply Subtype.ext
          apply Units.ext
          apply LinearMap.ext
          intro v
          obtain ⟨⟨d', w⟩, rfl⟩ := Φ.surjective v
          rw [hρ'act, QTwoFrameTorus.frameDiagGL_val]
          change Φ (Matrix.mulVec (Matrix.diagonal (fun i => (d i : M))) d', w) =
            CFSG.RankThree.Classical.spEnd g (Φ (d', w))
          rw [hact d' w]
          congr 1
          apply Prod.ext
          · funext i
            change ((Matrix.diagonal (fun i => a i)).mulVec d') i = a i * d' i
            rw [Matrix.mulVec_diagonal]
          · rfl
        rw [h, e₂.symm_apply_apply]
      exact ⟨A, hAdiag, hρA⟩
    · rintro ⟨A, hAdiag, hρA⟩
      let av : Fin n → M := fun i =>
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i
      have hAmat : ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
          Matrix.diagonal av := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [av]
        · rw [hAdiag i j hij]; simp [Matrix.diagonal, av, hij]
      have hdiag : ∀ i, τ (av i) * av i = 1 := by
        intro i
        have h1 : (Matrix.transpose
            ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).map ⇑τ)) *
            ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) i i = 1 := by
          rw [mem_heldGU.mp A.2]
          simp
        rw [hAmat] at h1
        have hmap : (Matrix.diagonal av).map ⇑τ =
            Matrix.diagonal (fun i => τ (av i)) := by
          ext a b
          by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
        have htrans : Matrix.transpose (Matrix.diagonal (fun i => τ (av i))) =
            Matrix.diagonal (fun i => τ (av i)) := by
          ext a b
          by_cases hab : a = b
          · subst hab; simp
          · simp [Matrix.diagonal, hab, Ne.symm hab]
        rw [hmap, htrans, Matrix.diagonal_mul_diagonal] at h1
        simpa [Matrix.diagonal] using h1
      have ha3 : ∀ i, av i ^ 3 = 1 := by
        intro i
        have h := hdiag i
        rw [hτ2] at h
        calc av i ^ 3 = av i ^ 2 * av i := by ring
          _ = 1 := h
      obtain ⟨e, he, hact⟩ := hEback av ha3
      have hρA' : ρ A = e := by
        dsimp [ρ]
        have h : ρ' A = e₂ e := by
          apply Subtype.ext
          apply Units.ext
          apply LinearMap.ext
          intro v
          obtain ⟨⟨d', w⟩, rfl⟩ := Φ.surjective v
          rw [hρ'act]
          change Φ (Matrix.mulVec (((A : GL (Fin n) M) :
            Matrix (Fin n) (Fin n) M)) d', w) =
            CFSG.RankThree.Classical.spEnd e (Φ (d', w))
          rw [hact d' w, hAmat]
          congr 1
          apply Prod.ext
          · funext i
            change ((Matrix.diagonal av).mulVec d') i = av i * d' i
            rw [Matrix.mulVec_diagonal]
          · rfl
        rw [h, e₂.symm_apply_apply]
      rw [← hρA, hρA']
      exact he
  have hζ2ζ : c ^ 2 ≠ c := hc
  have hN : ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(CFSG.Open.StatedSp m K)),
      ∀ A : ↥(heldGU n M τ hτ), (A : GL (Fin n) M) ∈ heldSU n M τ hτ →
      ∃ A' : ↥(heldGU n M τ hτ), (A' : GL (Fin n) M) ∈ heldSU n M τ hτ ∧
        g * ρ A * g⁻¹ = ρ A' := by
    intro g hg A hA
    have he₂ρ : ∀ B : ↥(heldGU n M τ hτ), e₂ (ρ B) = ρ' B :=
      fun B => e₂.apply_symm_apply (ρ' B)
    have hxρ : e₂ x = ρ' A₀ := by
      rw [← hxAx]
      exact e₂.apply_symm_apply (ρ' A₀)
    have hgx : e₂ g * ρ' A₀ = ρ' A₀ * e₂ g := by
      have h1 : g * x = x * g := (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
      have h2 : e₂ (g * x) = e₂ (x * g) := congrArg e₂ h1
      simpa [map_mul, hxρ] using h2
    obtain ⟨A₁, g₀, hA₁⟩ := hcentral (ρ' A₀) (e₂ g) c hc hs_act hgx
    let u' : ↥(heldGU n M τ hτ) := A₁ * A * A₁⁻¹
    have hu' : (u' : GL (Fin n) M) ∈ heldSU n M τ hτ :=
      heldSU_normal_in_heldGU hτ (A₁ : GL (Fin n) M) A₁.2 (A : GL (Fin n) M) hA
    have hconj : e₂ g * ρ' A = ρ' u' * e₂ g := by
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro v
      obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
      simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]
      rw [hρ'act A d w, hA₁ (Matrix.mulVec (((A : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) d) w]
      conv_rhs => rw [hA₁ d w]
      rw [hρ'act u' (Matrix.mulVec (((A₁ : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) d) (g₀ w)]
      congr 1
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp only [← Units.val_mul]
      have hu'A : (u' : GL (Fin n) M) * (A₁ : GL (Fin n) M) =
          (A₁ : GL (Fin n) M) * (A : GL (Fin n) M) := by
        dsimp [u']
        group
      rw [hu'A]
    refine ⟨u', hu', ?_⟩
    have hgρ : g * ρ A = ρ u' * g := by
      apply e₂.injective
      simpa [map_mul, he₂ρ] using hconj
    rw [hgρ, mul_assoc, mul_inv_cancel, mul_one]
  have hL := ggQTwo_L_eq_map_heldSU hC hM hτ2 hρinj hE hc hA₀mat hxAx hN
  have hα : ∀ i : Fin n, ∃ α : MulAut ↥(CFSG.Open.StatedSp m K),
      (∀ A A' : ↥(heldGU n M τ hτ),
        (∀ j k, j ≠ k → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
        (∀ j k, j ≠ k → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
        ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
          τ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) →
        (∀ j, j ≠ i → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j =
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j) →
        α (ρ A) = ρ A') ∧
      ∀ A : ↥(heldGU n M τ hτ),
        (∀ j, j ≠ i → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0 ∧
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j i = 0) →
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i = 1 → α (ρ A) = ρ A := by
    intro i
    obtain ⟨f, hf_act, hf_conj, hf_fix⟩ := hf i
    refine ⟨MulAut.conj (e₂.symm f), ?_, ?_⟩
    · intro A A' hA hA' hii hjj
      have h := congrArg e₂.symm (hf_conj A A' hA hA' hii hjj)
      simpa [ρ, MulAut.conj_apply, map_mul, map_inv] using h
    · intro A hA hii
      have h := congrArg e₂.symm (hf_fix A hA hii)
      simpa [ρ, MulAut.conj_apply, map_mul, map_inv] using h
  refine ⟨n, M, hMfield, hMfinite, τ, hτ, ρ, hM, hτ2, ?_⟩
  exact ⟨hρinj, hE, ⟨A₀, c, hc1, hA₀mat, hxAx⟩, hL, hα⟩

end CFSG.StandardType

end
