module

public import CFSG.Quasithin.Background.HPairGen
public import CFSG.Quasithin.Background.HConj

public section

namespace CFSG.Quasithin

namespace H

namespace PairG

open CFSG.Open Matrix
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def twistAut (A : GL ι K) (σ : K ≃+* K) : MulAut (StdMod ι K) :=
  (fieldMap σ)⁻¹ * matAut A⁻¹

theorem twistAut_mul (A : GL ι K) (σ : K ≃+* K) (g M : GL ι K)
    (hM : (M : Matrix ι ι K) = (A : Matrix ι ι K) * (g : Matrix ι ι K).map σ *
      ((A⁻¹ : GL ι K) : Matrix ι ι K)) :
    twistAut A σ * matAut M = matAut g * twistAut A σ := by
  refine toAddMap_injective fun v => ?_
  set w := toAddMap (matAut A⁻¹) v with hw
  have hMv : toAddMap (matAut A⁻¹) (toAddMap (matAut M) v) = (g : Matrix ι ι K).map σ *ᵥ w := by
    rw [hw, toAddMap_matAut, toAddMap_matAut, toAddMap_matAut, hM, Matrix.mulVec_mulVec]
    rw [show ((A⁻¹ : GL ι K) : Matrix ι ι K) * ((A : Matrix ι ι K) * (g : Matrix ι ι K).map σ *
        ((A⁻¹ : GL ι K) : Matrix ι ι K)) =
          (g : Matrix ι ι K).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K) by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]]
    rw [← Matrix.mulVec_mulVec]
  have hg := toAddMap_fieldMap_conj σ g w
  rw [twistAut]
  simp only [toAddMap_mul]
  rw [hMv, ← hg]
  simp only [toAddMap_mul, toAddMap_apply_inv]
  rfl

theorem exists_pair_model {Γ : Subgroup (GL ι K)} (θ : ↥Γ →* ↥Γ) {V : Type*} [CommGroup V]
    {H : Subgroup (MulAut V)} {V₁ : Subgroup V} (π : ↥Γ →* ↥H) (hπs : Function.Surjective π)
    (hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁) (e₁ : ↥V₁ ≃* StdMod ι K)
    (he₁ : ∀ (γ : ↥Γ) (u : ↥V₁) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL ι K) (e₁ u))
    (hAut : ∀ α : MulAut ↥Γ, ∃ (A : GL ι K) (σ : K ≃+* K),
      (∀ γ, (((α γ : ↥Γ) : GL ι K) : Matrix ι ι K) =
        (A : Matrix ι ι K) * ((γ : GL ι K) : Matrix ι ι K).map σ *
          ((A⁻¹ : GL ι K) : Matrix ι ι K)) ∨
      ∀ γ, (((α γ : ↥Γ) : GL ι K) : Matrix ι ι K) =
        (A : Matrix ι ι K) * (((θ γ : ↥Γ) : GL ι K) : Matrix ι ι K).map σ *
          ((A⁻¹ : GL ι K) : Matrix ι ι K))
    {φ : MulAut V} (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) :
    ∃ e : V ≃* PairMod ι K, H.map (congrHom e) = pairImg Γ θ := by
  classical
  set V₂ := V₁.map φ.toMonoidHom with hV₂
  have hinv₁ : Pair.IsInv H V₁ := fun l hl w hw => hU ⟨l, hl⟩ w hw
  have hinv₂ : Pair.IsInv H V₂ := Pair.isInv_map hφ hinv₁
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply Subtype.ext
    apply Units.ext
    show ((γ : GL ι K) : Matrix ι ι K) = 1
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [Matrix.one_mulVec]
    obtain ⟨u, hu⟩ := e₁.surjective (Multiplicative.ofAdd v)
    have h1 := he₁ γ u (by rw [hγ]; exact u.2)
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), by rw [hγ]; exact u.2⟩ : ↥V₁) = u := by
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (u : V) = u
      rw [hγ]
      rfl
    rw [h2, hu] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  have hφi : φ⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut V)) := Subgroup.inv_mem _ hφ
  let πe : ↥Γ ≃* ↥H := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let cφ : MulAut ↥H := H.normalizerMonoidHom ⟨φ⁻¹, hφi⟩
  have hcφ : ∀ h : ↥H, ((cφ h : ↥H) : MulAut V) = φ⁻¹ * h * φ := fun h => by
    change φ⁻¹ * (h : MulAut V) * φ⁻¹⁻¹ = _
    rw [inv_inv]
  let α' : MulAut ↥Γ := (MulAut.congr πe.symm) cφ
  have hα' : ∀ γ, ((π (α' γ) : ↥H) : MulAut V) = φ⁻¹ * (π γ : MulAut V) * φ := fun γ => by
    have : π (α' γ) = cφ (π γ) := by
      change πe (πe.symm (cφ (πe γ))) = cφ (π γ)
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [this, hcφ]
  obtain ⟨A, σ, hα⟩ := hAut α'
  let iφ : ↥V₁ ≃* ↥V₂ := Subgroup.equivMapOfInjective V₁ φ.toMonoidHom φ.injective
  let e₂ : ↥V₂ ≃* StdMod ι K := (iφ.symm.trans e₁).trans (twistAut A σ)
  have hiφ : ∀ v : ↥V₁, ((iφ v : ↥V₂) : V) = φ v := fun v => rfl
  have hgen : ∀ (γ : ↥Γ) (g : GL ι K),
      (((α' γ : ↥Γ) : GL ι K) : Matrix ι ι K) =
        (A : Matrix ι ι K) * (g : Matrix ι ι K).map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K) →
      ∀ (w : ↥V₂) (hw : ((π γ : ↥H) : MulAut V) (w : V) ∈ V₂),
        e₂ ⟨_, hw⟩ = matAut g (e₂ w) := by
    intro γ g hg w hw
    set v := iφ.symm w with hv
    have hwv : (w : V) = φ v := by rw [← hiφ, hv, MulEquiv.apply_symm_apply]
    have hmem : ((π (α' γ) : ↥H) : MulAut V) (v : V) ∈ V₁ := hU _ v v.2
    have hsymm : iφ.symm ⟨_, hw⟩ = ⟨_, hmem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (w : V) = φ (((π (α' γ) : ↥H) : MulAut V) (v : V))
      rw [hα', hwv]
      show _ = φ (φ⁻¹ (((π γ : ↥H) : MulAut V) (φ (v : V))))
      rw [MulAut.apply_inv_self]
    have h1 : e₂ ⟨_, hw⟩ = twistAut A σ (e₁ ⟨_, hmem⟩) := by
      change twistAut A σ (e₁ (iφ.symm ⟨_, hw⟩)) = _
      rw [hsymm]
    rw [h1, he₁ (α' γ) v hmem]
    change twistAut A σ (matAut ((α' γ : ↥Γ) : GL ι K) (e₁ v)) =
      matAut g (twistAut A σ (e₁ v))
    rw [← MulAut.mul_apply, twistAut_mul _ _ _ _ hg, MulAut.mul_apply]
  have hτ : ∀ γ, (((α' γ : ↥Γ) : GL ι K) : Matrix ι ι K) =
      (A : Matrix ι ι K) * (((θ γ : ↥Γ) : GL ι K) : Matrix ι ι K).map σ *
        ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
    rcases hα with h0 | h1
    · exfalso
      apply hniso
      refine ⟨e₁.trans e₂.symm, fun l hl w hw => ?_⟩
      obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
      have hl' : l = ((π γ : ↥H) : MulAut V) := by rw [hγ]
      subst hl'
      have hw2 : ((π γ : ↥H) : MulAut V) ((e₂.symm (e₁ w) : ↥V₂) : V) ∈ V₂ :=
        hinv₂ _ (π γ).2 _ (e₂.symm (e₁ w)).2
      have h1 := hgen γ γ (h0 γ) (e₂.symm (e₁ w)) hw2
      rw [MulEquiv.apply_symm_apply] at h1
      change ((e₂.symm (e₁ ⟨_, hw⟩) : ↥V₂) : V) = _
      rw [he₁ γ w hw, ← h1, MulEquiv.symm_apply_apply]
      rfl
    · exact h1
  have hgen₂ : ∀ (γ : ↥Γ) (w : ↥V₂) (hw : ((π γ : ↥H) : MulAut V) (w : V) ∈ V₂),
      e₂ ⟨_, hw⟩ = matAut ((θ γ : ↥Γ) : GL ι K) (e₂ w) := fun γ => hgen γ _ (hτ γ)
  let μ : ↥V₁ × ↥V₂ →* V := V₁.subtype.coprod V₂.subtype
  have hμ : Function.Bijective μ := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h' : (a : V) * b = c * d := h
      obtain ⟨h1, h2⟩ := Pair.decomp_unique hinf a.2 b.2 c.2 d.2 h'
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro v
      obtain ⟨a, ha, b, hb, hab⟩ := Pair.exists_decomp hsup v
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  let dec : (↥V₁ × ↥V₂) ≃* V := MulEquiv.ofBijective μ hμ
  let e : V ≃* PairMod ι K := dec.symm.trans (MulEquiv.prodCongr e₁ e₂)
  refine ⟨e, ?_⟩
  have hpair : ∀ γ : ↥Γ, congrHom e ((π γ : ↥H) : MulAut V) = pairHom Γ θ γ := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply, pairHom_apply, pairAut_apply]
    set a := e₁.symm x.1 with ha
    set b := e₂.symm x.2 with hb
    have hx : e.symm x = (a : V) * b := rfl
    rw [hx, map_mul]
    have ha' : ((π γ : ↥H) : MulAut V) (a : V) ∈ V₁ := hU _ a a.2
    have hb' : ((π γ : ↥H) : MulAut V) (b : V) ∈ V₂ := hinv₂ _ (π γ).2 b b.2
    have hdec : dec.symm (((π γ : ↥H) : MulAut V) (a : V) * ((π γ : ↥H) : MulAut V) (b : V)) =
        (⟨_, ha'⟩, ⟨_, hb'⟩) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change MulEquiv.prodCongr e₁ e₂ (dec.symm _) = _
    rw [hdec]
    change (e₁ ⟨_, ha'⟩, e₂ ⟨_, hb'⟩) = _
    rw [he₁ γ a ha', hgen₂ γ b hb', ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨h, hh⟩
    have : h = ((π γ : ↥H) : MulAut V) := by rw [hγ]
    rw [this, hpair]
    exact pairHom_mem_pairImg _ _ γ
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, hpair γ⟩

theorem map_le_pairNorm {Γ : Subgroup (GL ι K)} (θ : ↥Γ →* ↥Γ) {V : Type*} [CommGroup V]
    {H M : Subgroup (MulAut V)} (e : V ≃* PairMod ι K) (he : H.map (congrHom e) = pairImg Γ θ)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    M.map (congrHom e) ≤ pairNorm Γ θ := by
  have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
      Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod ι K))) :
        Set (MulAut (PairMod ι K))) :=
    Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
  rw [pairNorm, ← he, ← h3]
  exact Subgroup.map_mono hMN

@[expose] def swapAut (ι K : Type) [Field K] : MulAut (PairMod ι K) := MulEquiv.prodComm

omit [Fintype ι] [DecidableEq ι] in
theorem swapAut_mul_self : swapAut ι K * swapAut ι K = 1 := MulEquiv.ext fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem swapAut_inv : (swapAut ι K)⁻¹ = swapAut ι K := MulEquiv.ext fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem swapAut_conj_pairAut (a b : MulAut (StdMod ι K)) :
    swapAut ι K * pairAut a b * (swapAut ι K)⁻¹ = pairAut b a := MulEquiv.ext fun _ => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem map_V₁_swapAut : (V₁ ι K).map (swapAut ι K).toMonoidHom = V₂ ι K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_V₂]
    exact mem_V₁.mp hy
  · intro hx
    exact ⟨(swapAut ι K)⁻¹ x, mem_V₁.mpr (mem_V₂.mp hx), MulEquiv.apply_symm_apply _ x⟩

theorem swapAut_mem_pairNorm {Γ : Subgroup (GL ι K)} (θ : ↥Γ →* ↥Γ) (hθ : ∀ γ, θ (θ γ) = γ) :
    swapAut ι K ∈ pairNorm Γ θ := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨θ γ, ?_⟩
    rw [pairHom_apply, pairHom_apply, swapAut_conj_pairAut, hθ]
  · rintro ⟨γ, hγ⟩
    refine ⟨θ γ, ?_⟩
    have h1 : swapAut ι K * pairHom Γ θ γ * (swapAut ι K)⁻¹ = y := by
      rw [hγ, swapAut_inv]
      calc swapAut ι K * (swapAut ι K * y * swapAut ι K) * swapAut ι K =
            (swapAut ι K * swapAut ι K) * y * (swapAut ι K * swapAut ι K) := by group
        _ = y := by rw [swapAut_mul_self, one_mul, mul_one]
    rw [← h1, pairHom_apply, pairHom_apply, swapAut_conj_pairAut, hθ]

end PairG

end H

end CFSG.Quasithin
