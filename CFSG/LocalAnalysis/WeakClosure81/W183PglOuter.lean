module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
public import CFSG.LocalAnalysis.WeakClosure81.W183PglExt
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

section Outer

variable {Q : Type} [Group Q] {V : Type} [CommGroup V]

@[expose] def W183PglNat (ρ : Q →* MulAut V) (L : Subgroup Q) (I : Subgroup V)
    (e : ↥L ≃* GL (Fin 3) (ZMod 2)) (φ : ↥I ≃* W183PglVec) : Prop :=
  ∀ (l : ↥L) (i j : ↥I), (j : V) = ρ (l : Q) (i : V) →
    Multiplicative.toAdd (φ j) =
      (e l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (φ i)

private theorem w183Pgl_exists_gl_of_hom (T : W183PglVec →* W183PglVec)
    (hT : Function.Bijective T) :
    ∃ s : GL (Fin 3) (ZMod 2), ∀ x : Fin 3 → ZMod 2,
      (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x =
        Multiplicative.toAdd (T (Multiplicative.ofAdd x)) := by
  classical
  let Tl : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := fun x => Multiplicative.toAdd (T (Multiplicative.ofAdd x))
      map_add' := fun x y => by
        change Multiplicative.toAdd (T (Multiplicative.ofAdd (x + y))) =
          Multiplicative.toAdd (T (Multiplicative.ofAdd x)) +
            Multiplicative.toAdd (T (Multiplicative.ofAdd y))
        rw [ofAdd_add, map_mul, toAdd_mul]
      map_smul' := fun c x => by
        have hc : c = ((c.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val c).symm
        change Multiplicative.toAdd (T (Multiplicative.ofAdd (c • x))) =
          c • Multiplicative.toAdd (T (Multiplicative.ofAdd x))
        rw [hc, Nat.cast_smul_eq_nsmul (ZMod 2), Nat.cast_smul_eq_nsmul (ZMod 2), ofAdd_nsmul,
          map_pow, toAdd_pow] }
  have hTl : ∀ x, Tl x = Multiplicative.toAdd (T (Multiplicative.ofAdd x)) := fun x => rfl
  have hinj : Function.Injective Tl := fun x y h => by
    have h' : T (Multiplicative.ofAdd x) = T (Multiplicative.ofAdd y) := by
      apply Multiplicative.toAdd.injective
      simpa [hTl] using h
    exact Multiplicative.ofAdd.injective (hT.1 h')
  let M := LinearMap.toMatrix' Tl
  have hM : ∀ x, M *ᵥ x = Tl x := fun x => by
    simp [M]
  have hunit : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y h
    exact hinj (by rw [← hM, ← hM]; exact h)
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).1 hunit
    exact isUnit_iff_ne_zero.1 this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, fun x => ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  exact hM x

theorem w183Pgl_two_naturals_disjoint (ρ : Q →* MulAut V) {L : Subgroup Q} {I J : Subgroup V}
    (hI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I) (hJ : ∀ l ∈ L, ∀ j ∈ J, ρ l j ∈ J)
    {e₁ e₂ : ↥L ≃* GL (Fin 3) (ZMod 2)} {φ₁ : ↥I ≃* W183PglVec} {φ₂ : ↥J ≃* W183PglVec}
    (h₁ : W183PglNat ρ L I e₁ φ₁) (h₂ : W183PglNat ρ L J e₂ φ₂)
    (hout : ∀ s : GL (Fin 3) (ZMod 2), ∃ l : ↥L, e₂ l ≠ s * e₁ l * s⁻¹) : Disjoint I J := by
  classical
  by_cases hex : ∃ x : ↥I, (x : V) ∈ J ∧ φ₁ x ≠ 1
  · exfalso
    obtain ⟨x, hxJ, hx1⟩ := hex
    have hx0 : Multiplicative.toAdd (φ₁ x) ≠ 0 := fun h => hx1 (by
      rw [← ofAdd_toAdd (φ₁ x), h]
      rfl)
    have hle : ∀ i : ↥I, (i : V) ∈ J := by
      intro i
      by_cases hi : φ₁ i = 1
      · have : i = 1 := φ₁.injective (hi.trans φ₁.map_one.symm)
        rw [this]
        exact J.one_mem
      · have hi0 : Multiplicative.toAdd (φ₁ i) ≠ 0 := fun h => hi (by
          rw [← ofAdd_toAdd (φ₁ i), h]
          rfl)
        obtain ⟨g, hg⟩ := w183Pgl_transitive_nonzero hx0 hi0
        let l : ↥L := e₁.symm g
        have hl : e₁ l = g := e₁.apply_symm_apply g
        have hxl : ρ (l : Q) (x : V) ∈ I := hI l l.2 x x.2
        have hx'J : ρ (l : Q) (x : V) ∈ J := hJ l l.2 x hxJ
        have hφ : Multiplicative.toAdd (φ₁ ⟨ρ (l : Q) (x : V), hxl⟩) =
            Multiplicative.toAdd (φ₁ i) := by
          rw [h₁ l x ⟨ρ (l : Q) (x : V), hxl⟩ rfl, hl, hg]
        have hxi : (⟨ρ (l : Q) (x : V), hxl⟩ : ↥I) = i :=
          φ₁.injective (Multiplicative.toAdd.injective hφ)
        have : (i : V) = ρ (l : Q) (x : V) := by
          rw [← hxi]
        rw [this]
        exact hx'J
    have hle' : I ≤ J := fun v hv => hle ⟨v, hv⟩
    let T : W183PglVec →* W183PglVec :=
      (φ₂.toMonoidHom.comp (Subgroup.inclusion hle')).comp φ₁.symm.toMonoidHom
    have hTinj : Function.Injective T := by
      intro a b hab
      have h1 := φ₂.injective hab
      have h2 := Subgroup.inclusion_injective hle' h1
      exact φ₁.symm.injective h2
    have hTbij : Function.Bijective T := Finite.injective_iff_bijective.1 hTinj
    obtain ⟨s, hs⟩ := w183Pgl_exists_gl_of_hom T hTbij
    obtain ⟨l, hl⟩ := hout s
    apply hl
    have hcomm : ∀ (l : ↥L) (v : Fin 3 → ZMod 2),
        (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            ((e₁ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
          (e₂ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            ((s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
      intro l v
      let i : ↥I := φ₁.symm (Multiplicative.ofAdd v)
      have hi : Multiplicative.toAdd (φ₁ i) = v := by simp [i]
      have hρi : ρ (l : Q) (i : V) ∈ I := hI l l.2 i i.2
      let i' : ↥I := ⟨ρ (l : Q) (i : V), hρi⟩
      have hi' : Multiplicative.toAdd (φ₁ i') =
          (e₁ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := by
        rw [h₁ l i i' rfl, hi]
      have hi'' : i' = φ₁.symm (Multiplicative.ofAdd
          ((e₁ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)) := by
        apply φ₁.injective
        rw [MulEquiv.apply_symm_apply]
        apply Multiplicative.toAdd.injective
        rw [hi']
        rfl
      have hsv : (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v =
          Multiplicative.toAdd (φ₂ (Subgroup.inclusion hle' i)) := by
        rw [hs]
        simp [T, i]
      have hsv' : (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          ((e₁ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
            Multiplicative.toAdd (φ₂ (Subgroup.inclusion hle' i')) := by
        rw [hs, hi'']
        simp [T]
      rw [hsv', hsv]
      exact h₂ l (Subgroup.inclusion hle' i) (Subgroup.inclusion hle' i') rfl
    have hmat : (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (e₁ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (e₂ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      exact hcomm l v
    have hgl : s * e₁ l = e₂ l * s := Units.ext hmat
    rw [hgl]
    group
  · rw [Subgroup.disjoint_def]
    intro x hxI hxJ
    by_contra hne
    apply hex
    refine ⟨⟨x, hxI⟩, hxJ, fun h => hne ?_⟩
    have : (⟨x, hxI⟩ : ↥I) = 1 := φ₁.injective (h.trans φ₁.map_one.symm)
    exact congrArg Subtype.val this

theorem w183Pgl_two_naturals_pairing (ρ : Q →* MulAut V) {L : Subgroup Q} {I J : Subgroup V}
    (hI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I) (hJ : ∀ l ∈ L, ∀ j ∈ J, ρ l j ∈ J)
    {e₁ e₂ : ↥L ≃* GL (Fin 3) (ZMod 2)} {φ₁ : ↥I ≃* W183PglVec} {φ₂ : ↥J ≃* W183PglVec}
    (h₁ : W183PglNat ρ L I e₁ φ₁) (h₂ : W183PglNat ρ L J e₂ φ₂)
    (hout : ∀ s : GL (Fin 3) (ZMod 2), ∃ l : ↥L, e₂ l ≠ s * e₁ l * s⁻¹) :
    IsDualPairing ρ L I J := by
  classical
  let α : MulAut (GL (Fin 3) (ZMod 2)) := e₁.symm.trans e₂
  have hαe : ∀ l : ↥L, α (e₁ l) = e₂ l := fun l => by
    simp [α]
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 3) (ZMod 2),
      α = MulAut.conj s *
        CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2) := by
    rcases CFSG.QuasithinUnique.Setup.Family.aut_GL32_cases α with ⟨s, hs⟩ | h
    · exfalso
      obtain ⟨l, hl⟩ := hout s
      apply hl
      have := congrArg (fun φ : MulAut (GL (Fin 3) (ZMod 2)) => φ (e₁ l)) hs
      simp only [hαe, MulAut.conj_apply] at this
      exact this
    · exact h
  have he₂ : ∀ l : ↥L, e₂ l = s * w183PglTau (e₁ l) * s⁻¹ := fun l => by
    rw [← hαe l, hs]
    rfl
  have hsinv : ∀ u : Fin 3 → ZMod 2,
      (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        (((s⁻¹ : GL (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsinv' : ∀ u : Fin 3 → ZMod 2,
      ((s⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        ((s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hdot : ∀ (M : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2),
      (v ᵥ* ((M⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ
        ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) = v ⬝ᵥ w := fun M v w => by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let β : V → V → ZMod 2 := fun v w =>
    if hv : v ∈ I then
      if hw : w ∈ J then
        Multiplicative.toAdd (φ₁ ⟨v, hv⟩) ⬝ᵥ
          (((s⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (φ₂ ⟨w, hw⟩))
      else 0
    else 0
  have hβ : ∀ (v w : V) (hv : v ∈ I) (hw : w ∈ J), β v w =
      Multiplicative.toAdd (φ₁ ⟨v, hv⟩) ⬝ᵥ
        (((s⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (φ₂ ⟨w, hw⟩)) := by
    intro v w hv hw
    simp only [β, dif_pos hv, dif_pos hw]
  refine ⟨β, ?_, ?_, ?_, ?_, ?_⟩
  · intro i₁ hi₁ i₂ hi₂ j hj
    rw [hβ _ _ (I.mul_mem hi₁ hi₂) hj, hβ _ _ hi₁ hj, hβ _ _ hi₂ hj]
    have : (⟨i₁ * i₂, I.mul_mem hi₁ hi₂⟩ : ↥I) = ⟨i₁, hi₁⟩ * ⟨i₂, hi₂⟩ := rfl
    rw [this, map_mul, toAdd_mul, add_dotProduct]
  · intro i hi j₁ hj₁ j₂ hj₂
    rw [hβ _ _ hi (J.mul_mem hj₁ hj₂), hβ _ _ hi hj₁, hβ _ _ hi hj₂]
    have : (⟨j₁ * j₂, J.mul_mem hj₁ hj₂⟩ : ↥J) = ⟨j₁, hj₁⟩ * ⟨j₂, hj₂⟩ := rfl
    rw [this, map_mul, toAdd_mul, Matrix.mulVec_add, dotProduct_add]
  · intro i hi h
    have ha : Multiplicative.toAdd (φ₁ ⟨i, hi⟩) = 0 := by
      funext k
      obtain ⟨j, hj⟩ := φ₂.surjective
        (Multiplicative.ofAdd ((s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single k 1))
      have h0 := h j.1 j.2
      rw [hβ i j.1 hi j.2] at h0
      have hj' : Multiplicative.toAdd (φ₂ ⟨j.1, j.2⟩) =
          (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single k 1 := by
        rw [hj]
        rfl
      rw [hj', hsinv'] at h0
      simpa using h0
    have h1 : φ₁ ⟨i, hi⟩ = 1 := Multiplicative.toAdd.injective (by rw [ha]; rfl)
    have h2 := φ₁.injective (h1.trans φ₁.map_one.symm)
    exact congrArg Subtype.val h2
  · intro j hj h
    have hb : ((s⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (φ₂ ⟨j, hj⟩) = 0 := by
      funext k
      obtain ⟨i, hi⟩ := φ₁.surjective (Multiplicative.ofAdd (Pi.single k 1))
      have h0 := h i.1 i.2
      rw [hβ i.1 j i.2 hj] at h0
      have hi' : Multiplicative.toAdd (φ₁ ⟨i.1, i.2⟩) = Pi.single k 1 := by
        rw [hi]
        rfl
      rw [hi'] at h0
      simpa using h0
    have h1 : Multiplicative.toAdd (φ₂ ⟨j, hj⟩) = 0 := by
      have := congrArg (fun u => (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u) hb
      simpa [Matrix.mulVec_mulVec, Units.mul_inv] using this
    have h2 : φ₂ ⟨j, hj⟩ = 1 := Multiplicative.toAdd.injective (by rw [h1]; rfl)
    have h3 := φ₂.injective (h2.trans φ₂.map_one.symm)
    exact congrArg Subtype.val h3
  · intro l hl i hi j hj
    have hρi : ρ l i ∈ I := hI l hl i hi
    have hρj : ρ l j ∈ J := hJ l hl j hj
    rw [hβ _ _ hρi hρj, hβ _ _ hi hj]
    let l' : ↥L := ⟨l, hl⟩
    have ha := h₁ l' ⟨i, hi⟩ ⟨ρ l i, hρi⟩ rfl
    have hb := h₂ l' ⟨j, hj⟩ ⟨ρ l j, hρj⟩ rfl
    rw [ha, hb, he₂ l']
    have hτ : ((w183PglTau (e₁ l') : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (((e₁ l')⁻¹ : GL (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ :=
      Matrix.GeneralLinearGroup.coe_inverseTranspose _
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsinv',
      hτ, Matrix.mulVec_transpose, dotProduct_comm, hdot, dotProduct_comm]

theorem w183Pgl_isNaturalL3Two_conj (ρ : Q →* MulAut V) {L : Subgroup Q} [L.Normal]
    {I : Subgroup V} {e : ↥L ≃* GL (Fin 3) (ZMod 2)} {φ : ↥I ≃* W183PglVec}
    (h : W183PglNat ρ L I e φ) (hI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I) (g : Q) :
    (∀ l ∈ L, ∀ j ∈ I.map (ρ g).toMonoidHom, ρ l j ∈ I.map (ρ g).toMonoidHom) ∧
      ∃ (e₂ : ↥L ≃* GL (Fin 3) (ZMod 2)) (φ₂ : ↥(I.map (ρ g).toMonoidHom) ≃* W183PglVec),
        W183PglNat ρ L (I.map (ρ g).toMonoidHom) e₂ φ₂ ∧
          ∀ (l l' : ↥L), (l' : Q) = g⁻¹ * (l : Q) * g → e₂ l = e l' := by
  have hconj : ∀ l : Q, l ∈ L → g⁻¹ * l * g ∈ L := fun l hl => by
    have := (inferInstance : L.Normal).conj_mem l hl g⁻¹
    simpa using this
  have hmove : ∀ (l : Q) (i : V), ρ g (ρ (g⁻¹ * l * g) i) = ρ l (ρ g i) := fun l i => by
    change (ρ g) ((ρ (g⁻¹ * l * g)) i) = (ρ l) ((ρ g) i)
    rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  refine ⟨?_, ?_⟩
  · rintro l hl _ ⟨i, hi, rfl⟩
    exact ⟨ρ (g⁻¹ * l * g) i, hI _ (hconj l hl) i hi, hmove l i⟩
  · let c : ↥L ≃* ↥L := (MulAut.conjNormal (H := L) g).symm
    have hc : ∀ l : ↥L, ((c l : ↥L) : Q) = g⁻¹ * (l : Q) * g := fun l =>
      MulAut.conjNormal_symm_apply g l
    let θ : ↥I ≃* ↥(I.map (ρ g).toMonoidHom) := (ρ g).subgroupMap I
    have hθ : ∀ i : ↥I, ((θ i : ↥(I.map (ρ g).toMonoidHom)) : V) = ρ g (i : V) := fun i => rfl
    refine ⟨c.trans e, θ.symm.trans φ, ?_, ?_⟩
    · intro l i j hj
      obtain ⟨i', rfl⟩ := θ.surjective i
      obtain ⟨j', rfl⟩ := θ.surjective j
      rw [hθ, hθ] at hj
      have hj' : (j' : V) = ρ ((c l : ↥L) : Q) (i' : V) := by
        rw [hc]
        apply (ρ g).injective
        rw [hmove, hj]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact h (c l) i' j' hj'
    · intro l l' hl'
      have : c l = l' := Subtype.ext (by rw [hc, hl'])
      simp [this]

theorem w183Pgl_outer_not_inner {L : Subgroup Q} [L.Normal]
    (hcent : Subgroup.centralizer (L : Set Q) ≤ L)
    {g : Q} (hg : g ∉ L) (e e₂ : ↥L ≃* GL (Fin 3) (ZMod 2))
    (he₂ : ∀ (l l' : ↥L), (l' : Q) = g⁻¹ * (l : Q) * g → e₂ l = e l') :
    ∀ s : GL (Fin 3) (ZMod 2), ∃ l : ↥L, e₂ l ≠ s * e l * s⁻¹ := by
  intro s
  by_contra hcon
  have hall : ∀ l : ↥L, e₂ l = s * e l * s⁻¹ := fun l => by
    by_contra h
    exact hcon ⟨l, h⟩
  apply hg
  set l₀ : ↥L := e.symm s with hl₀
  have hcm : g * (l₀ : Q) ∈ Subgroup.centralizer (L : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (inferInstance : L.Normal).conj_mem l hl g⁻¹
      simpa using this
    have h1 : e₂ ⟨l, hl⟩ = e ⟨g⁻¹ * l * g, hl'⟩ := he₂ _ _ rfl
    have h2 : e₂ ⟨l, hl⟩ = e (l₀ * ⟨l, hl⟩ * l₀⁻¹) := by
      rw [hall, map_mul, map_mul, map_inv, hl₀, MulEquiv.apply_symm_apply]
    have h3 : (⟨g⁻¹ * l * g, hl'⟩ : ↥L) = l₀ * ⟨l, hl⟩ * l₀⁻¹ := e.injective (h1.symm.trans h2)
    have h4 : g⁻¹ * l * g = (l₀ : Q) * l * (l₀ : Q)⁻¹ := by
      simpa using congrArg Subtype.val h3
    calc l * (g * (l₀ : Q)) = g * (g⁻¹ * l * g) * (l₀ : Q) := by group
      _ = g * ((l₀ : Q) * l * (l₀ : Q)⁻¹) * (l₀ : Q) := by rw [h4]
      _ = g * (l₀ : Q) * l := by group
  have hmem := hcent hcm
  have hg' : g = (g * (l₀ : Q)) * (l₀ : Q)⁻¹ := by group
  rw [hg']
  exact L.mul_mem hmem (L.inv_mem l₀.2)

theorem w183Pgl_outer (ρ : Q →* MulAut V) {L : Subgroup Q} [L.Normal]
    (hcent : Subgroup.centralizer (L : Set Q) ≤ L) {I : Subgroup V}
    (hI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I) (hnat : IsNaturalL3Two ρ L I) {g : Q} (hg : g ∉ L) :
    Disjoint I (I.map (ρ g).toMonoidHom) ∧ IsDualPairing ρ L I (I.map (ρ g).toMonoidHom) := by
  obtain ⟨e, φ, h⟩ := hnat
  obtain ⟨hJ, e₂, φ₂, h₂, he₂⟩ :=
    w183Pgl_isNaturalL3Two_conj ρ (L := L) (I := I) (e := e) (φ := φ) h hI g
  have hout := w183Pgl_outer_not_inner hcent hg e e₂ he₂
  exact ⟨w183Pgl_two_naturals_disjoint ρ hI hJ h h₂ hout,
    w183Pgl_two_naturals_pairing ρ hI hJ h h₂ hout⟩

theorem w183Pgl_sup_eq (ρ : Q →* MulAut V) {L : Subgroup Q} (hidx : L.index = 2) {I : Subgroup V}
    (hI : ∀ l ∈ L, ∀ i ∈ I, ρ l i ∈ I) {g : Q} (hg : g ∉ L) :
    (⨆ y : Q, I.map (ρ y).toMonoidHom) = I ⊔ I.map (ρ g).toMonoidHom := by
  apply le_antisymm
  · refine iSup_le fun y => ?_
    by_cases hy : y ∈ L
    · refine le_sup_of_le_left ?_
      rintro _ ⟨i, hi, rfl⟩
      exact hI y hy i hi
    · have hl : g⁻¹ * y ∈ L := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact ⟨fun h => absurd (inv_mem_iff.mp h) hg, fun h => absurd h hy⟩
      refine le_sup_of_le_right ?_
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨ρ (g⁻¹ * y) i, hI _ hl i hi, ?_⟩
      change (ρ g) ((ρ (g⁻¹ * y)) i) = (ρ y) i
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
  · refine sup_le (le_iSup_of_le 1 ?_) (le_iSup (fun y => I.map (ρ y).toMonoidHom) g)
    rintro i hi
    exact ⟨i, hi, by simp⟩

end Outer

end CFSG.LocalAnalysis.WeakClosure81

end
