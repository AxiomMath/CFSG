module

public import CFSG.Quasithin.EmptyFaithful.S146zJVtx
public import CFSG.Quasithin.EmptyFaithful.S146P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

@[expose] def B2Out {G : Type} [Group G] [Finite G] (T M H Hi : Subgroup G) : Prop :=
  ∃ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
    F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g ∧
      F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (g : G) < F8.Uγ (VZ T M) H (g : G) ∧
      F8.Uγ (VZ T M) H (g : G) ≤ Hi ∧
      F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H Hi ∧
      quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H Hi)

@[expose] def Input14613B2In : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8 →
          ∀ (δ δ' : F8.Geom T (yOfL22 T M) H) (k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
            F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k →
            0 < mIdx (F8.Uγ (VZ T M) H (k : G))
              (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
            mIdx (conjClosure (VZ T M) H)
                (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
              mIdx (F8.Uγ (VZ T M) H (k : G))
                (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
              F8.Uγ (VZ T M) H (k : G) ≤ H₁ ∨ F8.Uγ (VZ T M) H (k : G) ≤ H₂

section Sym

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.conjSub_uHi_mem (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H)
    {X : Subgroup G} (hX : X = uHi T M H H₁ ∨ X = uHi T M H H₂) :
    conjSub x X = uHi T M H H₁ ∨ conjSub x X = uHi T M H H₂ := by
  rcases h.normalizer_or_swap S hred hx with ⟨-, h1, h2⟩ | ⟨h1, h2⟩
  · rcases hX with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr h2
  · rcases hX with rfl | rfl
    · exact Or.inr h1
    · exact Or.inl h2

theorem IsDecP.exists_Z_le_conj (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) {g k₂ y : G}
    (hyg : y * g ∈ H) (hky : k₂⁻¹ * y ∈ H) {X : Subgroup G}
    (hX : X = uHi T M H H₁ ∨ X = uHi T M H H₂)
    (hA : conjSub k₂ (quasithinOmegaOneCenter T) ≤ X) :
    quasithinOmegaOneCenter T ≤ conjSub g (uHi T M H H₁) ∨
      quasithinOmegaOneCenter T ≤ conjSub g (uHi T M H H₂) := by
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hZinv : ∀ x ∈ H, conjSub x (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
    fun x hx => conjSub_eq_of_mem_normalizer (hHN hx)
  have h1 : quasithinOmegaOneCenter T ≤ conjSub k₂⁻¹ X := (conjSub_le_iff k₂).mp hA
  have e : k₂⁻¹ = (k₂⁻¹ * y) * g * (y * g)⁻¹ := by group
  rw [e, conjSub_mul, conjSub_mul, le_conjSub_iff, hZinv _ (H.inv_mem hky)] at h1
  rcases h.conjSub_uHi_mem S hred (H.inv_mem hyg) hX with h2 | h2
  · left
    rw [h2] at h1
    exact h1
  · right
    rw [h2] at h1
    exact h1

end Sym

section Core

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.translate_out (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (hlt : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G) < F8.Uγ (VZ T M) H (k : G))
    (hU1 : F8.Uγ (VZ T M) H (k : G) ≤ H₁)
    (hA₁ : F8.A₁ (quasithinOmegaOneCenter T) (k : G) ≤ uHi T M H H₁)
    (hZ : quasithinOmegaOneCenter T ≤ conjSub (k : G) (uHi T M H H₂)) : B2Out T M H H₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  obtain ⟨h81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have htH : t ∈ H := hTH h.t_mem
  let τ : ↥(((yOfL22 T M) ⊔ T) ⊔ H) := ⟨t, h98.amalgamHypV.le₂ htH⟩
  have sτ := sk.smul_T h81 (τ := τ) h.t_mem
  have hUτ : F8.Uγ (VZ T M) H ((τ * k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)) : G) =
      conjSub t (F8.Uγ (VZ T M) H (k : G)) := by
    unfold F8.Uγ
    exact conjSub_mul t (k : G) _
  have hAτ : F8.A₁ (quasithinOmegaOneCenter T) ((τ * k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)) : G) =
      conjSub t (F8.A₁ (quasithinOmegaOneCenter T) (k : G)) := by
    unfold F8.A₁
    exact conjSub_mul t (k : G) _
  refine ⟨τ • δ, τ • δ', τ * k, sτ, ?_, ?_, ?_, ?_⟩
  · have hDeq := h98.Dγ_eq_inf_pCoreOf sτ
    have hDeqk := h98.Dγ_eq_inf_pCoreOf sk
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
    have hUQ : F8.Uγ (VZ T M) H ((τ * k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)) : G) ≤ pCoreOf 2 H :=
      inf_eq_left.mp (hDeq.symm.trans hD)
    rw [hUτ] at hUQ
    have h1 := conjSub_mono t⁻¹ hUQ
    rw [conjSub_conjSub_inv,
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H (H.inv_mem htH))] at h1
    apply hlt.ne
    rw [hDeqk]
    exact inf_eq_left.mpr h1
  · rw [hUτ]
    calc conjSub t (F8.Uγ (VZ T M) H (k : G)) ≤ conjSub t H₁ := conjSub_mono t hU1
      _ = H₂ := h.conj.symm
  · rw [hAτ]
    calc conjSub t (F8.A₁ (quasithinOmegaOneCenter T) (k : G)) ≤ conjSub t (uHi T M H H₁) :=
          conjSub_mono t hA₁
      _ = uHi T M H H₂ := h.conjSub_uHi hred
  · have hZt : conjSub t (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
      conjSub_eq_of_mem_normalizer (hHN htH)
    have e : conjSub ((τ * k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)) : G) (uHi T M H H₂) =
        conjSub t (conjSub (k : G) (uHi T M H H₂)) := conjSub_mul t (k : G) _
    rw [e]
    calc quasithinOmegaOneCenter T = conjSub t (quasithinOmegaOneCenter T) := hZt.symm
      _ ≤ conjSub t (conjSub (k : G) (uHi T M H H₂)) := conjSub_mono t hZ

theorem IsDecP.b2_core (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h8 : mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8)
    (hin : ∀ (δ δ' : F8.Geom T (yOfL22 T M) H) (k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
        F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k →
        0 < mIdx (F8.Uγ (VZ T M) H (k : G))
          (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
        mIdx (conjClosure (VZ T M) H)
            (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
          mIdx (F8.Uγ (VZ T M) H (k : G))
            (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
        F8.Uγ (VZ T M) H (k : G) ≤ H₁ ∨ F8.Uγ (VZ T M) H (k : G) ≤ H₂)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (hpos : 0 < mIdx (F8.Uγ (VZ T M) H (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hle : mIdx (conjClosure (VZ T M) H)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
      mIdx (F8.Uγ (VZ T M) H (k : G)) (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hU1 : F8.Uγ (VZ T M) H (k : G) ≤ H₁) :
    B2Out T M H H₁ ∨ B2Out T M H H₂ := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨h81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have hyp := h98.amalgamHypV
  obtain ⟨hm1, hm2⟩ := h.mIdx_eq_one_of_le S hred sk hpos hle hU1
  have hA₁ := h.A₁_le_uHi S hred h8 sk hpos hm2.le hU1
  have hDlt : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G) <
      F8.Uγ (VZ T M) H (k : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
    rw [hD] at hpos
    unfold mIdx at hpos
    rw [Subgroup.relIndex_self] at hpos
    simp at hpos
  obtain ⟨ε, ε', k₂, y, sk₂, hyγ, hyγ₁, eU, eB, eDH, eDγ⟩ :=
    h98.exists_symmetric_setup sk (h98.not_Vγ_le_ballStab_of_lt sk hDlt)
  have m1 : mIdx (F8.Uγ (VZ T M) H (k₂ : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k₂ : G)) =
      mIdx (conjClosure (VZ T M) H) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
    rw [eU, eDγ, F9.mIdx_conjSub]
  have m2 : mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k₂ : G)) =
      mIdx (F8.Uγ (VZ T M) H (k : G)) (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
    rw [eDH, ← eB, F9.mIdx_conjSub]
  have hpos₂ : 0 < mIdx (F8.Uγ (VZ T M) H (k₂ : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k₂ : G)) := by
    rw [m1]
    omega
  have hle₂ : mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k₂ : G)) ≤
      mIdx (F8.Uγ (VZ T M) H (k₂ : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k₂ : G)) := by
    rw [m2, m1]
    omega
  have hDH₂ : mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k₂ : G)) ≤ 1 := by
    rw [m2]
    exact hm1.le
  have hyg : (y : G) * (k : G) ∈ H := by
    have h1 : (y * k) • F8.γ₁ T (yOfL22 T M) H = F8.γ₁ T (yOfL22 T M) H := by
      rw [mul_smul, sk.edge₁, hyγ]
    have h2 := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at h2
    simpa using h2
  have hky : (k₂ : G)⁻¹ * (y : G) ∈ H := by
    have h1 : (k₂⁻¹ * y) • F8.γ₁ T (yOfL22 T M) H = F8.γ₁ T (yOfL22 T M) H := by
      rw [mul_smul, hyγ₁, ← sk₂.edge₁, inv_smul_smul]
    have h2 := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at h2
    simpa using h2
  have hZ : quasithinOmegaOneCenter T ≤ conjSub (k : G) (uHi T M H H₁) ∨
      quasithinOmegaOneCenter T ≤ conjSub (k : G) (uHi T M H H₂) := by
    rcases hin ε ε' k₂ sk₂ hpos₂ hle₂ with hU₂ | hU₂
    · have hA₂ := h.A₁_le_uHi S hred h8 sk₂ hpos₂ hDH₂ hU₂
      exact h.exists_Z_le_conj S hred hyg hky (Or.inl rfl) hA₂
    · have hA₂ := h.swap.A₁_le_uHi S hred h8 sk₂ hpos₂ hDH₂ hU₂
      exact h.exists_Z_le_conj S hred hyg hky (Or.inr rfl) hA₂
  rcases hZ with hZ | hZ
  · exact Or.inl ⟨δ, δ', k, sk, hDlt, hU1, hA₁, hZ⟩
  · exact Or.inr (h.translate_out S hred sk hDlt hU1 hA₁ hZ)

end Core

theorem input14613B2P_of_in (hin : Input14613B2In) : Input14613B2P := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h hex h8
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨γ, γ', g, hs, hlt⟩ := hex
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  obtain ⟨δ, δ', k, sk, hpos, hle, -⟩ := h98.lemma_14_5_18_four hs hlt
  have hin' := hin G T M S H PQ p hred H₀ H₁ H₂ t h h8
  rcases hin' δ δ' k sk hpos hle with hU1 | hU2
  · exact h.b2_core S hred h8 hin' sk hpos hle hU1
  · exact (h.swap.b2_core S hred h8 (fun δ δ' k sk hpos hle => (hin' δ δ' k sk hpos hle).symm)
      sk hpos hle hU2).symm

end CFSG.Quasithin
