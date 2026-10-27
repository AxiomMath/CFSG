module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Chain
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRep
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Core2

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N CFSG.RankThree.SubgroupLists
open Matrix
open scoped MatrixGroups

theorem nk_s9_mod_core (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep)
    (hConj : ∀ (X : Type) [Group X], IsPSL 3 2 1 X → ∀ a b : X, orderOf a = 2 → orderOf b = 2 →
      IsConj a b)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {Sg Gg Tg Vg : Subgroup (W ≃ₗ[ZMod 2] W)} {WB : Submodule (ZMod 2) W}
    (h : TransvConfig Sg Gg Tg Vg WB)
    {K₀ : Subgroup (W ≃ₗ[ZMod 2] W)} (hK₀G : K₀ ≤ Gg)
    (v : W ≃ₗ[ZMod 2] W) (hvV : v ∈ Vg) (hv1 : v ≠ 1)
    (hK₀v : K₀ ≤ Subgroup.closure {x | ∃ k ∈ K₀, x = k * v * k⁻¹})
    (hvK : ∀ k ∈ K₀, v * k * v⁻¹ ∈ K₀)
    (τ : W ≃ₗ[ZMod 2] W) (hτT : τ ∈ Tg) (hτK : ∀ k ∈ K₀, τ * k * τ⁻¹ ∈ K₀)
    {Ks : Type} [Group Ks] (hKs : IsSimpleGroup Ks) (hna : ∃ a b : Ks, a * b ≠ b * a)
    (hKs3 : IsPSL 3 2 1 Ks)
    (σ : K₀ →* Ks) (hσ : Function.Surjective σ)
    (hker : ∀ M : Subgroup K₀, M.Normal → M ≠ ⊤ → M ≤ σ.ker)
    (hout : ∀ y : K₀, ∃ x : K₀, ∃ z : K₀,
      (z : W ≃ₗ[ZMod 2] W) = τ * x * τ⁻¹ ∧ σ z ≠ σ (y * x * y⁻¹))
    (hK₀perf : commutator ↥K₀ = ⊤)
    (hQ : ∃ Q₀ : Subgroup (W ≃ₗ[ZMod 2] W), Q₀ ≤ K₀ ∧ (∀ q ∈ Q₀, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
      (∀ q ∈ Q₀, ∀ x ∈ K₀, x * q * x⁻¹ ∈ Q₀) ∧ (∀ q ∈ Q₀, v * q * v⁻¹ ∈ Q₀) ∧
      (∃ k₀ ∈ K₀, ∀ x ∈ K₀, ∃ q ∈ Q₀, v * x * v⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z : ↥K₀, σ z = 1 → ∀ x ∈ K₀, ∃ q ∈ Q₀, (z : W ≃ₗ[ZMod 2] W) * x *
        (z : W ≃ₗ[ZMod 2] W)⁻¹ = q * x)) :
    False := by
  obtain ⟨d, E, hFld, hFin, hChar, φ, hE2, hφinj, hbr, htr⟩ := nk_rep_main h
  obtain ⟨e, he, hE⟩ : ∃ e : ℕ, 1 ≤ e ∧ Nat.card E = 2 ^ e := by
    rcases hE2 with h2 | h4
    · exact ⟨1, le_rfl, by rw [h2]; norm_num⟩
    · exact ⟨2, by norm_num, by rw [h4]; norm_num⟩
  have hvG : v ∈ Gg := h.V_le hvV
  have hg₀ne : (⟨v, hvG⟩ : Gg) ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
  obtain ⟨t, htdef⟩ : ∃ t : GL (Fin d) E, t = φ ⟨v, hvG⟩ := ⟨_, rfl⟩
  have ht : IsTransvectionK t := by
    rw [htdef]
    exact htr ⟨v, hvG⟩ hg₀ne ⟨v, hvV, 1, Subgroup.one_mem _, by simp⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : K₀ →* GL (Fin d) E, ∀ k : K₀, ψ k = φ (Subgroup.inclusion hK₀G k) :=
    ⟨φ.comp (Subgroup.inclusion hK₀G), fun _ => rfl⟩
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    have h1 : φ (Subgroup.inclusion hK₀G a) = φ (Subgroup.inclusion hK₀G b) := by
      rw [← hψ, ← hψ]
      exact hab
    exact congrArg (fun x : Gg => (x : W ≃ₗ[ZMod 2] W)) (hφinj h1)
  have hrr : ∀ k : K₀, ((ψ.rangeRestrict k : ψ.range) : GL (Fin d) E) =
      φ (Subgroup.inclusion hK₀G k) :=
    fun k => hψ k
  have hK₁t : ∀ k ∈ ψ.range, t * k * t⁻¹ ∈ ψ.range := by
    rintro _ ⟨y, rfl⟩
    refine ⟨⟨v * y * v⁻¹, hvK y y.2⟩, ?_⟩
    simp only [hψ]
    rw [htdef, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hK₁N : ψ.range ≤ Subgroup.closure {x | ∃ k ∈ ψ.range, x = k * t * k⁻¹} := by
    rintro _ ⟨y, rfl⟩
    have hC : ∀ k : K₀, φ (Subgroup.inclusion hK₀G k) * φ ⟨v, hvG⟩ *
        (φ (Subgroup.inclusion hK₀G k))⁻¹ ∈
          Subgroup.closure {x | ∃ k ∈ ψ.range, x = k * t * k⁻¹} := by
      intro k
      apply Subgroup.subset_closure
      refine ⟨ψ k, ⟨k, rfl⟩, ?_⟩
      rw [hψ, htdef]
    rw [hψ]
    exact s9c_closure_transfer φ hK₀G hvG hC hK₀v y
  obtain ⟨hσ₁surj, hσ₁hker⟩ := s9c_range_hker σ hσ ψ hψinj hker
  have hσ₁apply : ∀ k : K₀,
      (σ.comp (MonoidHom.ofInjective hψinj).symm.toMonoidHom) (ψ.rangeRestrict k) = σ k := by
    intro k
    show σ ((MonoidHom.ofInjective hψinj).symm (ψ.rangeRestrict k)) = σ k
    congr 1
    exact (MulEquiv.symm_apply_eq _).mpr rfl
  have hsurjR : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
  have hK₁perf : commutator ↥ψ.range = ⊤ := by
    have key : (commutator ↥K₀).map ψ.rangeRestrict = commutator ↥ψ.range := by
      rw [commutator_def K₀, commutator_def ψ.range, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hsurjR]
    rw [← key, hK₀perf]
    exact Subgroup.map_top_of_surjective _ hsurjR
  have hQ₁ : ∃ Q : Subgroup (GL (Fin d) E), Q ≤ ψ.range ∧ (∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
      (∀ q ∈ Q, ∀ x ∈ ψ.range, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, t * q * t⁻¹ ∈ Q) ∧
      (∃ k₀ ∈ ψ.range, ∀ x ∈ ψ.range, ∃ q ∈ Q, t * x * t⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
      (∀ z : ↥ψ.range, (σ.comp (MonoidHom.ofInjective hψinj).symm.toMonoidHom) z = 1 →
        ∀ x ∈ ψ.range, ∃ q ∈ Q, (z : GL (Fin d) E) * x * (z : GL (Fin d) E)⁻¹ = q * x) := by
    obtain ⟨Q₀, hQ₀K, hQ₀2, hQ₀K₀, hQ₀v, ⟨k₀, hk₀, hvin⟩, hcen⟩ := hQ
    have hmemQ : ∀ q : K₀, (q : W ≃ₗ[ZMod 2] W) ∈ Q₀ → ψ q ∈ (Q₀.subgroupOf K₀).map ψ :=
      fun q hq => Subgroup.mem_map.mpr ⟨q, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    refine ⟨(Q₀.subgroupOf K₀).map ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨q, -, rfl⟩
      exact ⟨q, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨m, hm⟩ := hQ₀2 q.1 (Subgroup.mem_subgroupOf.mp hq)
      refine ⟨m, ?_⟩
      have : q ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
      rw [← map_pow, this, map_one]
    · rintro _ ⟨q, hq, rfl⟩ _ ⟨x, rfl⟩
      have h1 : (x * q * x⁻¹ : K₀) ∈ Q₀.subgroupOf K₀ := by
        rw [Subgroup.mem_subgroupOf]
        have := hQ₀K₀ q.1 (Subgroup.mem_subgroupOf.mp hq) x.1 x.2
        simpa using this
      have e : ψ x * ψ q * (ψ x)⁻¹ = ψ (x * q * x⁻¹) := by simp [map_mul, map_inv]
      show ψ x * ψ q * (ψ x)⁻¹ ∈ (Q₀.subgroupOf K₀).map ψ
      rw [e]
      exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      have hqQ := Subgroup.mem_subgroupOf.mp hq
      have hvq : v * (q : W ≃ₗ[ZMod 2] W) * v⁻¹ ∈ K₀ := hvK q.1 q.2
      have h1 : (⟨v * (q : W ≃ₗ[ZMod 2] W) * v⁻¹, hvq⟩ : K₀) ∈ Q₀.subgroupOf K₀ :=
        Subgroup.mem_subgroupOf.mpr (hQ₀v q.1 hqQ)
      have e : t * ψ q * t⁻¹ = ψ ⟨v * (q : W ≃ₗ[ZMod 2] W) * v⁻¹, hvq⟩ := by
        rw [htdef, hψ, hψ, ← map_inv, ← map_mul, ← map_mul]
        rfl
      show t * ψ q * t⁻¹ ∈ (Q₀.subgroupOf K₀).map ψ
      rw [e]
      exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    · refine ⟨ψ ⟨k₀, hk₀⟩, ⟨⟨k₀, hk₀⟩, rfl⟩, ?_⟩
      rintro _ ⟨x, rfl⟩
      obtain ⟨q, hq, hqe⟩ := hvin x.1 x.2
      have hqK : q ∈ K₀ := hQ₀K hq
      have e1 : (⟨v * (x : W ≃ₗ[ZMod 2] W) * v⁻¹, hvK x.1 x.2⟩ : K₀) =
          ⟨q, hqK⟩ * (⟨k₀, hk₀⟩ * x * ⟨k₀, hk₀⟩⁻¹) := Subtype.ext (by simpa using hqe)
      have e2 : t * ψ x * t⁻¹ = ψ ⟨v * (x : W ≃ₗ[ZMod 2] W) * v⁻¹, hvK x.1 x.2⟩ := by
        rw [htdef, hψ, hψ, ← map_inv, ← map_mul, ← map_mul]
        rfl
      refine ⟨ψ ⟨q, hqK⟩, hmemQ ⟨q, hqK⟩ hq, ?_⟩
      rw [e2, e1]
      simp [map_mul, map_inv]
    · intro z hz x hx
      obtain ⟨z₀, rfl⟩ := hsurjR z
      obtain ⟨x₀, rfl⟩ := hx
      rw [hσ₁apply] at hz
      obtain ⟨q, hq, hqe⟩ := hcen z₀ hz x₀.1 x₀.2
      have hqK : q ∈ K₀ := hQ₀K hq
      have e1 : (z₀ * x₀ * z₀⁻¹ : K₀) = ⟨q, hqK⟩ * x₀ := Subtype.ext (by simpa using hqe)
      refine ⟨ψ ⟨q, hqK⟩, hmemQ ⟨q, hqK⟩ hq, ?_⟩
      have e2 : ((ψ.rangeRestrict z₀ : ψ.range) : GL (Fin d) E) * ψ x₀ *
          ((ψ.rangeRestrict z₀ : ψ.range) : GL (Fin d) E)⁻¹ = ψ (z₀ * x₀ * z₀⁻¹) := by
        simp [map_mul, map_inv]
      rw [e2, e1, map_mul]
  obtain ⟨θ₁, hθ₁surj, hθ₁ker, hO2a, hO2b⟩ :=
    nk_s9_chain_main hSch hSL3 hConj hE2 he hE t ht ψ.range hK₁t hK₁N hKs hna hKs3
      (σ.comp (MonoidHom.ofInjective hψinj).symm.toMonoidHom) hσ₁surj hσ₁hker hK₁perf hQ₁
  obtain ⟨θ, hθdef⟩ : ∃ θ : K₀ →* SL(3, ZMod 2), θ = θ₁.comp ψ.rangeRestrict := ⟨_, rfl⟩
  have hθapp : ∀ k : K₀, θ k = θ₁ (ψ.rangeRestrict k) := fun k => by
    subst hθdef
    rfl
  have hθsurj : Function.Surjective θ := by
    rw [hθdef]
    exact hθ₁surj.comp (MonoidHom.rangeRestrict_surjective ψ)
  have hθker : θ.ker = σ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hθapp]
    have h1 : θ₁ (ψ.rangeRestrict k) = 1 ↔ ψ.rangeRestrict k ∈ θ₁.ker :=
      MonoidHom.mem_ker.symm
    rw [h1, hθ₁ker, MonoidHom.mem_ker, hσ₁apply]
  have hO2a' : ∀ k : K₀, ((θ k : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = s9M1 →
      (s9P1 ((φ (Subgroup.inclusion hK₀G k) : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det = 0 := by
    intro k hk
    rw [hθapp] at hk
    have h2 := hO2a (ψ.rangeRestrict k) hk
    rw [hrr] at h2
    exact h2
  have hO2b' : ∀ k : K₀,
      s9P2 (((θ k : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).map
        (fun a : ZMod 2 => ((a.val : ℕ) : E))) = 0 →
      (s9P1 ((φ (Subgroup.inclusion hK₀G k) : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det ≠ 0 := by
    intro k hk
    rw [hθapp] at hk
    have h2 := hO2b (ψ.rangeRestrict k) hk
    rw [hrr] at h2
    exact h2
  obtain ⟨c, hcdef⟩ := s9c_conj_hom K₀ τ hτK
  have hout' : ∀ y : K₀, ∃ x : K₀, σ (c x) ≠ σ (y * x * y⁻¹) := by
    intro y
    obtain ⟨x, z, hz, hne⟩ := hout y
    have hzc : z = c x := Subtype.ext (by rw [hz, hcdef x])
    exact ⟨x, by rw [← hzc]; exact hne⟩
  obtain ⟨g, hgM, hP2⟩ := s9c_alg_graph K₀ τ σ hσ hna hker c hcdef θ hθsurj hθker hout'
  obtain ⟨fr, hfr⟩ : ∃ fr : ZMod 2 →+* E, ∀ a : ZMod 2, fr a = ((a.val : ℕ) : E) :=
    ⟨ZMod.castHom (dvd_refl 2) E, fun a => by rw [ZMod.castHom_apply, ZMod.cast_eq_val]⟩
  have hfr_eq : (fun a : ZMod 2 => ((a.val : ℕ) : E)) = ⇑fr := funext fun a => (hfr a).symm
  have hP2E : s9P2 (((θ (c g) : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).map
      (fun a : ZMod 2 => ((a.val : ℕ) : E))) = 0 := by
    rw [hfr_eq, ← RingHom.mapMatrix_apply, s9c_map_P2, hP2, map_zero]
  have hdeth := hO2b' (c g) hP2E
  have hdetg := hO2a' g hgM
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (W ≃ₗ[ZMod 2] W) →* (W →ₗ[ZMod 2] W),
      ∀ x : W ≃ₗ[ZMod 2] W, ℓ x = ((x : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) :=
    ⟨LinearEquiv.automorphismGroup.toLinearMapMonoidHom, fun _ => rfl⟩
  have hτℓ : ℓ τ * ℓ τ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hτℓ' : ℓ τ⁻¹ * ℓ τ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcg : ℓ ((Subgroup.inclusion hK₀G (c g) : Gg) : W ≃ₗ[ZMod 2] W) =
      ℓ τ * ℓ ((Subgroup.inclusion hK₀G g : Gg) : W ≃ₗ[ZMod 2] W) * ℓ τ⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact hcdef g
  have hkerh : LinearMap.ker
      (s9P1 (ℓ ((Subgroup.inclusion hK₀G (c g) : Gg) : W ≃ₗ[ZMod 2] W))) = ⊥ := by
    rw [hℓ]
    exact (hbr (Subgroup.inclusion hK₀G (c g))).mpr hdeth
  have hkerg : LinearMap.ker
      (s9P1 (ℓ ((Subgroup.inclusion hK₀G g : Gg) : W ≃ₗ[ZMod 2] W))) ≠ ⊥ := by
    rw [hℓ]
    intro hb
    exact (hbr (Subgroup.inclusion hK₀G g)).mp hb hdetg
  have e1 := s9c_conj_P1 (ℓ τ) (ℓ τ⁻¹)
    (ℓ ((Subgroup.inclusion hK₀G g : Gg) : W ≃ₗ[ZMod 2] W)) hτℓ hτℓ'
  have hkerh' : LinearMap.ker (ℓ τ *
      s9P1 (ℓ ((Subgroup.inclusion hK₀G g : Gg) : W ≃ₗ[ZMod 2] W)) * ℓ τ⁻¹) = ⊥ := by
    rw [← e1, ← hcg]
    exact hkerh
  exact hkerg (s9c_ker_of_conj _ (ℓ τ) (ℓ τ⁻¹) hτℓ hτℓ' hkerh')

end CFSG.Quasithin.H13.L829NK
