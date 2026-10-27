module

public import CFSG.RankThree.GF2n.Smith81.S81JCubeIso
public import CFSG.RankThree.GF2n.Smith81.S81LModel
public import CFSG.RankThree.GF2n.Smith81.S81BA5Rank

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.S81J Module

section Aux

variable {K : Type} [Field K]

theorem twist_twist_symm (σ : K ≃+* K) (x : GL (Fin 6) K) : twist σ (twist σ.symm x) = x := by
  apply Units.ext
  rw [twist_val, twist_val]
  ext i j
  simp [Matrix.map_apply]

private theorem tw_mulVec_map (σ : K ≃+* K) (M : Matrix (Fin 6) (Fin 6) K) (v : Fin 6 → K)
    (i : Fin 6) :
    (M.map σ).mulVec v i = σ ((M.mulVec (fun j => σ.symm (v j))) i) := by
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem twist_mem_UnipGL_S0 (σ : K ≃+* K) {n : GL (Fin 6) K} (hn : n ∈ UnipGL K (S0 K)) :
    twist σ n ∈ UnipGL K (S0 K) := by
  obtain ⟨hdet, hX, hfix⟩ := mem_UnipGL_iff.1 hn
  refine mem_UnipGL_iff.2 ⟨?_, ?_, ?_⟩
  · rw [det_twist, hdet, map_one]
  · intro v
    rw [twist_val, s81A12_mem_S0]
    intro j hj
    have h1 : (n : Matrix (Fin 6) (Fin 6) K).mulVec (fun k => σ.symm (v k)) j = σ.symm (v j) := by
      have h0 := (s81A12_mem_S0.1 (hX (fun k => σ.symm (v k)))) j hj
      simp only [Pi.sub_apply] at h0
      exact sub_eq_zero.1 h0
    simp only [Pi.sub_apply]
    rw [tw_mulVec_map, h1, RingEquiv.apply_symm_apply, sub_self]
  · intro s hs
    have hs' : (fun k => σ.symm (s k)) ∈ S0 K := by
      rw [s81A12_mem_S0]
      intro k hk
      simp [(s81A12_mem_S0.1 hs) k hk]
    rw [twist_val]
    funext i
    rw [tw_mulVec_map, hfix _ hs']
    simp

theorem finrank_map_mulVecLin (g : GL (Fin 6) K) (W : Submodule K (Fin 6 → K)) :
    finrank K (W.map (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K))) = finrank K W := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K)) := by
    intro x y h
    have h' := congrArg (Matrix.mulVec ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) h
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h'
  exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

theorem finrank_Fix_of_three [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    (A : SLAct K V) {W₀ W : Submodule K (Fin 6 → K)}
    (hW₀ : finrank K W₀ = 3) (hW : finrank K W = 3) (h : finrank K (A.Fix W₀) = 1) :
    finrank K (A.Fix W) = 1 := by
  obtain ⟨g, hg, hmap⟩ := exists_sl_map_eq hW₀ hW
  rw [← hmap, A.finrank_Fix_map hg, h]

end Aux

section Assembly

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem uniform_of_core (hq : 4 ≤ Nat.card K) (hV : finrank K M₀.E = 20)
    (T : Lgen M (LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : Lgen M (LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hTker : ∀ s : Lgen M (LB M Q B), T s = 1 ↔ (s : G) ∈ Q)
    (hnorm : Lgen M (LB M Q B) ≤ Subgroup.normalizer (Q : Set G))
    (A : SLAct K M₀.E)
    (hAT1 : ∀ s : Lgen M (LB M Q B), ∃ h : GL (Fin 6) K,
      (h : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ ∀ v, T s v = A.act h v)
    (hAT2 : ∀ h : GL (Fin 6) K, (h : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ∃ s : Lgen M (LB M Q B), ∀ v, T s v = A.act h v)
    (hpts : ∀ A' : Subgroup G, IsZConjugate Z A' → A' ≤ Q → A' ≠ Z →
      ∃ W : Submodule K (Fin 6 → K), finrank K W = 3 ∧ finrank K (A.Fix W) = 1 ∧
        (∀ v, v ∈ A.Fix W ↔ ∃ x ∈ A', M₀.π x = v) ∧
        ∀ u ∈ UnipGL K W, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB A' ∧ ∀ v, T t v = A.act u v)
    (hB : IsZConjugate Z B ∧ B ≤ Q ∧ B ≠ Z)
    (hspan : ∀ v : M₀.E, v ∈ ⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
        Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G))) :
    ∃ (ψ : M₀.E ≃ₗ[K] Cube K) (φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)),
      EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K) := by
  classical
  obtain ⟨W₀, hW₀3, hW₀line, hW₀fix, -⟩ := hpts B hB.1 hB.2.1 hB.2.2
  have hspan' : ⨆ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
      (A.Fix W₀).map (A.act g.1) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hle : (⨆ A' : {A' : Subgroup G // IsZConjugate Z A' ∧ A' ≤ Q ∧ A' ≠ Z},
        Submodule.span K ((fun x : G => M₀.π x) '' ((A'.1 : Subgroup G) : Set G))) ≤
        ⨆ g : {g : GL (Fin 6) K // (g : Matrix (Fin 6) (Fin 6) K).det = 1},
          (A.Fix W₀).map (A.act g.1) := by
      apply iSup_le
      intro A'
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨W', hW'3, -, hW'fix, -⟩ := hpts A'.1 A'.2.1 A'.2.2.1 A'.2.2.2
      obtain ⟨g', hg', hmap⟩ := exists_sl_map_eq hW₀3 hW'3
      have hmem : M₀.π x ∈ (A.Fix W₀).map (A.act g') := by
        rw [SLAct.Fix_map A hg', hmap]
        exact (hW'fix _).mpr ⟨x, hx, rfl⟩
      exact Submodule.mem_iSup_of_mem (⟨g', hg'⟩ : {g : GL (Fin 6) K //
        (g : Matrix (Fin 6) (Fin 6) K).det = 1}) hmem
    exact hle (hspan v)
  obtain ⟨σ, g₀, Φ, hg₀, hΦ, hΦp⟩ := A.core_main hq hV hW₀3 hW₀line hspan'
  have hdetmul : ∀ g h : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      (h : Matrix (Fin 6) (Fin 6) K).det = 1 → ((g * h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    intro g h hg hh
    rw [Units.val_mul, Matrix.det_mul, hg, hh, mul_one]
  have hdetinv : ∀ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ((g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    intro g hg
    have h1 : ((g * g⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [mul_inv_cancel]; simp
    rw [Units.val_mul, Matrix.det_mul, hg, one_mul] at h1
    exact h1
  have hdettwist : ∀ (σ' : K ≃+* K) (h : GL (Fin 6) K), (h : Matrix (Fin 6) (Fin 6) K).det = 1 →
      ((twist σ' h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    intro σ' h hh
    rw [det_twist, hh, map_one]
  let ψ : M₀.E ≃ₗ[K] Cube K := Φ.symm
  let φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K) :=
    { toFun := fun s => transport ψ (T s)
      map_one' := by rw [map_one]; exact transport_one ψ
      map_mul' := fun a b => by rw [map_mul]; exact transport_mul ψ _ _ }
  have hφ : ∀ s, φ s = transport ψ (T s) := fun s => rfl
  have key : ∀ (h : GL (Fin 6) K) (s : Lgen M (LB M Q B)),
      (h : Matrix (Fin 6) (Fin 6) K).det = 1 →
      (∀ v, T s v = A.act (g₀ * twist σ h * g₀⁻¹) v) → φ s = rhoEquiv K h := by
    intro h s hh hs
    apply LinearEquiv.ext
    intro ξ
    rw [hφ, rhoEquiv_apply]
    show Φ.symm (T s (Φ ξ)) = rho K h ξ
    rw [hs, ← hΦ h hh ξ]
    simp
  have hex : ∀ s : Lgen M (LB M Q B), ∃ h : GL (Fin 6) K,
      (h : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ φ s = rhoEquiv K h := by
    intro s
    obtain ⟨h₀, hdet₀, hT⟩ := hAT1 s
    refine ⟨twist σ.symm (g₀⁻¹ * h₀ * g₀), hdettwist _ _
      (hdetmul _ _ (hdetmul _ _ (hdetinv _ hg₀) hdet₀) hg₀), key _ s (hdettwist _ _
      (hdetmul _ _ (hdetmul _ _ (hdetinv _ hg₀) hdet₀) hg₀)) ?_⟩
    intro v
    rw [twist_twist_symm, hT v]
    congr 2
    group
  refine ⟨ψ, φ, ?_, ?_, hnorm, ?_, ?_⟩
  ·
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨h, hh, hsh⟩ := hex s
      rw [hsh]
      exact Subgroup.mem_map_of_mem _ (CFSG.Open.StatedAPI.mem_statedSL_of_det hh)
    · intro hx
      obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hx
      have hh'det := CFSG.Open.StatedAPI.det_of_mem_statedSL hh'
      obtain ⟨s, hs⟩ := hAT2 (g₀ * twist σ h' * g₀⁻¹)
        (hdetmul _ _ (hdetmul _ _ hg₀ (hdettwist _ _ hh'det)) (hdetinv _ hg₀))
      exact ⟨s, key h' s hh'det hs⟩
  ·
    intro s
    rw [← hTker s, hφ]
    constructor
    · intro h
      apply transport_injective ψ
      rw [h, transport_one]
    · intro h
      rw [h, transport_one]
  ·
    intro s x hx
    show ψ (M₀.π ((s : G) * x * (s : G)⁻¹)) = transport ψ (T s) (ψ (M₀.π x))
    rw [transport_apply, hTe s x hx]
  ·
    intro A' hA'z hA'Q hA'Z
    obtain ⟨W, hW3, hWline, hWfix, hWrad⟩ := hpts A' hA'z hA'Q hA'Z
    have hS0' : finrank K ((S0 K).map (Matrix.mulVecLin (g₀ : Matrix (Fin 6) (Fin 6) K))) = 3 := by
      rw [finrank_map_mulVecLin, finrank_S0]
    obtain ⟨g₁, hg₁, hg₁map⟩ := exists_sl_map_eq hS0' hW3
    have hline0 : finrank K (A.Fix ((S0 K).map (Matrix.mulVecLin (g₀ : Matrix (Fin 6) (Fin 6) K))))
        = 1 := finrank_Fix_of_three A hW₀3 hS0' hW₀line
    have hΦp0 : Φ (p0 K) ≠ 0 := fun h => p0_ne_zero (Φ.map_eq_zero_iff.mp h)
    have hspanF : A.Fix ((S0 K).map (Matrix.mulVecLin (g₀ : Matrix (Fin 6) (Fin 6) K))) =
        Submodule.span K {Φ (p0 K)} := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hΦp
      · rw [finrank_span_singleton hΦp0, hline0]
    have hFixW : A.Fix W = Submodule.span K {A.act g₁ (Φ (p0 K))} := by
      rw [← hg₁map, ← SLAct.Fix_map A hg₁, hspanF, Submodule.map_span, Set.image_singleton]
    have hdet₁ : (g₁ : Matrix (Fin 6) (Fin 6) K).det = 1 := hg₁
    have hh₁det : ((twist σ.symm (g₀⁻¹ * g₁ * g₀) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det
        = 1 := hdettwist _ _ (hdetmul _ _ (hdetmul _ _ (hdetinv _ hg₀) hdet₁) hg₀)
    have hh₁ : g₀ * twist σ (twist σ.symm (g₀⁻¹ * g₁ * g₀)) * g₀⁻¹ = g₁ := by
      rw [twist_twist_symm]
      group
    set h₁ : GL (Fin 6) K := twist σ.symm (g₀⁻¹ * g₁ * g₀) with hh₁def
    have hΦh₁ : Φ (rho K h₁ (p0 K)) = A.act g₁ (Φ (p0 K)) := by
      rw [hΦ h₁ hh₁det (p0 K), hh₁]
    refine ⟨rhoEquiv K h₁, Subgroup.mem_map_of_mem _
      (CFSG.Open.StatedAPI.mem_statedSL_of_det hh₁det), ?_, ?_⟩
    ·
      ext w
      simp only [Set.mem_image, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hmem : M₀.π a ∈ A.Fix W := (hWfix _).mpr ⟨a, ha, rfl⟩
        rw [hFixW, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Submodule.mem_span_singleton]
        refine ⟨c, ?_⟩
        show c • rho K h₁ (p0 K) = Φ.symm (M₀.π a)
        rw [← hc, map_smul, ← hΦh₁]
        simp
      · intro hw
        rw [Submodule.mem_span_singleton] at hw
        obtain ⟨c, rfl⟩ := hw
        have hmem : Φ (c • rhoEquiv K h₁ (p0 K)) ∈ A.Fix W := by
          rw [hFixW, map_smul, rhoEquiv_apply, hΦh₁]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        obtain ⟨x, hx, hxπ⟩ := (hWfix _).mp hmem
        refine ⟨x, hx, ?_⟩
        show Φ.symm (M₀.π x) = _
        rw [hxπ]
        simp
    ·
      intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := mem_conjSub.mp hu
      rw [U0_eq_Urad] at hu₀
      obtain ⟨n, hn, rfl⟩ := mem_Urad_iff.mp hu₀
      have hdetn : (n : Matrix (Fin 6) (Fin 6) K).det = 1 := (mem_UnipGL_iff.mp hn).1
      have hh'det : ((h₁ * n * h₁⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
        hdetmul _ _ (hdetmul _ _ hh₁det hdetn) (hdetinv _ hh₁det)
      have he : g₀ * twist σ (h₁ * n * h₁⁻¹) * g₀⁻¹ ∈ UnipGL K W := by
        have e1 : g₀ * twist σ (h₁ * n * h₁⁻¹) * g₀⁻¹ =
            g₁ * (g₀ * twist σ n * g₀⁻¹) * g₁⁻¹ := by
          rw [← hh₁, map_mul, map_mul, map_inv]
          group
        rw [e1, ← hg₁map]
        exact s81A12_conj_mem g₁ _ (s81A12_conj_mem g₀ (S0 K) (twist_mem_UnipGL_S0 σ hn))
      obtain ⟨t, htQB, htT⟩ := hWrad _ he
      refine ⟨t, htQB, ?_⟩
      rw [key _ t hh'det htT, map_mul, map_mul, map_inv]

end Assembly

end CFSG.RankThree.GF2n.Smith81
