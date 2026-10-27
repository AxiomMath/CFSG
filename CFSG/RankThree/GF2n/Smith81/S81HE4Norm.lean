module

public import CFSG.RankThree.GF2n.Smith81.S81JGSide

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Fixed

private theorem exists_fixed_ne_zero {K E P : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup E] [Module K E] [Module.Finite K E] [Group P] (hP : IsPGroup 2 P)
    (ρ : P →* (E ≃ₗ[K] E)) {e : E} (he : e ≠ 0) : ∃ u : E, u ≠ 0 ∧ ∀ g, ρ g u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite E := Module.finite_of_finite K
  letI : MulAction P E :=
    { smul := fun g u => ρ g u
      one_smul := fun u => by
        show ρ 1 u = u
        simp
      mul_smul := fun g h u => by
        show ρ (g * h) u = ρ g (ρ h u)
        simp [LinearEquiv.mul_apply] }
  have h0 : (0 : E) ∈ MulAction.fixedPoints P E := fun g => map_zero (ρ g)
  have hdvd : 2 ∣ Nat.card E := by
    have hord : addOrderOf e = 2 := by
      apply addOrderOf_eq_prime
      · rw [two_nsmul, ← two_smul K e, CharTwo.two_eq_zero, zero_smul]
      · exact he
    rw [← hord]
    exact addOrderOf_dvd_natCard e
  obtain ⟨u, hu, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hdvd h0
  exact ⟨u, fun h => hne h.symm, fun g => hu g⟩

end Fixed

section Line

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem fixed_iff_mem_img_of_isPGroup [CharP K 2] (hg : GlobalModelData M Q Z γ M₀)
    {A S L : Subgroup G} (hctx : Ctx M Q Z A)
    (hCQt : CQt Q Z (LB M Q A) = ((A ⊔ Z : Subgroup G) : Set G))
    (T : L →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : L) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hAS : LB M Q A ≤ S) (hSL : S ≤ L) (hS : IsPGroup 2 S) (v : M₀.E) :
    (∀ s : L, (s : G) ∈ S → T s v = v) ↔ ∃ x ∈ A, M₀.π x = v := by
  have hfixA := fixed_iff_mem_img (Lg := L) hctx hctx.LB_le_M hctx.hyp.Q_normal.2
    hctx.hyp.Z_normal.1 rfl hCQt hctx.le T hTe (hAS.trans hSL)
  obtain ⟨g, hgA⟩ := hctx.conj
  obtain ⟨e, he0, hline⟩ := hg.line g (by rw [← hgA]; exact hctx.ne) (by rw [← hgA]; exact hctx.le)
  rw [← hgA] at hline
  have himg : ∀ w, (∃ x ∈ A, M₀.π x = w) ↔ w ∈ M₀.img A := fun w =>
    ⟨fun ⟨x, hx, hxw⟩ => ⟨x, hx, hctx.le hx, hxw⟩, fun ⟨x, hx, _, hxw⟩ => ⟨x, hx, hxw⟩⟩
  obtain ⟨u, hu0, hu⟩ := exists_fixed_ne_zero hS (T.comp (Subgroup.inclusion hSL)) he0
  have hufix : ∀ s : L, (s : G) ∈ S → T s u = u := fun s hs => hu ⟨s, hs⟩
  obtain ⟨c, rfl⟩ := (hline u).1 ((himg u).1 ((hfixA u).1 fun s hs => hufix s (hAS hs)))
  have hc : c ≠ 0 := by
    rintro rfl
    exact hu0 (zero_smul K e)
  constructor
  · intro hv
    exact (hfixA v).1 fun s hs => hv s (hAS hs)
  · intro hv s hs
    obtain ⟨d, rfl⟩ := (hline v).1 ((himg v).1 hv)
    have h1 : d • e = (d * c⁻¹) • (c • e) := by
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [h1, map_smul, hufix s hs]

theorem mem_normalizer_LB_of_isPGroup [CharP K 2] (hg : GlobalModelData M Q Z γ M₀)
    {A S L : Subgroup G} (hctx : Ctx M Q Z A)
    (hCQt : CQt Q Z (LB M Q A) = ((A ⊔ Z : Subgroup G) : Set G)) (hLM : L ≤ M)
    (T : L →* (M₀.E ≃ₗ[K] M₀.E))
    (hTe : ∀ (s : L) (x : G), x ∈ Q → M₀.π ((s : G) * x * (s : G)⁻¹) = T s (M₀.π x))
    (hAS : LB M Q A ≤ S) (hSL : S ≤ L) (hS : IsPGroup 2 S) {s : G} (hs : s ∈ L)
    (hsS : s ∈ Subgroup.normalizer (S : Set G)) :
    s ∈ Subgroup.normalizer (LB M Q A : Set G) := by
  have hZQ : Z ≤ Q := hctx.hyp.Z_normal.1
  have hsM : s ∈ M := hLM hs
  have hfix := fixed_iff_mem_img_of_isPGroup hg hctx hCQt T hTe hAS hSL hS
  let s' : L := ⟨s, hs⟩
  have hsinv : s⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hsS
  have hstab : ∀ v, (∀ t : L, (t : G) ∈ S → T t v = v) →
      ∀ t : L, (t : G) ∈ S → T t (T s' v) = T s' v := by
    intro v hv t ht
    have hconj : ((s'⁻¹ * t * s' : L) : G) ∈ S := by
      show s⁻¹ * (t : G) * s ∈ S
      have h := (Subgroup.mem_normalizer_iff.mp hsinv (t : G)).mp ht
      rwa [inv_inv] at h
    have h1 : T t * T s' = T s' * T (s'⁻¹ * t * s') := by
      rw [← map_mul, ← map_mul, show s' * (s'⁻¹ * t * s') = t * s' by group]
    have h2 := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f v) h1
    simp only [LinearEquiv.mul_apply] at h2
    rw [h2, hv _ hconj]
  rw [hctx.mem_normalizer_LB_iff hCQt hsM]
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have haQ : a ∈ Q := (sup_le hctx.le hZQ) ha
  have hsaQ : s * a * s⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hctx.hyp.Q_normal.2 hsM) a).mp haQ
  have hπa : ∃ x ∈ A, M₀.π x = M₀.π a := by
    have hmem : (fun b : G => (LinearEquiv.refl K M₀.E) (M₀.π b)) a ∈
        (fun b : G => (LinearEquiv.refl K M₀.E) (M₀.π b)) '' ((A ⊔ Z : Subgroup G) : Set G) :=
      Set.mem_image_of_mem _ ha
    rw [psi_image_sup_Z (LinearEquiv.refl K M₀.E) hctx.le hZQ] at hmem
    obtain ⟨x, hx, hxa⟩ := hmem
    simp only [LinearEquiv.refl_apply] at hxa
    exact ⟨x, hx, hxa⟩
  obtain ⟨x, hxA, hx⟩ := (hfix (T s' (M₀.π a))).1 (hstab _ ((hfix (M₀.π a)).2 hπa))
  rw [← hTe s' a haQ] at hx
  exact (M₀.mem_img_iff le_sup_right hsaQ).1 ⟨x, Subgroup.mem_sup_left hxA, hctx.le hxA, hx⟩

end Line

end CFSG.RankThree.GF2n.Smith81
