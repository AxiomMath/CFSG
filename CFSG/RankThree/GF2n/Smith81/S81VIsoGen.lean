module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {M V : Type} [AddCommGroup M] [Module K M]
  [AddCommGroup V] [Module K V]

theorem iso_of_generation [FiniteDimensional K M] [FiniteDimensional K V]
    (AM : Γ →* (M ≃ₗ[K] M)) (AV : Γ →* (V ≃ₗ[K] V)) (p₀ : M) (v₀ : V)
    {Pt : Type} (pt : Γ → Pt) (Col : Pt → Pt → Pt → Prop) (Pi : Finset Pt) (s : Γ) (xs : K → Γ)
    (hhom : ∀ g g' : Γ, pt g = pt g' →
      ∃ c : K, c ≠ 0 ∧ AM g p₀ = c • AM g' p₀ ∧ AV g v₀ = c • AV g' v₀)
    (hline : ∀ x y z : Pt, Col x y z → x ≠ y → ∃ (g : Γ) (t : K),
      pt g = x ∧ pt (g * s) = y ∧ (z = x ∨ z = pt (g * xs t * s)))
    (hR1M : ∀ t : K, AM (xs t) (AM s p₀) = AM s p₀ + t • p₀)
    (hR1V : ∀ t : K, AV (xs t) (AV s v₀) = AV s v₀ + t • v₀)
    (hsurj : Function.Surjective pt)
    (hGen : ∀ Q : Pt → Prop, (∀ x ∈ Pi, Q x) →
      (∀ x y z : Pt, Q x → Q y → x ≠ y → Col x y z → Q z) → ∀ x, Q x)
    (hPi : Pi.card ≤ finrank K V)
    (hspanV : Submodule.span K (Set.range fun g => AV g v₀) = ⊤)
    (hspanM : Submodule.span K (Set.range fun g => AM g p₀) = ⊤)
    (hdim : finrank K V ≤ finrank K M) :
    ∃ ψ : V ≃ₗ[K] M, (∀ g v, ψ (AV g v) = AM g (ψ v)) ∧ ψ v₀ = p₀ := by
  have hVmul : ∀ (γ δ : Γ) (w : V), AV (γ * δ) w = AV γ (AV δ w) := by
    intro γ δ w
    rw [map_mul]
    rfl
  have hMmul : ∀ (γ δ : Γ) (w : M), AM (γ * δ) w = AM γ (AM δ w) := by
    intro γ δ w
    rw [map_mul]
    rfl
  have hV1 : ∀ (g : Γ) (t : K), AV (g * xs t * s) v₀ = AV (g * s) v₀ + t • AV g v₀ := by
    intro g t
    rw [hVmul (g * xs t) s, hVmul g (xs t), hR1V t, map_add, map_smul, hVmul g s]
  have hM1 : ∀ (g : Γ) (t : K), AM (g * xs t * s) p₀ = AM (g * s) p₀ + t • AM g p₀ := by
    intro g t
    rw [hMmul (g * xs t) s, hMmul g (xs t), hR1M t, map_add, map_smul, hMmul g s]
  have hs : ∀ x : Pt, ∃ g : Γ, pt g = x := hsurj
  choose gX hgX using hs
  obtain ⟨bfam, hbfam⟩ : ∃ f : ↥Pi → V, ∀ x : ↥Pi, f x = AV (gX x.1) v₀ :=
    ⟨fun x => AV (gX x.1) v₀, fun x => rfl⟩
  have hQ : ∀ x : Pt, ∀ g : Γ, pt g = x → AV g v₀ ∈ Submodule.span K (Set.range bfam) := by
    refine hGen (fun x => ∀ g : Γ, pt g = x → AV g v₀ ∈ Submodule.span K (Set.range bfam))
      ?_ ?_
    · intro x hx g hg
      obtain ⟨c, -, -, hcV⟩ := hhom g (gX x) (hg.trans (hgX x).symm)
      have hmem : AV (gX x) v₀ ∈ Submodule.span K (Set.range bfam) :=
        Submodule.subset_span ⟨⟨x, hx⟩, hbfam ⟨x, hx⟩⟩
      rw [hcV]
      exact Submodule.smul_mem _ c hmem
    · intro x y z hQx hQy hxy hcol
      obtain ⟨g, t, hgx, hgy, hz⟩ := hline x y z hcol hxy
      rcases hz with hz | hz
      · intro g'' hg''
        exact hQx g'' (hg''.trans hz)
      · intro g'' hg''
        obtain ⟨c, -, -, hcV⟩ := hhom g'' (g * xs t * s) (hg''.trans hz)
        rw [hcV, hV1 g t]
        exact Submodule.smul_mem _ c (Submodule.add_mem _ (hQy (g * s) hgy)
          (Submodule.smul_mem _ t (hQx g hgx)))
  have hDall : ∀ g : Γ, AV g v₀ ∈ Submodule.span K (Set.range bfam) :=
    fun g => hQ (pt g) g rfl
  have hspanfam : (⊤ : Submodule K V) ≤ Submodule.span K (Set.range bfam) := by
    rw [← hspanV, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hDall g
  have hSeq : Submodule.span K (Set.range bfam) = ⊤ := eq_top_iff.mpr hspanfam
  have hcard : Fintype.card ↥Pi = finrank K V := by
    apply le_antisymm
    · rw [Fintype.card_coe]
      exact hPi
    · have h : finrank K (Submodule.span K (Set.range bfam)) ≤ Fintype.card ↥Pi :=
        finrank_range_le_card bfam
      rwa [hSeq, finrank_top] at h
  have hli : LinearIndependent K bfam :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanfam hcard
  obtain ⟨bas, hbas⟩ : ∃ bas : Basis ↥Pi K V, ∀ x, bas x = bfam x :=
    ⟨Basis.mk hli hspanfam, fun x => Basis.mk_apply hli hspanfam x⟩
  obtain ⟨L, hL⟩ : ∃ L : V →ₗ[K] M, ∀ x : ↥Pi, L (bfam x) = AM (gX x.1) p₀ :=
    ⟨bas.constr K (fun x : ↥Pi => AM (gX x.1) p₀), fun x => by
      rw [← hbas x]
      exact bas.constr_basis K _ x⟩
  have hLx : ∀ (x : Pt) (hx : x ∈ Pi), L (AV (gX x) v₀) = AM (gX x) p₀ := by
    intro x hx
    have h := hL ⟨x, hx⟩
    rw [hbfam] at h
    exact h
  have hLQ : ∀ x : Pt, ∀ g : Γ, pt g = x → L (AV g v₀) = AM g p₀ := by
    refine hGen (fun x => ∀ g : Γ, pt g = x → L (AV g v₀) = AM g p₀) ?_ ?_
    · intro x hx g hg
      obtain ⟨c, -, hcM, hcV⟩ := hhom g (gX x) (hg.trans (hgX x).symm)
      rw [hcV, map_smul, hLx x hx, hcM]
    · intro x y z hQx hQy hxy hcol
      obtain ⟨g, t, hgx, hgy, hz⟩ := hline x y z hcol hxy
      rcases hz with hz | hz
      · intro g'' hg''
        exact hQx g'' (hg''.trans hz)
      · intro g'' hg''
        obtain ⟨c, -, hcM, hcV⟩ := hhom g'' (g * xs t * s) (hg''.trans hz)
        rw [hcM, hcV, map_smul, hV1 g t, map_add, map_smul, hQy (g * s) hgy, hQx g hgx,
          hM1 g t]
  have hLall : ∀ g : Γ, L (AV g v₀) = AM g p₀ := fun g => hLQ (pt g) g rfl
  have hequiv : ∀ (γ : Γ) (v : V), L (AV γ v) = AM γ (L v) := by
    intro γ
    have hfun : L.comp (AV γ : V →ₗ[K] V) = (AM γ : M →ₗ[K] M).comp L := by
      apply LinearMap.ext_on_range hspanV
      intro g
      show L (AV γ (AV g v₀)) = AM γ (L (AV g v₀))
      rw [← hVmul γ g, hLall (γ * g), hLall g, hMmul]
    intro v
    exact LinearMap.congr_fun hfun v
  have hrange : LinearMap.range L = ⊤ := by
    rw [eq_top_iff, ← hspanM, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact LinearMap.mem_range.mpr ⟨AV g v₀, hLall g⟩
  have hLsurj : Function.Surjective L := LinearMap.range_eq_top.mp hrange
  have hfinle : finrank K M ≤ finrank K V := by
    have h := LinearMap.finrank_range_le L
    rwa [hrange, finrank_top] at h
  have hfineq : finrank K V = finrank K M := le_antisymm hdim hfinle
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfineq).mpr hLsurj
  refine ⟨LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩, ?_, ?_⟩
  · intro g v
    exact hequiv g v
  · have h1 : AV (1 : Γ) v₀ = v₀ := by
      rw [map_one]
      rfl
    have h2 : AM (1 : Γ) p₀ = p₀ := by
      rw [map_one]
      rfl
    show L v₀ = p₀
    calc L v₀ = L (AV 1 v₀) := by rw [h1]
      _ = AM 1 p₀ := hLall 1
      _ = p₀ := h2

end CFSG.RankThree.GF2n.Smith81.S81V
