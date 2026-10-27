module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nDR_resEndo {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (g : V ≃ₗ[ZMod p] V)
    (hg : ∀ u ∈ U, g u ∈ U) : ↥U →ₗ[ZMod p] ↥U :=
  { toFun := fun u => ⟨g u, hg u u.2⟩
    map_add' := by intro a b; ext; simp
    map_smul' := by intro c a; ext; simp }

private theorem l05nDR_resEndo_apply {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (g : V ≃ₗ[ZMod p] V)
    (hg : ∀ u ∈ U, g u ∈ U) (u : ↥U) :
    ((l05nDR_resEndo U g hg u : ↥U) : V) = g u := rfl

private theorem l05nDR_resEndo_injective {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (g : V ≃ₗ[ZMod p] V)
    (hg : ∀ u ∈ U, g u ∈ U) : Function.Injective (l05nDR_resEndo U g hg) := by
  intro a b hab
  apply Subtype.ext
  exact g.injective (by simpa [l05nDR_resEndo_apply] using congrArg Subtype.val hab)

theorem ggDepA_linRefl_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : V ≃ₗ[ZMod p] V) : GGLinRefl T ↔ IsLinRefl T := by
  constructor
  · intro h
    obtain ⟨hTT, hfr⟩ := h
    let L : V →ₗ[ZMod p] V := T.toLinearMap - LinearMap.id
    have hfr' : Module.finrank (ZMod p) (LinearMap.range L) = 1 := by
      have hW : ggLinMove T = LinearMap.range L := rfl
      rw [← hW]; exact hfr
    have hne : LinearMap.range L ≠ ⊥ := by
      intro hbot
      rw [hbot] at hfr'
      simp at hfr'
    obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff _).mp hne
    have hspan : LinearMap.range L = ZMod p ∙ y :=
      eq_span_singleton_of_mem_of_finrank_eq_one hfr' hyW hy0
    obtain ⟨f0, hf0⟩ : ∃ f0 : Module.Dual (ZMod p) V, f0 y = 1 := by
      have hy : y ∉ (⊥ : Submodule (ZMod p) V) := by simpa using hy0
      obtain ⟨f, hfy, -⟩ := Submodule.exists_le_ker_of_notMem hy
      exact ⟨(f y)⁻¹ • f, by
        simp only [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfy]⟩
    let g : Module.Dual (ZMod p) V := f0.comp L
    have hg_apply : ∀ v, g v = f0 (L v) := fun _ => rfl
    have hLg : ∀ v, L v = g v • y := by
      intro v
      have hv : L v ∈ ZMod p ∙ y := by
        rw [← hspan]; exact LinearMap.mem_range_self L v
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
      rw [← hc]
      show c • y = g v • y
      congr 1
      rw [hg_apply, ← hc, map_smul, hf0, smul_eq_mul, mul_one]
    have hTv : ∀ v, T v = v + g v • y := by
      intro v
      have h2 : T v - v = g v • y := by simpa [L] using hLg v
      have h3 : T v - g v • y = v := by rw [← h2]; abel
      exact sub_eq_iff_eq_add.mp h3
    have hgy : g y = -2 := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hyW
      have hgu : g u ≠ 0 := by
        rw [hg_apply, hu, hf0]; exact one_ne_zero
      have h1 : T (T u) = u := by
        have := congrArg (fun e : V ≃ₗ[ZMod p] V => e u) hTT
        simpa [LinearEquiv.mul_apply] using this
      have h2 : T (T u) = u + (g u + g (T u)) • y := by
        rw [hTv (T u), hTv u]
        module
      have h3 : (g u + g (T u)) • y = 0 := by
        have h : u + (g u + g (T u)) • y = u + 0 := by simpa using h2.symm.trans h1
        exact add_left_cancel h
      have h4 : g u + g (T u) = 0 := by
        rcases smul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h hy0
      have h5 : g (T u) = g u + g u * g y := by
        rw [hTv u, map_add, map_smul]
        simp [smul_eq_mul]
      have h6 : g u * (2 + g y) = 0 := by
        have h := h4
        rw [h5] at h
        calc g u * (2 + g y) = g u + (g u + g u * g y) := by ring
          _ = 0 := h
      rcases mul_eq_zero.mp h6 with h | h
      · exact absurd h hgu
      · have h' : g y + 2 = 0 := by simpa [add_comm] using h
        exact eq_neg_of_add_eq_zero_left h'
    refine ⟨y, -g, ?_, ?_⟩
    · show (-g) y = 2
      rw [LinearMap.neg_apply, hgy, neg_neg]
    · intro v
      rw [hTv v, LinearMap.neg_apply, neg_smul, sub_neg_eq_add]
  · rintro ⟨x, f, hfx, hT⟩
    have hrefl : IsLinRefl T := ⟨x, f, hfx, hT⟩
    have hx0 : x ≠ 0 := (ne_zero_of_apply_eq_two hp2 hfx).1
    have hf : f ≠ 0 := (ne_zero_of_apply_eq_two hp2 hfx).2
    refine ⟨?_, ?_⟩
    · ext v
      simpa [LinearEquiv.mul_apply] using IsLinRefl.apply_apply hrefl v
    · have hL : T.toLinearMap - LinearMap.id = (-f).smulRight x := by
        ext v
        change T v - v = (LinearMap.smulRight (-f) x) v
        rw [hT v, LinearMap.smulRight_apply, LinearMap.neg_apply, neg_smul]
        abel
      rw [ggLinMove, hL, LinearMap.range_smulRight_apply (neg_ne_zero.mpr hf)]
      exact finrank_span_singleton hx0

theorem ggDepA_restrict {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (U : Submodule (ZMod p) V) (S : Set (V ≃ₗ[ZMod p] V))
    (hS : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U) :
    ∃ res : ↥(Subgroup.closure S) →* (↥U ≃ₗ[ZMod p] ↥U),
      (∀ (g : ↥(Subgroup.closure S)) (u : ↥U),
        ((res g u : ↥U) : V) = (g : V ≃ₗ[ZMod p] V) u) ∧
      Nat.card ↥res.range ≤ Nat.card ↥(Subgroup.closure S) ∧
      res.range = Subgroup.closure
        {t | ∃ (s : V ≃ₗ[ZMod p] V) (hs : s ∈ S), t = res ⟨s, Subgroup.subset_closure hs⟩} := by
  haveI hfinU : Module.Finite (ZMod p) ↥U :=
    FiniteDimensional.finiteDimensional_submodule U
  let H : Subgroup (V ≃ₗ[ZMod p] V) :=
    { carrier := {g | ∀ u ∈ U, g u ∈ U}
      one_mem' := by intro u hu; simpa using hu
      mul_mem' := by intro g h hg hh u hu; exact hg (h u) (hh u hu)
      inv_mem' := by
        intro g hg u hu
        obtain ⟨w, hw⟩ :=
          LinearMap.surjective_of_injective (l05nDR_resEndo_injective U g hg) (⟨u, hu⟩ : ↥U)
        have hgw : g w = u := by
          simpa [l05nDR_resEndo_apply] using congrArg Subtype.val hw
        have hgi : g⁻¹ u = w := by rw [← hgw]; simp
        rw [hgi]; exact w.2 }
  have hSH : S ⊆ H := fun s hs => hS s hs
  have hmap : ∀ g ∈ Subgroup.closure S, ∀ u ∈ U, g u ∈ U := fun g hg =>
    (Subgroup.closure_le H).mpr hSH hg
  let res : ↥(Subgroup.closure S) →* (↥U ≃ₗ[ZMod p] ↥U) :=
    { toFun := fun g =>
        LinearEquiv.ofInjectiveEndo (l05nDR_resEndo U (g : V ≃ₗ[ZMod p] V) (hmap g g.2))
          (l05nDR_resEndo_injective U (g : V ≃ₗ[ZMod p] V) (hmap g g.2))
      map_one' := by
        ext u
        simp only [LinearEquiv.coe_ofInjectiveEndo, l05nDR_resEndo_apply, Subgroup.coe_one]
        rfl
      map_mul' := by
        intro g h
        ext u
        simp only [LinearEquiv.mul_apply, LinearEquiv.coe_ofInjectiveEndo, l05nDR_resEndo_apply]
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply] }
  refine ⟨res, ?_, ?_, ?_⟩
  · intro g u
    show ((l05nDR_resEndo U (g : V ≃ₗ[ZMod p] V) (hmap g g.2) u : ↥U) : V) =
      (g : V ≃ₗ[ZMod p] V) u
    rw [l05nDR_resEndo_apply]
  · haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : Finite V := Module.finite_of_finite (ZMod p)
    haveI : Finite (V ≃ₗ[ZMod p] V) :=
      Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
        (fun _ _ h => LinearEquiv.ext (congrFun h))
    haveI : Finite ↥(Subgroup.closure S) :=
      Finite.of_injective (Subtype.val : ↥(Subgroup.closure S) → V ≃ₗ[ZMod p] V)
        Subtype.val_injective
    refine Nat.card_le_card_of_surjective
      (fun g : ↥(Subgroup.closure S) =>
        (⟨res g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : ↥res.range)) ?_
    intro t
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp t.2
    exact ⟨g, Subtype.ext hg⟩
  · let T : Set ↥(Subgroup.closure S) :=
      ((↑) : ↥(Subgroup.closure S) → V ≃ₗ[ZMod p] V) ⁻¹' S
    have hT : Subgroup.closure T = ⊤ := by
      show Subgroup.closure (((↑) : ↥(Subgroup.closure S) → V ≃ₗ[ZMod p] V) ⁻¹' S) = ⊤
      exact Subgroup.closure_closure_coe_preimage
    have hset : res '' T =
        {t | ∃ (s : V ≃ₗ[ZMod p] V) (hs : s ∈ S),
          t = res ⟨s, Subgroup.subset_closure hs⟩} := by
      ext t
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨(g : V ≃ₗ[ZMod p] V), hg, congrArg res (Subtype.ext rfl)⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, Subgroup.subset_closure hs⟩, hs, rfl⟩
    calc res.range = (⊤ : Subgroup ↥(Subgroup.closure S)).map res :=
          MonoidHom.range_eq_map res
      _ = (Subgroup.closure T).map res := by rw [hT]
      _ = Subgroup.closure (res '' T) := MonoidHom.map_closure res T
      _ = Subgroup.closure
            {t | ∃ (s : V ≃ₗ[ZMod p] V) (hs : s ∈ S),
              t = res ⟨s, Subgroup.subset_closure hs⟩} := by rw [hset]

end CFSG.StandardType

end
