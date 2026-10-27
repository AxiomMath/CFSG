module

public import CFSG.RankThree.PartTwo.KFacts.K74Irreducible

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.Classical
open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

theorem exists_dual_eq_one_of_not_mem {p : Submodule (ZMod 3) V} {x : V} (hx : x ∉ p) :
    ∃ φ : Dual (ZMod 3) V, φ x = 1 ∧ ∀ y ∈ p, φ y = 0 := by
  obtain ⟨f, hf, hfp⟩ := p.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(f x)⁻¹ • f, ?_, fun y hy => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
  · have h : f y ∈ p.map f := Submodule.mem_map_of_mem hy
    rw [hfp, Submodule.mem_bot] at h
    rw [LinearMap.smul_apply, h, smul_zero]

theorem dual_ne_zero_of_eq_one {φ : Dual (ZMod 3) V} {x : V} (h : φ x = 1) : φ ≠ 0 := by
  rintro rfl
  rw [LinearMap.zero_apply] at h
  exact zero_ne_one h

theorem smul_mem_span_singleton (k : ZMod 3) (x : V) :
    k • x ∈ Submodule.span (ZMod 3) ({x} : Set V) :=
  Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

theorem mem_span_of_transvections [FiniteDimensional (ZMod 3) V]
    (hV : finrank (ZMod 3) V = 3) {G' : Subgroup (V ≃ₗ[ZMod 3] V)} {u w : V} (hu : u ≠ 0)
    (hT : ∀ φ : Dual (ZMod 3) V, φ u = 0 → ∃ g ∈ G', ∀ x, g x = x + φ x • u)
    (hc : ∀ g ∈ G', g w ∉ Submodule.span (ZMod 3) ({u} : Set V))
    (hH : ∀ g ∈ G', g w ∈ Submodule.span (ZMod 3) ({w} : Set V) →
      g u ∈ Submodule.span (ZMod 3) ({u} : Set V)) :
    ∀ g ∈ G', g u ∈ Submodule.span (ZMod 3) ({u} : Set V) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g0, hg0, hg0u⟩ := hcon
  set U := Submodule.span (ZMod 3) ({u} : Set V) with hUdef
  have huU : u ∈ U := Submodule.mem_span_singleton_self u
  set S : Set V := {x | ∃ g ∈ G', g u = x} with hSdef
  set B := Submodule.span (ZMod 3) S with hBdef
  have hBinv : ∀ g ∈ G', ∀ x ∈ B, g x ∈ B := by
    intro g hg x hx
    have hle : B.map (g : V →ₗ[ZMod 3] V) ≤ B := by
      rw [hBdef, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, ⟨h, hh, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, G'.mul_mem hg hh, rfl⟩
    exact hle (Submodule.mem_map_of_mem hx)
  by_cases hBtop : B = ⊤
  ·
    have hirr : ∀ W : Submodule (ZMod 3) V, (∀ g ∈ G', ∀ x ∈ W, g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_cases hW0 : W = ⊥
      · exact Or.inl hW0
      right
      obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      have huW : u ∈ W := by
        by_cases hxU : x ∈ U
        · obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hxU
          have hk : k ≠ 0 := by
            rintro rfl
            exact hx0 (zero_smul _ _)
          have h1 : u = k⁻¹ • (k • u) := by rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
          rw [h1]
          exact W.smul_mem _ hxW
        · obtain ⟨φ, hφx, hφU⟩ := exists_dual_eq_one_of_not_mem hxU
          obtain ⟨t, htG, ht⟩ := hT φ (hφU u huU)
          have h1 := hW t htG x hxW
          rw [ht, hφx, one_smul] at h1
          have h2 : u = (x + u) - x := by abel
          rw [h2]
          exact W.sub_mem h1 hxW
      rw [eq_top_iff, ← hBtop, hBdef, Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact hW g hg u huW
    obtain ⟨x0, hx0⟩ : ∃ x, x ∉ U := by
      by_contra h
      push Not at h
      have hUtop : U = ⊤ := eq_top_iff.mpr fun x _ => h x
      have h1 := finrank_span_singleton (K := ZMod 3) hu
      rw [← hUdef, hUtop, finrank_top, hV] at h1
      norm_num at h1
    obtain ⟨φ0, hφ0x, hφ0U⟩ := exists_dual_eq_one_of_not_mem hx0
    obtain ⟨t0, ht0G, ht0⟩ := hT φ0 (hφ0U u huU)
    have ht0T : IsTransvectionWith t0 u φ0 :=
      ⟨hu, dual_ne_zero_of_eq_one hφ0x, hφ0U u huU, ht0⟩
    have hSL := Sec3.det_eq_one_mem_of_irreducible hV G' hirr ht0G ht0T
    by_cases hwU : w ∈ U
    · exact hc 1 G'.one_mem hwU
    · have hv0 : u - w ≠ 0 := fun h => hwU (by
        rw [← sub_eq_zero.mp h]
        exact huU)
      have hwv : w ∉ Submodule.span (ZMod 3) ({u - w} : Set V) := by
        intro h
        obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h
        have h2 : (k + 1) • w = k • u := by
          calc (k + 1) • w = k • w + w := by rw [add_smul, one_smul]
            _ = k • w + k • (u - w) := by rw [hk]
            _ = k • u := by rw [smul_sub]; abel
        by_cases hk1 : k + 1 = 0
        · apply hu
          have hk0 : k ≠ 0 := by
            rintro rfl
            rw [zero_add] at hk1
            exact one_ne_zero hk1
          rw [hk1, zero_smul] at h2
          exact (smul_eq_zero.mp h2.symm).resolve_left hk0
        · apply hwU
          have h3 : w = ((k + 1)⁻¹ * k) • u := by
            rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hk1, one_smul]
          rw [h3]
          exact smul_mem_span_singleton _ u
      obtain ⟨ψ, hψw, hψv⟩ := exists_dual_eq_one_of_not_mem hwv
      have hψ : ψ (u - w) = 0 := hψv _ (Submodule.mem_span_singleton_self _)
      have htT : IsTransvectionWith (LinearEquiv.transvection hψ) (u - w) ψ :=
        ⟨hv0, dual_ne_zero_of_eq_one hψw, hψ, fun x => LinearEquiv.transvection.apply hψ x⟩
      have htG := hSL _ (Sec3.det_eq_one_of_isTransvectionWith htT)
      apply hc _ htG
      rw [LinearEquiv.transvection.apply, hψw, one_smul, add_sub_cancel]
      exact huU
  ·
    set u' := g0 u with hu'def
    have hu'B : u' ∈ B := Submodule.subset_span ⟨g0, hg0, rfl⟩
    have huB : u ∈ B := Submodule.subset_span ⟨1, G'.one_mem, rfl⟩
    set P := Submodule.span (ZMod 3) ({u, u'} : Set V) with hPdef
    have huP : u ∈ P := Submodule.subset_span (Set.mem_insert u _)
    have hu'P : u' ∈ P := Submodule.subset_span (Set.mem_insert_of_mem u rfl)
    have hPB : P ≤ B := by
      rw [hPdef, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact huB
      · exact hu'B
    have hli : LinearIndependent (ZMod 3) ![u, u'] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right hu, rfl⟩
      · exfalso
        apply hg0u
        have h' : t • u' = -(s • u) := eq_neg_of_add_eq_zero_right hst
        have h'' : u' = t⁻¹ • -(s • u) := by
          rw [← h', smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h'', ← neg_smul]
        exact Submodule.smul_mem _ _ (smul_mem_span_singleton _ u)
    have hP2 : finrank (ZMod 3) P = 2 := by
      have h := finrank_span_eq_card hli
      rw [Fintype.card_fin] at h
      have hr : Set.range ![u, u'] = ({u, u'} : Set V) := by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.singleton_union]
      rw [hr] at h
      exact h
    have hBP : B = P := by
      symm
      apply Submodule.eq_of_le_of_finrank_le hPB
      have hlt := Submodule.finrank_lt hBtop
      omega
    have hPinv : ∀ g ∈ G', ∀ x ∈ P, g x ∈ P := by
      rw [← hBP]
      exact hBinv
    obtain ⟨φ, hφu', hφU⟩ := exists_dual_eq_one_of_not_mem hg0u
    have hφu : φ u = 0 := hφU u huU
    obtain ⟨t, htG, ht⟩ := hT φ hφu
    have htT : IsTransvectionWith t u φ := ⟨hu, dual_ne_zero_of_eq_one hφu', hφu, ht⟩
    have hwP : w ∉ P := by
      intro hw
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hw
      by_cases hβ : β = 0
      · rw [hβ, zero_smul, add_zero] at hαβ
        apply hc 1 G'.one_mem
        rw [← hαβ]
        exact smul_mem_span_singleton _ u
      · have hk : (((β⁻¹ * α).val : ℕ) : ZMod 3) = β⁻¹ * α := ZMod.natCast_zmod_val _
        have hpow := htT.pow_apply (β⁻¹ * α).val u'
        rw [hφu', mul_one, hk] at hpow
        have hg : t ^ (β⁻¹ * α).val * g0 ∈ G' := G'.mul_mem (G'.pow_mem htG _) hg0
        have hgu : (t ^ (β⁻¹ * α).val * g0) (β • u) = w := by
          rw [map_smul, LinearEquiv.mul_apply, ← hu'def, hpow, smul_add, smul_smul,
            mul_inv_cancel_left₀ hβ, ← hαβ, add_comm]
        apply hc _ (G'.inv_mem hg)
        have h1 : (t ^ (β⁻¹ * α).val * g0)⁻¹ w = β • u := by
          rw [← hgu]
          exact LinearEquiv.symm_apply_apply _ _
        rw [h1]
        exact smul_mem_span_singleton _ u
    obtain ⟨φ1, hφ1w, hφ1P⟩ := exists_dual_eq_one_of_not_mem hwP
    have hker : LinearMap.ker φ1 = P := by
      symm
      apply Submodule.eq_of_le_of_finrank_le fun y hy => LinearMap.mem_ker.mpr (hφ1P y hy)
      have hne : LinearMap.ker φ1 ≠ ⊤ := by
        intro h
        have hw : w ∈ LinearMap.ker φ1 := by
          rw [h]
          exact Submodule.mem_top
        rw [LinearMap.mem_ker, hφ1w] at hw
        exact one_ne_zero hw
      have hlt := Submodule.finrank_lt hne
      omega
    have hdecomp : ∀ x, x - φ1 x • w ∈ P := by
      intro x
      rw [← hker, LinearMap.mem_ker, map_sub, map_smul, hφ1w, smul_eq_mul, mul_one]
      exact sub_self _
    obtain ⟨τ1, hτ1G, hτ1⟩ := hT φ1 (hφ1P u huP)
    have hτ1T : IsTransvectionWith τ1 u φ1 :=
      ⟨hu, dual_ne_zero_of_eq_one hφ1w, hφ1P u huP, hτ1⟩
    have hτ2T := hτ1T.conj g0
    have hτ2G : g0 * τ1 * g0⁻¹ ∈ G' := G'.mul_mem (G'.mul_mem hg0 hτ1G) (G'.inv_mem hg0)
    set lam := φ1 (g0.symm w) with hlam
    have hlam0 : lam ≠ 0 := by
      intro h0
      apply hwP
      have h1 := hdecomp (g0.symm w)
      rw [← hlam, h0, zero_smul, sub_zero] at h1
      have h2 := hPinv g0 hg0 _ h1
      rwa [LinearEquiv.apply_symm_apply] at h2
    have hexτ : ∀ b ∈ P, ∃ τ ∈ G', (∀ x ∈ P, τ x = x) ∧ τ w = w + b := by
      intro b hb
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hb
      refine ⟨τ1 ^ α.val * (g0 * τ1 * g0⁻¹) ^ (β * lam⁻¹).val,
        G'.mul_mem (G'.pow_mem hτ1G _) (G'.pow_mem hτ2G _), fun x hx => ?_, ?_⟩
      · have h0 : (φ1.comp (g0.symm : V →ₗ[ZMod 3] V)) x = 0 :=
          hφ1P _ (hPinv _ (G'.inv_mem hg0) x hx)
        rw [LinearEquiv.mul_apply, hτ2T.pow_apply, h0, mul_zero, zero_smul, add_zero,
          hτ1T.pow_apply, hφ1P x hx, mul_zero, zero_smul, add_zero]
      · have h0 : (φ1.comp (g0.symm : V →ₗ[ZMod 3] V)) w = lam := rfl
        have hu'0 : φ1 u' = 0 := hφ1P u' hu'P
        rw [LinearEquiv.mul_apply, hτ2T.pow_apply, h0, ZMod.natCast_zmod_val,
          inv_mul_cancel_right₀ hlam0, hτ1T.pow_apply, ZMod.natCast_zmod_val, map_add,
          map_smul, hφ1w, hu'0, smul_eq_mul, mul_zero, add_zero, mul_one, ← hu'def]
        abel
    set μ0 := φ1 (g0 w) with hμ0def
    have hμ0 : μ0 ≠ 0 := by
      intro h0
      apply hwP
      have h1 := hdecomp (g0 w)
      rw [← hμ0def, h0, zero_smul, sub_zero] at h1
      have h2 := hPinv _ (G'.inv_mem hg0) _ h1
      rwa [show (g0⁻¹ : V ≃ₗ[ZMod 3] V) (g0 w) = w from g0.symm_apply_apply w] at h2
    set p0 := g0 w - μ0 • w with hp0def
    have hp0 : p0 ∈ P := hdecomp (g0 w)
    obtain ⟨τ, hτG, hτP, hτw⟩ := hexτ (-(μ0⁻¹ • p0)) (P.neg_mem (P.smul_mem _ hp0))
    have hτg0w : (τ * g0) w = μ0 • w := by
      have hg0w : g0 w = p0 + μ0 • w := by rw [hp0def, sub_add_cancel]
      rw [LinearEquiv.mul_apply, hg0w, map_add, map_smul, hτP p0 hp0, hτw, smul_add, smul_neg,
        smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      abel
    have h1 := hH (τ * g0) (G'.mul_mem hτG hg0)
      (by rw [hτg0w]; exact smul_mem_span_singleton _ w)
    rw [LinearEquiv.mul_apply, ← hu'def, hτP u' hu'P] at h1
    exact hg0u h1

section Coords

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] def ofCoordLin (f : Multiplicative V ≃* A) (g : V ≃ₗ[ZMod 3] V) : MulAut A :=
  (f.symm.trans (AddEquiv.toMultiplicative g.toAddEquiv)).trans f

theorem ofCoordLin_apply (f : Multiplicative V ≃* A) (g : V ≃ₗ[ZMod 3] V) (a : A) :
    ofCoordLin f g a = f (Multiplicative.ofAdd (g (Multiplicative.toAdd (f.symm a)))) :=
  rfl

theorem coordHom_ofCoordLin (f : Multiplicative V ≃* A) (g : V ≃ₗ[ZMod 3] V) :
    Sec12.coordHom f (ofCoordLin f g) = g := by
  ext v
  simp [Sec12.coordHom_apply, ofCoordLin_apply]

omit [Module (ZMod 3) V] in
theorem coordVec_injective (f : Multiplicative V ≃* A) : Function.Injective (Sec12.coordVec f) :=
  fun _ _ h => f.symm.injective (Multiplicative.toAdd.injective h)

omit [Module (ZMod 3) V] in
theorem coordVec_pow (f : Multiplicative V ≃* A) (x : A) (n : ℕ) :
    Sec12.coordVec f (x ^ n) = n • Sec12.coordVec f x := by
  simp [Sec12.coordVec, map_pow, toAdd_pow]

theorem coordVec_mem_span_iff (f : Multiplicative V ≃* A) {x y : A} :
    Sec12.coordVec f x ∈ Submodule.span (ZMod 3) ({Sec12.coordVec f y} : Set V) ↔
      x ∈ Subgroup.zpowers y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨(k.val : ℤ), ?_⟩
    rw [zpow_natCast]
    apply coordVec_injective f
    rw [coordVec_pow, ← hk, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Submodule.mem_span_singleton]
    refine ⟨(k : ZMod 3), ?_⟩
    rw [Sec12.coordVec, Sec12.coordVec, map_zpow, toAdd_zpow, Int.cast_smul_eq_zsmul]

theorem ofCoordLin_mem_transvectionGroup (f : Multiplicative V ≃* A) {d : A}
    {φ : Dual (ZMod 3) V} (hφ : φ (Sec12.coordVec f d) = 0) :
    ofCoordLin f (LinearEquiv.transvection hφ) ∈ Sec12.transvectionGroup A d := by
  refine ⟨?_, fun a => ?_⟩
  · show f (Multiplicative.ofAdd (LinearEquiv.transvection hφ (Sec12.coordVec f d))) = d
    rw [LinearEquiv.transvection.apply, hφ, zero_smul, add_zero, Sec12.coordVec, ofAdd_toAdd,
      MulEquiv.apply_symm_apply]
  · have key : ∀ k : ZMod 3,
        f (Multiplicative.ofAdd (k • Sec12.coordVec f d)) ∈ Subgroup.zpowers d := by
      intro k
      have h1 : k • Sec12.coordVec f d = k.val • Sec12.coordVec f d := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
      rw [h1, ofAdd_nsmul, map_pow, Sec12.coordVec, ofAdd_toAdd, MulEquiv.apply_symm_apply]
      exact Subgroup.npow_mem_zpowers d _
    have h2 : ofCoordLin f (LinearEquiv.transvection hφ) a =
        f (Multiplicative.ofAdd (φ (Multiplicative.toAdd (f.symm a)) • Sec12.coordVec f d)) *
          a := by
      rw [ofCoordLin_apply, LinearEquiv.transvection.apply, add_comm, ofAdd_add, map_mul,
        ofAdd_toAdd, MulEquiv.apply_symm_apply]
    rw [h2, mul_inv_cancel_right]
    exact key _

theorem mem_zpowers_of_transvectionGroup_le [Finite A] (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {S : Subgroup (MulAut A)} {c d : A} (hd : d ≠ 1)
    (hT : Sec12.transvectionGroup A d ≤ S) (hc : ∀ σ ∈ S, σ c ∉ Subgroup.zpowers d)
    (hH : ∀ σ ∈ S, σ c ∈ Subgroup.zpowers c → σ d ∈ Subgroup.zpowers d) :
    ∀ σ ∈ S, σ d ∈ Subgroup.zpowers d := by
  obtain ⟨V, _, _, hV, ⟨f⟩⟩ := Sec12.exists_coords_module hA (n := 3) (by rw [h27]; norm_num)
  have : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_eq_succ hV
  have key := mem_span_of_transvections hV (G' := S.map (Sec12.coordHom f))
    (u := Sec12.coordVec f d) (w := Sec12.coordVec f c) (Sec12.coordVec_ne_zero f hd)
    (fun φ hφ => ⟨LinearEquiv.transvection hφ, ⟨ofCoordLin f (LinearEquiv.transvection hφ),
      hT (ofCoordLin_mem_transvectionGroup f hφ), coordHom_ofCoordLin f _⟩,
      fun x => LinearEquiv.transvection.apply hφ x⟩)
    (by
      rintro _ ⟨σ, hσ, rfl⟩
      rw [coordHom_coordVec, coordVec_mem_span_iff]
      exact hc σ hσ)
    (by
      rintro _ ⟨σ, hσ, rfl⟩ h
      rw [coordHom_coordVec, coordVec_mem_span_iff] at h ⊢
      exact hH σ hσ h)
  intro σ hσ
  have h := key _ ⟨σ, hσ, rfl⟩
  rwa [coordHom_coordVec, coordVec_mem_span_iff] at h

end Coords

end CFSG.RankThree.PartTwo.KFacts
