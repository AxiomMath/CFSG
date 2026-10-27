module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAB
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAC
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAE

public section

namespace CFSG.StandardType.QTwo

open CFSG.LinearAlgebra
open CFSG.LinearAlgebra.SteinbergBQ
open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

theorem qtwoDB41_blocks {m : ℕ} (hm : 6 ≤ m) {c : Fin m}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (τ : Multiplicative (DVec m) →* (V ≃ₗ[ZMod 2] V))
    (hτO : τ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hτker : ∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ n ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ v : DVec m, n * τ (Multiplicative.ofAdd v) * n⁻¹ = τ (Multiplicative.ofAdd (w v)))
    (hdim : Module.finrank (ZMod 2) V = 2 * (m - 1) ∨
      (Module.finrank (ZMod 2) V = 2 * m ∧
        ¬ (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m))) :
    ∃ U : Fin (m - 1) → Submodule (ZMod 2)
        ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (fixedSub τ.range)),
      Module.finrank (ZMod 2) (fixedSub τ.range) + 2 * (m - 1) = Module.finrank (ZMod 2) V ∧
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem
        (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
          (fixedSub τ.range))) U ∧
      (∀ v : DVec m, (∀ i, i ≠ c → v i ≠ 0) →
        ∀ x : V, τ (Multiplicative.ofAdd v) x = x → x ∈ fixedSub τ.range) := by
  classical
  have hodd : Odd (Nat.card τ.range) := qtwoDB41_odd_card_range τ
  have hEcard : Nat.card τ.range = 3 ^ (m - 1) := by
    have hker : Nat.card τ.ker = 3 := by
      have hbij : Function.Bijective (fun x : ↥τ.ker => (x.1.toAdd) c) := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          funext i
          by_cases hic : i = c
          · subst hic; exact hxy
          · have hx0 : (x.1.toAdd) i = 0 :=
              (hτker x.1.toAdd).1 (MonoidHom.mem_ker.mpr x.2) i hic
            have hy0 : (y.1.toAdd) i = 0 :=
              (hτker y.1.toAdd).1 (MonoidHom.mem_ker.mpr y.2) i hic
            rw [hx0, hy0]
        · intro a
          refine ⟨⟨Multiplicative.ofAdd (a • Pi.single c 1), ?_⟩, ?_⟩
          · rw [MonoidHom.mem_ker]
            exact (hτker (a • Pi.single c 1)).2 (fun i hi => by
              rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero])
          · change (a • Pi.single c 1) c = a
            rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
      simpa [Nat.card_zmod] using h1
    have hG : Nat.card (Multiplicative (DVec m)) = 3 ^ m := by
      have : Nat.card (Multiplicative (DVec m)) = Nat.card (DVec m) := rfl
      rw [this]
      simp [DVec, Nat.card_fun, Nat.card_zmod]
    have hp : 3 ^ m = 3 * 3 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [pow_succ']
    have h2 := Subgroup.card_ker_mul_card_range τ
    rw [hker, hG, hp] at h2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hnd : ∀ x ∈ fixedSub τ.range,
      (∀ y ∈ fixedSub τ.range, QuadraticMap.polar Q x y = 0) → x = 0 :=
    qtwoDB41_fixedSub_nondegenerate hQ hτO hodd
  set V₀ : Submodule (ZMod 2) V := fixedSub τ.range with hV₀
  set W : Submodule (ZMod 2) V :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) V₀ with hWdef
  have hdisj : Disjoint V₀ W := by
    rw [Submodule.disjoint_def]
    intro x hx hxW
    exact hnd x (hV₀ ▸ hx) fun y hy => by
      have h0 : (QuadraticMap.polarBilin Q) y x = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp (hWdef ▸ hxW)) y (hV₀ ▸ hy)
      calc QuadraticMap.polar Q x y = QuadraticMap.polar Q y x := QuadraticMap.polar_comm Q x y
        _ = (QuadraticMap.polarBilin Q) y x :=
              (QuadraticMap.polarBilin_apply_apply Q y x).symm
        _ = 0 := h0
  have hcompl : IsCompl V₀ W := by
    rw [hWdef]
    exact (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
      (qtwoDB41_polarBilin_isAlt Q).isRefl).2 (by
      rwa [hWdef] at hdisj)
  have hWstable : ∀ g ∈ τ.range, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
    intro y hy
    show QuadraticMap.polar Q y (g w) = 0
    have h0 : QuadraticMap.polar Q y w = 0 := hw y hy
    have hgy : g⁻¹ y = y := (mem_fixedSub.mp (hV₀ ▸ hy)) g⁻¹ (τ.range.inv_mem hg)
    have hgy' : g (g⁻¹ y) = y := by simp
    calc QuadraticMap.polar Q y (g w) = QuadraticMap.polar Q (g (g⁻¹ y)) (g w) := by
          rw [hgy']
      _ = QuadraticMap.polar Q (g⁻¹ y) w :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hτO hg) (g⁻¹ y) w
      _ = QuadraticMap.polar Q y w := by rw [hgy]
      _ = 0 := h0
  have hφinj : Function.Injective (qtwoDB41_restrictHom τ.range hWstable) := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ V₀ ⊔ W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp hv
    have hgu : g.1 u = u := (mem_fixedSub.mp (hV₀ ▸ hu)) g.1 g.2
    have hhu : h.1 u = u := (mem_fixedSub.mp (hV₀ ▸ hu)) h.1 h.2
    have hgw : g.1 w = h.1 w := by
      have h1 := congrArg (fun e : ↥W ≃ₗ[ZMod 2] ↥W => (e ⟨w, hw⟩ : V)) hgh
      rwa [qtwoDB41_restrictHom_apply, qtwoDB41_restrictHom_apply] at h1
    rw [← huv, map_add, map_add, hgu, hhu, hgw]
  have hBcard : Nat.card (qtwoDB41_restrictHom τ.range hWstable).range = 3 ^ (m - 1) := by
    have hbij : Function.Bijective (MonoidHom.rangeRestrict
        (qtwoDB41_restrictHom τ.range hWstable)) :=
      ⟨fun g h hgh => hφinj (Subtype.ext_iff.mp hgh), MonoidHom.rangeRestrict_surjective _⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm.trans hEcard
  have hBiso : IsElementaryAbelian 3 (qtwoDB41_restrictHom τ.range hWstable).range :=
    CFSG.IsElementaryAbelian.of_mulEquiv (MonoidHom.ofInjective hφinj)
      (qtwoDB41_isElementaryAbelian_range τ)
  have hBO : (qtwoDB41_restrictHom τ.range hWstable).range ≤
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W) := by
    rintro b ⟨g, rfl⟩
    exact qtwoDB41_restrictEquiv_mem_orthogonalGroup (hWstable g g.2) (hτO g.2)
  have hBfix : fixedSub (qtwoDB41_restrictHom τ.range hWstable).range = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [mem_fixedSub] at hw
    apply Subtype.ext
    apply hnd w.1
    · intro g hg
      have h1 := hw (qtwoDB41_restrictHom τ.range hWstable ⟨g, hg⟩)
        (MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩)
      have h2 := congrArg (fun z : ↥W => (z : V)) h1
      rwa [qtwoDB41_restrictHom_apply] at h2
    · intro y hy
      have h0 : (QuadraticMap.polarBilin Q) y w.1 = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) y (hV₀ ▸ hy)
      calc QuadraticMap.polar Q w.1 y = QuadraticMap.polar Q y w.1 :=
            QuadraticMap.polar_comm Q w.1 y
        _ = (QuadraticMap.polarBilin Q) y w.1 :=
              (QuadraticMap.polarBilin_apply_apply Q y w.1).symm
        _ = 0 := h0
  have hWnd : (QuadraticMap.polarBilin (Q.restrict W)).Nondegenerate := by
    have hrc : Q.restrict W = Q.comp W.subtype := rfl
    rw [hrc, CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarBilin_comp_subtype_cent]
    have horthW : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W = V₀ := by
      rw [hWdef,
        LinearMap.BilinForm.orthogonal_orthogonal hQ (qtwoDB41_polarBilin_isAlt Q).isRefl]
    exact (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (qtwoDB41_polarBilin_isAlt Q).isRefl).mpr (by rw [horthW]; exact hcompl.symm)
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank (ZMod 2) ↥W = 2 * k := by
    obtain ⟨k, hk⟩ := qtwoDB41_even_finrank_of_nondegenerate
      (qtwoDB41_polarBilin_isAlt (Q.restrict W)) hWnd
    exact ⟨k, by rw [hk, two_mul]⟩
  letI : IsElementaryAbelian 3 (qtwoDB41_restrictHom τ.range hWstable).range := hBiso
  obtain ⟨I, d, hI, ⟨hindep, hsup, horth⟩, hblocks, hsum, hinf, hrI, hIm, hI3, hm0, hr0,
      hplanes, hnorm, hAll, hmr⟩ :=
    binary_quadratic_three_action_canonical_kernel_blocks (Q.restrict W) hWnd hk
      (qtwoDB41_restrictHom τ.range hWstable).range hBO hBcard hBfix
  have hfinV : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) V₀ + Module.finrank (ZMod 2) ↥W :=
    (Submodule.finrank_add_eq_of_isCompl hcompl).symm
  have hWV : Module.finrank (ZMod 2) ↥W ≤ Module.finrank (ZMod 2) V := by
    rw [hfinV]; exact Nat.le_add_left _ _
  have hk_eq : k = m - 1 := by
    rcases hdim with hdim1 | ⟨hdim2, hnot⟩
    · have h1 : 2 * k ≤ 2 * (m - 1) := by
        calc 2 * k = Module.finrank (ZMod 2) ↥W := hk.symm
          _ ≤ Module.finrank (ZMod 2) V := hWV
          _ = 2 * (m - 1) := hdim1
      omega
    · by_contra hne
      have hkm : k = m := by
        have h1 : 2 * k ≤ 2 * m := by
          calc 2 * k = Module.finrank (ZMod 2) ↥W := hk.symm
            _ ≤ Module.finrank (ZMod 2) V := hWV
            _ = 2 * m := hdim2
        omega
      have hV₀fin : Module.finrank (ZMod 2) V₀ = 0 := by omega
      have hV₀bot : V₀ = ⊥ := Submodule.finrank_eq_zero.mp hV₀fin
      haveI : IsElementaryAbelian 3 τ.range := qtwoDB41_isElementaryAbelian_range τ
      have htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m :=
        qtwoDB41_fixedFree_type hQ τ.range hτO hEcard (hV₀ ▸ hV₀bot) hdim2
      exact hnot htype
  obtain ⟨hIcard, hd1, -, -⟩ := hmr hk_eq
  have hIcard' : Fintype.card ↥I = m - 1 := by rw [Fintype.card_coe]; exact hIcard
  let e : Fin (m - 1) ≃ ↥I := (Fintype.equivFinOfCardEq hIcard').symm
  have hPlane : ∀ N ∈ I, ∀ (P : Fin (d N) → Submodule (ZMod 2) ↥W) (i : Fin (d N)),
      (⨆ j, P j = fixedSub N) → P i = fixedSub N := by
    intro N hN P i hsup
    haveI : Subsingleton (Fin (d N)) := by rw [hd1 N hN]; infer_instance
    refine le_antisymm ?_ ?_
    · rw [← hsup]; exact le_iSup P i
    · rw [← hsup]; exact iSup_le fun j => by rw [Subsingleton.elim j i]
  refine ⟨fun i => fixedSub (e i : Subgroup (↥W ≃ₗ[ZMod 2] ↥W)), ?_, ?_, ?_⟩
  · have hWdim : Module.finrank (ZMod 2) ↥W = 2 * (m - 1) := by rw [hk, hk_eq]
    omega
  · refine { finrank_eq := ?_, nondeg := ?_, not_isPlusType := ?_, perp := ?_ }
    · intro i
      have := (hblocks (e i) (e i).2).2.1
      rw [hd1 (e i) (e i).2] at this
      simpa using this
    · intro i
      refine ⟨?_, ?_⟩
      · intro x hx
        apply Subtype.ext
        exact (hblocks (e i) (e i).2).1 x.1 x.2 fun y hy => by
          rw [← QuadraticMap.polarBilin_apply_apply]
          exact hx ⟨y, hy⟩
      · intro y hy
        apply Subtype.ext
        exact (hblocks (e i) (e i).2).1 y.1 y.2 fun x hx => by
          have h := hy ⟨x, hx⟩
          rw [QuadraticMap.polar_comm]
          exact h
    · intro i
      obtain ⟨P, hP⟩ := hplanes (e i) (e i).2
      have hpos : 0 < d (e i) := Nat.lt_of_lt_of_le Nat.zero_lt_one
        (hblocks (e i) (e i).2).2.2.1
      have hPeq := hPlane (e i) (e i).2 P ⟨0, hpos⟩ hP.2.2.2
      rw [← hPeq]
      exact qtwoDB41_not_isPlusType_of_aniso (hP.1 ⟨0, hpos⟩).2.1
        (hP.1 ⟨0, hpos⟩).2.2.1
    · intro i j hij
      have hne : (e i : Subgroup (↥W ≃ₗ[ZMod 2] ↥W)) ≠ (e j : Subgroup _) :=
        fun h => hij (e.injective (Subtype.ext h))
      exact horth (e i) (e i).2 (e j) (e j).2 hne
  ·
    let σ : Multiplicative (DVec m) →* (↥W ≃ₗ[ZMod 2] ↥W) :=
      (qtwoDB41_restrictHom τ.range hWstable).comp τ.rangeRestrict
    have hσ : ∀ (u : Multiplicative (DVec m)) (y : ↥W), ((σ u y : ↥W) : V) = τ u y :=
      fun u y => qtwoDB41_restrictHom_apply τ.range hWstable (τ.rangeRestrict u) y
    have hσO : σ.range ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W) := by
      rintro _ ⟨u, rfl⟩
      exact hBO ⟨τ.rangeRestrict u, rfl⟩
    have hσker : ∀ v : DVec m, σ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0 := by
      intro v
      rw [← hτker v]
      constructor
      · intro h
        have h1 : τ.rangeRestrict (Multiplicative.ofAdd v) = 1 :=
          hφinj (h.trans (map_one _).symm)
        exact congrArg Subtype.val h1
      · intro h
        have h1 : τ.rangeRestrict (Multiplicative.ofAdd v) = 1 := Subtype.ext h
        show qtwoDB41_restrictHom τ.range hWstable (τ.rangeRestrict (Multiplicative.ofAdd v)) = 1
        rw [h1, map_one]
    have hσfix : fixedSub σ.range = ⊥ := by
      have hσrange : σ.range = (qtwoDB41_restrictHom τ.range hWstable).range := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ τ.rangeRestrict_surjective,
          ← MonoidHom.range_eq_map]
      rw [hσrange]
      exact hBfix
    have hσW : ∀ w ∈ dEvenStab m (Pi.single c 1),
        ∃ n ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W),
          ∀ v : DVec m, n * σ (Multiplicative.ofAdd v) * n⁻¹ = σ (Multiplicative.ofAdd (w v)) := by
      intro w hw
      obtain ⟨n, hnO, hn⟩ := hW w hw
      have hnn : ∀ x : V, n (n⁻¹ x) = x := fun x => by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq]
      have hn' : ∀ (v : DVec m) (x : V),
          n (τ (Multiplicative.ofAdd v) x) = τ (Multiplicative.ofAdd (w v)) (n x) := by
        intro v x
        have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (n x)) (hn v)
        simp only [LinearEquiv.mul_apply] at h
        rwa [show (n⁻¹ : V ≃ₗ[ZMod 2] V) (n x) = x from by
          rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id_eq]] at h
      have hnV₀ : ∀ x ∈ V₀, n⁻¹ x ∈ V₀ := by
        intro x hx
        rw [hV₀, mem_fixedSub] at hx ⊢
        rintro _ ⟨u, rfl⟩
        obtain ⟨v, rfl⟩ := (Multiplicative.ofAdd : DVec m ≃ Multiplicative (DVec m)).surjective u
        apply n.injective
        rw [hn' v (n⁻¹ x), hnn]
        exact hx _ ⟨Multiplicative.ofAdd (w v), rfl⟩
      have hnW : ∀ y ∈ W, n y ∈ W := by
        intro y hy
        rw [hWdef, LinearMap.BilinForm.mem_orthogonal_iff] at hy ⊢
        intro x hx
        have h0 : (QuadraticMap.polarBilin Q) (n⁻¹ x) y = 0 := hy _ (hnV₀ x hx)
        rw [QuadraticMap.polarBilin_apply_apply] at h0 ⊢
        rw [← hnn x, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hnO]
        exact h0
      refine ⟨restrictEquiv hnW, qtwoDB41_restrictEquiv_mem_orthogonalGroup hnW hnO,
        fun v => ?_⟩
      rw [mul_inv_eq_iff_eq_mul]
      refine LinearEquiv.ext fun y => Subtype.ext ?_
      show ((restrictEquiv hnW (σ (Multiplicative.ofAdd v) y) : ↥W) : V) =
        ((σ (Multiplicative.ofAdd (w v)) (restrictEquiv hnW y) : ↥W) : V)
      rw [restrictEquiv_apply, hσ, hσ, restrictEquiv_apply]
      exact hn' v y
    have hdimW : Module.finrank (ZMod 2) ↥W = 2 * (m - 1) := by rw [hk, hk_eq]
    have hgen := qtwoDB41_generic_fixed_W hm hWnd hdimW σ hσO hσker hσfix hσW
    intro v hv x hx
    have hxs : x ∈ V₀ ⊔ W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x₀, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.mp hxs
    have hτx₀ : τ (Multiplicative.ofAdd v) x₀ = x₀ := by
      have hx₀' : x₀ ∈ fixedSub τ.range := hV₀ ▸ hx₀
      exact (mem_fixedSub.mp hx₀') _
        (show τ (Multiplicative.ofAdd v) ∈ τ.range from ⟨Multiplicative.ofAdd v, rfl⟩)
    have hτy : τ (Multiplicative.ofAdd v) y = y := by
      rw [map_add, hτx₀] at hx
      exact add_left_cancel hx
    have hy0 : (⟨y, hy⟩ : ↥W) = 0 :=
      hgen v hv ⟨y, hy⟩ (Subtype.ext (by rw [hσ]; exact hτy))
    have hy0' : y = 0 := congrArg Subtype.val hy0
    rw [hy0', add_zero]
    exact hx₀

end CFSG.StandardType.QTwo

end
