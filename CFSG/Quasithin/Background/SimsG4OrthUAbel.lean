module

public import CFSG.Quasithin.Background.SimsG4OrthUPrim
public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.Quasithin.SimsG4

open scoped IsMulCommutative

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

section Decomp

theorem isImprimitiveOnV_or_injective [FiniteDimensional K W] (G₀ : Subgroup (W ≃ₗ[K] W))
    (E : Subalgebra K (Module.End K W)) [IsMulCommutative E]
    (hred : ∀ a ∈ E, IsNilpotent a → a = 0)
    (hEG : ∀ g ∈ G₀, ∀ a ∈ E,
      (g : Module.End K W) ∘ₗ a ∘ₗ (g.symm : Module.End K W) ∈ E) :
    IsImprimitiveOnV G₀ ∨ ∀ a ∈ E, a ≠ 0 → Function.Injective a := by
  classical
  have : IsArtinianRing E := IsArtinianRing.of_finite K E
  have : IsReduced E := ⟨fun x hx => Subtype.ext (hred x.1 x.2 (hx.map E.val))⟩
  have : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  set φ := IsArtinianRing.equivPi E with hφ
  have hmk : ∀ (y : E) (m : MaximalSpectrum E), φ y m = 0 ↔ y ∈ m.asIdeal := fun y m => by
    rw [hφ, IsArtinianRing.equivPi_apply]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hzero : ∀ y : E, (∀ m : MaximalSpectrum E, y ∈ m.asIdeal) → y = 0 := fun y hy =>
    φ.injective (funext fun m => by rw [map_zero, Pi.zero_apply, hmk]; exact hy m)
  rcases subsingleton_or_nontrivial (MaximalSpectrum E) with hsub | hnt
  ·
    right
    intro a ha ha0
    have hne : (⟨a, ha⟩ : E) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    obtain ⟨m, hm⟩ : ∃ m : MaximalSpectrum E, (⟨a, ha⟩ : E) ∉ m.asIdeal := by
      by_contra hcon
      push Not at hcon
      exact hne (hzero _ hcon)
    have hu : IsUnit (⟨a, ha⟩ : E) := by
      rw [← MulEquiv.isUnit_map φ, Pi.isUnit_iff]
      intro m'
      rw [Subsingleton.elim m' m]
      have := m.isMaximal
      obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (I := m.asIdeal) (a := φ ⟨a, ha⟩ m)
        (fun h => hm ((hmk _ _).mp h))
      exact IsUnit.of_mul_eq_one _ hb
    obtain ⟨b, hb⟩ := hu.exists_left_inv
    intro x y hxy
    have h1 : ((b * ⟨a, ha⟩ : E) : Module.End K W) x = ((b * ⟨a, ha⟩ : E) : Module.End K W) y := by
      change (b : Module.End K W) (a x) = (b : Module.End K W) (a y)
      rw [hxy]
    rwa [hb] at h1
  ·
    left
    let e : MaximalSpectrum E → E := fun m => φ.symm (Pi.single m 1)
    have hφe : ∀ m, φ (e m) = Pi.single m 1 := fun m => by
      simp only [e, AlgEquiv.apply_symm_apply]
    have he_mem : ∀ m m', m ≠ m' → e m ∈ m'.asIdeal := fun m m' hne =>
      (hmk _ _).mp (by rw [hφe]; exact Pi.single_eq_of_ne (Ne.symm hne) _)
    have he_one : ∀ m, 1 - e m ∈ m.asIdeal := fun m =>
      (hmk _ _).mp (by
        rw [map_sub, map_one, Pi.sub_apply, hφe, Pi.single_eq_same, Pi.one_apply, sub_self])
    have he_ann : ∀ m, ∀ y ∈ m.asIdeal, y * e m = 0 := fun m y hy => hzero _ fun m' => by
      by_cases h : m = m'
      · subst h
        exact Ideal.mul_mem_right _ _ hy
      · exact Ideal.mul_mem_left _ _ (he_mem m m' h)
    have he_ne : ∀ m, e m ≠ 0 := fun m h => by
      have := he_one m
      rw [h, sub_zero] at this
      exact m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have he_sum : ∑ m, e m = 1 := φ.injective (by
      rw [map_sum, map_one]
      funext m'
      rw [Finset.sum_apply, Pi.one_apply]
      simp only [hφe]
      exact Fintype.sum_pi_single m' (fun x => (1 : E ⧸ x.asIdeal)))
    let A : MaximalSpectrum E → Submodule K W := fun m =>
      LinearMap.range ((e m : E) : Module.End K W)
    have hA : ∀ m w, w ∈ A m ↔ ∀ y ∈ m.asIdeal, (y : Module.End K W) w = 0 := by
      intro m w
      constructor
      · rintro ⟨v, rfl⟩ y hy
        have := congrArg (fun z : E => (z : Module.End K W) v) (he_ann m y hy)
        simpa using this
      · intro hw
        have h1 := hw _ (he_one m)
        refine ⟨w, ?_⟩
        simp only [Subalgebra.coe_sub, Subalgebra.coe_one, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero] at h1
        exact h1.symm
    have hA0 : ∀ m, A m ≠ ⊥ := by
      intro m h
      apply he_ne m
      apply Subtype.ext
      exact LinearMap.range_eq_bot.mp h
    have hind : iSupIndep A := by
      intro i
      rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have hker : (⨆ (j) (_ : j ≠ i), A j) ≤ LinearMap.ker ((e i : E) : Module.End K W) := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨v, rfl⟩
        rw [LinearMap.mem_ker]
        have := congrArg (fun z : E => (z : Module.End K W) v)
          (he_ann j (e i) (he_mem i j (Ne.symm hj)))
        simpa using this
      have h0 : ((e i : E) : Module.End K W) x = 0 := hker hx2
      have h1 := (hA i x).mp hx1 _ (he_one i)
      simp only [Subalgebra.coe_sub, Subalgebra.coe_one, LinearMap.sub_apply,
        Module.End.one_apply, h0, sub_zero] at h1
      exact h1
    have hsup : (⨆ m, A m) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      have hx : ∑ m, ((e m : E) : Module.End K W) x = x := by
        have := congrArg (fun z : E => (z : Module.End K W) x) he_sum
        simpa [AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply] using this
      rw [← hx]
      exact Submodule.sum_mem _ fun m _ =>
        Submodule.mem_iSup_of_mem m (LinearMap.mem_range_self _ x)
    have hperm : ∀ g ∈ G₀, ∀ m, ∃ m', (A m).map (g : W →ₗ[K] W) = A m' := by
      intro g hg m
      let ψ : E →ₐ[K] E := ((g.symm.conjAlgEquiv K).toAlgHom.comp E.val).codRestrict E
        (fun y => hEG g⁻¹ (G₀.inv_mem hg) y.1 y.2)
      have hψ : ∀ y : E, ((ψ y : E) : Module.End K W) =
          (g.symm : Module.End K W) ∘ₗ (y : Module.End K W) ∘ₗ (g : Module.End K W) :=
        fun y => rfl
      have hψsurj : Function.Surjective ψ := by
        intro y
        refine ⟨⟨(g : Module.End K W) ∘ₗ (y : Module.End K W) ∘ₗ (g.symm : Module.End K W),
          hEG g hg y.1 y.2⟩, ?_⟩
        apply Subtype.ext
        rw [hψ]
        ext x
        simp
      have := m.isMaximal
      refine ⟨⟨m.asIdeal.comap ψ, Ideal.comap_isMaximal_of_surjective ψ hψsurj⟩, ?_⟩
      ext w
      rw [Submodule.mem_map_equiv, hA, hA]
      constructor
      · intro hw z hz
        have h1 := hw (ψ z) hz
        rw [hψ] at h1
        simpa using h1
      · intro hw y hy
        let z : E := ⟨(g : Module.End K W) ∘ₗ (y : Module.End K W) ∘ₗ (g.symm : Module.End K W),
          hEG g hg y.1 y.2⟩
        have hz : ψ z = y := Subtype.ext (by rw [hψ]; ext x; simp [z])
        have h1 := hw z (by show ψ z ∈ m.asIdeal; rw [hz]; exact hy)
        simpa [z] using h1
    exact isImprimitiveOnV_of_family Finite.one_lt_card A hA0 hind hsup hperm

end Decomp

section Abel

theorem coe_pow_end (c : W ≃ₗ[K] W) (n : ℕ) :
    ((c ^ n : W ≃ₗ[K] W) : Module.End K W) = (c : Module.End K W) ^ n :=
  map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := W)) c n

theorem isSemisimple_of_natCast_orderOf_ne_zero {c : W ≃ₗ[K] W}
    (hc : ((orderOf c : ℕ) : K) ≠ 0) :
    Module.End.IsSemisimple (c : Module.End K W) := by
  have hpow : (c : Module.End K W) ^ orderOf c = 1 := by
    rw [← coe_pow_end, pow_orderOf_eq_one]
    rfl
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (1 : K) hc one_ne_zero).squarefree ?_
  simp [hpow]

theorem isImprimitiveOnV_or_injective_of_commute [FiniteDimensional K W] [PerfectField K]
    (G C : Subgroup (W ≃ₗ[K] W))
    (hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hCss : ∀ c ∈ C, Module.End.IsSemisimple (c : Module.End K W))
    (hCG : ∀ g ∈ G, ∀ c ∈ C, g * c * g⁻¹ ∈ C) :
    IsImprimitiveOnV G ∨ ∀ a ∈ Algebra.adjoin K
      ((fun c : W ≃ₗ[K] W => (c : Module.End K W)) '' (C : Set (W ≃ₗ[K] W))),
        a ≠ 0 → Function.Injective a := by
  classical
  set S : Set (Module.End K W) :=
    (fun c : W ≃ₗ[K] W => (c : Module.End K W)) '' (C : Set (W ≃ₗ[K] W))
  set E : Subalgebra K (Module.End K W) := Algebra.adjoin K S with hE
  have hScomm : S.Pairwise Commute := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    show (a : Module.End K W) * b = b * a
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hCcomm a ha b hb]
  have hEinst : IsMulCommutative E := Algebra.isMulCommutative_adjoin K hScomm
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hEss : ∀ a ∈ E, a.IsSemisimple := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact hCss c hc
    | algebraMap r =>
      exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (Polynomial.irreducible_X_sub_C r).squarefree (by simp)
    | add x y hx hy hxs hys =>
      exact Module.End.IsSemisimple.add_of_commute (hEcomm x hx y hy) hxs hys
    | mul x y hx hy hxs hys =>
      exact Module.End.IsSemisimple.mul_of_commute (hEcomm x hx y hy) hxs hys
  have hred : ∀ a ∈ E, IsNilpotent a → a = 0 := fun a ha hn =>
    Module.End.eq_zero_of_isNilpotent_isSemisimple hn (hEss a ha)
  have hEG : ∀ g ∈ G, ∀ a ∈ E,
      (g : Module.End K W) ∘ₗ a ∘ₗ (g.symm : Module.End K W) ∈ E := by
    intro g hg a ha
    have hle : E.map (g.conjAlgEquiv K).toAlgHom ≤ E := by
      rw [hE, AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨g * c * g⁻¹, hCG g hg c hc, rfl⟩
    exact hle (Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩)
  exact @isImprimitiveOnV_or_injective K _ W _ _ _ G E hEinst hred hEG

variable [CharP K 2]

theorem isSemisimple_of_odd_orderOf {c : W ≃ₗ[K] W} (hc : Odd (orderOf c)) :
    Module.End.IsSemisimple (c : Module.End K W) := by
  refine isSemisimple_of_natCast_orderOf_ne_zero ?_
  rw [Ne, CharP.cast_eq_zero_iff K 2]
  exact fun h => (Nat.not_even_iff_odd.mpr hc) (even_iff_two_dvd.mpr h)

variable [PerfectField K]

theorem false_of_abelian_odd_normal (hdim : 2 < Module.finrank K W)
    {G : Subgroup (W ≃ₗ[K] W)} (hprim : ¬ IsImprimitiveOnV G) {d : W ≃ₗ[K] W} (hd : d ∈ G)
    (hdt : IsTransv d) {C : Subgroup (W ≃ₗ[K] W)} (hC : C ≠ ⊥)
    (hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hCodd : ∀ c ∈ C, Odd (orderOf c))
    (hCG : ∀ g ∈ G, ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (hCsc : ∀ c ∈ C, ∀ a : K, (∀ x, c x = a • x) → c = 1) : False := by
  classical
  have hfd : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  set E : Subalgebra K (Module.End K W) := Algebra.adjoin K
    ((fun c : W ≃ₗ[K] W => (c : Module.End K W)) '' (C : Set (W ≃ₗ[K] W))) with hE
  have hCss : ∀ c ∈ C, Module.End.IsSemisimple (c : Module.End K W) :=
    fun c hc => isSemisimple_of_odd_orderOf (hCodd c hc)
  rcases @isImprimitiveOnV_or_injective_of_commute K _ W _ _ hfd _ G C hCcomm hCss hCG
    with himp | hinj
  · exact hprim himp
  obtain ⟨⟨c, hcC⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hC
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcE : (c : Module.End K W) ∈ E := Algebra.subset_adjoin ⟨c, hcC, rfl⟩
  by_cases hdc : d * c = c * d
  ·
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hdt.1
    obtain ⟨y, hy⟩ := v.2
    have hcv : (c : Module.End K W) v ∈
        LinearMap.range ((d : Module.End K W) - LinearMap.id) := by
      refine ⟨c y, ?_⟩
      rw [← hy]
      have hdcy : d (c y) = c (d y) := LinearEquiv.congr_fun hdc y
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub, hdcy]
    obtain ⟨μ, hμ⟩ := hv ⟨_, hcv⟩
    have hμ' : c v = μ • (v : W) := by
      have := congrArg Subtype.val hμ
      simpa using this.symm
    have hθ : (c : Module.End K W) - algebraMap K (Module.End K W) μ ∈ E :=
      sub_mem hcE (Subalgebra.algebraMap_mem E μ)
    by_cases hθ0 : (c : Module.End K W) - algebraMap K (Module.End K W) μ = 0
    · apply hc1'
      refine hCsc c hcC μ fun x => ?_
      have := LinearMap.congr_fun hθ0 x
      simpa [sub_eq_zero, Module.algebraMap_end_apply] using this
    · have hθv : ((c : Module.End K W) - algebraMap K (Module.End K W) μ) (v : W) =
          ((c : Module.End K W) - algebraMap K (Module.End K W) μ) 0 := by
        simp [hμ', Module.algebraMap_end_apply]
      exact hv0 (Subtype.ext (hinj _ hθ hθ0 hθv))
  ·
    set c' := d * c * d⁻¹ with hc'
    have hc'C : c' ∈ C := hCG d hd c hcC
    have hc'E : (c' : Module.End K W) ∈ E := Algebra.subset_adjoin ⟨c', hc'C, rfl⟩
    have hθE : (c : Module.End K W) - c' ∈ E := sub_mem hcE hc'E
    have hθ0 : (c : Module.End K W) - c' ≠ 0 := by
      intro h
      apply hdc
      have hcc' : c = c' := LinearEquiv.ext fun x => by
        have := LinearMap.congr_fun h x
        simpa [sub_eq_zero] using this
      calc d * c = d * c * d⁻¹ * d := by group
        _ = c * d := by rw [← hc', ← hcc']
    have hinjθ := hinj _ hθE hθ0
    have hX : Module.finrank K (LinearMap.ker ((d : W →ₗ[K] W) - LinearMap.id)) + 1 =
        Module.finrank K W := by
      have := LinearMap.finrank_range_add_finrank_ker ((d : W →ₗ[K] W) - LinearMap.id)
      rw [hdt.1] at this
      omega
    set X := LinearMap.ker ((d : W →ₗ[K] W) - LinearMap.id)
    set Y := X.map (c : Module.End K W)
    have hY : Module.finrank K Y = Module.finrank K X := LinearEquiv.finrank_map_eq c X
    have hXY : X ⊓ Y = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwX, hwY⟩ := Submodule.mem_inf.mp hw
      obtain ⟨y, hyX, rfl⟩ := Submodule.mem_map.mp hwY
      rw [Submodule.mem_bot]
      have hdw : d (c y) = c y := by
        have := LinearMap.mem_ker.mp hwX
        simpa [sub_eq_zero] using this
      have hdy : d y = y := by
        have := LinearMap.mem_ker.mp hyX
        simpa [sub_eq_zero] using this
      have hdy' : d⁻¹ y = y := by
        conv_lhs => rw [← hdy]
        exact d.symm_apply_apply y
      have hcy : c' y = c y := by
        rw [hc', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdy']
        exact hdw
      have hθy : ((c : Module.End K W) - c') y = ((c : Module.End K W) - c') 0 := by
        simp [hcy]
      have hy0 : y = 0 := hinjθ hθy
      simp [hy0]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq X Y
    rw [hXY, finrank_bot, add_zero, hY] at hsum
    have hle := Submodule.finrank_le (X ⊔ Y)
    omega

end Abel

end CFSG.Quasithin.SimsG4
