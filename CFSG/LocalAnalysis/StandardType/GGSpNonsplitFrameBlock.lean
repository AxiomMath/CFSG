module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCyc

public section

open Polynomial Module

namespace CFSG.StandardType

namespace SpNS

@[expose] def SpBlockExists (K : Type) [Field K] (ℓ : ℕ) (D : Type) [AddCommGroup D]
    [Module K D] (c : D →ₗ[K] D) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (S : Set (Module.End K V)), B.IsAlt → B.Nondegenerate →
    (∀ x ∈ S, ∀ x' ∈ S, Commute x x') → (∀ x ∈ S, x ^ ℓ = 1) →
    (∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w) → (∃ x ∈ S, x ≠ 1) →
    ∃ (P : Submodule K V) (Ψ : D ≃ₗ[K] P), (B.restrict P).Nondegenerate ∧
      (∀ d d', B (Ψ (c d)) (Ψ (c d')) = B (Ψ d) (Ψ d')) ∧
      ∀ x ∈ S, ∃ a : ℕ, ∀ d, x (Ψ d) = Ψ ((c ^ a) d)

section Pow

variable {M : Type*} [Monoid M] {ℓ : ℕ}

theorem pow_pred_pow_pred {y : M} (hℓ : 2 ≤ ℓ) (hy : y ^ ℓ = 1) :
    (y ^ (ℓ - 1)) ^ (ℓ - 1) = y := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by omega⟩
  rw [← pow_mul, pow_eq_pow_mod _ hy]
  have e : (m + 2 - 1) * (m + 2 - 1) = 1 + (m + 2) * m := by
    rw [show m + 2 - 1 = m + 1 by omega]
    ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 1 < m + 2), pow_one]

theorem mul_pow_pred {y : M} (hℓ : 1 ≤ ℓ) (hy : y ^ ℓ = 1) : y * y ^ (ℓ - 1) = 1 := by
  rw [← pow_succ', Nat.sub_add_cancel hℓ, hy]

theorem pow_pred_mul {y : M} (hℓ : 1 ≤ ℓ) (hy : y ^ ℓ = 1) : y ^ (ℓ - 1) * y = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel hℓ, hy]

end Pow

section Aux

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {g : K[X]}

theorem aeval_pow_apply (z : Module.End K V) {w : V} (hw : aeval z g w = 0) (m : ℕ) :
    aeval (z ^ m) g w = cycMap z w hw (aeval (AdjoinRoot.root g ^ m) g) := by
  have h1 : aeval (z ^ m) g = aeval z (g.comp (X ^ m)) := by rw [aeval_comp, map_pow, aeval_X]
  have h2 : aeval (AdjoinRoot.root g ^ m) g = AdjoinRoot.mk g (g.comp (X ^ m)) := by
    rw [← AdjoinRoot.aeval_eq, aeval_comp, map_pow, aeval_X]
  rw [h1, h2, cycMap_mk]

theorem orthogonal_invariant {B : LinearMap.BilinForm K V} {y y' : Module.End K V}
    (hyy : y' * y = 1) (hy'B : ∀ u w, B (y' u) (y' w) = B u w) {N : Submodule K V}
    (hN : ∀ n ∈ N, y' n ∈ N) : ∀ r ∈ B.orthogonal N, y r ∈ B.orthogonal N := by
  intro r hr
  refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => ?_
  rw [← bilin_apply_left hyy hy'B]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp hr _ (hN n hn)

variable [Fact (Irreducible g)]

theorem eq_zero_of_cycMap_mem {z : Module.End K V} {v : V} (hv : aeval z g v = 0)
    {R : Submodule K V} (hR : ∀ r ∈ R, z r ∈ R) (hvR : v ∉ R) {μ : AdjoinRoot g}
    (hμ : cycMap z v hv μ ∈ R) : μ = 0 := by
  by_contra hne
  have h1 := cycMap_mem_of_mem z hv hR hne hμ 1
  rw [cycMap_one] at h1
  exact hvR h1

omit [Fact (Irreducible g)] in
theorem bilin_eq_zero_of_disjoint [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    {y y' : Module.End K V} (hyy : y * y' = 1) (hyB : ∀ u w, B (y u) (y w) = B u w)
    (hcomm : Commute y y') (hdisj : ∀ v, aeval y g v = 0 → aeval y' g v = 0 → v = 0) {u u' : V}
    (hu : aeval y g u = 0) (hu' : aeval y g u' = 0) : B u u' = 0 := by
  have hmaps : ∀ v ∈ LinearMap.ker (aeval y g), aeval y' g v ∈ LinearMap.ker (aeval y g) :=
    OrdPNS.mapsTo_ker_aeval (OrdPNS.commute_aeval hcomm.symm g).symm g
  set T := (aeval y' g).restrict hmaps with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hdisj _ v.2 (congrArg Subtype.val hv))
  obtain ⟨w₀, hw₀⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨u', hu'⟩
  have e : aeval y' g (w₀ : V) = u' := congrArg Subtype.val hw₀
  rw [← e, ← bilin_aeval_left hyy hyB, hu, map_zero, LinearMap.zero_apply]

end Aux

section Pair

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {g : K[X]} [Fact (Irreducible g)] {ℓ : ℕ}
  {B : LinearMap.BilinForm K V}

theorem exists_pair (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    (hnd : B.Nondegenerate) {S : Set (Module.End K V)} (hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x')
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) (hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w)
    {y : Module.End K V} (hyS : ∀ x ∈ S, Commute x y) (hyℓ : y ^ ℓ = 1)
    (hyB : ∀ u w, B (y u) (y w) = B u w) (hker : LinearMap.ker (aeval y g) ≠ ⊥) :
    ∃ u₁ u₂ : V, aeval y g u₁ = 0 ∧ aeval (y ^ (ℓ - 1)) g u₂ = 0 ∧ B u₁ u₂ ≠ 0 ∧
      ∀ x ∈ S, ∃ a : ℕ, x u₁ = (y ^ a) u₁ ∧ x u₂ = (y ^ a) u₂ := by
  classical
  have hℓ1 : 1 ≤ ℓ := hℓ.one_lt.le
  set y' := y ^ (ℓ - 1) with hy'
  have hyy : y * y' = 1 := mul_pow_pred hℓ1 hyℓ
  have hy'ℓ : y' ^ ℓ = 1 := by rw [hy', ← pow_mul, mul_comm, pow_mul, hyℓ, one_pow]
  have hy'S : ∀ x ∈ S, Commute x y' := fun x hx => (hyS x hx).pow_right _
  obtain ⟨ι, _, b, hb, hb0, hbS, hbspan⟩ := exists_eigenBasis hℓ hℓK hgd y S hSc hyS hSp
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hι : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    obtain ⟨μ, hμ⟩ := hbspan v₀ hv₀
    apply hv₀0
    rw [hμ, Finset.univ_eq_empty, Finset.sum_empty]
  obtain ⟨i₀⟩ := hι
  obtain ⟨w, hw⟩ : ∃ w, B (b i₀) w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb0 i₀ (hnd.1 _ hcon)
  obtain ⟨h, hc, -⟩ := OrdPNS.isCompl_ker_aeval hℓ hℓK hy'ℓ (Fact.out : Irreducible g) hgd
  have hwmem : w ∈ LinearMap.ker (aeval y' g) ⊔ LinearMap.ker (aeval y' h) := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hwmem
  have h2 : B (b i₀) w₂ = 0 := bilin_eq_zero_of_ker hyy hyB hc (hb i₀) hw₂
  rw [map_add, h2, add_zero] at hw
  obtain ⟨ι', _, b', hb', -, hb'S, hb'span⟩ := exists_eigenBasis hℓ hℓK hgd y' S hSc hy'S hSp
  obtain ⟨μ, hμ⟩ := hb'span w₁ (LinearMap.mem_ker.mp hw₁)
  rw [hμ, map_sum] at hw
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine ⟨b i₀, cycMap y' (b' i₁) (hb' i₁) (μ i₁), hb i₀, aeval_cycMap _ _ _ _, hi₁,
    fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hbS x hx i₀
  obtain ⟨a', ha'⟩ := hb'S x hx i₁
  have hxu₂ : x (cycMap y' (b' i₁) (hb' i₁) (μ i₁)) =
      (y ^ ((ℓ - 1) * a')) (cycMap y' (b' i₁) (hb' i₁) (μ i₁)) := by
    have e : y' ^ a' = y ^ ((ℓ - 1) * a') := by rw [hy', ← pow_mul]
    rw [apply_cycMap (hy'S x hx) (hb' i₁) ha', cycMap_root_pow_mul, e]
  have hmod := mod_eq_of_pair hℓ hℓK hgd hyℓ hyB (hSB x hx) (hyS x hx) (hb i₀) ha hxu₂ hi₁
  refine ⟨a, ha, ?_⟩
  rw [hxu₂, pow_eq_pow_mod ((ℓ - 1) * a') hyℓ, ← hmod, ← pow_eq_pow_mod a hyℓ]

end Pair

section Blocks

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {ℓ : ℕ}

omit [Finite K] in
theorem exists_base {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    {B : LinearMap.BilinForm K V} {S : Set (Module.End K V)}
    (hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x') (hSp : ∀ x ∈ S, x ^ ℓ = 1)
    (hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w) (h1 : ∃ x ∈ S, x ≠ 1) :
    ∃ y : Module.End K V, (∀ x ∈ S, Commute x y) ∧ y ^ ℓ = 1 ∧
      (∀ u w, B (y u) (y w) = B u w) ∧ LinearMap.ker (aeval y g) ≠ ⊥ := by
  obtain ⟨x₀, hx₀, hx₀1⟩ := h1
  obtain ⟨j, hj⟩ := NSFrame.exists_pow_ker_ne_bot hℓ hℓK hgd (hSp x₀ hx₀) hx₀1
  refine ⟨x₀ ^ j, fun x hx => (hSc x hx x₀ hx₀).pow_right j, ?_, bilin_pow_pow (hSB x₀ hx₀) j,
    hj⟩
  rw [← pow_mul, mul_comm, pow_mul, hSp x₀ hx₀, one_pow]

theorem spBlockExists_selfDual (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (hgd : g ∣ cyclotomic ℓ K) (hσ : aeval (AdjoinRoot.root g ^ (ℓ - 1)) g = 0) :
    SpBlockExists K ℓ (AdjoinRoot g) (LinearMap.mulLeft K (AdjoinRoot.root g)) := by
  intro V _ _ _ B S hAlt hnd hSc hSp hSB h1
  classical
  obtain ⟨y, hyS, hyℓ, hyB, hker⟩ := exists_base hℓ hℓK hgd hSc hSp hSB h1
  have hℓ1 : 1 ≤ ℓ := hℓ.one_lt.le
  set y' := y ^ (ℓ - 1) with hy'
  have hy'y : y' * y = 1 := pow_pred_mul hℓ1 hyℓ
  have hy'B : ∀ u w, B (y' u) (y' w) = B u w := bilin_pow_pow hyB _
  obtain ⟨u₁, u₂, hu₁, hu₂, h12, hchar⟩ := exists_pair hℓ hℓK hgd hnd hSc hSp hSB hyS hyℓ hyB hker
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hℓ hℓK hgd
  have hu₂' : aeval y g u₂ = 0 := by
    have e : y = y' ^ (ℓ - 1) := (pow_pred_pow_pred hℓ.two_le hyℓ).symm
    rw [e, aeval_pow_apply y' hu₂, hσ, map_zero]
  have hne : AdjoinRoot.root g - AdjoinRoot.root g ^ (ℓ - 1) ≠ 0 := by
    intro h0
    have h2 : AdjoinRoot.root g ^ 2 = 1 := by
      calc AdjoinRoot.root g ^ 2 = AdjoinRoot.root g * AdjoinRoot.root g := sq _
        _ = AdjoinRoot.root g * AdjoinRoot.root g ^ (ℓ - 1) :=
            congrArg (AdjoinRoot.root g * ·) (sub_eq_zero.mp h0)
        _ = 1 := by rw [← pow_succ', Nat.sub_add_cancel hℓ1, hζ.pow_eq_one]
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hζ.dvd_of_pow_eq_one 2 h2))
  set v₁ := cycMap y u₁ hu₁ (AdjoinRoot.root g - AdjoinRoot.root g ^ (ℓ - 1))⁻¹ with hv₁
  have hv₁u : y v₁ - y' v₁ = u₁ := by
    rw [hv₁, ← cycMap_root_mul, hy', ← cycMap_root_pow_mul, ← map_sub, ← sub_mul,
      mul_inv_cancel₀ hne, cycMap_one]
  have hv₁k : aeval y g v₁ = 0 := aeval_cycMap _ _ _ _
  have hpol : ∃ v, aeval y g v = 0 ∧ B (y v) v ≠ 0 ∧ ∀ x ∈ S, ∃ a : ℕ, x v = (y ^ a) v := by
    have hxv₁ : ∀ x ∈ S, ∀ a : ℕ, x u₁ = (y ^ a) u₁ → x v₁ = (y ^ a) v₁ := fun x hx a ha => by
      rw [hv₁, apply_cycMap (hyS x hx) hu₁ ha, cycMap_root_pow_mul]
    by_cases hA : B (y v₁) v₁ = 0
    · by_cases hC : B (y u₂) u₂ = 0
      · refine ⟨v₁ + u₂, by rw [map_add, hv₁k, hu₂', add_zero], fun h0 => h12 ?_,
          fun x hx => ?_⟩
        · have e1 : B (y u₂) v₁ = -B (y' v₁) u₂ := by
            rw [← hAlt.neg_eq v₁ (y u₂), bilin_apply_left hy'y hy'B]
          have e2 : B (y (v₁ + u₂)) (v₁ + u₂) =
              B (y v₁) v₁ + B (y v₁) u₂ + (B (y u₂) v₁ + B (y u₂) u₂) := by
            simp only [map_add, LinearMap.add_apply]
            ring
          have e3 : B u₁ u₂ = B (y v₁) u₂ - B (y' v₁) u₂ := by
            rw [← hv₁u, LinearMap.map_sub₂]
          linear_combination e3 - e1 - e2 + h0 - hA - hC
        · obtain ⟨a, ha₁, ha₂⟩ := hchar x hx
          exact ⟨a, by rw [map_add, map_add, hxv₁ x hx a ha₁, ha₂]⟩
      · exact ⟨u₂, hu₂', hC, fun x hx => (hchar x hx).imp fun a ha => ha.2⟩
    · exact ⟨v₁, hv₁k, hA, fun x hx => (hchar x hx).imp fun a ha => hxv₁ x hx a ha.1⟩
  obtain ⟨v, hv, hvB, hvS⟩ := hpol
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hvB (by simp)
  set Ψ₀ := cycMap y v hv with hΨ₀
  have hinj := cycMap_injective y hv hv0
  refine ⟨LinearMap.range Ψ₀, LinearEquiv.ofInjective Ψ₀ hinj, ?_, fun d d' => ?_,
    fun x hx => ?_⟩
  ·
    have hrefl : (B.restrict (LinearMap.range Ψ₀)).IsRefl := fun a b h => hAlt.isRefl a b h
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).2 fun z hz => ?_
    obtain ⟨μ, hμ⟩ := z.2
    have hinv : ∀ n ∈ LinearMap.range Ψ₀, y' n ∈ LinearMap.range Ψ₀ := by
      rintro _ ⟨ν, rfl⟩
      exact ⟨AdjoinRoot.root g ^ (ℓ - 1) * ν, by rw [hΨ₀, cycMap_root_pow_mul]⟩
    have hR := orthogonal_invariant hy'y hy'B hinv
    have hvR : v ∉ B.orthogonal (LinearMap.range Ψ₀) := fun h => hvB
      (LinearMap.BilinForm.mem_orthogonal_iff.mp h _
        ⟨AdjoinRoot.root g, by rw [hΨ₀, ← mul_one (AdjoinRoot.root g), cycMap_root_mul,
          cycMap_one]⟩)
    have hzR : Ψ₀ μ ∈ B.orthogonal (LinearMap.range Ψ₀) := by
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => ?_
      have h0 := hz ⟨n, hn⟩
      rw [hμ]
      exact hAlt.isRefl _ _ h0
    have hμ0 := eq_zero_of_cycMap_mem hv hR hvR hzR
    exact Subtype.ext (by rw [← hμ, hμ0, map_zero, Submodule.coe_zero])
  · rw [LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply,
      LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, LinearMap.mulLeft_apply,
      LinearMap.mulLeft_apply, hΨ₀, cycMap_root_mul, cycMap_root_mul, hyB]
  · obtain ⟨a, ha⟩ := hvS x hx
    refine ⟨a, fun d => ?_⟩
    rw [LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, LinearMap.pow_mulLeft,
      LinearMap.mulLeft_apply, hΨ₀, apply_cycMap (hyS x hx) hv ha]

theorem spBlockExists_paired (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    (hσ : aeval (AdjoinRoot.root g ^ (ℓ - 1)) g ≠ 0) :
    SpBlockExists K ℓ (AdjoinRoot g × AdjoinRoot g)
      ((LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap
        (LinearMap.mulLeft K (AdjoinRoot.root g ^ (ℓ - 1)))) := by
  intro V _ _ _ B S hAlt hnd hSc hSp hSB h1
  classical
  obtain ⟨y, hyS, hyℓ, hyB, hker⟩ := exists_base hℓ hℓK hgd hSc hSp hSB h1
  have hℓ1 : 1 ≤ ℓ := hℓ.one_lt.le
  set y' := y ^ (ℓ - 1) with hy'
  have hyy : y * y' = 1 := mul_pow_pred hℓ1 hyℓ
  have hy'y : y' * y = 1 := pow_pred_mul hℓ1 hyℓ
  have hy'B : ∀ u w, B (y' u) (y' w) = B u w := bilin_pow_pow hyB _
  have hcomm : Commute y y' := (Commute.refl y).pow_right _
  have hyy' : y' ^ (ℓ - 1) = y := pow_pred_pow_pred hℓ.two_le hyℓ
  obtain ⟨u₁, u₂, hu₁, hu₂, h12, hchar⟩ := exists_pair hℓ hℓK hgd hnd hSc hSp hSB hyS hyℓ hyB hker
  have hdisj : ∀ v, aeval y g v = 0 → aeval y' g v = 0 → v = 0 := by
    intro v hv hv'
    by_contra hv0
    rw [hy', aeval_pow_apply y hv] at hv'
    exact hσ (cycMap_injective y hv hv0 (hv'.trans (map_zero _).symm))
  have hiso : ∀ u u', aeval y g u = 0 → aeval y g u' = 0 → B u u' = 0 := fun u u' hu hu' =>
    bilin_eq_zero_of_disjoint hyy hyB hcomm hdisj hu hu'
  have hiso' : ∀ u u', aeval y' g u = 0 → aeval y' g u' = 0 → B u u' = 0 := fun u u' hu hu' =>
    bilin_eq_zero_of_disjoint hy'y hy'B hcomm.symm (fun v h₁ h₂ => hdisj v h₂ h₁) hu hu'
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    exact h12 (by simp)
  have hu₂0 : u₂ ≠ 0 := by
    rintro rfl
    exact h12 (by simp)
  set Ψ₀ := (cycMap y u₁ hu₁).coprod (cycMap y' u₂ hu₂) with hΨ₀
  have hΨ₀a : ∀ μ ν, Ψ₀ (μ, ν) = cycMap y u₁ hu₁ μ + cycMap y' u₂ hu₂ ν := fun _ _ => rfl
  have hinj : Function.Injective Ψ₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨μ, ν⟩ h0
    rw [hΨ₀a] at h0
    have e₁ : cycMap y u₁ hu₁ μ = 0 := by
      refine hdisj _ (aeval_cycMap _ _ _ _) ?_
      rw [eq_neg_of_add_eq_zero_left h0, map_neg, aeval_cycMap, neg_zero]
    have e₂ : cycMap y' u₂ hu₂ ν = 0 := by
      rw [e₁, zero_add] at h0
      exact h0
    have hμ : μ = 0 := cycMap_injective y hu₁ hu₁0 (e₁.trans (map_zero _).symm)
    have hν : ν = 0 := cycMap_injective y' hu₂ hu₂0 (e₂.trans (map_zero _).symm)
    simp [hμ, hν]
  have hc : ∀ d, Ψ₀ (((LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap
      (LinearMap.mulLeft K (AdjoinRoot.root g ^ (ℓ - 1)))) d) = y (Ψ₀ d) := by
    rintro ⟨μ, ν⟩
    simp only [LinearMap.prodMap_apply, LinearMap.mulLeft_apply, hΨ₀a]
    rw [cycMap_root_mul, cycMap_root_pow_mul, hyy', map_add]
  refine ⟨LinearMap.range Ψ₀, LinearEquiv.ofInjective Ψ₀ hinj, ?_, fun d d' => ?_,
    fun x hx => ?_⟩
  ·
    have hrefl : (B.restrict (LinearMap.range Ψ₀)).IsRefl := fun a b h => hAlt.isRefl a b h
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).2 fun z hz => ?_
    obtain ⟨⟨μ, ν⟩, hμν⟩ := z.2
    have hz' : ∀ w ∈ LinearMap.range Ψ₀, B (z : V) w = 0 := fun w hw => hz ⟨w, hw⟩
    have hmem₁ : ∀ μ', cycMap y u₁ hu₁ μ' ∈ LinearMap.range Ψ₀ := fun μ' =>
      ⟨(μ', 0), by rw [hΨ₀a, map_zero, add_zero]⟩
    have hmem₂ : ∀ ν', cycMap y' u₂ hu₂ ν' ∈ LinearMap.range Ψ₀ := fun ν' =>
      ⟨(0, ν'), by rw [hΨ₀a, map_zero, zero_add]⟩
    have hμ0 : μ = 0 := by
      have hinv : ∀ n ∈ LinearMap.range (cycMap y' u₂ hu₂),
          y' n ∈ LinearMap.range (cycMap y' u₂ hu₂) := by
        rintro _ ⟨ν', rfl⟩
        exact ⟨AdjoinRoot.root g * ν', cycMap_root_mul _ _ _ _⟩
      have hR := orthogonal_invariant hy'y hy'B hinv
      have hvR : u₁ ∉ B.orthogonal (LinearMap.range (cycMap y' u₂ hu₂)) := fun h =>
        h12 (hAlt.isRefl _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp h u₂
          ⟨1, cycMap_one _ _ _⟩))
      refine eq_zero_of_cycMap_mem hu₁ hR hvR
        (LinearMap.BilinForm.mem_orthogonal_iff.mpr ?_)
      rintro _ ⟨ν', rfl⟩
      have h0 := hz' _ (hmem₂ ν')
      rw [← hμν, hΨ₀a, LinearMap.map_add₂,
        hiso' _ _ (aeval_cycMap _ _ _ _) (aeval_cycMap _ _ _ _), add_zero] at h0
      exact hAlt.isRefl _ _ h0
    have hν0 : ν = 0 := by
      have hinv : ∀ n ∈ LinearMap.range (cycMap y u₁ hu₁),
          y n ∈ LinearMap.range (cycMap y u₁ hu₁) := by
        rintro _ ⟨μ', rfl⟩
        exact ⟨AdjoinRoot.root g * μ', cycMap_root_mul _ _ _ _⟩
      have hR := orthogonal_invariant hyy hyB hinv
      have hvR : u₂ ∉ B.orthogonal (LinearMap.range (cycMap y u₁ hu₁)) := fun h =>
        h12 (LinearMap.BilinForm.mem_orthogonal_iff.mp h u₁ ⟨1, cycMap_one _ _ _⟩)
      refine eq_zero_of_cycMap_mem hu₂ hR hvR
        (LinearMap.BilinForm.mem_orthogonal_iff.mpr ?_)
      rintro _ ⟨μ', rfl⟩
      have h0 := hz' _ (hmem₁ μ')
      rw [← hμν, hΨ₀a, LinearMap.map_add₂,
        hiso _ _ (aeval_cycMap _ _ _ _) (aeval_cycMap _ _ _ _), zero_add] at h0
      exact hAlt.isRefl _ _ h0
    exact Subtype.ext (by rw [← hμν, hμ0, hν0, hΨ₀a, map_zero, map_zero, add_zero,
      Submodule.coe_zero])
  · rw [LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply,
      LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, hc, hc, hyB]
  · obtain ⟨a, ha₁, ha₂⟩ := hchar x hx
    have ha₂' : x u₂ = (y' ^ ((ℓ - 1) * a)) u₂ := by rw [pow_mul, hyy', ha₂]
    refine ⟨a, ?_⟩
    rintro ⟨μ, ν⟩
    rw [LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, OrdPNS.prodMap_pow,
      LinearMap.pow_mulLeft, LinearMap.pow_mulLeft]
    simp only [LinearMap.prodMap_apply, LinearMap.mulLeft_apply, hΨ₀a]
    rw [map_add, apply_cycMap (hyS x hx) hu₁ ha₁,
      apply_cycMap ((hyS x hx).pow_right _) hu₂ ha₂', ← pow_mul]

end Blocks

end SpNS

end CFSG.StandardType
