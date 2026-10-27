module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCartanScalar
public import CFSG.LocalAnalysis.StandardType.GGTBWNormInnerPowerMap

public noncomputable section
open scoped BigOperators
namespace CFSG.StandardType
open CFSG CFSG.Assembly TableB
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem false_of_eigen_mem_cartan_reflection_datum
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M)
    (C : Matrix ι ι ℤ) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (σ : ι → V ≃ₗ[ZMod p] V) (hσ : ∀ i v, σ i v = v - α i v • h i)
    (s : V ≃ₗ[ZMod p] V) (hs : s ∈ Subgroup.closure (Set.range σ))
    (hfix : ∀ v, s v = v → v = 0) {c : ZMod p} {v : V} (hv : v ≠ 0) (hsv : s v = c • v)
    (hinv : ∀ w, c • s w = w → w = 0) : False := by
  classical
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz
    have hl := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hz
    have hl := Nat.le_of_dvd (by norm_num : 0 < 3) hd
    omega
  obtain ⟨D, hTree, hbond⟩ := ggFLW_cartanTree_bonds hM
  have hP : ∀ i j, i ≠ j → (α i (h j) ≠ 0 ↔ D i j ≠ 0) := by
    intro i j hij
    rw [hbond i j hij]
    rcases hC.entries hij with ⟨hm, h0, -⟩ | ⟨hm, h1, -⟩ |
      ⟨hm, ⟨h1, -⟩ | ⟨h2', -⟩⟩ | ⟨hm, ⟨h1, -⟩ | ⟨h3', -⟩⟩
    · rw [hpair, h0, hm]
      norm_num
    · rw [hpair, h1, hm]
      norm_num
    · rw [hpair, h1, hm]
      norm_num
    · rw [hpair, h2', hm]
      norm_num [h2]
    · rw [hpair, h1, hm]
      norm_num
    · rw [hpair, h3', hm]
      norm_num [h3]
  obtain ⟨d, hd, hsym⟩ := ggFLW_symmetrizer D hTree (fun i j => α i (h j)) hP
  have hα : ∀ i, α i (h i) = 2 := by
    intro i
    rw [hpair, hC.1 i]
    norm_num
  let H := Submodule.span (ZMod p) (Set.range h)
  have hdisp : ∀ t ∈ Subgroup.closure (Set.range σ), ∀ v, t v - v ∈ H := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      intro v
      rw [hσ, sub_sub_cancel_left]
      exact H.neg_mem (H.smul_mem _ (Submodule.subset_span (Set.mem_range_self i)))
    | one => intro v; simp
    | mul a b _ _ ha hb =>
      intro v
      rw [LinearEquiv.mul_apply, show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
      exact H.add_mem (ha (b v)) (hb v)
    | inv a _ ha =>
      intro v
      change a.symm v - v ∈ H
      have hv := H.neg_mem (ha (a.symm v))
      simpa only [LinearEquiv.apply_symm_apply, neg_sub] using hv
  have hsurj : Function.Surjective ((s : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) := by
    refine LinearMap.injective_iff_surjective.mp ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hfix w (sub_eq_zero.mp hw)
  have hspan : Submodule.span (ZMod p) (Set.range h) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, rfl⟩ := hsurj w
    exact hdisp s hs u
  have hker : ∀ w, (∀ i, α i w = 0) → w = 0 := by
    intro w hw
    have hfixw : ∀ t ∈ Subgroup.closure (Set.range σ), t w = w := by
      intro t ht
      induction ht using Subgroup.closure_induction with
      | mem t ht =>
        obtain ⟨i, rfl⟩ := ht
        rw [hσ, hw, zero_smul, sub_zero]
      | one => rfl
      | mul a b _ _ ha hb => rw [LinearEquiv.mul_apply, hb, ha]
      | inv a _ ha =>
        change a.symm w = w
        apply a.injective
        rw [LinearEquiv.apply_symm_apply, ha]
    exact hfix w (hfixw s hs)
  obtain ⟨B, hB, hInv⟩ := ggFLW_invariantForm hp2 h α σ hσ hα hspan hker d hd hsym
  have hcl : ∀ t ∈ Subgroup.closure (Set.range σ), ∀ u v, B (t u) (t v) = B u v := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      exact hInv i
    | one => intro u v; rfl
    | mul a b _ _ ha hb =>
      intro u v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
    | inv a _ ha =>
      intro u v
      change B (a.symm u) (a.symm v) = B u v
      have he := ha (a.symm u) (a.symm v)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at he
      exact he.symm
  have hsurj' : Function.Surjective
      (c • (s : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) := by
    refine LinearMap.injective_iff_surjective.mp ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hinv w (sub_eq_zero.mp hw)
  refine hv (hB v fun u => ?_)
  obtain ⟨w, rfl⟩ := hsurj' u
  have he := hcl s hs v w
  rw [hsv, map_smul, LinearMap.smul_apply, smul_eq_mul] at he
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    map_sub, map_smul, smul_eq_mul, he, sub_self]

theorem false_of_eigen_mem_ggAutomizer {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {L' : Type}
    [Group L'] [Finite L'] {A : Subgroup (MulAut L')} (Λ : Type) [Fintype Λ] [DecidableEq Λ]
    (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A = Subgroup.closure (Set.range φ))
    {k : ℕ} {u : MulAut ↥A} (hu : u ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hfix : ∀ a, u a = a → a = 1) (hev : ∃ a, a ≠ 1 ∧ u a = a ^ k)
    (hinv : ∀ a, u a ^ k = a → a = 1) : False := by
  classical
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  rw [hgen] at hu
  have hs : ggLin (p := p) ι u ∈
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
    have h1 := Subgroup.mem_map_of_mem (ggLin (p := p) ι) hu
    rw [MonoidHom.map_closure] at h1
    convert h1 using 2
    ext x
    simp
  have hι : ∀ b : ↥A, ggLin (p := p) ι u (ι (Additive.ofMul b)) = ι (Additive.ofMul (u b)) :=
    ggLin_apply_ofMul ι u
  have hsurj : ∀ w : V, ∃ b : ↥A, ι (Additive.ofMul b) = w := fun w =>
    ⟨Additive.toMul (ι.symm w), by rw [ofMul_toMul, AddEquiv.apply_symm_apply]⟩
  have hzero : ∀ b : ↥A, ι (Additive.ofMul b) = 0 → b = 1 := fun b hb => by
    rw [← map_zero ι] at hb
    exact ι.injective hb
  have hpow : ∀ b : ↥A, ι (Additive.ofMul (b ^ k)) = (k : ZMod p) • ι (Additive.ofMul b) :=
    fun b => by rw [ofMul_pow, map_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨a, ha1, hak⟩ := hev
  refine false_of_eigen_mem_cartan_reflection_datum hp5 M hM C hC h α hpair
    (fun i => ggLin (p := p) ι (φ i)) hlin (ggLin (p := p) ι u) hs ?_
    (v := ι (Additive.ofMul a)) (c := (k : ZMod p)) (fun h0 => ha1 (hzero a h0)) ?_ ?_
  · intro w hw
    obtain ⟨b, rfl⟩ := hsurj w
    rw [hι] at hw
    rw [hfix b (Additive.ofMul.injective (ι.injective hw)), ofMul_one, map_zero]
  · rw [hι, hak, hpow]
  · intro w hw
    obtain ⟨b, rfl⟩ := hsurj w
    rw [hι, ← hpow] at hw
    rw [hinv b (Additive.ofMul.injective (ι.injective hw)), ofMul_one, map_zero]

theorem exists_eigen_mem_ggAutomizer_of_innerModel {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I)
    (hcp : GGCenterPrime p R) {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent p A) {k : ℕ}
    (hsupp : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E = Nat.card A →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∃ z : R, (∀ x ∈ E, z * x * z⁻¹ ∈ E) ∧ (∀ x ∈ E, z * x * z⁻¹ = x → x = 1) ∧
        (∃ x ∈ E, x ≠ 1 ∧ z * x * z⁻¹ = x ^ k) ∧ ∀ x ∈ E, (z * x * z⁻¹) ^ k = x → x = 1) :
    ∃ u ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
      (∀ a, u a = a → a = 1) ∧ (∃ a, a ≠ 1 ∧ u a = a ^ k) ∧ ∀ a, u a ^ k = a → a = 1 := by
  obtain ⟨Λ, hΛeq, hΛinj, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel hp hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  obtain ⟨z, hzE, hzfix, ⟨x₀, hx₀, hx₀1, hx₀k⟩, hzinv⟩ := hsupp (A.comap Λ) hE hEc hEsc
  obtain ⟨n, rfl⟩ := hψ z
  have hΛn : Λ (ψ n) = MulAut.conj n := hΛeq rfl
  have hconj : ∀ e : R, MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ = Λ (ψ n * e * (ψ n)⁻¹) :=
    fun e => by rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
  have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    Subgroup.mem_normalizer_fintype fun a ha => by
      obtain ⟨e, rfl⟩ := hAΛ a ha
      rw [hconj e]
      exact hzE e ha
  have key : ∀ a : ↥A, ∃ e ∈ A.comap Λ, (a : MulAut L') = Λ e ∧
      ((ggConjAut A hn a : ↥A) : MulAut L') = Λ (ψ n * e * (ψ n)⁻¹) := by
    intro a
    obtain ⟨e, he⟩ := hAΛ a a.2
    have he' : e ∈ A.comap Λ := by
      show Λ e ∈ A
      rw [he]
      exact a.2
    refine ⟨e, he', he.symm, ?_⟩
    rw [ggConjAut_apply, ← he, hconj e]
  refine ⟨ggConjAut A hn, ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn,
    fun a ha => ?_, ⟨⟨Λ x₀, hx₀⟩, fun h1 => hx₀1 (hΛinj ?_), Subtype.ext ?_⟩, fun a ha => ?_⟩
  · obtain ⟨e, he, hae, hue⟩ := key a
    have h1 : ψ n * e * (ψ n)⁻¹ = e := hΛinj (by rw [← hue, ← hae, ha])
    exact Subtype.ext (by rw [hae, hzfix e he h1, map_one]; rfl)
  · rw [map_one]
    exact congrArg Subtype.val h1
  · rw [ggConjAut_apply, Subgroup.coe_pow]
    change MulAut.conj n * Λ x₀ * (MulAut.conj n)⁻¹ = Λ x₀ ^ k
    rw [hconj x₀, hx₀k, map_pow]
  · obtain ⟨e, he, hae, hue⟩ := key a
    have h2 : (ψ n * e * (ψ n)⁻¹) ^ k = e := hΛinj (by
      rw [map_pow, ← hue, ← Subgroup.coe_pow, ha, hae])
    exact Subtype.ext (by rw [hae, hzinv e he h2, map_one]; rfl)

end CFSG.StandardType
