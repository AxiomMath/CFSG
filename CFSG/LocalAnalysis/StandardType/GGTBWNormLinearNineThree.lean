module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvection
public import CFSG.LocalAnalysis.StandardType.GGPGLCubicBlockNormalizer
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityEigenspace
public import CFSG.LocalAnalysis.StandardType.GGNbrCanCartan
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType.TypeA

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace PGLTor

theorem exists_quadPhase_three_of_nine_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (h9 : 9 ∣ Fintype.card ι) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {h g : GL ι K} (hh : h ^ 3 = 1) {u₀ : Kˣ}
    (hu₀ : u₀ ≠ 1) (hu₀p : u₀ ^ 3 = 1)
    (hhg : h * g = GeneralLinearGroup.scalar ι u₀ * (g * h)) :
    ∃ D : GL ι K, (D : Matrix ι ι K).det = 1 ∧
      ∀ (x : GL ι K) (m : ℕ), h * x = GeneralLinearGroup.scalar ι (ζ ^ m) * (x * h) →
        ∃ c : Kˣ, D * x * D⁻¹ = GeneralLinearGroup.scalar ι c * (x * h ^ m) := by
  obtain ⟨D, hdet, hact⟩ := exists_quadPhase_three hζ hh hu₀ hu₀p hhg
  obtain ⟨n, hn⟩ := h9
  have hdim : Fintype.card ι / 3 = 3 * n := by omega
  have hζ3 : (ζ : K) ^ 3 = 1 :=
    (IsPrimitiveRoot.coe_units_iff.mpr hζ).pow_eq_one
  refine ⟨D, ?_, hact⟩
  rw [hdet, hdim, pow_mul, hζ3, one_pow]

end PGLTor

private theorem card_le_three_of_dihedral_cube_subgroup
    {n : ℕ} (P : Subgroup (DihedralGroup n)) [Finite P]
    (hcube : ∀ g ∈ P, g ^ 3 = 1) : Nat.card P ≤ 3 := by
  have hrot : P ≤ TauCeti.dihedralRotations n := by
    intro g hg
    cases g with
    | r i => exact TauCeti.r_mem_dihedralRotations i
    | sr i =>
      have hz := hcube (DihedralGroup.sr i) hg
      have hne : DihedralGroup.sr i ≠ (1 : DihedralGroup n) := by simp
      apply (hne ?_).elim
      simp [pow_succ] at hz
  let f : P →* TauCeti.dihedralRotations n :=
    { toFun := fun g => ⟨g, hrot g.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have : IsCyclic (TauCeti.dihedralRotations n) := TauCeti.isCyclic_dihedralRotations n
  have : IsCyclic P := isCyclic_of_injective f fun x y h =>
    Subtype.ext (congrArg (fun z : TauCeti.dihedralRotations n =>
      (z : DihedralGroup n)) h)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hcube g g.property)
  have hd := orderOf_dvd_of_pow_eq_one hg3
  rw [hg] at hd
  exact Nat.le_of_dvd (by decide : 0 < 3) hd

theorem card_le_three_of_cube_subgroup_of_two_involutions
    {G : Type} [Group G] [Finite G] {s t : G}
    (hs : s * s = 1) (ht : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1)
    (hgen : Subgroup.closure ({s, t} : Set G) = ⊤)
    (P : Subgroup G) (hcube : ∀ g ∈ P, g ^ 3 = 1) : Nat.card P ≤ 3 := by
  let e : DihedralGroup (orderOf (s * t)) ≃* G :=
    TauCeti.dihedralGroupMulEquiv hs ht hs1 ht1 rfl hgen
  have : Finite (DihedralGroup (orderOf (s * t))) :=
    Finite.of_injective e e.injective
  let P' := P.comap e.toMonoidHom
  have hcube' : ∀ g ∈ P', g ^ 3 = 1 := by
    intro g hg
    apply e.injective
    simpa only [map_pow, map_one] using hcube (e g) hg
  let f : P' ≃* P :=
    { toFun := fun g => ⟨e g, g.property⟩
      invFun := fun g => ⟨e.symm g, by
        change e (e.symm g) ∈ P
        simp⟩
      left_inv := fun g => by
        apply Subtype.ext
        exact e.symm_apply_apply g
      right_inv := fun g => by
        apply Subtype.ext
        exact e.apply_symm_apply g
      map_mul' := fun g h => by
        apply Subtype.ext
        exact e.map_mul g h }
  calc Nat.card P = Nat.card P' := (Nat.card_congr f.toEquiv).symm
    _ ≤ 3 := card_le_three_of_dihedral_cube_subgroup P' hcube'

theorem card_le_three_of_cube_subgroup_of_small_involution_family
    {G : Type} [Group G] [Finite G] {Λ : Type} [Fintype Λ]
    (φ : Λ → G) (hsq : ∀ i, φ i * φ i = 1) (hne : ∀ i, φ i ≠ 1)
    (hgen : Subgroup.closure (Set.range φ) = ⊤) (hcard : Fintype.card Λ ≤ 2)
    (P : Subgroup G) (hcube : ∀ g ∈ P, g ^ 3 = 1) : Nat.card P ≤ 3 := by
  classical
  rcases isEmpty_or_nonempty Λ with hΛ | hΛ
  · have := hΛ
    have hrange : Set.range φ = (∅ : Set G) := by
      ext x
      constructor
      · rintro ⟨i, -⟩
        exact isEmptyElim i
      · intro hx
        exact False.elim hx
    have hbot : (⊥ : Subgroup G) = ⊤ := by
      simpa only [hrange, Subgroup.closure_empty] using hgen
    have hone : ∀ x : G, x = 1 := fun x =>
      Subgroup.mem_bot.mp (hbot.symm ▸ Subgroup.mem_top x)
    have hinj : Function.Injective (fun _ : P => ()) := by
      intro x y _
      apply Subtype.ext
      exact (hone x).trans (hone y).symm
    exact (Nat.card_le_card_of_injective _ hinj).trans (by simp : Nat.card Unit ≤ 3)
  have := hΛ
  have hcover : ∃ i j : Λ, ∀ k, k = i ∨ k = j := by
    by_cases h1 : Fintype.card Λ ≤ 1
    · let i : Λ := Classical.arbitrary Λ
      exact ⟨i, i, fun k => Or.inl ((Fintype.card_le_one_iff.mp h1) k i)⟩
    · have hc : Nat.card Λ = 2 := by rw [Nat.card_eq_fintype_card]; omega
      obtain ⟨i, j, -, hij⟩ := Nat.card_eq_two_iff.mp hc
      refine ⟨i, j, fun k => ?_⟩
      have hk : k ∈ ({i, j} : Set Λ) := by rw [hij]; trivial
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
  obtain ⟨i, j, hij⟩ := hcover
  have hrange : Set.range φ = ({φ i, φ j} : Set G) := by
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      rcases hij k with rfl | rfl <;> simp
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨i, rfl⟩
      · exact ⟨j, rfl⟩
  apply card_le_three_of_cube_subgroup_of_two_involutions
    (hsq i) (hsq j) (hne i) (hne j) (by simpa only [hrange] using hgen) P hcube

theorem card_le_three_of_cube_subgroup_of_small_reflection_datum
    {E : Type} [Group E] [Finite E] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Λ : Type} [Fintype Λ]
    (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (Γ : Subgroup (MulAut E)) (hgen : Γ = Subgroup.closure (Set.range φ))
    (hcard : Fintype.card Λ ≤ 2) (P : Subgroup Γ)
    (hcube : ∀ g ∈ P, g ^ 3 = 1) : Nat.card P ≤ 3 := by
  classical
  have : Finite (MulAut E) :=
    Finite.of_injective (fun f : MulAut E => (f : E → E)) DFunLike.coe_injective
  have hginj : Function.Injective (ggLin (p := 3) ι) := by
    intro f g hfg
    ext a
    have hv := LinearEquiv.congr_fun hfg (ι (Additive.ofMul a))
    change ggLin (p := 3) ι (f : MulAut E) (ι (Additive.ofMul a)) =
      ggLin (p := 3) ι (g : MulAut E) (ι (Additive.ofMul a)) at hv
    have ha : ι (Additive.ofMul (f a)) = ι (Additive.ofMul (g a)) := by
      simpa only [ggLin_apply_ofMul] using hv
    simpa using congrArg Additive.toMul (ι.injective ha)
  have hsq : ∀ i, φ i * φ i = 1 := by
    intro i
    apply hginj
    rw [map_mul, map_one]
    ext v
    change ggLin (p := 3) ι (φ i) (ggLin (p := 3) ι (φ i) v) = v
    rw [hlin, hlin, map_sub, map_smul, hdiag]
    module
  have hne : ∀ i, φ i ≠ 1 := by
    intro i hi
    have hv := congrArg (α i) (hlin i (h i))
    rw [hi, map_one] at hv
    change α i (h i) = α i (h i - α i (h i) • h i) at hv
    rw [map_sub, map_smul, hdiag] at hv
    norm_num [smul_eq_mul] at hv
    have hz : (4 : ZMod 3) = 0 := by linear_combination hv
    have hd : 3 ∣ 4 := (ZMod.natCast_eq_zero_iff 4 3).mp hz
    norm_num at hd
  let f : Λ → Γ := fun i => ⟨φ i, by
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hle : Γ ≤ (Subgroup.closure (Set.range f)).map Γ.subtype := by
    apply (le_of_eq hgen).trans
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
  have hfgen : Subgroup.closure (Set.range f) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle x.property
    have hxy : y = x := Subtype.ext hyx
    exact hxy ▸ hy
  have hfsq : ∀ i, f i * f i = 1 := fun i => Subtype.ext (hsq i)
  have hfne : ∀ i, f i ≠ 1 := fun i hi => hne i (congrArg Subtype.val hi)
  exact card_le_three_of_cube_subgroup_of_small_involution_family f hfsq hfne hfgen hcard P hcube

theorem card_le_two_of_coroot_span_le_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hspan : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) ≤ 2) :
    Fintype.card Λ ≤ 2 := by
  classical
  let W := Submodule.span (ZMod p) (Set.range h)
  let hW : Λ → W := fun i => ⟨h i, Submodule.subset_span ⟨i, rfl⟩⟩
  let αW : Λ → Module.Dual (ZMod p) W := fun i => (α i).comp W.subtype
  have hpairW : ∀ i j, αW i (hW j) = (C i j : ZMod p) := hpair
  have hrank := LevTwo.levTwoS4a_rank_core_add (V := W) (C := C)
    (h := hW) (α := αW) hpairW (T := ⊥) (by simp)
  rw [finrank_bot, add_zero] at hrank
  change Module.finrank (ZMod p) W ≤ 2 at hspan
  have hcard := ggIntCartan_card_le_rank_add_one hM hC p hp2
  by_contra hn
  have hthree : Fintype.card Λ = 3 := by omega
  have hfull := ggIntCartan_rank_eq_three hp2 hM hC hthree
  omega

theorem card_le_two_of_invariant_linearForm
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (hdim : Module.finrank (ZMod p) V = 3)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (σ : Λ → V ≃ₗ[ZMod p] V)
    (hlin : ∀ i v, σ i v = v - α i v • h i)
    (T : Module.Dual (ZMod p) V) (hT : T ≠ 0)
    (hinv : ∀ i v, T (σ i v) = T v) : Fintype.card Λ ≤ 2 := by
  classical
  have : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdiv)
  have hz : ∀ i, T (h i) = 0 := by
    intro i
    have hdiag : α i (h i) = 2 := by rw [hpair, hC.1 i]; simp
    have hi := hinv i (h i)
    rw [hlin, hdiag, map_sub, map_smul] at hi
    simp only [smul_eq_mul] at hi
    have hmul : (2 : ZMod p) * T (h i) = 0 := by
      linear_combination -hi
    exact (mul_eq_zero.mp hmul).resolve_left h2
  have hspan : Submodule.span (ZMod p) (Set.range h) ≤ T.ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hz i)
  have hex : ∃ v, T v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hT
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hex
  have hsurj : Function.Surjective T := fun a =>
    ⟨(a / T v) • v, by simp [hv]⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker T
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hdim] at hsum
  apply card_le_two_of_coroot_span_le_two hp2 hM hC h α hpair
  have hm := Submodule.finrank_mono hspan
  omega

theorem false_of_invariant_linearForm_and_nine_subgroup
    {E : Type} [Group E] [Finite E] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (M : CoxeterMatrix Λ) (hM : GGIsWeylMatrix M)
    (C : Matrix Λ Λ ℤ) (hC : GGIntCartan M C)
    (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (Γ : Subgroup (MulAut E)) (hgen : Γ = Subgroup.closure (Set.range φ))
    (hdim : Module.finrank (ZMod 3) V = 3)
    (j : Module.Dual (ZMod 3) V) (hj : j ≠ 0)
    (hinv : ∀ i v, j (ggLin (p := 3) ι (φ i) v) = j v)
    (P : Subgroup Γ) (hcube : ∀ g ∈ P, g ^ 3 = 1) (hcardP : Nat.card P = 9) : False := by
  have hcard := card_le_two_of_invariant_linearForm (by decide) hM hC hdim h α hpair
    (fun i => ggLin (p := 3) ι (φ i)) hlin j hj hinv
  have hdiag : ∀ i, α i (h i) = 2 := fun i => by rw [hpair, hC.1 i]; simp
  have hp := card_le_three_of_cube_subgroup_of_small_reflection_datum
    ι φ h α hdiag hlin Γ hgen hcard P hcube
  omega

theorem exists_nine_cube_subgroup_of_kernel_shears
    {E : Type} [Group E] [Finite E] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (ι : Additive E ≃+ V) (Γ : Subgroup (MulAut E))
    (j : Module.Dual (ZMod 3) V) (hj : j ≠ 0)
    (hdim : Module.finrank (ZMod 3) V = 3)
    (hall : ∀ b : j.ker, ∃ g : Γ, ∀ v,
      ggLin (p := 3) ι g v = v + j v • (b : V)) :
    ∃ P : Subgroup Γ, Nat.card P = 9 ∧ ∀ g ∈ P, g ^ 3 = 1 := by
  classical
  have : FiniteDimensional (ZMod 3) V := Module.Finite.of_finite
  have : Finite (MulAut E) :=
    Finite.of_injective (fun f : MulAut E => (f : E → E)) DFunLike.coe_injective
  let ρ : Γ →* (V ≃ₗ[ZMod 3] V) :=
    { toFun := fun g => ggLin (p := 3) ι (g : MulAut E)
      map_one' := by rw [Subgroup.coe_one, map_one]
      map_mul' := fun g h => by rw [Subgroup.coe_mul, map_mul] }
  have hρinj : Function.Injective ρ := by
    intro f g hfg
    apply Subtype.ext
    ext a
    have hv := LinearEquiv.congr_fun hfg (ι (Additive.ofMul a))
    change ggLin (p := 3) ι (f : MulAut E) (ι (Additive.ofMul a)) =
      ggLin (p := 3) ι (g : MulAut E) (ι (Additive.ofMul a)) at hv
    have ha : ι (Additive.ofMul ((f : MulAut E) a)) =
        ι (Additive.ofMul ((g : MulAut E) a)) := by
      simpa only [ρ, ggLin_apply_ofMul] using hv
    simpa using congrArg Additive.toMul (ι.injective ha)
  choose g hg using hall
  have hgρ : ∀ b : j.ker, ∀ v, ρ (g b) v = v + j v • (b : V) := hg
  let F : Multiplicative ↥j.ker →* Γ :=
    { toFun := fun b => g (Multiplicative.toAdd b)
      map_one' := by
        apply hρinj
        change ρ (g 0) = ρ (1 : Γ)
        rw [MonoidHom.map_one ρ]
        ext v
        change ρ (g 0) v = v
        rw [hgρ]
        simp
      map_mul' := by
        intro b c
        apply hρinj
        change ρ (g (Multiplicative.toAdd b + Multiplicative.toAdd c)) =
          ρ (g (Multiplicative.toAdd b) * g (Multiplicative.toAdd c))
        rw [MonoidHom.map_mul ρ]
        ext v
        change ρ (g (Multiplicative.toAdd b + Multiplicative.toAdd c)) v =
          ρ (g (Multiplicative.toAdd b)) (ρ (g (Multiplicative.toAdd c)) v)
        simp only [hgρ, map_add, map_smul, Submodule.coe_add,
          LinearMap.mem_ker.mp (Multiplicative.toAdd c).property,
          smul_zero, add_zero, smul_add]
        module }
  have hex : ∃ v, j v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hj
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hex
  let v₀ := (j v)⁻¹ • v
  have hv₀ : j v₀ = 1 := by simp [v₀, hv]
  have hFinj : Function.Injective F := by
    intro b c hbc
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    have h := LinearEquiv.congr_fun (congrArg ρ hbc) v₀
    change ρ (g (Multiplicative.toAdd b)) v₀ = ρ (g (Multiplicative.toAdd c)) v₀ at h
    rw [hgρ, hgρ, hv₀, one_smul, one_smul] at h
    exact add_left_cancel h
  have hsurj : Function.Surjective j := fun a => ⟨a • v₀, by simp [hv₀]⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker j
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hdim] at hsum
  have hkerdim : Module.finrank (ZMod 3) ↥j.ker = 2 := by omega
  have hcardD : Nat.card (Multiplicative ↥j.ker) = 9 := by
    change Nat.card ↥j.ker = 9
    rw [← FiniteField.pow_finrank_eq_natCard 3 ↥j.ker, hkerdim]
    norm_num
  have hDcube : ∀ b : Multiplicative ↥j.ker, b ^ 3 = 1 := by
    intro b
    apply Multiplicative.toAdd.injective
    change (3 : ℕ) • (Multiplicative.toAdd b) = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_self, zero_smul]
  let P := F.range
  let f : Multiplicative ↥j.ker → P := fun b => ⟨F b, ⟨b, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro b c hbc
      exact hFinj (congrArg (fun x : P => (x : Γ)) hbc)
    · rintro ⟨x, b, rfl⟩
      exact ⟨b, rfl⟩
  have hcardP : Nat.card P = 9 :=
    (Nat.card_congr (Equiv.ofBijective f hbij)).symm.trans hcardD
  refine ⟨P, hcardP, ?_⟩
  rintro _ ⟨b, rfl⟩
  rw [← map_pow, hDcube, map_one]

theorem false_of_invariant_linearForm_and_kernel_shears
    {E : Type} [Group E] [Finite E] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (M : CoxeterMatrix Λ) (hM : GGIsWeylMatrix M)
    (C : Matrix Λ Λ ℤ) (hC : GGIntCartan M C)
    (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i k, α i (h k) = (C i k : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (Γ : Subgroup (MulAut E)) (hgen : Γ = Subgroup.closure (Set.range φ))
    (hdim : Module.finrank (ZMod 3) V = 3)
    (j : Module.Dual (ZMod 3) V) (hj : j ≠ 0)
    (hinv : ∀ i v, j (ggLin (p := 3) ι (φ i) v) = j v)
    (hall : ∀ b : j.ker, ∃ g : Γ, ∀ v,
      ggLin (p := 3) ι g v = v + j v • (b : V)) : False := by
  obtain ⟨P, hcardP, hcube⟩ := exists_nine_cube_subgroup_of_kernel_shears ι Γ j hj hdim hall
  exact false_of_invariant_linearForm_and_nine_subgroup M hM C hC ι φ h α
    hpair hlin Γ hgen hdim j hj hinv P hcube hcardP

theorem exists_linearForm_of_prime_three_character
    {E H : Type} [Group E] [Group H] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive E ≃+ V) (ν : E →* H) (hH : Nat.card H = 3)
    (hν : ∃ a, ν a ≠ 1) :
    ∃ j : Module.Dual (ZMod 3) V, j ≠ 0 ∧
      (∀ a, j (ι (Additive.ofMul a)) = 0 ↔ ν a = 1) ∧
      ∀ f : MulAut E, (∀ a, ν (f a) = ν a) →
        ∀ v, j (ggLin (p := 3) ι f v) = j v := by
  classical
  have hHA : Nat.card (Additive H) = 3 :=
    (Nat.card_congr (Additive.toMul : Additive H ≃ H)).trans hH
  let κ : Additive H ≃+ ZMod 3 := addEquivOfPrimeCardEq hHA (by simp)
  let a : V →+ ZMod 3 := (κ.toAddMonoidHom.comp ν.toAdditive).comp ι.symm.toAddMonoidHom
  let j : Module.Dual (ZMod 3) V := a.toZModLinearMap 3
  have hspec : ∀ x, j (ι (Additive.ofMul x)) = κ (Additive.ofMul (ν x)) := by
    intro x
    change κ (ν.toAdditive (ι.symm (ι (Additive.ofMul x)))) = κ (Additive.ofMul (ν x))
    simp
  have hkernel : ∀ x, j (ι (Additive.ofMul x)) = 0 ↔ ν x = 1 := by
    intro x
    rw [hspec]
    simp
  have hj : j ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hν
    apply hx
    exact (hkernel x).mp (by rw [hz]; simp)
  refine ⟨j, hj, hkernel, ?_⟩
  intro f hf v
  obtain ⟨x, rfl⟩ : ∃ x, ι (Additive.ofMul x) = v :=
    ⟨Additive.toMul (ι.symm v), by simp⟩
  rw [ggLin_apply_ofMul, hspec, hspec, hf]

theorem card_powQuot_three_of_nontrivial
    {K : Type} [Field K] [Finite K]
    (hne : ∃ u : PGLTor.PowQuot K 3, u ≠ 1) : Nat.card (PGLTor.PowQuot K 3) = 3 := by
  obtain ⟨u, hu⟩ := hne
  have hu3 : u ^ 3 = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    rw [← QuotientGroup.mk_pow, PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨a, rfl⟩
  have hdiv := orderOf_dvd_of_pow_eq_one hu3
  have ho : orderOf u = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with h1 | h3
    · have h := pow_orderOf_eq_one u
      rw [h1, pow_one] at h
      exact (hu h).elim
    · exact h3
  have hd := orderOf_dvd_natCard u
  rw [ho] at hd
  exact Nat.le_antisymm (PGLTor.card_powQuot_le (K := K) (p := 3))
    (Nat.le_of_dvd Nat.card_pos hd)

theorem exists_linearForm_of_cube_class_character
    {K E : Type} [Field K] [Finite K] [Group E] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive E ≃+ V) (ν : E →* PGLTor.PowQuot K 3)
    (hν : ∃ a, ν a ≠ 1) :
    ∃ j : Module.Dual (ZMod 3) V, j ≠ 0 ∧
      (∀ a, j (ι (Additive.ofMul a)) = 0 ↔ ν a = 1) ∧
      ∀ f : MulAut E, (∀ a, ν (f a) = ν a) →
        ∀ v, j (ggLin (p := 3) ι f v) = j v :=
  exists_linearForm_of_prime_three_character ι ν
    (card_powQuot_three_of_nontrivial (by obtain ⟨a, ha⟩ := hν; exact ⟨ν a, ha⟩)) hν

theorem false_of_power_class_kernel_moves
    {K E : Type} [Field K] [Finite K] [Group E] [Finite E] [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (M : CoxeterMatrix Λ) (hM : GGIsWeylMatrix M)
    (C : Matrix Λ Λ ℤ) (hC : GGIntCartan M C)
    (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (Γ : Subgroup (MulAut E)) (hgen : Γ = Subgroup.closure (Set.range φ))
    (hdim : Module.finrank (ZMod 3) V = 3)
    (ν : E →* PGLTor.PowQuot K 3) (a₀ : E) (hνa₀ : ν a₀ ≠ 1)
    (hνinv : ∀ f ∈ Γ, ∀ a, ν (f a) = ν a)
    (hall : ∀ b : ν.ker, ∃ t : Γ,
      (∀ a : E, ν a = 1 → (t : MulAut E) a = a) ∧
        (t : MulAut E) a₀ = a₀ * (b : E)) : False := by
  obtain ⟨j₀, -, hj₀ker, hj₀inv⟩ :=
    exists_linearForm_of_cube_class_character ι ν ⟨a₀, hνa₀⟩
  let v₀ : V := ι (Additive.ofMul a₀)
  have hv₀ : j₀ v₀ ≠ 0 := fun hz => hνa₀ ((hj₀ker a₀).mp hz)
  let j : Module.Dual (ZMod 3) V := (j₀ v₀)⁻¹ • j₀
  have hjv₀ : j v₀ = 1 := by simp [j, hv₀, smul_eq_mul]
  have hj : j ≠ 0 := by
    intro hz
    rw [hz] at hjv₀
    simp at hjv₀
  have hjker : ∀ a, j (ι (Additive.ofMul a)) = 0 ↔ ν a = 1 := by
    intro a
    change (j₀ v₀)⁻¹ * j₀ (ι (Additive.ofMul a)) = 0 ↔ ν a = 1
    simpa only [mul_eq_zero, inv_ne_zero hv₀, false_or] using hj₀ker a
  have hjinv : ∀ f ∈ Γ, ∀ v, j (ggLin (p := 3) ι f v) = j v := by
    intro f hf v
    change (j₀ v₀)⁻¹ • j₀ (ggLin (p := 3) ι f v) = (j₀ v₀)⁻¹ • j₀ v
    rw [hj₀inv f (hνinv f hf)]
  have hshear : ∀ b : j.ker, ∃ t : Γ, ∀ v,
      ggLin (p := 3) ι t v = v + j v • (b : V) := by
    intro b
    let a : E := Additive.toMul (ι.symm (b : V))
    have hba : ι (Additive.ofMul a) = (b : V) := by simp [a]
    have hνa : ν a = 1 := (hjker a).mp (by rw [hba]; exact b.property)
    obtain ⟨t, htfix, htmove⟩ := hall ⟨a, hνa⟩
    have htker : ∀ w, j w = 0 → ggLin (p := 3) ι t w = w := by
      intro w hw
      obtain ⟨x, rfl⟩ : ∃ x, ι (Additive.ofMul x) = w :=
        ⟨Additive.toMul (ι.symm w), by simp⟩
      rw [ggLin_apply_ofMul, htfix x ((hjker x).mp hw)]
    have htv₀ : ggLin (p := 3) ι t v₀ = v₀ + (b : V) := by
      change ggLin (p := 3) ι t (ι (Additive.ofMul a₀)) = _
      rw [ggLin_apply_ofMul, htmove]
      change ι (Additive.ofMul a₀ + Additive.ofMul a) = v₀ + (b : V)
      rw [map_add, hba]
    refine ⟨t, fun v => ?_⟩
    let w := v - j v • v₀
    have hw : j w = 0 := by
      change j (v - j v • v₀) = 0
      rw [map_sub, map_smul, hjv₀]
      simp [smul_eq_mul]
    calc
      ggLin (p := 3) ι t v = ggLin (p := 3) ι t w + j v • ggLin (p := 3) ι t v₀ := by
        rw [← map_smul, ← map_add]
        congr 1
        dsimp [w]
        module
      _ = w + j v • (v₀ + (b : V)) := by rw [htker w hw, htv₀]
      _ = v + j v • (b : V) := by dsimp [w]; module
  apply false_of_invariant_linearForm_and_kernel_shears M hM C hC ι φ h α
    hpair hlin Γ hgen hdim j hj
  · intro i v
    apply hjinv (φ i) _ v
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  · exact hshear

theorem false_of_nonsplit_lift_of_kernel_normalizers
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {K : Type} [Field K] [Finite K] {R : Type} [Group R]
    {N S : Subgroup (GL κ K)} {c : N →* MulAut R}
    (hc : QuotMove.IsScalarQuot c S)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ z : N, ∀ l : L', c z (ψ l) = ψ (a l))
    (hcardA : Nat.card A = 27)
    {x₀ : N} (hx₀ : c x₀ ∈ inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : (x₀ : GL κ K) ^ 3 = GeneralLinearGroup.scalar κ l₀)
    (hl₀ : ∀ μ : Kˣ, μ ^ 3 ≠ l₀)
    (hall : ∀ z : N, c z ∈ inducedSub ψ A → (z : GL κ K) ^ 3 = 1 →
      ∃ E : S,
        (∀ y : N, c y ∈ inducedSub ψ A → (y : GL κ K) ^ 3 = 1 →
          (E : GL κ K) * y * (E : GL κ K)⁻¹ = y) ∧
        (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ = (x₀ : GL κ K) * z)
    [Fact (Nat.Prime 3)] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (M : CoxeterMatrix Λ) (hM : GGIsWeylMatrix M)
    (C : Matrix Λ Λ ℤ) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) DFunLike.coe_injective
  have : Finite V := Finite.of_injective ι.symm ι.symm.injective
  obtain ⟨ν, hspec, hνker, hνinv⟩ :=
    QuotMove.exists_power_class_character hc (by decide) (by decide) hψ hA hAI
  obtain ⟨a₀v, ha₀v, ha₀⟩ := mem_inducedSub.mp hx₀
  let a₀ : ↥A := ⟨a₀v, ha₀v⟩
  have hνa₀ : ν a₀ ≠ 1 := by
    rw [hspec a₀ x₀ l₀ ha₀ hx₀p]
    intro hz
    obtain ⟨μ, hμ⟩ := PGLTor.powQuot_mk_eq_one_iff.mp hz
    exact hl₀ μ hμ
  have hcardV : Nat.card V = 27 := by
    calc Nat.card V = Nat.card (Additive ↥A) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card A := Nat.card_congr (Additive.toMul : Additive ↥A ≃ ↥A)
      _ = 27 := hcardA
  have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 3 := by
    simpa using (FiniteField.pow_finrank_eq_natCard 3 V).trans hcardV
  have hdim : Module.finrank (ZMod 3) V = 3 := Nat.le_antisymm
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp hpow.le)
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp hpow.ge)
  let Γ := ggAutomizer (MulAut.conj : L' →* MulAut L').range A
  apply false_of_power_class_kernel_moves M hM C hC ι φ h α hpair hlin Γ hgen hdim
    ν a₀ hνa₀ hνinv
  intro b
  obtain ⟨z, hzact, hz3⟩ := (hνker (b : ↥A)).mp b.property
  have hzX : c z ∈ inducedSub ψ A := mem_inducedSub.mpr ⟨b, b.1.2, hzact⟩
  obtain ⟨E, hEfix, hEmove⟩ := hall z hzX hz3
  let E' : N := Subgroup.inclusion hc.le E
  have hfix : ∀ y : N, c y ∈ inducedSub ψ A → (y : GL κ K) ^ 3 = 1 →
      E' * y * E'⁻¹ = y := fun y hy hy3 => Subtype.ext (hEfix y hy hy3)
  have hmove : E' * x₀ * E'⁻¹ = x₀ * z := Subtype.ext hEmove
  let δ : N := x₀ * z * x₀⁻¹
  have hδX : c δ ∈ inducedSub ψ A := by
    change c (x₀ * z * x₀⁻¹) ∈ inducedSub ψ A
    rw [map_mul, map_mul, map_inv]
    exact (inducedSub ψ A).mul_mem ((inducedSub ψ A).mul_mem hx₀ hzX)
      ((inducedSub ψ A).inv_mem hx₀)
  have hEx : (E' : GL κ K) * x₀ * (E' : GL κ K)⁻¹ = (δ : GL κ K) * x₀ := by
    change (E : GL κ K) * x₀ * (E : GL κ K)⁻¹ =
      ((x₀ : GL κ K) * z * (x₀ : GL κ K)⁻¹) * x₀
    rw [hEmove]
    group
  have hEy : ∀ y : N, c y ∈ inducedSub ψ A → (y : GL κ K) ^ 3 = 1 →
      (E' : GL κ K) * y = y * E' := by
    intro y hy hy3
    have h : E' * y = y * E' := by
      calc E' * y = (E' * y * E'⁻¹) * E' := by group
        _ = y * E' := by rw [hfix y hy hy3]
    exact congrArg (fun v : N => (v : GL κ K)) h
  have hEN : ∀ y : N, c y ∈ inducedSub ψ A →
      c (E' * y * E'⁻¹) ∈ inducedSub ψ A := by
    intro y hy
    have h := QuotMove.conj_mem_inducedSub_of_commute_order_p hc (by decide) (by decide)
      hψ hA hAI hx₀ hx₀p hl₀ E' δ hδX hEx hEy (c y) hy
    simpa only [map_mul, map_inv] using h
  have hlift : ∀ a : ↥A, ∃ B : N, ∀ l, c B (ψ l) = ψ ((a : MulAut L') l) :=
    fun a => hAI a a.2
  choose B hB using hlift
  have hBperm : ∀ a : ↥A, ∃ a' : ↥A, ∃ u : Kˣ,
      (E : GL κ K) * B a * (E : GL κ K)⁻¹ = GeneralLinearGroup.scalar κ u * B a' := by
    intro a
    obtain ⟨a', ha', hact⟩ := mem_inducedSub.mp
      (hEN (B a) (mem_inducedSub.mpr ⟨a, a.2, hB a⟩))
    obtain ⟨u, hu⟩ := hc.exists_scalar_mul_of_eq (M := E' * B a * E'⁻¹)
      (M' := B ⟨a', ha'⟩) (induced_unique ψ hψ hact (hB ⟨a', ha'⟩))
    exact ⟨⟨a', ha'⟩, u, hu⟩
  obtain ⟨n, hcn, hnN, -⟩ :=
    QuotMove.exists_inner_of_permuting_lifts hc hψ hker hperf B hB E hBperm
  have hact : ∀ (a a' : ↥A) (y y' : N),
      (∀ l, c y (ψ l) = ψ ((a : MulAut L') l)) →
      (∀ l, c y' (ψ l) = ψ ((a' : MulAut L') l)) →
      c (E' * y * E'⁻¹) = c y' →
      MulAut.conj n * (a : MulAut L') * (MulAut.conj n)⁻¹ = (a' : MulAut L') := by
    intro a a' y y' hya hya' hyy'
    apply mulAut_eq_of_forall ψ hker hperf
    intro l
    rw [← conj_induced_apply ψ hya n l, hcn]
    have heq : c E' * c y * (c E')⁻¹ = c (E' * y * E'⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [heq, hyy', hya']
  let t : Γ := ⟨ggConjAut A hnN,
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hnN⟩
  refine ⟨t, ?_, ?_⟩
  · intro a ha
    obtain ⟨y, hya, hy3⟩ := (hνker a).mp ha
    have hyX : c y ∈ inducedSub ψ A := mem_inducedSub.mpr ⟨a, a.2, hya⟩
    apply Subtype.ext
    change ((ggConjAut A hnN) a : MulAut L') = _
    rw [ggConjAut_apply]
    exact hact a a y y hya hya (by rw [hfix y hyX hy3])
  · have hprod : ∀ l, c (x₀ * z) (ψ l) = ψ (((a₀ * (b : ↥A) : ↥A) : MulAut L') l) := by
      intro l
      rw [map_mul, MulAut.mul_apply, hzact, ha₀]
      rfl
    apply Subtype.ext
    change ((ggConjAut A hnN) a₀ : MulAut L') = _
    rw [ggConjAut_apply]
    exact hact a₀ (a₀ * (b : ↥A)) x₀ (x₀ * z) ha₀ hprod (by rw [hmove])

theorem false_of_nonsplit_lift_nine_three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* projectiveSL 9 K}
    {A : Subgroup (MulAut L')}
    (h3 : 3 ∣ Nat.card K - 1) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ f ∈ Set.range (conjAut 9 K), ∀ l, f (ψ l) = ψ (a l))
    (hcardA : Nat.card A = 27)
    (hcent : ∀ y ∈ (inducedSub ψ A).comap (conjAut 9 K), y ^ 3 = 1 →
      ∀ x ∈ (inducedSub ψ A).comap (conjAut 9 K), x * y = y * x)
    {x₀ : GL (Fin 9) K} (hx₀ : conjAut 9 K x₀ ∈ inducedSub ψ A) {l₀ : Kˣ}
    (hx₀p : x₀ ^ 3 = GeneralLinearGroup.scalar (Fin 9) l₀)
    (hl₀ : ∀ μ : Kˣ, μ ^ 3 ≠ l₀)
    [Fact (Nat.Prime 3)] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (M : CoxeterMatrix Λ) (hM : GGIsWeylMatrix M)
    (C : Matrix Λ Λ ℤ) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  let T := (⊤ : Subgroup (GL (Fin 9) K))
  let c := (conjAut 9 K).comp T.subtype
  let S := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 9) K →* GL (Fin 9) K).range
  have hc : QuotMove.IsScalarQuot c S := QuotMove.isScalarQuot_PSL (by decide)
  let x : T := ⟨x₀, Subgroup.mem_top _⟩
  have hAI' : ∀ a ∈ A, ∃ y : T, ∀ l, c y (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨f, ⟨y, rfl⟩, hfa⟩ := hAI a ha
    exact ⟨⟨y, Subgroup.mem_top _⟩, hfa⟩
  let G := (inducedSub ψ A).comap (conjAut 9 K)
  have hdecomp : ∀ Y ∈ G, ∃ (s : Kˣ) (y : T) (k : ℕ),
      (y : GL (Fin 9) K) ∈ G ∧ (y : GL (Fin 9) K) ^ 3 = 1 ∧
      Y = GeneralLinearGroup.scalar (Fin 9) s * y * x₀ ^ k := by
    intro Y hY
    exact QuotMove.exists_decomp_of_class hc (by decide) (by decide) hψ hA
      (x₀ := x) hx₀ hx₀p hl₀ (M := ⟨Y, Subgroup.mem_top _⟩) hY
  have hXcomm : ∀ Y ∈ G, Commute x₀ Y := by
    intro Y hY
    obtain ⟨s, y, k, hy, hy3, hfac⟩ := hdecomp Y hY
    rw [hfac]
    exact ((PGLTor.commute_scalar s x₀).symm.mul_right (hcent y hy hy3 x₀ hx₀)).mul_right
      ((Commute.refl x₀).pow_right k)
  have hcomm : ∀ Y ∈ G, ∀ Z ∈ G, Y * Z = Z * Y := by
    intro Y hY Z hZ
    obtain ⟨s, y, k, hy, hy3, hfac⟩ := hdecomp Z hZ
    rw [hfac]
    exact (((PGLTor.commute_scalar s Y).symm.mul_right (hcent y hy hy3 Y hY)).mul_right
      ((hXcomm Y hY).symm.pow_right k)).eq
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL 9 K))) :
      Set (MulAut (projectiveSL 9 K))) ⊆ Set.range (conjAut 9 K) := by
    rintro f ⟨a, ha, hfa⟩
    obtain ⟨g, hg, hga⟩ := hAI a ha
    exact induced_unique ψ hψ hga hfa ▸ hg
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨f, -, hfa⟩ := hAI a ha
      exact ⟨f, hfa⟩)
  have hcardG : Nat.card G = 27 * (Nat.card K - 1) := by
    change Nat.card ((inducedSub ψ A).comap (conjAut 9 K)) = _
    rw [card_comap_eq (by decide : 0 < 9) hXI, hcardX, hcardA]
  have hcastG : (Nat.card G : K) ≠ 0 := by
    let : Fintype K := Fintype.ofFinite K
    have hKcast : (Nat.card K : K) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero (K := K)
    have hKmod := Nat.mod_eq_zero_of_dvd
      ((CharP.cast_eq_zero_iff K 2 (Nat.card K)).mp hKcast)
    have hKpos := Finite.one_lt_card (α := K)
    have hGmod : Nat.card G % 2 = 1 := by rw [hcardG]; omega
    intro hz
    have hzero := Nat.mod_eq_zero_of_dvd ((CharP.cast_eq_zero_iff K 2 (Nat.card G)).mp hz)
    omega
  apply false_of_nonsplit_lift_of_kernel_normalizers hc hψ hker hperf hA hAI' hcardA
    (x₀ := x) hx₀ hx₀p hl₀ _ M hM C hC ι φ h α hpair hlin hgen
  intro z hz hz3
  obtain ⟨E, hdet, hfix, hmove⟩ := PGLTor.exists_cubic_kernel_normalizer h3 hcomm hcastG
    hx₀ hz hx₀p hl₀ hz3
  have hES : E ∈ S :=
    ⟨⟨(E : Matrix (Fin 9) (Fin 9) K), hdet⟩, Units.ext rfl⟩
  refine ⟨⟨E, hES⟩, ?_, ?_⟩
  · intro y hy hy3
    exact hfix y hy hy3
  · exact hmove

theorem false_of_noncomm_lifts_nine_three
    {K : Type} [Field K] [Finite K] {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL 9 K} {A : Subgroup (MulAut L')}
    (hpK : 3 ∣ Nat.card K - 1) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut 9 K), ∀ l : L', φ (ψ l) = ψ (a l))
    {x₀ y₀ : GL (Fin 9) K} (hx₀ : conjAut 9 K x₀ ∈ inducedSub ψ A)
    (hy₀ : conjAut 9 K y₀ ∈ inducedSub ψ A) (hx₀p : x₀ ^ 3 = 1) {u₀ : Kˣ}
    (hu₀ : x₀ * y₀ = GeneralLinearGroup.scalar (Fin 9) u₀ * (y₀ * x₀))
    (hu₀1 : u₀ ≠ 1) (hu₀p : u₀ ^ 3 = 1)
    [Fact (Nat.Prime 3)] {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  obtain ⟨ζ₀, hζ₀⟩ := PGLTor.exists_isPrimitiveRoot_of_dvd (by decide : Nat.Prime 3) hpK
  let ζ : Kˣ := (hζ₀.isUnit (by decide : 3 ≠ 0)).unit
  have hζ : IsPrimitiveRoot ζ 3 := by
    rw [← IsPrimitiveRoot.coe_units_iff, IsUnit.unit_spec]
    exact hζ₀
  obtain ⟨D, hdet, hDact⟩ := PGLTor.exists_quadPhase_three_of_nine_dvd
    (by simp) hζ hx₀p hu₀1 hu₀p hu₀
  let Ds : SpecialLinearGroup (Fin 9) K := ⟨(D : Matrix (Fin 9) (Fin 9) K), hdet⟩
  have hDsGL : SpecialLinearGroup.toGL Ds = D := Units.ext rfl
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have huK : (u₀ : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hu₀p
  obtain ⟨k, -, hkK⟩ := hζK.eq_pow_of_pow_eq_one huK
  have hk : ζ ^ k = u₀ := Units.ext (by simpa using hkK)
  have hk0 : ¬ 3 ∣ k := by
    rintro ⟨j, rfl⟩
    apply hu₀1
    rw [← hk, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨cE, hcE⟩ := hDact y₀ k (by rw [hk]; exact hu₀)
  refine false_of_normalizing_move (by decide) hpK (by decide) (by decide)
    hψ hker hperf hA hAI hx₀ hy₀ hu₀ hu₀1 Ds ?_ hk0
    (by rw [hDsGL]; exact hcE) ι φ h α hdiag hlin hgen
  intro g hg
  obtain ⟨m, hm⟩ := exists_comm_pow_of_mem (by decide) (by decide) (by decide)
    hψ hA hζ hx₀ hg
  obtain ⟨c, hc⟩ := hDact g m hm
  rw [hDsGL, hc, map_mul, conjAut_scalar, one_mul, map_mul, map_pow]
  exact Subgroup.mul_mem _ hg (Subgroup.pow_mem _ hx₀ _)

theorem order_three_lifts_central_of_datum
    {K : Type} [Field K] [Finite K] {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL 9 K} {A : Subgroup (MulAut L')}
    (hpK : 3 ∣ Nat.card K - 1) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut 9 K), ∀ l : L', φ (ψ l) = ψ (a l))
    [Fact (Nat.Prime 3)] {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) :
    ∀ x ∈ (inducedSub ψ A).comap (conjAut 9 K), x ^ 3 = 1 →
      ∀ y ∈ (inducedSub ψ A).comap (conjAut 9 K), y * x = x * y := by
  intro x hx hx3 y hy
  by_contra hne
  have hG := isProjElem_comap (by decide : 0 < 9) (isElemAbelian_inducedSub hψ hA)
  have hu1 : PGLTor.commChar hG hx ⟨y, hy⟩ ≠ 1 := fun h1 =>
    hne ((PGLTor.commChar_eq_one_iff hG hx ⟨y, hy⟩).mp h1).symm
  exact false_of_noncomm_lifts_nine_three hpK hψ hker hperf hA hAI hx hy hx3
    (PGLTor.commChar_spec hG hx ⟨y, hy⟩) hu1
    (PGLTor.commChar_pow_eq_one hG hx ⟨y, hy⟩) ι φ h α hdiag hlin hgen

theorem isToral_or_card_eq_twenty_seven_of_datum
    {K : Type} [Field K] [Finite K] {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL 9 K} {A : Subgroup (MulAut L')}
    (hpK : 3 ∣ Nat.card K - 1) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut 9 K), ∀ l : L', φ (ψ l) = ψ (a l))
    (h3 : 3 ^ 3 ≤ Nat.card A)
    [Fact (Nat.Prime 3)] {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) :
    PGLTor.IsToral ((inducedSub ψ A).comap (conjAut 9 K)) ∨ Nat.card A = 27 := by
  classical
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL 9 K))) :
      Set (MulAut (projectiveSL 9 K))) ⊆ Set.range (conjAut 9 K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (inducedSub ψ A) = Nat.card A :=
    card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hcardG : Nat.card ((inducedSub ψ A).comap (conjAut 9 K)) =
      Nat.card A * (Nat.card K - 1) := by
    rw [card_comap_eq (by decide : 0 < 9) hXI, hcardX]
  have hG := isProjElem_comap (by decide : 0 < 9) (isElemAbelian_inducedSub hψ hA)
  have hcent := order_three_lifts_central_of_datum hpK hψ hker hperf hA hAI
    ι φ h α hdiag hlin hgen
  rcases PGLTor.toral_or_card_le_of_central_sharp (by decide) (by decide) hpK hG hcent with
    htor | hle
  · exact Or.inl htor
  · refine Or.inr ?_
    rw [hcardG, Fintype.card_fin] at hle
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    have hu := Nat.le_of_mul_le_mul_right hle hK1
    norm_num at hu h3
    omega

theorem ggTorusWNormSC_nine_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpK : 3 ∣ Nat.card K - 1) :
    GGTorusWNormSC 3 (projectiveSL 9 K) (Set.range (conjAut 9 K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    hM hC hpair hlin hgen s hs
  classical
  let G := (inducedSub ψ A).comap (conjAut 9 K)
  have hG : PGLTor.IsProjElem 3 G :=
    isProjElem_comap (by decide : 0 < 9) (isElemAbelian_inducedSub hψ hA)
  have hdiag : ∀ i, α i (h i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
  by_cases htor : PGLTor.IsToral G
  · obtain ⟨A₀, hA₀⟩ := htor
    have hperfSL : commutator (SpecialLinearGroup (Fin 9) K) = ⊤ :=
      (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 9) (by decide)
        (Or.inl (by decide))).commutator_eq_top
    obtain ⟨π, hπs, hπker, hacts⟩ := TypeANbrDvd.exists_actsDiag_model hperfSL
      (slHasSections_of_five_le (by decide : 5 ≤ 9)) hψ hker hperf hAI
      (A₀ := A₀) fun B hB => hA₀ B hB
    exact ggWNormConcl_of_linear_diagonal (by decide) (by decide) hpK (by decide)
      hπs hπker hA h3 hsc hacts hM hC ι φ h α hpair hlin hgen hs
  · have hcardA : Nat.card A = 27 :=
      (isToral_or_card_eq_twenty_seven_of_datum hpK hψ hker hperf hA hAI h3
        ι φ h α hdiag hlin hgen).resolve_left htor
    have hcent := order_three_lifts_central_of_datum hpK hψ hker hperf hA hAI
      ι φ h α hdiag hlin hgen
    have hn : ¬ ∀ x ∈ G, ∃ c : Kˣ,
        x ^ 3 = GeneralLinearGroup.scalar (Fin 9) (c ^ 3) := fun hall =>
      htor (PGLTor.isToral_of_central_cube hpK hG hcent hall)
    push Not at hn
    obtain ⟨x₀, hx₀, hbad⟩ := hn
    obtain ⟨l₀, hx₀p⟩ := hG.pow_scalar x₀ hx₀
    have hl₀ : ∀ μ : Kˣ, μ ^ 3 ≠ l₀ := fun μ hμ => hbad μ (by rw [hx₀p, hμ])
    exact (false_of_nonsplit_lift_nine_three hpK hψ hker hperf hA hAI hcardA hcent
      hx₀ hx₀p hl₀ M hM C hC ι φ h α hpair hlin hgen).elim

end CFSG.StandardType.TypeA

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix

theorem ggTorusWNormSC_linear_nine_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpK : 3 ∣ Nat.card K - 1) :
    GGTorusWNormSC 3 (LargeEvenProj (LargeEvenSLGroup (Fin 9) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) :=
  ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv 9 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_nine_three hpK)

theorem largeEvenLabelAll_wnorm_linear_nine_three {lab : LargeEvenLabel}
    (ht : lab.tag = .A) (hd : lab.rank + 1 = 9) (hpq : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC 3 R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hd hpq ⊢
  subst tag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ GGTorusWNormSC 3 R I)
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  have hr : r = 8 := by omega
  subst r
  exact ggTorusWNormSC_linear_nine_three (by rwa [hK])

end CFSG.StandardType
