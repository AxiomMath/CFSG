module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Module Polynomial

private theorem twslr_split_torus {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ℓ : ℕ} [NeZero ℓ] {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    {ι : Type} [Finite ι] (f : ι → Module.End K V)
    (hfc : ∀ i j, Commute (f i) (f j)) (hfp : ∀ i, f i ^ ℓ = 1) :
    ∃ S : Set (Module.End K V), (∀ x ∈ S, ∀ y ∈ S, Commute x y) ∧ (∀ x ∈ S, x ^ ℓ = 1) ∧
      (∀ x ∈ S, ∀ i, Commute x (f i)) ∧ ℓ ^ (finrank K V) ≤ Nat.card S := by
  classical
  obtain ⟨b, μ, hb⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ f hfc hfp
  let D : (Fin (finrank K V) → rootsOfUnity ℓ K) → Module.End K V := fun c =>
    b.constr K fun j => ((c j : Kˣ) : K) • b j
  have hDapp : ∀ c (j : Fin (finrank K V)), D c (b j) = ((c j : Kˣ) : K) • b j :=
    fun c j => Basis.constr_basis b K _ j
  have hpow : ∀ c (k : ℕ) (j : Fin (finrank K V)),
      (D c ^ k) (b j) = (((c j : Kˣ) : K) ^ k) • b j := by
    intro c k
    induction k with
    | zero => intro j; rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
    | succ k ih =>
      intro j
      rw [pow_succ, Module.End.mul_apply, hDapp c j, map_smul, ih]
      simp only [smul_smul, pow_succ, mul_comm]
  have hDpow : ∀ c, D c ^ ℓ = 1 := by
    intro c
    refine b.ext fun j => ?_
    rw [hpow c ℓ j, ← Units.val_pow_eq_pow_val, (c j).2, Units.val_one, one_smul,
      Module.End.one_apply]
  have hDinj : Function.Injective D := by
    intro c c' hcc
    funext j
    have h1 := congrArg (fun x : Module.End K V => x (b j)) hcc
    rw [hDapp, hDapp] at h1
    have h2 : (((c j : Kˣ) : K) - ((c' j : Kˣ) : K)) • b j = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 : ((c j : Kˣ) : K) - ((c' j : Kˣ) : K) = 0 :=
      (smul_eq_zero.mp h2).resolve_right (b.ne_zero j)
    exact Subtype.ext (Units.ext (sub_eq_zero.mp h3))
  refine ⟨Set.range D, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    refine b.ext fun j => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hDapp c' j, map_smul, hDapp c j,
      map_smul, hDapp c' j]
    simp only [smul_smul, mul_comm]
  · rintro _ ⟨c, rfl⟩
    exact hDpow c
  · rintro _ ⟨c, rfl⟩ i
    refine b.ext fun j => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hb i j, map_smul, hDapp c j,
      map_smul, hb i j]
    simp only [smul_smul, mul_comm]
  · rw [Nat.card_range_of_injective hDinj, Nat.card_fun, Nat.card_fin, hζ.card_rootsOfUnity]

private theorem twslr_exists_card_ge_pow_ordQ_family {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓK : (ℓ : K) ≠ 0) {ι : Type} [Finite ι] (f : ι → Module.End K V)
    (hfc : ∀ i j, Commute (f i) (f j)) (hfp : ∀ i, f i ^ ℓ = 1) :
    ∃ S : Set (Module.End K V), (∀ x ∈ S, ∀ y ∈ S, Commute x y) ∧ (∀ x ∈ S, x ^ ℓ = 1) ∧
      (∀ x ∈ S, ∀ i, Commute x (f i)) ∧
      ℓ ^ (finrank K V / OrdPNS.ordQ K ℓ) ≤ Nat.card S := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  induction hn : finrank K V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases hlt : n < OrdPNS.ordQ K ℓ
  · refine ⟨{1}, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
    · intro x hx
      rw [Set.mem_singleton_iff.mp hx, one_pow]
    · intro x hx i
      rw [Set.mem_singleton_iff.mp hx]
      exact Commute.one_left _
    · rw [Nat.div_eq_of_lt hlt, pow_zero, Nat.card_unique]
  by_cases hall : ∀ i, f i = 1
  · obtain ⟨S, hSc, hSp, hSA, hScard⟩ :=
      OrdPNS.exists_card_ge_pow_ordQ hℓ hℓK (1 : Module.End K V) (one_pow ℓ)
    exact ⟨S, hSc, hSp, fun x hx i => by rw [hall i]; exact hSA x hx, by rw [← hn]; exact hScard⟩
  · simp only [not_forall] at hall
    obtain ⟨i0, hi0⟩ := hall
    have hep : f i0 ^ ℓ = 1 := hfp i0
    have he1 : f i0 ≠ 1 := hi0
    obtain ⟨g, hg, hgd, hker⟩ := OrdPNS.exists_irreducible_ker_ne_bot hℓ hep he1
    obtain ⟨h, hcompl, hgh⟩ := OrdPNS.isCompl_ker_aeval hℓ hℓK hep hg hgd
    set V₁ : Submodule K V := LinearMap.ker (aeval (f i0) g) with hV₁
    set V₂ : Submodule K V := LinearMap.ker (aeval (f i0) h) with hV₂
    have hm₁ : ∀ i, ∀ v ∈ V₁, f i v ∈ V₁ := fun i => OrdPNS.mapsTo_ker_aeval (hfc i0 i) g
    have hm₂ : ∀ i, ∀ v ∈ V₂, f i v ∈ V₂ := fun i => OrdPNS.mapsTo_ker_aeval (hfc i0 i) h
    have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
    have hpos : 0 < finrank K V₁ :=
      Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.mp h0)
    have hlt₂ : finrank K V₂ < n := by rw [← hn]; omega
    haveI : Fact (Irreducible g) := ⟨hg⟩
    have hg0 : g ≠ 0 := hg.ne_zero
    let e₁ : Module.End K V₁ := (f i0).restrict (hm₁ i0)
    have hge : aeval e₁ g = 0 := LinearMap.ext fun w => Subtype.ext (by
      rw [OrdPNS.coe_aeval_restrict_apply]
      exact w.2)
    let φ : AdjoinRoot g →ₐ[K] Module.End K V₁ :=
      Ideal.Quotient.liftₐ (Ideal.span {g}) (aeval e₁) (fun a ha => by
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, hge, mul_zero])
    letI : Module (AdjoinRoot g) V₁ := Module.compHom V₁ φ.toRingHom
    have hsmul : ∀ (l : AdjoinRoot g) (v : V₁), l • v = φ l v := fun _ _ => rfl
    have : IsScalarTower K (AdjoinRoot g) V₁ := ⟨fun a l v => by
      rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
    have : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
    have : Module.Finite (AdjoinRoot g) V₁ :=
      Module.Finite.of_restrictScalars_finite K (AdjoinRoot g) V₁
    have hcommφ : ∀ x : Module.End K V₁, Commute x e₁ → ∀ l, Commute x (φ l) := by
      intro x hx l
      obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective l
      have hφmk : φ (AdjoinRoot.mk g P) = aeval e₁ P := rfl
      rw [hφmk]
      exact (OrdPNS.commute_aeval hx.symm P).symm
    let toL : ∀ x : Module.End K V₁, Commute x e₁ → Module.End (AdjoinRoot g) V₁ :=
      fun x hx =>
        { toFun := x
          map_add' := x.map_add
          map_smul' := fun l v => by
            rw [hsmul, hsmul, RingHom.id_apply, ← Module.End.mul_apply,
              (hcommφ x hx l).eq, Module.End.mul_apply] }
    have hcomm_e₁ : ∀ i, Commute ((f i).restrict (hm₁ i)) e₁ :=
      fun i => OrdPNS.restrict_commute' (hfc i i0) (hm₁ i) (hm₁ i0)
    let g' : ι → Module.End (AdjoinRoot g) V₁ := fun i => toL _ (hcomm_e₁ i)
    have hg'c : ∀ i j, Commute (g' i) (g' j) := by
      intro i j
      have hK : Commute ((f i).restrict (hm₁ i)) ((f j).restrict (hm₁ j)) :=
        OrdPNS.restrict_commute' (hfc i j) (hm₁ i) (hm₁ j)
      exact LinearMap.ext fun v => LinearMap.congr_fun hK.eq v
    have hg'p : ∀ i, g' i ^ ℓ = 1 := by
      intro i
      refine LinearMap.ext fun v => ?_
      rw [Module.End.pow_apply, Module.End.one_apply]
      have h1 := LinearMap.congr_fun (OrdPNS.restrict_pow_eq_one (hfp i) (hm₁ i)) v
      rw [Module.End.pow_apply, Module.End.one_apply] at h1
      exact h1
    have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := by
      haveI : NeZero (ℓ : AdjoinRoot g) := by
        refine ⟨fun h0 => hℓK ?_⟩
        have h1 : algebraMap K (AdjoinRoot g) (ℓ : K) = 0 := by rw [map_natCast]; exact h0
        exact (injective_iff_map_eq_zero _).mp (algebraMap K (AdjoinRoot g)).injective _ h1
      rw [← isRoot_cyclotomic_iff]
      have h1 := (AdjoinRoot.isRoot_root g).dvd (map_dvd (AdjoinRoot.of g) hgd)
      rwa [map_cyclotomic] at h1
    obtain ⟨S_L, hS_Lc, hS_Lp, hS_Lcen, hS_Lcard⟩ :=
      twslr_split_torus (K := AdjoinRoot g) hζ g' hg'c hg'p
    let rs : Module.End (AdjoinRoot g) V₁ → Module.End K V₁ := LinearMap.restrictScalars K
    let T₁ : Set (Module.End K V₁) := rs '' S_L
    have hrs_apply : ∀ (a : Module.End (AdjoinRoot g) V₁) (v : V₁), rs a v = a v :=
      fun a v => LinearMap.restrictScalars_apply K a v
    have hrs_one : rs 1 = 1 := LinearMap.ext fun v => rfl
    have hrs_mul : ∀ a b : Module.End (AdjoinRoot g) V₁, rs (a * b) = rs a * rs b :=
      fun a b => LinearMap.ext fun v => rfl
    have hrs_pow : ∀ (a : Module.End (AdjoinRoot g) V₁) (k : ℕ), rs (a ^ k) = (rs a) ^ k := by
      intro a k
      induction k with
      | zero => rw [pow_zero, pow_zero, hrs_one]
      | succ k ih => rw [pow_succ, hrs_mul, ih, pow_succ]
    have hrs_inj : Function.Injective rs := by
      intro a b hab
      refine LinearMap.ext fun v => ?_
      have h := congrArg (fun x : Module.End K V₁ => x v) hab
      rwa [hrs_apply, hrs_apply] at h
    have hgi : ∀ i, rs (g' i) = (f i).restrict (hm₁ i) := fun i => rfl
    have hT₁c : ∀ x ∈ T₁, ∀ y ∈ T₁, Commute x y := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      change rs a * rs b = rs b * rs a
      rw [← hrs_mul, ← hrs_mul, (hS_Lc a ha b hb).eq]
    have hT₁p : ∀ x ∈ T₁, x ^ ℓ = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      rw [← hrs_pow, hS_Lp a ha, hrs_one]
    have hT₁cen : ∀ x ∈ T₁, ∀ i, Commute x ((f i).restrict (hm₁ i)) := by
      rintro _ ⟨a, ha, rfl⟩ i
      rw [← hgi i]
      change rs a * rs (g' i) = rs (g' i) * rs a
      rw [← hrs_mul, ← hrs_mul, (hS_Lcen a ha i).eq]
    have hT₁card : ℓ ^ (finrank (AdjoinRoot g) V₁) ≤ Nat.card T₁ := by
      rw [Nat.card_image_of_injective hrs_inj]
      exact hS_Lcard
    obtain ⟨T₂, hT₂c, hT₂p, hT₂cen, hT₂card⟩ :=
      ih (finrank K V₂) hlt₂ (fun i => (f i).restrict (hm₂ i))
        (fun i j => OrdPNS.restrict_commute' (hfc i j) (hm₂ i) (hm₂ j))
        (fun i => OrdPNS.restrict_pow_eq_one (hfp i) (hm₂ i)) rfl
    set ιe := Submodule.prodEquivOfIsCompl V₁ V₂ hcompl with hιe
    let Φ : Module.End K V₁ × Module.End K V₂ → Module.End K V := fun t =>
      ιe.conjAlgEquiv K (t.1.prodMap t.2)
    have hΦmul : ∀ t s, Φ t * Φ s = Φ (t * s) := fun t s => by
      simp only [Φ, ← map_mul, LinearMap.prodMap_mul, Prod.fst_mul, Prod.snd_mul]
    have hΦpow : ∀ t (k : ℕ), Φ t ^ k = Φ (t ^ k) := fun t k => by
      simp only [Φ, ← map_pow, OrdPNS.prodMap_pow, Prod.pow_fst, Prod.pow_snd]
    have hΦ1 : Φ 1 = 1 := by
      simp only [Φ, Prod.fst_one, Prod.snd_one, LinearMap.prodMap_one, map_one]
    have hΦinj : Function.Injective Φ := by
      intro t s hts
      have h1 : t.1.prodMap t.2 = s.1.prodMap s.2 := (ιe.conjAlgEquiv K).injective hts
      refine Prod.ext (LinearMap.ext fun w => ?_) (LinearMap.ext fun w => ?_)
      · have h2 := congrArg Prod.fst (LinearMap.congr_fun h1 (w, 0))
        simpa using h2
      · have h2 := congrArg Prod.snd (LinearMap.congr_fun h1 (0, w))
        simpa using h2
    have hΦf : ∀ i, Φ ((f i).restrict (hm₁ i), (f i).restrict (hm₂ i)) = f i := by
      intro i
      refine LinearMap.ext fun v => ?_
      obtain ⟨w, rfl⟩ := ιe.surjective v
      change ιe (((f i).restrict (hm₁ i)).prodMap ((f i).restrict (hm₂ i)) (ιe.symm (ιe w))) =
        f i (ιe w)
      rw [LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, hιe,
        Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
      rfl
    refine ⟨Φ '' (T₁ ×ˢ T₂), ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
      change Φ t * Φ s = Φ s * Φ t
      rw [hΦmul, hΦmul]
      exact congrArg Φ (Prod.ext (hT₁c _ ht.1 _ hs.1).eq (hT₂c _ ht.2 _ hs.2).eq)
    · rintro _ ⟨t, ht, rfl⟩
      rw [hΦpow, ← hΦ1]
      exact congrArg Φ (Prod.ext (hT₁p _ ht.1) (hT₂p _ ht.2))
    · rintro _ ⟨t, ht, rfl⟩ i
      rw [← hΦf i]
      change Φ t * Φ _ = Φ _ * Φ t
      rw [hΦmul, hΦmul]
      exact congrArg Φ (Prod.ext (hT₁cen _ ht.1 i).eq (hT₂cen _ ht.2 i).eq)
    · rw [Nat.card_image_of_injective hΦinj, Nat.card_congr (Equiv.Set.prod T₁ T₂),
        Nat.card_prod]
      have hdimL : finrank K (AdjoinRoot g) = OrdPNS.ordQ K ℓ := by
        rw [PowerBasis.finrank (AdjoinRoot.powerBasis hg0), AdjoinRoot.powerBasis_dim,
          OrdPNS.natDegree_eq_ordQ hℓ hℓK hg hgd]
      have hdim : finrank K V₁ = OrdPNS.ordQ K ℓ * finrank (AdjoinRoot g) V₁ := by
        rw [← hdimL, Module.finrank_mul_finrank]
      calc ℓ ^ (n / OrdPNS.ordQ K ℓ)
          = ℓ ^ (finrank (AdjoinRoot g) V₁ + finrank K V₂ / OrdPNS.ordQ K ℓ) := by
            rw [← hn, ← hfr, hdim, Nat.mul_add_div (OrdPNS.ordQ_pos hℓ hℓK)]
        _ = ℓ ^ finrank (AdjoinRoot g) V₁ * ℓ ^ (finrank K V₂ / OrdPNS.ordQ K ℓ) :=
            pow_add _ _ _
        _ ≤ Nat.card T₁ * Nat.card T₂ := Nat.mul_le_mul hT₁card hT₂card

private theorem twslr_exists_card_ge_pow_ordQ_matrix_family {K : Type} [Field K] [Finite K]
    {n ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    (S₀ : Set (Matrix (Fin n) (Fin n) K))
    (hS₀c : ∀ x ∈ S₀, ∀ y ∈ S₀, Commute x y) (hS₀p : ∀ x ∈ S₀, x ^ ℓ = 1)
    (hS₀fin : S₀.Finite) :
    ∃ S : Set (Matrix (Fin n) (Fin n) K), (∀ x ∈ S, ∀ y ∈ S, Commute x y) ∧
      (∀ x ∈ S, x ^ ℓ = 1) ∧ (∀ x ∈ S, ∀ y ∈ S₀, Commute x y) ∧
      ℓ ^ (n / OrdPNS.ordQ K ℓ) ≤ Nat.card S := by
  classical
  haveI : Finite S₀ := hS₀fin.to_subtype
  let f : S₀ → Module.End K (Fin n → K) := fun x => Matrix.toLinAlgEquiv' x.1
  have hfc : ∀ i j, Commute (f i) (f j) := fun i j =>
    (hS₀c i.1 i.2 j.1 j.2).map Matrix.toLinAlgEquiv'
  have hfp : ∀ i, f i ^ ℓ = 1 := fun i => by rw [← map_pow, hS₀p i.1 i.2, map_one]
  obtain ⟨S, hSc, hSp, hScen, hScard⟩ :=
    twslr_exists_card_ge_pow_ordQ_family (V := Fin n → K) hℓ hℓK f hfc hfp
  refine ⟨Matrix.toLinAlgEquiv'.symm '' S, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hSc x hx y hy).map Matrix.toLinAlgEquiv'.symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hSp x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ y hy
    have h := (hScen x hx ⟨y, hy⟩).map Matrix.toLinAlgEquiv'.symm
    simpa only [f, AlgEquiv.symm_apply_apply] using h
  · rw [Nat.card_image_of_injective Matrix.toLinAlgEquiv'.symm.injective]
    simpa [Module.finrank_fin_fun] using hScard

private theorem twslr_ordQ_eq_two {K : Type} [Field K]
    (h3 : 3 ∣ Nat.card K + 1) : OrdPNS.ordQ K 3 = 2 := by
  rw [OrdPNS.ordQ_def]
  have h0 : ((Nat.card K + 1 : ℕ) : ZMod 3) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod 3) 3]
    exact h3
  rw [Nat.cast_add, Nat.cast_one] at h0
  have hcast : ((Nat.card K : ℕ) : ZMod 3) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact h0
  rw [hcast]
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

private theorem twslr_three_ne_zero {K : Type} [Field K] [CharP K 2] : (3 : K) ≠ 0 := by
  intro hzero
  have h23 : 2 = 3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (by norm_num : (3 : ℕ).Prime)).mp
    ((CharP.cast_eq_zero_iff K 2 3).mp hzero)
  norm_num at h23

private theorem twslr_exists_section {K : Type} [Field K] [Finite K] [CharP K 2]
    {d : ℕ} (hd0 : 0 < d) (h3 : 3 ∣ Nat.card K + 1)
    (E : Subgroup (projectiveSL d K)) (hE : IsElemAbelian 3 E) :
    ∃ s : ↥E →* Matrix.SpecialLinearGroup (Fin d) K,
      (∀ e, proj d K (s e) = e) ∧ ∀ e, (s e) ^ 3 = 1 := by
  classical
  have hp3 : (3 : ℕ).Prime := by norm_num
  have h3K : (3 : K) ≠ 0 := twslr_three_ne_zero
  have h3K' : ¬ 3 ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp3 (by norm_num) h3
  have hker : (proj d K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K) := by
    intro x hx
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hx
  have hcp : ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)) := by
    intro h
    exact h3K' (h.trans (card_center_specialLinear_dvd (d := d) (K := K) hd0))
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2) }
  have hV : ∀ v : ↥E, v ^ 3 = 1 := fun v => Subtype.ext (hE.2 v v.2)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_centerPrime hp3 (proj_surjective d K) hker hcp
    (V := ↥E) hV E.subtype
  exact ⟨s, hs, hsp⟩

private theorem twslr_card_le_psl {K : Type} [Field K] [Finite K] [CharP K 2] {d r : ℕ}
    (hr : 3 ≤ r) (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ Nat.card K + 1)
    (E : Subgroup (projectiveSL d K)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ r := by
  classical
  have hp3 : (3 : ℕ).Prime := by norm_num
  have h3K : (3 : K) ≠ 0 := twslr_three_ne_zero
  obtain ⟨s, hs, hsp⟩ := twslr_exists_section (by omega) h3 E hE
  set S : Set (Matrix (Fin d) (Fin d) K) :=
    Set.range fun e : ↥E => ((s e : Matrix.SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    have h1 : s e * s e' = s e' * s e := by
      rw [← map_mul, ← map_mul]
      exact congrArg s (Subtype.ext (TableB.IsElemAbelian.comm hE e.2 e'.2))
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  have hSp : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨e, rfl⟩
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) (hsp e)
  have hinj : Function.Injective (fun e : ↥E =>
      ((s e : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
    intro e e' hee'
    have h1 : s e = s e' := Subtype.ext hee'
    refine Subtype.ext ?_
    calc (e : projectiveSL d K) = proj d K (s e) := (hs e).symm
      _ = proj d K (s e') := by rw [h1]
      _ = (e' : projectiveSL d K) := hs e'
  have hcardS : Nat.card S = Nat.card E := by
    rw [hS]
    exact Nat.card_range_of_injective hinj
  have hdiv : d / OrdPNS.ordQ K 3 = r := by rw [twslr_ordQ_eq_two h3]; omega
  have hbound := OrdPNS.card_le_pow_ordQ_matrix (K := K) (n := d) hp3 h3K S hSc hSp
  rw [hcardS, hdiv] at hbound
  exact hbound

private theorem twslr_selfCent_psl {K : Type} [Field K] [Finite K] [CharP K 2] {d r : ℕ}
    (hr : 3 ≤ r) (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ Nat.card K + 1)
    {E : Subgroup (projectiveSL d K)} (hE : IsElemAbelian 3 E)
    (hsc : ∀ g : projectiveSL d K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    3 ^ r ≤ Nat.card E := by
  classical
  have hp3 : (3 : ℕ).Prime := by norm_num
  have h3K : (3 : K) ≠ 0 := twslr_three_ne_zero
  have h3K' : ¬ 3 ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp3 (by norm_num) h3
  have hker : (proj d K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K) := by
    intro x hx
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hx
  obtain ⟨s, hs, hsp⟩ := twslr_exists_section (by omega) h3 E hE
  set S₀ : Set (Matrix (Fin d) (Fin d) K) :=
    Set.range fun e : ↥E => ((s e : Matrix.SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) with hS₀
  have hS₀c : ∀ x ∈ S₀, ∀ y ∈ S₀, Commute x y := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    have h1 : s e * s e' = s e' * s e := by
      rw [← map_mul, ← map_mul]
      exact congrArg s (Subtype.ext (TableB.IsElemAbelian.comm hE e.2 e'.2))
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  have hS₀p : ∀ x ∈ S₀, x ^ 3 = 1 := by
    rintro _ ⟨e, rfl⟩
    exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) K =>
      ((z : Matrix.SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)) (hsp e)
  have hS₀fin : S₀.Finite := by rw [hS₀]; exact Set.finite_range _
  obtain ⟨S, hSc, hSp, hScen, hScard⟩ :=
    twslr_exists_card_ge_pow_ordQ_matrix_family hp3 h3K S₀ hS₀c hS₀p hS₀fin
  obtain ⟨T, hTS, hTcard⟩ := OrdPNS.exists_gl_set (by norm_num : 0 < 3) S hSp
  obtain ⟨F, hFel, hFcard, hFcenter, hFX, -⟩ := OrdPNS.exists_elemAbelian_of_set hp3 h3K' T
    (fun x hx y hy => Units.ext (hSc _ (hTS x hx) _ (hTS y hy)).eq)
    (fun x hx => Units.ext (by
      rw [Units.val_pow_eq_pow_val, hSp _ (hTS x hx), Units.val_one]))
  have hFcen : ∀ u ∈ F, ∀ e : ↥E, Commute (Matrix.SpecialLinearGroup.toGL u) (s e) := by
    intro u hu e
    exact hFX (s e) (fun x hx => Units.ext (hScen _ (hTS x hx) _ ⟨e, rfl⟩).eq) u hu
  have hπF : ∀ u ∈ F, proj d K (u : Matrix.SpecialLinearGroup (Fin d) K) ∈ E := by
    intro u hu
    refine hsc (proj d K u) (fun e he => ?_) (by rw [← map_pow, hFel.2 u hu, map_one])
    have hse : proj d K (s ⟨e, he⟩) = e := hs ⟨e, he⟩
    rw [← hse, ← map_mul, ← map_mul]
    congr 1
    exact Matrix.SpecialLinearGroup.toGL_injective (by
      rw [map_mul, map_mul]
      exact (hFcen u hu ⟨e, he⟩).eq)
  have hπinj : Function.Injective (fun u : F =>
      proj d K (u : Matrix.SpecialLinearGroup (Fin d) K)) := by
    intro u v huv
    have h1 : (u : Matrix.SpecialLinearGroup (Fin d) K) *
        (v : Matrix.SpecialLinearGroup (Fin d) K)⁻¹ ∈ (proj d K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [show proj d K (u : Matrix.SpecialLinearGroup (Fin d) K) =
        proj d K (v : Matrix.SpecialLinearGroup (Fin d) K) from huv]
      exact mul_inv_cancel _
    have h2 := hFcenter _ (F.mul_mem u.2 (F.inv_mem v.2)) (hker h1)
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hFE : Nat.card F ≤ Nat.card E :=
    Nat.card_le_card_of_injective
      (fun u : F => (⟨proj d K (u : Matrix.SpecialLinearGroup (Fin d) K), hπF u u.2⟩ : E))
      (fun u v huv => hπinj (Subtype.ext_iff.mp huv))
  have hdiv : d / OrdPNS.ordQ K 3 = r := by rw [twslr_ordQ_eq_two h3]; omega
  calc 3 ^ r = 3 ^ (d / OrdPNS.ordQ K 3) := by rw [hdiv]
    _ ≤ Nat.card S := hScard
    _ ≤ Nat.card T := hTcard
    _ ≤ Nat.card F := hFcard
    _ ≤ Nat.card E := hFE

theorem ggTwSL_rankLE_rec {K : Type} [Field K] [Finite K] [CharP K 2] {d r : ℕ} (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ Nat.card K + 1) :
    GGElemAbelianRankLE (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) 3 r := by
  intro E hE
  have hinj : Function.Injective (TypeA.recipeEquiv d K) := (TypeA.recipeEquiv d K).injective
  have hE' : IsElemAbelian 3 (E.map (TypeA.recipeEquiv d K).toMonoidHom) :=
    TableB.isElemAbelian_map hE _
  have hcard : Nat.card (E.map (TypeA.recipeEquiv d K).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rw [← hcard]
  exact twslr_card_le_psl hr hd h3 _ hE'

theorem ggTwSL_scRank_rec {K : Type} [Field K] [Finite K] [CharP K 2] {d r : ℕ} (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ Nat.card K + 1) :
    GGSelfCentRankGE 3 r (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
  intro E hE hsc
  set e := TypeA.recipeEquiv d K with he
  have hinj : Function.Injective e := e.injective
  have hE' : IsElemAbelian 3 (E.map e.toMonoidHom) := TableB.isElemAbelian_map hE _
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  have hsc' : ∀ g : projectiveSL d K, (∀ f ∈ E.map e.toMonoidHom, g * f = f * g) →
      g ^ 3 = 1 → g ∈ E.map e.toMonoidHom := by
    intro g hg hg3
    have hg' : ∀ x ∈ E, e.symm g * x = x * e.symm g := by
      intro x hx
      calc e.symm g * x = e.symm (g * e x) := by rw [map_mul, e.symm_apply_apply]
        _ = e.symm (e x * g) := by
          rw [hg (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)]
        _ = x * e.symm g := by rw [map_mul, e.symm_apply_apply]
    have hmem : e.symm g ∈ E := hsc (e.symm g) hg' (by
      calc (e.symm g) ^ 3 = e.symm (g ^ 3) := by rw [map_pow]
        _ = e.symm 1 := by rw [hg3]
        _ = 1 := map_one e.symm)
    exact Subgroup.mem_map.mpr ⟨e.symm g, hmem, e.apply_symm_apply g⟩
  rw [← hcard]
  exact twslr_selfCent_psl hr hd h3 hE' hsc'

end CFSG.StandardType

end
