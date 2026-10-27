module

public import CFSG.LocalAnalysis.StandardType.GGModRank
public import CFSG.LocalAnalysis.StandardType.GGWeylCartan

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

private theorem ggZMod_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)

private noncomputable def ggWeylLin {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (p : ℕ)
    (w : (coxeterMatrix hC).Group) : (ι → ZMod p) →ₗ[ZMod p] (ι → ZMod p) :=
  Matrix.toLin' ((ggWeylMat hC w).map (Int.castRingHom (ZMod p)))

private theorem ggWeylLin_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (p : ℕ) :
    ggWeylLin hC p (1 : (coxeterMatrix hC).Group) = 1 := by
  refine LinearMap.ext fun c => ?_
  have hmap1 : (1 : Matrix ι ι ℤ).map (Int.castRingHom (ZMod p)) = 1 := by
    ext a b
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [ggWeylLin, ggWeylMat, map_one, LinearMap.toMatrix'_one, hmap1, Matrix.toLin'_one]
  rfl

private theorem ggWeylLin_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (p : ℕ)
    (w w' : (coxeterMatrix hC).Group) :
    ggWeylLin hC p (w * w') = ggWeylLin hC p w * ggWeylLin hC p w' := by
  refine LinearMap.ext fun c => ?_
  rw [ggWeylLin, ggWeylLin, ggWeylLin, ggWeylMat, ggWeylMat, map_mul,
    LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]
  rfl

private theorem ggWeylLin_mul_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (p : ℕ)
    (w w' : (coxeterMatrix hC).Group) (c : ι → ZMod p) :
    ggWeylLin hC p (w * w') c = ggWeylLin hC p w (ggWeylLin hC p w' c) := by
  rw [ggWeylLin_mul]
  rfl

private theorem ggWeylLin_simple_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (p : ℕ) (i : ι) (v : ι → ℤ) :
    ggWeylLin hC p ((coxeterMatrix hC).toCoxeterSystem.simple i)
      (fun j => (v j : ZMod p)) = fun k => (reflection C i v k : ZMod p) := by
  funext k
  rw [ggWeylLin, ggWeylMat, weylAction_simple, Matrix.toLin'_apply]
  change ((LinearMap.toMatrix' (reflection C i)).map (Int.castRingHom (ZMod p))).mulVec
      ((Int.castRingHom (ZMod p)) ∘ v) k = ((reflection C i v k : ℤ) : ZMod p)
  rw [← RingHom.map_mulVec (Int.castRingHom (ZMod p))
    (LinearMap.toMatrix' (reflection C i)) v k, LinearMap.toMatrix'_mulVec]
  rfl

private theorem ggWeylLin_simple {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) (p : ℕ) (i : ι) (c : ι → ZMod p) :
    ggWeylLin hC p ((coxeterMatrix hC).toCoxeterSystem.simple i) c =
      c - (∑ j, ((C i j : ℤ) : ZMod p) * c j) • Pi.single i 1 := by
  obtain ⟨v, rfl⟩ : ∃ v : ι → ℤ, (fun j => (v j : ZMod p)) = c := by
    choose v hv using fun j => ZMod.intCast_surjective (c j)
    exact ⟨v, funext hv⟩
  rw [ggWeylLin_simple_apply hC p i v]
  funext k
  rw [reflection_apply]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    push_cast
    ring
  · have hki : k ≠ i := fun h => hk h
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hki, mul_zero, sub_zero,
      smul_eq_mul]

private theorem ggDual_linearCombination {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (hfh : ∀ i j, f i (h j) = ((C i j : ℤ) : ZMod p)) (i : ι) (c : ι → ZMod p) :
    f i (Fintype.linearCombination (ZMod p) h c) = ∑ j, ((C i j : ℤ) : ZMod p) * c j := by
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hfh, smul_eq_mul, mul_comm]

private theorem ggWeylLin_equiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) {p : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (h : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (hfh : ∀ i j, f i (h j) = ((C i j : ℤ) : ZMod p))
    (ρ : (coxeterMatrix hC).Group →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i v, ρ ((coxeterMatrix hC).toCoxeterSystem.simple i) v = v - f i v • h i)
    (w : (coxeterMatrix hC).Group) (c : ι → ZMod p) :
    Fintype.linearCombination (ZMod p) h (ggWeylLin hC p w c) =
      ρ w (Fintype.linearCombination (ZMod p) h c) := by
  let cs := (coxeterMatrix hC).toCoxeterSystem
  have hsingle : ∀ i, Fintype.linearCombination (ZMod p) h (Pi.single i 1) = h i := by
    intro i
    rw [Fintype.linearCombination_apply,
      Finset.sum_eq_single i
        (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
        (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  have hw : w ∈ Subgroup.closure (Set.range cs.simple) := by
    rw [CoxeterSystem.subgroup_closure_range_simple]
    exact Subgroup.mem_top w
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ c : ι → ZMod p,
      Fintype.linearCombination (ZMod p) h (ggWeylLin hC p g c) =
      ρ g (Fintype.linearCombination (ZMod p) h c)) ?_ ?_ ?_ ?_ hw c
  · rintro x ⟨i, rfl⟩ c
    rw [ggWeylLin_simple hC p i c, hρ i (Fintype.linearCombination (ZMod p) h c),
      ggDual_linearCombination h f hfh i c, map_sub, map_smul, hsingle i]
  · intro c
    rw [ggWeylLin_one hC p]
    show Fintype.linearCombination (ZMod p) h c =
      ρ 1 (Fintype.linearCombination (ZMod p) h c)
    rw [map_one]
    rfl
  · intro x y hx hy hx' hy' c
    rw [ggWeylLin_mul_apply, map_mul, LinearEquiv.mul_apply,
      hx' (ggWeylLin hC p y c), hy' c]
  · intro x hx hx' c
    have h1 : ggWeylLin hC p x (ggWeylLin hC p (x⁻¹) c) = c := by
      rw [← ggWeylLin_mul_apply, mul_inv_cancel, ggWeylLin_one]
      rfl
    have h2 : ρ x (Fintype.linearCombination (ZMod p) h (ggWeylLin hC p (x⁻¹) c)) =
        Fintype.linearCombination (ZMod p) h c := by
      rw [← hx' (ggWeylLin hC p (x⁻¹) c), h1]
    have h3 := congrArg (fun v => ρ (x⁻¹) v) h2
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h3
    simpa using h3

private theorem ggWeylLin_fixes_ker {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C) {p : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (h : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (hfh : ∀ i j, f i (h j) = ((C i j : ℤ) : ZMod p))
    (w : (coxeterMatrix hC).Group) (c : ι → ZMod p)
    (hc : Fintype.linearCombination (ZMod p) h c = 0) :
    ggWeylLin hC p w c = c := by
  let cs := (coxeterMatrix hC).toCoxeterSystem
  have hw : w ∈ Subgroup.closure (Set.range cs.simple) := by
    rw [CoxeterSystem.subgroup_closure_range_simple]
    exact Subgroup.mem_top w
  refine Subgroup.closure_induction (p := fun g _ => ggWeylLin hC p g c = c) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨i, rfl⟩
    rw [ggWeylLin_simple hC p i c]
    have hzero : (∑ j, ((C i j : ℤ) : ZMod p) * c j) = 0 := by
      rw [← ggDual_linearCombination h f hfh i c, hc, map_zero]
    rw [hzero, zero_smul, sub_zero]
  · rw [ggWeylLin_one hC p]
    rfl
  · intro x y hx hy hx' hy'
    rw [ggWeylLin_mul_apply, hy', hx']
  · intro x hx hx'
    have h1 : ggWeylLin hC p (x⁻¹) (ggWeylLin hC p x c) = c := by
      rw [← ggWeylLin_mul_apply, inv_mul_cancel, ggWeylLin_one]
      rfl
    rw [hx'] at h1
    exact h1

theorem ggRefl_sub_mem {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (ρ : (coxeterMatrix hC).Group →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i v, ρ ((coxeterMatrix hC).toCoxeterSystem.simple i) v = v - f i v • h i)
    (w : (coxeterMatrix hC).Group) (v : V) :
    ρ w v - v ∈ Submodule.span (ZMod p) (Set.range h) := by
  classical
  let cs := (coxeterMatrix hC).toCoxeterSystem
  let V₁ : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hmem : ∀ i : ι, h i ∈ V₁ := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hw : w ∈ Subgroup.closure (Set.range cs.simple) := by
    rw [CoxeterSystem.subgroup_closure_range_simple]
    exact Subgroup.mem_top w
  refine Subgroup.closure_induction (p := fun g _ => ∀ v : V, ρ g v - v ∈ V₁)
    ?_ ?_ ?_ ?_ hw v
  · rintro x ⟨i, rfl⟩ v
    rw [hρ i v]
    rw [show v - f i v • h i - v = -(f i v • h i) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (hmem i))
  · intro v
    rw [map_one]
    simp
  · intro x y hx hy hx' hy' v
    rw [map_mul, LinearEquiv.mul_apply]
    rw [show ρ x (ρ y v) - v = (ρ x (ρ y v) - ρ y v) + (ρ y v - v) by abel]
    exact Submodule.add_mem _ (hx' (ρ y v)) (hy' v)
  · intro x hx hx' v
    have h1 : ρ x (ρ (x⁻¹) v) = v := by
      have hmul : ρ x * ρ (x⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hmul
      simpa [LinearEquiv.mul_apply] using this
    have hx2 : ρ x (ρ (x⁻¹) v) - ρ (x⁻¹) v ∈ V₁ := hx' (ρ (x⁻¹) v)
    rw [h1] at hx2
    rw [show ρ (x⁻¹) v - v = -(v - ρ (x⁻¹) v) by abel]
    exact Submodule.neg_mem _ hx2

theorem ggRefl_minus_finrank {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (h : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (hfh : ∀ i j, f i (h j) = ((C i j : ℤ) : ZMod p))
    (ρ : (coxeterMatrix hC).Group →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i v, ρ ((coxeterMatrix hC).toCoxeterSystem.simple i) v = v - f i v • h i)
    (t : (coxeterMatrix hC).Group) (ht : t * t = 1) :
    Module.finrank (ZMod p)
        ↥(LinearMap.ker ((ρ t).toLinearMap + 1) ⊓ Submodule.span (ZMod p) (Set.range h)) =
      Module.finrank ℚ
        (LinearMap.ker (Matrix.toLin' ((ggWeylMat hC t).map (Int.castRingHom ℚ) + 1))) := by
  classical
  let π : (ι → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  let V₁ : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let T : (ι → ZMod p) →ₗ[ZMod p] (ι → ZMod p) := ggWeylLin hC p t
  have hsingle : ∀ i, π (Pi.single i 1) = h i := by
    intro i
    show Fintype.linearCombination (ZMod p) h (Pi.single i 1) = h i
    rw [Fintype.linearCombination_apply,
      Finset.sum_eq_single i
        (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
        (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  have hrange : LinearMap.range π = V₁ := by
    apply le_antisymm
    · rintro y ⟨c, rfl⟩
      show Fintype.linearCombination (ZMod p) h c ∈ V₁
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      exact ⟨Pi.single j 1, hsingle j⟩
  have hX : ggWeylMat hC t * ggWeylMat hC t = 1 := by
    rw [ggWeylMat, ← LinearMap.toMatrix'_mul, ← map_mul, ht, map_one,
      LinearMap.toMatrix'_one]
  have hT2 : T * T = 1 := by
    show ggWeylLin hC p t * ggWeylLin hC p t = 1
    rw [← ggWeylLin_mul, ht, ggWeylLin_one]
  have hTfix : ∀ c, T (T c) = c := by
    intro c
    have h := congrArg (fun g : (ι → ZMod p) →ₗ[ZMod p] (ι → ZMod p) => g c) hT2
    simpa [Module.End.mul_apply] using h
  have hπT : ∀ c, π (T c) = ρ t (π c) := by
    intro c
    show Fintype.linearCombination (ZMod p) h (ggWeylLin hC p t c) =
      ρ t (Fintype.linearCombination (ZMod p) h c)
    exact ggWeylLin_equiv hC h f hfh ρ hρ t c
  have hπfix : ∀ c, π c = 0 → T c = c := by
    intro c hc
    show ggWeylLin hC p t c = c
    exact ggWeylLin_fixes_ker hC h f hfh t c hc
  let E : Submodule (ZMod p) (ι → ZMod p) := LinearMap.ker (T + 1)
  let K : Submodule (ZMod p) V := LinearMap.ker ((ρ t).toLinearMap + 1) ⊓ V₁
  have hE : ∀ c, c ∈ E ↔ T c = -c := by
    intro c
    show c ∈ LinearMap.ker (T + 1) ↔ T c = -c
    rw [LinearMap.mem_ker, LinearMap.add_apply]
    show T c + c = 0 ↔ T c = -c
    rw [add_eq_zero_iff_eq_neg]
    rfl
  have hK : ∀ v, v ∈ K ↔ ((ρ t) v = -v ∧ v ∈ V₁) := by
    intro v
    show v ∈ (LinearMap.ker ((ρ t).toLinearMap + 1) ⊓ V₁) ↔ ((ρ t) v = -v ∧ v ∈ V₁)
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply]
    show ((ρ t) v + v = 0) ∧ v ∈ V₁ ↔ ((ρ t) v = -v ∧ v ∈ V₁)
    rw [add_eq_zero_iff_eq_neg]
  have hφ : ∀ c : E, π (c : ι → ZMod p) ∈ K := by
    intro c
    rw [hK]
    refine ⟨?_, ?_⟩
    · have hcT : T (c : ι → ZMod p) = -(c : ι → ZMod p) := (hE c).mp c.2
      show (ρ t) (π (c : ι → ZMod p)) = -π (c : ι → ZMod p)
      rw [← hπT c, hcT]
      exact map_neg π (c : ι → ZMod p)
    · show π (c : ι → ZMod p) ∈ Submodule.span (ZMod p) (Set.range h)
      exact (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mpr
        ⟨c, (Fintype.linearCombination_apply (ZMod p) h c).symm⟩
  let φ : E →ₗ[ZMod p] K := LinearMap.codRestrict K (π.comp E.subtype) (fun c => hφ c)
  have hinj : Function.Injective φ := by
    intro c1 c2 h
    have hπeq : π (c1 : ι → ZMod p) = π (c2 : ι → ZMod p) := by
      have hh := congrArg (fun x : K => (x : V)) h
      simpa [φ, LinearMap.codRestrict] using hh
    set d : ι → ZMod p := (c1 : ι → ZMod p) - (c2 : ι → ZMod p) with hd
    have hdπ : π d = 0 := by rw [hd, map_sub, hπeq, sub_self]
    have hdE : d ∈ E := by
      rw [hE, hd, map_sub]
      have h1 : T (c1 : ι → ZMod p) = -(c1 : ι → ZMod p) := (hE _).mp c1.2
      have h2 : T (c2 : ι → ZMod p) = -(c2 : ι → ZMod p) := (hE _).mp c2.2
      rw [h1, h2]
      abel
    have hdT : T d = d := hπfix d hdπ
    have hdT' : T d = -d := (hE d).mp hdE
    have hdz : d = 0 := by
      have hneg : d = -d := hdT.symm.trans hdT'
      have hcc := eq_neg_iff_add_eq_zero.mp hneg
      have h2 : (2 : ZMod p) • d = 0 := by rwa [two_smul]
      rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h (ggZMod_two_ne_zero hp2)
      · exact h
    apply Subtype.ext
    have hzero : (c1 : ι → ZMod p) - (c2 : ι → ZMod p) = 0 := by rwa [← hd]
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective φ := by
    intro y
    have hyK := (hK (y : V)).mp y.2
    have hyV : (y : V) ∈ Submodule.span (ZMod p) (Set.range h) := hyK.2
    obtain ⟨c0, hc0⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hyV
    have hc0' : π c0 = (y : V) := by
      show Fintype.linearCombination (ZMod p) h c0 = (y : V)
      rw [Fintype.linearCombination_apply]
      exact hc0
    refine ⟨⟨(2 : ZMod p)⁻¹ • (c0 - T c0), ?_⟩, ?_⟩
    · rw [hE]
      show T ((2 : ZMod p)⁻¹ • (c0 - T c0)) = -((2 : ZMod p)⁻¹ • (c0 - T c0))
      rw [map_smul, map_sub, hTfix c0]
      have hinner : T c0 - c0 = -(c0 - T c0) := by abel
      calc (2 : ZMod p)⁻¹ • (T c0 - c0)
          = (2 : ZMod p)⁻¹ • (-(c0 - T c0)) := congrArg _ hinner
        _ = -((2 : ZMod p)⁻¹ • (c0 - T c0)) := smul_neg _ _
    · apply Subtype.ext
      show π ((2 : ZMod p)⁻¹ • (c0 - T c0)) = (y : V)
      rw [map_smul, map_sub, hπT c0, hc0']
      have h2y : (y : V) - -(y : V) = (2 : ZMod p) • (y : V) := by
        rw [two_smul]; abel
      rw [hyK.1, h2y, smul_smul, inv_mul_cancel₀ (ggZMod_two_ne_zero hp2), one_smul]
  have heq : Module.finrank (ZMod p) E = Module.finrank (ZMod p) K :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)
  have hEeq : E = LinearMap.ker
      (Matrix.toLin' ((ggWeylMat hC t).map (Int.castRingHom (ZMod p)) + 1)) := by
    show LinearMap.ker (T + 1) = _
    have hTunfold : T = Matrix.toLin'
        ((ggWeylMat hC t).map (Int.castRingHom (ZMod p))) := rfl
    rw [hTunfold]
    congr 1
    simp only [Matrix.toLin'_apply', Matrix.mulVecLin_add, Matrix.mulVecLin_one]
    rfl
  have hbb := ggFinrankKerAddOne_zmod_eq_rat hp2 (ggWeylMat hC t) hX
  rw [← hEeq] at hbb
  change Module.finrank (ZMod p) K = Module.finrank ℚ
    (LinearMap.ker (Matrix.toLin' ((ggWeylMat hC t).map (Int.castRingHom ℚ) + 1)))
  rw [← heq]
  exact hbb

theorem ggFinrank_minus_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (T : V ≃ₗ[ZMod p] V) (hT : T ^ 2 = 1)
    (hfix : Nat.card {v : V // T v = v} * p = Nat.card V) :
    Module.finrank (ZMod p) (LinearMap.ker (T.toLinearMap + 1)) = 1 := by
  classical
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hTv : ∀ v : V, T (T v) = v := by
    intro v
    have h := DFunLike.congr_fun hT v
    change T (T v) = v at h
    exact h
  let Vp : Submodule (ZMod p) V := LinearMap.ker (T.toLinearMap - 1)
  let Vm : Submodule (ZMod p) V := LinearMap.ker (T.toLinearMap + 1)
  have hmemVp : ∀ v : V, v ∈ Vp ↔ T v = v := by
    intro v
    simp [Vp, sub_eq_zero]
  have hmemVm : ∀ v : V, v ∈ Vm ↔ T v = -v := by
    intro v
    simp [Vm, add_eq_zero_iff_eq_neg]
  have hdisj : Disjoint Vp Vm := by
    rw [Submodule.disjoint_def]
    intro v hv hw
    have hv' : T v = v := (hmemVp v).mp hv
    have hw' : T v = -v := (hmemVm v).mp hw
    have hvv : v + v = 0 := by
      have hv'' : v = -v := hv'.symm.trans hw'
      exact eq_neg_iff_add_eq_zero.mp hv''
    have h2v : (2 : ZMod p) • v = 0 := by rw [two_smul, hvv]
    rcases smul_eq_zero.mp h2v with h | h
    · exact absurd h h2
    · exact h
  have htop : Vp ⊔ Vm = ⊤ := by
    rw [Submodule.sup_eq_top_iff]
    intro v
    refine ⟨(2 : ZMod p)⁻¹ • (v + T v), ?_, (2 : ZMod p)⁻¹ • (v - T v), ?_, ?_⟩
    · rw [hmemVp, map_smul, map_add, hTv, add_comm (T v) v]
    · rw [hmemVm, map_smul, map_sub, hTv, ← smul_neg, neg_sub]
    · rw [← smul_add]
      have hsum : v + T v + (v - T v) = (2 : ZMod p) • v := by
        rw [two_smul]; abel
      rw [hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hcompl : IsCompl Vp Vm := isCompl_iff.mpr ⟨hdisj, codisjoint_iff.mpr htop⟩
  have hfin : Module.finrank (ZMod p) V =
      Module.finrank (ZMod p) Vp + Module.finrank (ZMod p) Vm :=
    (Submodule.finrank_add_eq_of_isCompl hcompl).symm
  have hcard : Nat.card {v : V // T v = v} = Nat.card Vp :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hmemVp v).symm))
  have hpowVp := FiniteField.pow_finrank_eq_natCard p Vp
  have hpowV := FiniteField.pow_finrank_eq_natCard p V
  have hkey : p ^ (Module.finrank (ZMod p) Vp + 1) =
      p ^ (Module.finrank (ZMod p) Vp + Module.finrank (ZMod p) Vm) := by
    rw [pow_succ, hpowVp, ← hcard, hfix, ← hpowV, ← hfin]
  have hle : 2 ≤ p := hp.two_le
  have hcancel := Nat.pow_right_injective hle hkey
  change Module.finrank (ZMod p) Vm = 1
  omega

end CFSG.StandardType
