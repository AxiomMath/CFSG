module

public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}

@[expose] def IsIrreducibleOn (G : Subgroup (GL σ K)) : Prop :=
  ∀ W : Submodule K (σ → K), (∀ g ∈ G, ∀ w ∈ W, (g : Matrix σ σ K) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤

theorem isIrreducibleOn_iff {G : Subgroup (GL (Fin n) K)} :
    IsIrreducibleOn G ↔ IsIrreducibleMatrixRep G.subtype :=
  ⟨fun h W hW => h W fun g hg w hw => hW ⟨g, hg⟩ w hw,
    fun h W hW => h W fun g w hw => hW g g.2 w hw⟩

@[expose] noncomputable def commutant (G : Subgroup (GL σ K)) : Subalgebra K (Matrix σ σ K) :=
  Subalgebra.centralizer K ((fun g : GL σ K => (g : Matrix σ σ K)) '' (G : Set (GL σ K)))

theorem mem_commutant {G : Subgroup (GL σ K)} {M : Matrix σ σ K} :
    M ∈ commutant G ↔ ∀ g ∈ G, (g : Matrix σ σ K) * M = M * g := by
  simp [commutant, Subalgebra.mem_centralizer_iff]

theorem scalar_mulVec_eq_smul (a : K) (v : σ → K) : Matrix.scalar σ a *ᵥ v = a • v := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem not_irreducibleOn_of_forall_scalar (hσ : 2 ≤ Fintype.card σ) {G : Subgroup (GL σ K)}
    (hG : ∀ g ∈ G, ∃ a : K, (g : Matrix σ σ K) = Matrix.scalar σ a) : ¬ IsIrreducibleOn G := by
  classical
  intro hirr
  have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  set v₀ : σ → K := Pi.single (Classical.arbitrary σ) 1 with hv₀
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary σ)
    simp [v₀] at this
  rcases hirr (Submodule.span K {v₀}) (by
      intro g hg w hw
      obtain ⟨a, ha⟩ := hG g hg
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [ha, Matrix.mulVec_smul, scalar_mulVec_eq_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      with h | h
  · exact hv₀0 (by simpa using h)
  · have := congrArg (fun W : Submodule K (σ → K) => Module.finrank K W) h
    simp only [finrank_span_singleton hv₀0, finrank_top, Module.finrank_fintype_fun_eq_card]
      at this
    omega

theorem not_irreducible_of_forall_scalar (hn : 2 ≤ n) {G : Subgroup (GL (Fin n) K)}
    (hG : ∀ g ∈ G, ∃ a : K, (g : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a) :
    ¬ IsIrreducibleMatrixRep G.subtype := fun h =>
  not_irreducibleOn_of_forall_scalar (by simpa using hn) hG (isIrreducibleOn_iff.mpr h)

theorem isUnit_of_mem_commutant {G : Subgroup (GL σ K)} (hG : IsIrreducibleOn G)
    {M : Matrix σ σ K} (hM : M ∈ commutant G) (h0 : M ≠ 0) : IsUnit M := by
  classical
  rw [← Matrix.mulVec_injective_iff_isUnit]
  let W : Submodule K (σ → K) := LinearMap.ker (Matrix.toLin' M)
  have hW : ∀ g ∈ G, ∀ w ∈ W, (g : Matrix σ σ K) *ᵥ w ∈ W := by
    intro g hg w hw
    simp only [W, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    have := (mem_commutant.mp hM) g hg
    rw [Matrix.mulVec_mulVec, ← this, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  rcases hG W hW with h | h
  · intro x y hxy
    have : x - y ∈ W := by simp [W, Matrix.mulVec_sub, hxy]
    rw [h, Submodule.mem_bot] at this
    exact sub_eq_zero.mp this
  · exfalso
    apply h0
    ext i j
    have : Pi.single j 1 ∈ W := h ▸ Submodule.mem_top
    simp only [W, LinearMap.mem_ker, Matrix.toLin'_apply] at this
    have := congrFun this i
    simpa [Matrix.mulVec_single] using this

theorem inv_mem_commutant {G : Subgroup (GL σ K)} {M : Matrix σ σ K} (hM : M ∈ commutant G) :
    M⁻¹ ∈ commutant G := by
  rw [mem_commutant] at hM ⊢
  intro g hg
  by_cases h : IsUnit M.det
  · calc (g : Matrix σ σ K) * M⁻¹ = M⁻¹ * (M * g) * M⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
      _ = M⁻¹ * (g * M) * M⁻¹ := by rw [hM g hg]
      _ = M⁻¹ * g := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

@[expose, instance_reducible] noncomputable def commutantDivisionRing [Nonempty σ]
    {G : Subgroup (GL σ K)} (hG : IsIrreducibleOn G) : DivisionRing (commutant G) :=
  DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · left
      have h0 : (a : Matrix σ σ K) ≠ 0 := fun h' => h (Subtype.ext h')
      have hdet : IsUnit (a : Matrix σ σ K).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mem_commutant hG a.2 h0)
      refine ⟨⟨a, ⟨(a : Matrix σ σ K)⁻¹, inv_mem_commutant a.2⟩, ?_, ?_⟩, rfl⟩
      · exact Subtype.ext (Matrix.mul_nonsing_inv _ hdet)
      · exact Subtype.ext (Matrix.nonsing_inv_mul _ hdet)

@[expose, instance_reducible] noncomputable def commutantField [Nonempty σ] [Finite K]
    {G : Subgroup (GL σ K)} (hG : IsIrreducibleOn G) : Field (commutant G) :=
  letI := commutantDivisionRing hG
  littleWedderburn (commutant G)

theorem finrank_commutant_dvd [Nonempty σ] [Finite K] {G : Subgroup (GL σ K)}
    (hG : IsIrreducibleOn G) : Module.finrank K (commutant G) ∣ Fintype.card σ := by
  let := commutantDivisionRing hG
  have : Module.Finite (commutant G) (σ → K) :=
    Module.Finite.of_restrictScalars_finite K (commutant G) (σ → K)
  have h1 : Nat.card (σ → K) = Nat.card K ^ Fintype.card σ := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := σ)]
  have h2 : Nat.card (σ → K) =
      Nat.card (commutant G) ^ Module.finrank (commutant G) (σ → K) :=
    Module.natCard_eq_pow_finrank
  have h3 : Nat.card (commutant G) = Nat.card K ^ Module.finrank K (commutant G) :=
    Module.natCard_eq_pow_finrank
  rw [h3, ← pow_mul, h1] at h2
  exact ⟨_, Nat.pow_right_injective Finite.one_lt_card h2⟩

theorem mem_commutant_of_finrank_eq [Nonempty σ] [Finite K] {G : Subgroup (GL σ K)}
    (hG : IsIrreducibleOn G) (hfull : Module.finrank K (commutant G) = Fintype.card σ) :
    ∀ g ∈ G, (g : Matrix σ σ K) ∈ commutant G := by
  classical
  let := commutantField hG
  set v₀ : σ → K := Pi.single (Classical.arbitrary σ) 1 with hv₀
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary σ)
    simp [v₀] at this
  let φ : commutant G →ₗ[K] (σ → K) :=
    { toFun := fun c => (c : Matrix σ σ K) *ᵥ v₀
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun a b => by simp [Matrix.smul_mulVec] }
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    have h0' : (c : Matrix σ σ K) ≠ 0 := fun h => h0 (Subtype.ext h)
    apply hv₀0
    apply Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_of_mem_commutant hG c.2 h0')
    simpa [φ] using hc
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hfull)).mp hφinj
  have hcomm : ∀ a b : commutant G, (a : Matrix σ σ K) * b = b * a :=
    fun a b => congrArg Subtype.val (mul_comm a b)
  intro g hg
  obtain ⟨c₀, hc₀⟩ := hφsurj ((g : Matrix σ σ K) *ᵥ v₀)
  have hgc : (g : Matrix σ σ K) = c₀ := by
    rw [Matrix.ext_iff_mulVec]
    intro w
    obtain ⟨c, rfl⟩ := hφsurj w
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at hc₀ ⊢
    rw [Matrix.mulVec_mulVec, (mem_commutant.mp c.2) g hg, ← Matrix.mulVec_mulVec, ← hc₀,
      Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  rw [hgc]
  exact c₀.2

theorem commutant_eq_bot_or_cyclic [Finite K] (hn : n.Prime) {G : Subgroup (GL (Fin n) K)}
    (hG : IsIrreducibleMatrixRep G.subtype) :
    commutant G = ⊥ ∨
      (IsCyclic G ∧ Nat.card G ∣ Nat.card K ^ n - 1 ∧ ¬ Nat.card G ∣ Nat.card K - 1) := by
  classical
  have : NeZero n := ⟨hn.ne_zero⟩
  have hG' : IsIrreducibleOn G := isIrreducibleOn_iff.mpr hG
  have hdvd := finrank_commutant_dvd hG'
  rw [Fintype.card_fin] at hdvd
  rcases (Nat.dvd_prime hn).mp hdvd with h1 | hfull
  · exact Or.inl (Subalgebra.finrank_eq_one_iff.mp h1)
  right
  let := commutantField hG'
  have hGC := mem_commutant_of_finrank_eq hG' (by rw [hfull, Fintype.card_fin])
  let f : G →* commutant G :=
    { toFun := fun g => ⟨((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hGC g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hf : ∀ g, ((f g : commutant G) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun g => rfl
  have hfinj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  refine ⟨isCyclic_of_injective_ringHom f hfinj, ?_, ?_⟩
  · have := Subgroup.card_dvd_of_injective f.toHomUnits (fun a b h => hfinj (by
        have := congrArg Units.val h
        simpa using this))
    rwa [Nat.card_units, Module.natCard_eq_pow_finrank (K := K) (V := commutant G), hfull] at this
  ·
    intro hdvd
    have : Fintype K := Fintype.ofFinite K
    have hq : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
    have hq2 : 2 ≤ Fintype.card K := by rw [← hq]; exact Finite.one_lt_card
    have hpos : 0 < Fintype.card K - 1 := by omega
    refine not_irreducible_of_forall_scalar hn.two_le ?_ hG
    intro g hg
    have hpow : (f ⟨g, hg⟩) ^ (Fintype.card K - 1) = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : G) ^ (Fintype.card K - 1) = 1 := by
        obtain ⟨k, hk⟩ := hdvd
        rw [← hq, hk, pow_mul, pow_card_eq_one', one_pow]
      rw [this, map_one]
    let T : Finset (commutant G) :=
      (Finset.univ.filter (fun a : K => a ≠ 0)).image (algebraMap K (commutant G))
    have hTcard : T.card = Fintype.card K - 1 := by
      rw [Finset.card_image_of_injective _ (algebraMap K (commutant G)).injective,
        Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have hTroots : T ⊆ Polynomial.nthRootsFinset (Fintype.card K - 1) (1 : commutant G) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.mem_nthRootsFinset hpos, ← map_pow,
        FiniteField.pow_card_sub_one_eq_one a (Finset.mem_filter.mp ha).2, map_one]
    by_contra hnot
    have hfg : f ⟨g, hg⟩ ∉ T := by
      intro hx
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hx
      apply hnot
      refine ⟨a, ?_⟩
      have := congrArg Subtype.val ha
      rw [hf] at this
      rw [← this]
      simp [Matrix.algebraMap_eq_diagonal]
    have hsub : insert (f ⟨g, hg⟩) T ⊆
        Polynomial.nthRootsFinset (Fintype.card K - 1) (1 : commutant G) :=
      Finset.insert_subset ((Polynomial.mem_nthRootsFinset hpos _).mpr hpow) hTroots
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hfg, hTcard] at hcard
    have hle : (Polynomial.nthRootsFinset (Fintype.card K - 1) (1 : commutant G)).card ≤
        Fintype.card K - 1 := by
      rw [Polynomial.nthRootsFinset_def]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    omega

theorem scalar_commutant_or_cyclic [Finite K] (hn : n.Prime) {G : Subgroup (GL (Fin n) K)}
    (hG : IsIrreducibleMatrixRep G.subtype) :
    (∀ M : Matrix (Fin n) (Fin n) K, (∀ g ∈ G, (g : Matrix (Fin n) (Fin n) K) * M = M * g) →
      ∃ c : K, M = Matrix.scalar (Fin n) c) ∨
      (IsCyclic G ∧ Nat.card G ∣ Nat.card K ^ n - 1 ∧ ¬ Nat.card G ∣ Nat.card K - 1) := by
  rcases commutant_eq_bot_or_cyclic hn hG with h | h
  · left
    intro M hM
    have hM' : M ∈ commutant G := mem_commutant.mpr hM
    rw [h, Algebra.mem_bot] at hM'
    obtain ⟨c, rfl⟩ := hM'
    exact ⟨c, by simp [Matrix.algebraMap_eq_diagonal]⟩
  · exact Or.inr h

theorem cyclic_of_irreducible_of_commute [Finite K] (hn : n.Prime) {G : Subgroup (GL (Fin n) K)}
    (hG : IsIrreducibleMatrixRep G.subtype) (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a) :
    IsCyclic G ∧ Nat.card G ∣ Nat.card K ^ n - 1 ∧ ¬ Nat.card G ∣ Nat.card K - 1 := by
  refine (scalar_commutant_or_cyclic hn hG).resolve_left fun h => ?_
  refine not_irreducible_of_forall_scalar hn.two_le (fun g hg => h g fun x hx => ?_) hG
  rw [← Units.val_mul, ← Units.val_mul, hcomm x hx g hg]

end CFSG.RankThree.SubgroupLists
