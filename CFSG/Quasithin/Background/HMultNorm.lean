module

public import CFSG.Quasithin.Background.HMult

public section

namespace CFSG.Quasithin.H.Mult

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix Kronecker

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private def hmnToAddHom {k : ℕ} (T : MulAut (StdMod (Fin k × ι) K)) :
    (Fin k × ι → K) →+ (Fin k × ι → K) where
  toFun := toAddMap T
  map_zero' := toAddMap_zero T
  map_add' := toAddMap_add T

private def hmnBlk {k : ℕ} (T : MulAut (StdMod (Fin k × ι) K)) (j' j : Fin k) :
    (ι → K) →+ (ι → K) where
  toFun x := fun i => toAddMap T (blockVec (ι := ι) j x) (j', i)
  map_zero' := by
    have h0 : blockVec (ι := ι) j (0 : ι → K) = 0 := by
      funext p
      simp [blockVec]
    funext i
    rw [h0, toAddMap_zero]
    rfl
  map_add' x y := by
    funext i
    rw [blockVec_add, toAddMap_add]
    rfl

private theorem hmnToAddMap_eq_sum_blk {k : ℕ} (T : MulAut (StdMod (Fin k × ι) K))
    (v : Fin k × ι → K) (p : Fin k × ι) :
    toAddMap T v p = ∑ j, hmnBlk T p.1 j (fun i => v (j, i)) p.2 := by
  conv_lhs => rw [← sum_blockVec (ι := ι) v]
  rw [show toAddMap T (∑ j, blockVec (ι := ι) j (fun i => v (j, i))) =
      ∑ j, toAddMap T (blockVec (ι := ι) j (fun i => v (j, i))) from
    map_sum (hmnToAddHom T) _ _]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

private theorem hmnBlk_twisted {k : ℕ} {T : MulAut (StdMod (Fin k × ι) K)} {γ γ' : GL ι K}
    (h : T * matAut (diagGL k γ) * T⁻¹ = matAut (diagGL k γ')) (j' j : Fin k) (x : ι → K) :
    hmnBlk T j' j (((γ : Matrix ι ι K) *ᵥ x)) =
      ((γ' : Matrix ι ι K) *ᵥ hmnBlk T j' j x) := by
  have hT : T * matAut (diagGL k γ) = matAut (diagGL k γ') * T := by
    calc T * matAut (diagGL k γ)
        = (T * matAut (diagGL k γ) * T⁻¹) * T := by group
      _ = matAut (diagGL k γ') * T := by rw [h]
  have h1 : ∀ w : Fin k × ι → K,
      toAddMap T (((diagGL k γ : GL (Fin k × ι) K) :
          Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ w) =
        ((diagGL k γ' : GL (Fin k × ι) K) :
          Matrix (Fin k × ι) (Fin k × ι) K) *ᵥ toAddMap T w := by
    intro w
    have := congrArg (fun y => toAddMap y w) hT
    simpa only [toAddMap_mul, toAddMap_matAut] using this
  funext i
  have h2 := congrFun (h1 (blockVec (ι := ι) j x)) (j', i)
  rw [diagGL_blockVec, diagGL_mulVec] at h2
  change toAddMap T (blockVec (ι := ι) j (((γ : Matrix ι ι K) *ᵥ x))) (j', i) =
    ((γ' : Matrix ι ι K) *ᵥ fun i => toAddMap T (blockVec (ι := ι) j x) (j', i)) i
  exact h2

theorem exists_of_mem_normalizer_diag [Finite K] [Nonempty ι] {k : ℕ} [NeZero k]
    {Γ : Subgroup (GL ι K)} (hΓ : HasScalarCommutant Γ)
    {T : MulAut (StdMod (Fin k × ι) K)}
    (hT : T ∈ Subgroup.normalizer
      (natImage (diagSub k Γ) : Set (MulAut (StdMod (Fin k × ι) K)))) :
    ∃ (A : MulAut (StdMod ι K)) (σ : K ≃+* K) (B : GL (Fin k) K),
      A ∈ natNorm Γ ∧ IsSemilinear A σ ∧ IsSemilinear T σ ∧
      (∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap T v p =
        toAddMap A (fun i => ∑ j, (B : Matrix (Fin k) (Fin k) K) p.1 j * v (j, i)) p.2) ∧
      (∀ γ ∈ Γ, ∃ γ' ∈ Γ, A * matAut γ * A⁻¹ = matAut γ' ∧
        T * matAut (diagGL k γ) * T⁻¹ = matAut (diagGL k γ')) := by
  classical
  have hconj : ∀ γ : ↥Γ, ∃ γ' : ↥Γ,
      T * matAut (diagGL k (γ : GL ι K)) * T⁻¹ =
        matAut (diagGL k (γ' : GL ι K)) := by
    intro γ
    have hmem : matAut (diagGL k (γ : GL ι K)) ∈ natImage (diagSub k Γ) := by
      refine ⟨⟨diagGL k (γ : GL ι K), Subgroup.mem_map_of_mem (diagGL k) γ.2⟩, rfl⟩
    have hX : T * matAut (diagGL k (γ : GL ι K)) * T⁻¹ ∈ natImage (diagSub k Γ) :=
      (Subgroup.mem_normalizer_iff.mp hT (matAut (diagGL k (γ : GL ι K)))).mp hmem
    obtain ⟨⟨g, hgmem⟩, hgval⟩ := hX
    obtain ⟨γ', hγ'Γ, hγ'eq⟩ := Subgroup.mem_map.mp hgmem
    refine ⟨⟨γ', hγ'Γ⟩, ?_⟩
    rw [← hgval]
    show matAut g = matAut (diagGL k (γ' : GL ι K))
    rw [← hγ'eq]
  let S : MulAut (StdMod (Fin k × ι) K) := T⁻¹
  have hconjS : ∀ γ γ' : ↥Γ,
      T * matAut (diagGL k (γ : GL ι K)) * T⁻¹ =
        matAut (diagGL k (γ' : GL ι K)) →
      S * matAut (diagGL k (γ' : GL ι K)) * S⁻¹ =
        matAut (diagGL k (γ : GL ι K)) := by
    intro γ γ' h
    dsimp only [S]
    have h' := congrArg (fun y => T⁻¹ * y * T) h
    simpa [mul_assoc] using h'.symm
  have hscalar : ∀ j : Fin k, ∃ c : K, ∀ x : ι → K,
      hmnBlk S (0 : Fin k) j (hmnBlk T j (0 : Fin k) x) = c • x := by
    intro j
    let f : (ι → K) →+ (ι → K) := (hmnBlk S (0 : Fin k) j).comp (hmnBlk T j (0 : Fin k))
    have hf : ∀ γ ∈ Γ, ∀ x : ι → K,
        f (((γ : GL ι K) : Matrix ι ι K) *ᵥ x) =
          ((γ : GL ι K) : Matrix ι ι K) *ᵥ f x := by
      intro γ hγ x
      obtain ⟨γ', hγ'⟩ := hconj ⟨γ, hγ⟩
      have hS := hconjS ⟨γ, hγ⟩ γ' hγ'
      have h1 : hmnBlk T j (0 : Fin k) (((γ : GL ι K) : Matrix ι ι K) *ᵥ x) =
          ((γ' : GL ι K) : Matrix ι ι K) *ᵥ hmnBlk T j (0 : Fin k) x :=
        hmnBlk_twisted hγ' j (0 : Fin k) x
      have h2 : hmnBlk S (0 : Fin k) j
          (((γ' : GL ι K) : Matrix ι ι K) *ᵥ hmnBlk T j (0 : Fin k) x) =
          ((γ : GL ι K) : Matrix ι ι K) *ᵥ
            hmnBlk S (0 : Fin k) j (hmnBlk T j (0 : Fin k) x) :=
        hmnBlk_twisted hS (0 : Fin k) j (hmnBlk T j (0 : Fin k) x)
      change hmnBlk S (0 : Fin k) j
          (hmnBlk T j (0 : Fin k) (((γ : GL ι K) : Matrix ι ι K) *ᵥ x)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ hmnBlk S (0 : Fin k) j (hmnBlk T j (0 : Fin k) x)
      rw [h1, h2]
    obtain ⟨c, hc⟩ := hΓ f hf
    exact ⟨c, hc⟩
  choose c hc using hscalar
  have hsum : (∑ j : Fin k, c j) = 1 := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hcomp : ∀ (x : ι → K) (i : ι),
        (∑ j : Fin k, hmnBlk S (0 : Fin k) j (hmnBlk T j (0 : Fin k) x) i) = x i := by
      intro x i
      have hT0 : toAddMap T (blockVec (ι := ι) (0 : Fin k) x) =
          fun p => hmnBlk T p.1 (0 : Fin k) x p.2 := by
        funext p
        rw [hmnToAddMap_eq_sum_blk]
        rw [Finset.sum_eq_single (0 : Fin k)]
        · simp [blockVec]
        · intro b _ hb
          have hx : (fun i => blockVec (ι := ι) (0 : Fin k) x (b, i)) = 0 := by
            funext i
            simp [blockVec, hb]
          rw [hx]
          simp
        · intro hb
          exact (hb (Finset.mem_univ _)).elim
      have h1 : toAddMap T⁻¹ (toAddMap T (blockVec (ι := ι) (0 : Fin k) x)) =
          blockVec (ι := ι) (0 : Fin k) x := toAddMap_apply_inv T _
      have h2 : toAddMap T⁻¹ (fun p => hmnBlk T p.1 (0 : Fin k) x p.2) =
          blockVec (ι := ι) (0 : Fin k) x := by
        rw [← hT0]
        exact h1
      have h3 := congrFun h2 ((0 : Fin k), i)
      rw [hmnToAddMap_eq_sum_blk] at h3
      simpa [S, blockVec] using h3
    have hx := hcomp (Pi.single i₀ (1 : K)) i₀
    simp only [hc, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hx
    exact hx
  have hne : ∃ j : Fin k, c j ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : (∑ j : Fin k, c j) = 0 := Finset.sum_eq_zero (fun j _ => h j)
    rw [hsum] at h0
    exact one_ne_zero h0
  obtain ⟨j₀, hj₀⟩ := hne
  have hinj : Function.Injective (hmnBlk T j₀ (0 : Fin k)) := by
    intro x y hxy
    have h0 : hmnBlk T j₀ (0 : Fin k) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h1 : hmnBlk S (0 : Fin k) j₀ (hmnBlk T j₀ (0 : Fin k) (x - y)) = 0 := by
      rw [h0, map_zero]
    rw [hc j₀ (x - y)] at h1
    have h2 : x - y = 0 := by
      rcases smul_eq_zero.mp h1 with hc0 | hxy0
      · exact absurd hc0 hj₀
      · exact hxy0
    exact sub_eq_zero.mp h2
  have hsurj : Function.Surjective (hmnBlk T j₀ (0 : Fin k)) :=
    Finite.surjective_of_injective hinj
  let eA : (ι → K) ≃+ (ι → K) :=
    AddEquiv.ofBijective (hmnBlk T j₀ (0 : Fin k)) ⟨hinj, hsurj⟩
  let A : MulAut (StdMod ι K) := AddEquiv.toMultiplicative eA
  have hA_apply : ∀ v : ι → K, toAddMap A v = hmnBlk T j₀ (0 : Fin k) v := fun v => rfl
  have hA_eq : ∀ v : ι → K, toAddMap A v = eA v := fun v => rfl
  have hconjA : ∀ γ : ↥Γ, ∃ γ' : ↥Γ,
      (∀ x : ι → K, eA (((γ : GL ι K) : Matrix ι ι K) *ᵥ x) =
        ((γ' : GL ι K) : Matrix ι ι K) *ᵥ eA x) ∧
      T * matAut (diagGL k (γ : GL ι K)) * T⁻¹ =
        matAut (diagGL k (γ' : GL ι K)) := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hconj γ
    refine ⟨γ', ?_, hγ'⟩
    intro x
    change hmnBlk T j₀ (0 : Fin k) (((γ : GL ι K) : Matrix ι ι K) *ᵥ x) =
      ((γ' : GL ι K) : Matrix ι ι K) *ᵥ hmnBlk T j₀ (0 : Fin k) x
    exact hmnBlk_twisted hγ' j₀ (0 : Fin k) x
  have hAconj_of : ∀ (γ γ' : ↥Γ),
      (∀ x : ι → K, eA (((γ : GL ι K) : Matrix ι ι K) *ᵥ x) =
        ((γ' : GL ι K) : Matrix ι ι K) *ᵥ eA x) →
      A * natAut Γ γ * A⁻¹ = natAut Γ γ' := by
    intro γ γ' hblk
    have hmul : A * natAut Γ γ = natAut Γ γ' * A := by
      apply toAddMap_injective
      intro v
      rw [toAddMap_mul, toAddMap_mul, toAddMap_natAut, toAddMap_natAut]
      change eA (((γ : GL ι K) : Matrix ι ι K) *ᵥ v) =
        ((γ' : GL ι K) : Matrix ι ι K) *ᵥ eA v
      exact hblk v
    calc A * natAut Γ γ * A⁻¹ = (natAut Γ γ' * A) * A⁻¹ := by rw [hmul]
      _ = natAut Γ γ' := by group
  have hforward : ∀ γ : ↥Γ, A * natAut Γ γ * A⁻¹ ∈ natImage Γ := by
    intro γ
    obtain ⟨γ', hblk, -⟩ := hconjA γ
    exact ⟨γ', (hAconj_of γ γ' hblk).symm⟩
  have hmap_le : Subgroup.map (MulAut.conj A).toMonoidHom (natImage Γ) ≤ natImage Γ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨γ, hγ⟩ := hy
    rw [← hγ]
    simpa [MulAut.conj_apply] using hforward γ
  have hcard_map : Nat.card ↥(Subgroup.map (MulAut.conj A).toMonoidHom (natImage Γ)) =
      Nat.card ↥(natImage Γ) :=
    Subgroup.card_map_of_injective (MulAut.conj A).injective
  have hmap_eq : Subgroup.map (MulAut.conj A).toMonoidHom (natImage Γ) = natImage Γ :=
    Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard_map.symm)
  have hinv_mem : ∀ h ∈ natImage Γ, A⁻¹ * h * A ∈ natImage Γ := by
    intro h hh
    have hmem : h ∈ Subgroup.map (MulAut.conj A).toMonoidHom (natImage Γ) := by
      rw [hmap_eq]
      exact hh
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
    have hx' : A⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj A)) x * A = x := by
      change A⁻¹ * (MulAut.conj A) x * A = x
      rw [MulAut.conj_apply]
      group
    rw [← hxeq, hx']
    exact hx
  have hA_mem : A ∈ natNorm Γ := by
    rw [natNorm, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨γ, hγ⟩ := hh
      rw [← hγ]
      exact hforward γ
    · intro hh
      have := hinv_mem (A * h * A⁻¹) hh
      simpa [mul_assoc] using this
  obtain ⟨σ, hAsemi⟩ := exists_semilinear hΓ hA_mem
  have hmu_exists : ∀ j' j : Fin k, ∃ μ : K, ∀ x : ι → K,
      eA.symm (hmnBlk T j' j x) = μ • x := by
    intro j' j
    let g : (ι → K) →+ (ι → K) := (eA.symm.toAddMonoidHom).comp (hmnBlk T j' j)
    have hg : ∀ γ ∈ Γ, ∀ x : ι → K,
        g (((γ : GL ι K) : Matrix ι ι K) *ᵥ x) =
          ((γ : GL ι K) : Matrix ι ι K) *ᵥ g x := by
      intro γ hγ x
      obtain ⟨γ', hblk, hTconj⟩ := hconjA ⟨γ, hγ⟩
      have hTb := hmnBlk_twisted hTconj j' j x
      have hinv : ∀ y : ι → K,
          eA.symm (((γ' : GL ι K) : Matrix ι ι K) *ᵥ y) =
            ((γ : GL ι K) : Matrix ι ι K) *ᵥ eA.symm y := by
        intro y
        apply eA.injective
        rw [eA.apply_symm_apply, hblk, eA.apply_symm_apply]
      change eA.symm (hmnBlk T j' j (((γ : GL ι K) : Matrix ι ι K) *ᵥ x)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ eA.symm (hmnBlk T j' j x)
      rw [hTb]
      exact hinv _
    obtain ⟨μ, hμ⟩ := hΓ g hg
    exact ⟨μ, hμ⟩
  choose μ hμ using hmu_exists
  have hTblk : ∀ (j' j : Fin k) (x : ι → K),
      hmnBlk T j' j x = eA (μ j' j • x) := by
    intro j' j x
    have h := congrArg eA (hμ j' j x)
    rwa [eA.apply_symm_apply] at h
  let B : Matrix (Fin k) (Fin k) K := Matrix.of fun j' j => μ j' j
  have hTform : ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap T v p =
      toAddMap A (fun i => ∑ j, B p.1 j * v (j, i)) p.2 := by
    intro v p
    rw [hmnToAddMap_eq_sum_blk]
    have h2 : ∀ j : Fin k, hmnBlk T p.1 j (fun i => v (j, i)) p.2 =
        eA (μ p.1 j • (fun i => v (j, i))) p.2 := by
      intro j
      rw [hTblk]
    rw [Finset.sum_congr rfl (fun j _ => h2 j)]
    rw [← Finset.sum_apply, ← map_sum, hA_eq]
    have hvec : (∑ j : Fin k, μ p.1 j • (fun i => v (j, i))) =
        (fun i => ∑ j, B p.1 j * v (j, i)) := by
      funext i
      simp [B, Pi.smul_apply, smul_eq_mul]
    rw [hvec]
  let G : (Fin k × ι → K) →+ (Fin k × ι → K) :=
    AddMonoidHom.mk' (fun v p => ∑ j, B p.1 j * v (j, p.2)) (by
      intro x y
      funext p
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
  let D : (Fin k × ι → K) →+ (Fin k × ι → K) :=
    AddMonoidHom.mk' (fun v p => eA (fun i => v (p.1, i)) p.2) (by
      intro x y
      funext p
      have h1 : (fun i => (x + y) (p.1, i)) =
          (fun i => x (p.1, i) + y (p.1, i)) := rfl
      have h2 : (fun i => x (p.1, i) + y (p.1, i)) =
          (fun i => x (p.1, i)) + (fun i => y (p.1, i)) := rfl
      rw [h1, h2, map_add]
      rfl)
  have hD_inj : Function.Injective D := by
    intro x y hxy
    have h : D (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    funext p
    have hp : ∀ i : ι, eA (fun i' => (x - y) (p.1, i')) i = 0 := by
      intro i
      have hpi := congrFun h (p.1, i)
      simpa [D] using hpi
    have hblock : (fun i' => (x - y) (p.1, i')) = 0 := by
      apply eA.injective
      rw [map_zero]
      funext i
      exact hp i
    have hxy : x p - y p = 0 := by simpa using congrFun hblock p.2
    exact sub_eq_zero.mp hxy
  have hTG : ∀ v : Fin k × ι → K, toAddMap T v = D (G v) := by
    intro v
    funext p
    rw [hTform]
    rfl
  have hT_inj : Function.Injective (toAddMap T) := by
    intro x y h
    have := congrArg (toAddMap T⁻¹) h
    simpa only [toAddMap_apply_inv] using this
  have hT_surj : Function.Surjective (toAddMap T) := by
    intro y
    exact ⟨toAddMap T⁻¹ y, by simpa only [toAddMap_inv_apply]⟩
  have hG_inj : Function.Injective G := by
    intro x y hxy
    apply hT_inj
    rw [hTG, hTG, hxy]
  have hG_surj : Function.Surjective G := by
    intro y
    obtain ⟨v, hv⟩ := hT_surj (D y)
    exact ⟨v, hD_inj (by rw [← hTG, hv])⟩
  have hBsurj : Function.Surjective B.mulVec := by
    intro w
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    let z : Fin k × ι → K := fun p => w p.1
    obtain ⟨v, hv⟩ := hG_surj z
    refine ⟨fun j => v (j, i₀), ?_⟩
    funext i
    have h := congrFun hv (i, i₀)
    simpa [G, z, Matrix.mulVec, dotProduct] using h
  have hunit : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hBsurj
  have hTsemi : IsSemilinear T σ := by
    intro c v
    funext p
    rw [hTform]
    have harg : (fun i => ∑ j, B p.1 j * (c • v) (j, i)) =
        c • (fun i => ∑ j, B p.1 j * v (j, i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [harg, hAsemi]
    simp only [Pi.smul_apply, smul_eq_mul, hTform]
  refine ⟨A, σ, hunit.unit, hA_mem, hAsemi, hTsemi, ?_, ?_⟩
  · intro v p
    have hBcoe : ((hunit.unit : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = B :=
      hunit.unit_spec
    rw [hTform, hBcoe]
  · intro γ hγ
    obtain ⟨γ'sub, hblk, hTconj⟩ := hconjA ⟨γ, hγ⟩
    refine ⟨(γ'sub : GL ι K), γ'sub.2, ?_, ?_⟩
    · exact hAconj_of ⟨γ, hγ⟩ γ'sub hblk
    · exact hTconj

private def hmnCurryMul {k : ℕ} : StdMod (Fin k × ι) K ≃* (Fin k → StdMod ι K) where
  toFun v j := Multiplicative.ofAdd (fun i => Multiplicative.toAdd v (j, i))
  invFun w := Multiplicative.ofAdd (fun p => Multiplicative.toAdd (w p.1) p.2)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext p
    simp
  right_inv w := by
    funext j
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' v w := by
    funext j
    apply Multiplicative.toAdd.injective
    funext i
    simp [toAdd_mul]

theorem rkIdx_fixV_of_diag_formula {k : ℕ} {T : MulAut (StdMod (Fin k × ι) K)}
    {A : MulAut (StdMod ι K)}
    (hT : ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap T v p =
      toAddMap A (fun i => v (p.1, i)) p.2) :
    rkIdx (fixV (Subgroup.zpowers T)) = k * rkIdx (fixV (Subgroup.zpowers A)) := by
  classical
  have hmap : Subgroup.map (hmnCurryMul (k := k) (ι := ι) (K := K)).toMonoidHom
      (fixV (Subgroup.zpowers T)) =
      Subgroup.pi Set.univ (fun _ : Fin k => fixV (Subgroup.zpowers A)) := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
      rw [Subgroup.mem_pi]
      intro j _
      rw [mem_fixV_zpowers_iff] at hv ⊢
      apply Multiplicative.toAdd.injective
      funext i
      have h1 : toAddMap T (Multiplicative.toAdd v) (j, i) =
          Multiplicative.toAdd v (j, i) := by
        simpa [toAddMap] using congrFun (congrArg Multiplicative.toAdd hv) (j, i)
      rw [hT] at h1
      simpa [hmnCurryMul, toAddMap] using h1
    · intro hw
      rw [Subgroup.mem_pi] at hw
      refine Subgroup.mem_map.mpr ⟨hmnCurryMul.symm w, ?_, ?_⟩
      · rw [mem_fixV_zpowers_iff]
        apply Multiplicative.toAdd.injective
        funext p
        have hwfix : A (w p.1) = w p.1 :=
          mem_fixV_zpowers_iff.mp (hw p.1 (Set.mem_univ _))
        have hblock : (fun i => Multiplicative.toAdd (hmnCurryMul.symm w) (p.1, i)) =
            Multiplicative.toAdd (w p.1) := by
          funext i
          simp [hmnCurryMul]
        change toAddMap T (Multiplicative.toAdd (hmnCurryMul.symm w)) p =
          Multiplicative.toAdd (hmnCurryMul.symm w) p
        rw [hT, hblock]
        change Multiplicative.toAdd (A (w p.1)) p.2 =
          Multiplicative.toAdd (hmnCurryMul.symm w) p
        rw [hwfix]
        simp [hmnCurryMul]
      · exact hmnCurryMul.apply_symm_apply w
  have hidx_map : (fixV (Subgroup.zpowers T)).index =
      (Subgroup.map (hmnCurryMul (k := k) (ι := ι) (K := K)).toMonoidHom
        (fixV (Subgroup.zpowers T))).index := by
    have h := Subgroup.index_map (H := fixV (Subgroup.zpowers T))
      (f := (hmnCurryMul (k := k) (ι := ι) (K := K)).toMonoidHom)
    have hker : (hmnCurryMul (k := k) (ι := ι) (K := K)).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr hmnCurryMul.injective
    rw [hker, sup_bot_eq,
      MonoidHom.range_eq_top_of_surjective _ hmnCurryMul.surjective, Subgroup.index_top,
      mul_one] at h
    exact h.symm
  have hidx_pi :
      (Subgroup.pi Set.univ (fun _ : Fin k => fixV (Subgroup.zpowers A))).index =
        ((fixV (Subgroup.zpowers A)).index) ^ k := by
    rw [Subgroup.index_pi]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hidx : (fixV (Subgroup.zpowers T)).index =
      ((fixV (Subgroup.zpowers A)).index) ^ k := by
    rw [hidx_map, hmap, hidx_pi]
  calc rkIdx (fixV (Subgroup.zpowers T))
      = padicValNat 2 ((fixV (Subgroup.zpowers T)).index) := rfl
    _ = padicValNat 2 (((fixV (Subgroup.zpowers A)).index) ^ k) := by rw [hidx]
    _ = k * padicValNat 2 ((fixV (Subgroup.zpowers A)).index) := padicValNat.pow _ _
    _ = k * rkIdx (fixV (Subgroup.zpowers A)) := rfl

private theorem hmnLineEmb_ne {k : ℕ} {u v : Fin k → K} (hu : u ≠ 0)
    (hv : v ∉ Submodule.span K ({u} : Set (Fin k → K))) {x : ι → K} (hx : x ≠ 0)
    (y : ι → K) :
    lineEmb (ι := ι) v (Multiplicative.ofAdd y) ≠
      lineEmb (ι := ι) u (Multiplicative.ofAdd x) := by
  intro h
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hcoord : ∀ j, v j * y i₀ = u j * x i₀ := by
    intro j
    have := congrFun (congrArg Multiplicative.toAdd h) (j, i₀)
    simpa [lineEmb_toAdd] using this
  have hy : y i₀ ≠ 0 := by
    intro hy0
    have huj : ∀ j, u j = 0 := by
      intro j
      have hj := hcoord j
      rw [hy0, mul_zero] at hj
      exact (mul_eq_zero.mp hj.symm).resolve_right hi₀
    exact hu (funext huj)
  refine hv ?_
  rw [Submodule.mem_span_singleton]
  refine ⟨x i₀ / y i₀, ?_⟩
  funext j
  rw [Pi.smul_apply, smul_eq_mul]
  have hj := hcoord j
  field_simp [hy]
  rw [mul_comm (x i₀) (u j), mul_comm (y i₀) (v j), hj]

theorem le_rkIdx_fixV_of_nonscalar [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) {k : ℕ}
    {T : MulAut (StdMod (Fin k × ι) K)} {A : MulAut (StdMod ι K)}
    (hA : IsSemilinear A (RingEquiv.refl K)) {B : Matrix (Fin k) (Fin k) K}
    (hT : ∀ (v : Fin k × ι → K) (p : Fin k × ι), toAddMap T v p =
      toAddMap A (fun i => ∑ j, B p.1 j * v (j, i)) p.2)
    (hB : ∀ c : K, B ≠ c • (1 : Matrix (Fin k) (Fin k) K)) :
    n * Fintype.card ι ≤ rkIdx (fixV (Subgroup.zpowers T)) := by
  classical
  let f : (Fin k → K) →ₗ[K] (Fin k → K) := Matrix.mulVecLin B
  have hnot : ¬ ∀ v : Fin k → K, ¬ LinearIndependent K ![v, f v] := by
    intro h
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
    apply hB a
    ext i j
    have h1 := congrFun (congrArg (fun g : (Fin k → K) →ₗ[K] (Fin k → K) =>
      g (Pi.single j 1)) ha) i
    simpa [f, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
      Matrix.smul_apply, Matrix.one_apply] using h1
  push Not at hnot
  obtain ⟨u, hli⟩ := hnot
  have hli' : LinearIndependent K ![u, B *ᵥ u] := by
    simpa [f, Matrix.mulVecLin_apply] using hli
  have hu : u ≠ 0 := hli'.ne_zero 0
  have hspan : B *ᵥ u ∉ Submodule.span K ({u} : Set (Fin k → K)) := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hzero : (-c) • u + (1 : K) • (B *ᵥ u) = 0 := by
      rw [← hc]
      simp
    have hpair := LinearIndependent.pair_iff.mp hli' (-c) 1 hzero
    exact one_ne_zero hpair.2
  have hline : ∀ x : StdMod ι K, T (lineEmb (ι := ι) u x) =
      lineEmb (ι := ι) (fun j => (B *ᵥ u) j) (A x) := by
    intro x
    have := normalForm_lineEmb (k := k) (T := T) (A := A)
      (σ := RingEquiv.refl K) hA hT u x
    simpa using this
  have hfix_inf : fixV (Subgroup.zpowers T) ⊓ lineSub (ι := ι) u = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzfix, hzline⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨x, hxeq⟩ := hzline
    by_cases hx : x = 0
    · rw [Subgroup.mem_bot]
      apply Multiplicative.toAdd.injective
      rw [hxeq]
      funext p
      simp [hx]
    · exfalso
      have hTz : T z = z := mem_fixV_zpowers_iff.mp hzfix
      let xs : StdMod ι K := Multiplicative.ofAdd x
      have hxs : xs ≠ 1 := by
        intro h0
        exact hx (by simpa [xs] using congrArg Multiplicative.toAdd h0)
      have hz_eq : z = lineEmb (ι := ι) u xs := by
        apply Multiplicative.toAdd.injective
        rw [lineEmb_toAdd]
        exact hxeq
      rw [hz_eq, hline xs] at hTz
      have hTz' : lineEmb (ι := ι) (fun j => (B *ᵥ u) j)
          (Multiplicative.ofAdd (Multiplicative.toAdd (A xs))) =
            lineEmb (ι := ι) u (Multiplicative.ofAdd x) := by
        simpa using hTz
      exact hmnLineEmb_ne hu hspan hx _ hTz'
  let H : Subgroup (StdMod (Fin k × ι) K) := fixV (Subgroup.zpowers T)
  let φ : ↥(lineSub (ι := ι) u) →* (StdMod (Fin k × ι) K ⧸ H) :=
    (QuotientGroup.mk' H).comp (lineSub (ι := ι) u).subtype
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have hq : (QuotientGroup.mk' H) (a : StdMod (Fin k × ι) K) =
        (QuotientGroup.mk' H) (b : StdMod (Fin k × ι) K) := hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
    have hmemH : (a : StdMod (Fin k × ι) K)⁻¹ * (b : StdMod (Fin k × ι) K) ∈ H := hq
    have hmemL : (a : StdMod (Fin k × ι) K)⁻¹ * (b : StdMod (Fin k × ι) K) ∈
        lineSub (ι := ι) u :=
      (lineSub (ι := ι) u).mul_mem ((lineSub (ι := ι) u).inv_mem a.2) b.2
    have hbot : (a : StdMod (Fin k × ι) K)⁻¹ * (b : StdMod (Fin k × ι) K) ∈
        (⊥ : Subgroup (StdMod (Fin k × ι) K)) := by
      rw [← hfix_inf]
      exact Subgroup.mem_inf.mpr ⟨hmemH, hmemL⟩
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hbot
    exact hbot
  have hker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hφ_inj
  have hcard_range : Nat.card ↥(lineSub (ι := ι) u) = Nat.card ↥φ.range := by
    calc Nat.card ↥(lineSub (ι := ι) u)
        = Nat.card (↥(lineSub (ι := ι) u) ⧸ (⊥ : Subgroup ↥(lineSub (ι := ι) u))) :=
          (Nat.card_congr (QuotientGroup.quotientBot (G := ↥(lineSub (ι := ι) u))).toEquiv).symm
      _ = Nat.card (↥(lineSub (ι := ι) u) ⧸ φ.ker) := by rw [hker]
      _ = Nat.card ↥φ.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hlinecard : Nat.card ↥(lineSub (ι := ι) u) = 2 ^ (n * Fintype.card ι) := by
    obtain ⟨e, -⟩ := exists_lineSub_equiv (k := k) (ι := ι) u hu
    rw [Nat.card_congr e.toEquiv, card_stdMod, hK, ← pow_mul]
  have hdvd : 2 ^ (n * Fintype.card ι) ∣ (fixV (Subgroup.zpowers T)).index := by
    rw [← hlinecard, hcard_range]
    rw [show (fixV (Subgroup.zpowers T)).index =
      Nat.card (StdMod (Fin k × ι) K ⧸ H) from Subgroup.index_eq_card _]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have hindex_ne : (fixV (Subgroup.zpowers T)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hbound : n * Fintype.card ι ≤
      padicValNat 2 ((fixV (Subgroup.zpowers T)).index) :=
    (padicValNat_dvd_iff_le (p := 2) (a := (fixV (Subgroup.zpowers T)).index)
      (n := n * Fintype.card ι) hindex_ne).mp hdvd
  simpa [rkIdx] using hbound

end CFSG.Quasithin.H.Mult

end
