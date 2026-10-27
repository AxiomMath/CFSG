module

public import CFSG.RankThree.PartOne.K133.ProjUnip3
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly.LowTwoRank Matrix Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K133
open scoped commutatorElement

theorem sign_patterns {K : Type} [Field K] (hm1 : (-1 : K) ≠ 1) (ε δ : Fin 3 → K)
    (hε2 : ∀ j, ε j * ε j = 1) (hδ2 : ∀ j, δ j * δ j = 1) (hε : ε 0 * ε 1 * ε 2 = 1)
    (hδ : δ 0 * δ 1 * δ 2 = 1) (hε1 : ε 0 ≠ 1 ∨ ε 1 ≠ 1 ∨ ε 2 ≠ 1)
    (hδ1 : δ 0 ≠ 1 ∨ δ 1 ≠ 1 ∨ δ 2 ≠ 1) (hεδ : ε 0 ≠ δ 0 ∨ ε 1 ≠ δ 1 ∨ ε 2 ≠ δ 2) :
    (ε 0 = -1 ∨ δ 0 = -1) ∧ (ε 1 = -1 ∨ δ 1 = -1) ∧ (ε 2 = -1 ∨ δ 2 = -1) ∧
      (ε 0 ≠ ε 1 ∨ δ 0 ≠ δ 1) ∧ (ε 0 ≠ ε 2 ∨ δ 0 ≠ δ 2) ∧ (ε 1 ≠ ε 2 ∨ δ 1 ≠ δ 2) := by
  have hs : ∀ x : K, x * x = 1 → x = 1 ∨ x = -1 := fun x hx => mul_self_eq_one_iff.1 hx
  have hm1' : (1 : K) ≠ -1 := hm1.symm
  rcases hs _ (hε2 0) with h0 | h0 <;> rcases hs _ (hε2 1) with h1 | h1 <;>
    rcases hs _ (hε2 2) with h2 | h2 <;> rcases hs _ (hδ2 0) with g0 | g0 <;>
    rcases hs _ (hδ2 1) with g1 | g1 <;> rcases hs _ (hδ2 2) with g2 | g2 <;>
    simp_all

section Coord

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem diag_coord_apply (b : Basis ι K V) (g : Module.End K V) (lam : ι → K)
    (hg : ∀ j, g (b j) = lam j • b j) (w : V) (j : ι) :
    b.equivFun (g w) j = lam j * b.equivFun w j := by
  let A : V →ₗ[K] (ι → K) := b.equivFun.toLinearMap ∘ₗ g
  let B : V →ₗ[K] (ι → K) := (LinearMap.pi fun k => lam k • LinearMap.proj k) ∘ₗ
    b.equivFun.toLinearMap
  have hAB : A = B := by
    refine b.ext fun i => ?_
    funext k
    simp only [A, B, LinearMap.comp_apply, LinearEquiv.coe_coe, hg, map_smul, Basis.equivFun_self,
      Pi.smul_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul]
    split_ifs with hik
    · subst hik
      simp
    · simp
  have := congrArg (fun F : V →ₗ[K] (ι → K) => F w j) hAB
  simpa [A, B] using this

theorem diag_coord_eigen (b : Basis ι K V) (g : Module.End K V) (lam : ι → K)
    (hg : ∀ j, g (b j) = lam j • b j) (θ : K) (w : V) (hw : g w = θ • w) (j : ι) :
    (lam j - θ) * b.equivFun w j = 0 := by
  have h1 := diag_coord_apply b g lam hg w j
  rw [hw] at h1
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h1
  linear_combination -h1

theorem eq_one_of_smul_eq_self {c : K} {v : V} (hv : v ≠ 0) (h : c • v = v) : c = 1 := by
  by_contra hc
  have : (c - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.1 this with h1 | h1
  · exact hc (sub_eq_zero.1 h1)
  · exact hv h1

theorem eq_zero_of_neg_eq_self (h2 : (2 : K) ≠ 0) {v : V} (h : -v = v) : v = 0 := by
  have h1 : v + v = 0 := neg_eq_iff_add_eq_zero.1 h
  have h3 : (2 : K) • v = 0 := by rw [two_smul]; exact h1
  exact (smul_eq_zero.1 h3).resolve_left h2

theorem toMatrix_eq_diagonal (b : Basis ι K V) (g : Module.End K V) (lam : ι → K)
    (hg : ∀ j, g (b j) = lam j • b j) : LinearMap.toMatrix b b g = Matrix.diagonal lam := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [LinearMap.toMatrix_apply, hg i]
  · simp [LinearMap.toMatrix_apply, hg j, hij]

end Coord

theorem core_three_klein {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {P : Type*} [Group P]
    (ρ : P →* Module.End K (Fin 3 → K)) (hP : Group.IsPerfect P)
    (hdet : ∀ y, LinearMap.det (ρ y) = 1)
    {z₁ z₂ : P} (hz1 : z₁ * z₁ = 1) (hz2 : z₂ * z₂ = 1) (hc : z₁ * z₂ = z₂ * z₁)
    (hne1 : ρ z₁ ≠ 1) (hne2 : ρ z₂ ≠ 1) (hne12 : ρ z₁ ≠ ρ z₂)
    (fa : Module.End K (Fin 3 → K)) (hfa : ∀ y, ρ y * fa = fa * ρ y)
    (hns : ∀ α : K, fa ≠ α • 1) : False := by
  classical
  have hm1 : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hprim : IsPrimitiveRoot (-1 : K) 2 := by
    have := ringChar.charP K
    have hne2' : ringChar K ≠ 2 := fun h => by
      have h0 : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
      rw [h] at h0
      exact h2 (by simpa using h0)
    exact IsPrimitiveRoot.neg_one (ringChar K) hne2'
  have hcomm : ∀ i j : Fin 2, Commute (![ρ z₁, ρ z₂] i) (![ρ z₁, ρ z₂] j) := by
    intro i j
    have h12 : Commute (ρ z₁) (ρ z₂) := by
      show ρ z₁ * ρ z₂ = ρ z₂ * ρ z₁
      rw [← map_mul, ← map_mul, hc]
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact h12
    · exact h12.symm
    · exact Commute.refl _
  have hpow : ∀ i : Fin 2, ![ρ z₁, ρ z₂] i ^ 2 = 1 := by
    intro i
    fin_cases i
    · show ρ z₁ ^ 2 = 1
      rw [← map_pow, pow_two, hz1, map_one]
    · show ρ z₂ ^ 2 = 1
      rw [← map_pow, pow_two, hz2, map_one]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one (p := 2) hprim
    (V := Fin 3 → K) (ι := Fin 2) ![ρ z₁, ρ z₂] hcomm hpow
  have hr : finrank K (Fin 3 → K) = 3 := by simp
  let b' : Basis (Fin 3) K (Fin 3 → K) := b.reindex (finCongr hr)
  let ε : Fin 3 → K := fun j => μ 0 ((finCongr hr).symm j)
  let δ : Fin 3 → K := fun j => μ 1 ((finCongr hr).symm j)
  have hε : ∀ j, ρ z₁ (b' j) = ε j • b' j := fun j => by
    have := hb 0 ((finCongr hr).symm j)
    simpa [b', ε] using this
  have hδ : ∀ j, ρ z₂ (b' j) = δ j • b' j := fun j => by
    have := hb 1 ((finCongr hr).symm j)
    simpa [b', δ] using this
  have hb0 : ∀ j, b' j ≠ 0 := fun j => b'.ne_zero j
  have hε2 : ∀ j, ε j * ε j = 1 := by
    intro j
    have h1 : ρ z₁ (ρ z₁ (b' j)) = b' j := by
      have := congrArg (fun m : Module.End K (Fin 3 → K) => m (b' j)) (show ρ z₁ * ρ z₁ = 1 by
        rw [← map_mul, hz1, map_one])
      simpa using this
    rw [hε j, map_smul, hε j, smul_smul] at h1
    exact eq_one_of_smul_eq_self (hb0 j) h1
  have hδ2 : ∀ j, δ j * δ j = 1 := by
    intro j
    have h1 : ρ z₂ (ρ z₂ (b' j)) = b' j := by
      have := congrArg (fun m : Module.End K (Fin 3 → K) => m (b' j)) (show ρ z₂ * ρ z₂ = 1 by
        rw [← map_mul, hz2, map_one])
      simpa using this
    rw [hδ j, map_smul, hδ j, smul_smul] at h1
    exact eq_one_of_smul_eq_self (hb0 j) h1
  have hdε : ε 0 * ε 1 * ε 2 = 1 := by
    have h1 := hdet z₁
    rw [← LinearMap.det_toMatrix b', toMatrix_eq_diagonal b' (ρ z₁) ε hε, Matrix.det_diagonal,
      Fin.prod_univ_three] at h1
    exact h1
  have hdδ : δ 0 * δ 1 * δ 2 = 1 := by
    have h1 := hdet z₂
    rw [← LinearMap.det_toMatrix b', toMatrix_eq_diagonal b' (ρ z₂) δ hδ, Matrix.det_diagonal,
      Fin.prod_univ_three] at h1
    exact h1
  have hε1 : ε 0 ≠ 1 ∨ ε 1 ≠ 1 ∨ ε 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne1
    refine b'.ext fun j => ?_
    rw [hε j, Module.End.one_apply]
    fin_cases j
    · simp [hall.1]
    · simp [hall.2.1]
    · simp [hall.2.2]
  have hδ1 : δ 0 ≠ 1 ∨ δ 1 ≠ 1 ∨ δ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne2
    refine b'.ext fun j => ?_
    rw [hδ j, Module.End.one_apply]
    fin_cases j
    · simp [hall.1]
    · simp [hall.2.1]
    · simp [hall.2.2]
  have hεδ : ε 0 ≠ δ 0 ∨ ε 1 ≠ δ 1 ∨ ε 2 ≠ δ 2 := by
    by_contra hall
    push Not at hall
    apply hne12
    refine b'.ext fun j => ?_
    rw [hε j, hδ j]
    fin_cases j
    · simp [hall.1]
    · simp [hall.2.1]
    · simp [hall.2.2]
  obtain ⟨s0, s1, s2, d01, d02, d12⟩ := sign_patterns hm1 ε δ hε2 hδ2 hdε hdδ hε1 hδ1 hεδ
  have hS2 : ∀ j l : Fin 3, j ≠ l → ε j ≠ ε l ∨ δ j ≠ δ l := by
    intro j l hjl
    fin_cases j <;> fin_cases l
    · exact absurd rfl hjl
    · exact d01
    · exact d02
    · exact d01.imp Ne.symm Ne.symm
    · exact absurd rfl hjl
    · exact d12
    · exact d02.imp Ne.symm Ne.symm
    · exact d12.imp Ne.symm Ne.symm
    · exact absurd rfl hjl
  have hS1 : ∀ j : Fin 3, ε j = -1 ∨ δ j = -1 := by
    intro j
    fin_cases j
    · exact s0
    · exact s1
    · exact s2
  have hdiag : ∀ j, ∃ α : K, fa (b' j) = α • b' j := by
    intro j
    set w := fa (b' j) with hw
    have hw1 : ρ z₁ w = ε j • w := by
      have := congrArg (fun m : Module.End K (Fin 3 → K) => m (b' j)) (hfa z₁)
      simp only [Module.End.mul_apply] at this
      rw [hε j, map_smul] at this
      exact this
    have hw2 : ρ z₂ w = δ j • w := by
      have := congrArg (fun m : Module.End K (Fin 3 → K) => m (b' j)) (hfa z₂)
      simp only [Module.End.mul_apply] at this
      rw [hδ j, map_smul] at this
      exact this
    have hc1 := diag_coord_eigen b' (ρ z₁) ε hε (ε j) w hw1
    have hc2 := diag_coord_eigen b' (ρ z₂) δ hδ (δ j) w hw2
    refine ⟨b'.equivFun w j, ?_⟩
    apply b'.ext_elem
    intro l
    by_cases hlj : l = j
    · subst hlj
      simp [Basis.repr_self]
    · have hz : b'.equivFun w l = 0 := by
        rcases hS2 l j hlj with h | h
        · exact (mul_eq_zero.1 (hc1 l)).resolve_left (sub_ne_zero.2 h)
        · exact (mul_eq_zero.1 (hc2 l)).resolve_left (sub_ne_zero.2 h)
      have hz' : b'.repr w l = 0 := by simpa [Basis.equivFun_apply] using hz
      simp [Basis.repr_self, hlj, hz']
  choose α hα using hdiag
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, ∀ l, l ≠ k → α l ≠ α k := by
    by_cases h01 : α 0 = α 1
    · by_cases h12 : α 1 = α 2
      · exfalso
        apply hns (α 0)
        refine b'.ext fun j => ?_
        rw [hα j, LinearMap.smul_apply, Module.End.one_apply]
        fin_cases j
        · rfl
        · simp [h01]
        · simp [h01, h12]
      · refine ⟨2, fun l hl => ?_⟩
        fin_cases l
        · simp only [Fin.zero_eta]
          rw [h01]
          exact h12
        · exact h12
        · exact absurd rfl hl
    · by_cases h02 : α 0 = α 2
      · refine ⟨1, fun l hl => ?_⟩
        fin_cases l
        · exact h01
        · exact absurd rfl hl
        · simp only [Fin.reduceFinMk]
          rw [← h02]
          exact h01
      · refine ⟨0, fun l hl => ?_⟩
        fin_cases l
        · exact absurd rfl hl
        · exact fun h => h01 h.symm
        · exact fun h => h02 h.symm
  have htriv : ∀ y : P, ρ y (b' k) = b' k := by
    intro y
    have hw : fa (ρ y (b' k)) = α k • ρ y (b' k) := by
      have := congrArg (fun m : Module.End K (Fin 3 → K) => m (b' k)) (hfa y)
      simp only [Module.End.mul_apply] at this
      rw [hα k, map_smul] at this
      exact this.symm
    have hmem : ∀ y : P, ρ y (b' k) ∈ Submodule.span K {b' k} := by
      intro y'
      have hw' : fa (ρ y' (b' k)) = α k • ρ y' (b' k) := by
        have := congrArg (fun m : Module.End K (Fin 3 → K) => m (b' k)) (hfa y')
        simp only [Module.End.mul_apply] at this
        rw [hα k, map_smul] at this
        exact this.symm
      have hdiagα : ∀ j, fa (b' j) = α j • b' j := hα
      have hco := diag_coord_eigen b' fa α hdiagα (α k) (ρ y' (b' k)) hw'
      have hcoord : ∀ l, l ≠ k → b'.equivFun (ρ y' (b' k)) l = 0 := fun l hl =>
        (mul_eq_zero.1 (hco l)).resolve_left (sub_ne_zero.2 (hk l hl))
      rw [Submodule.mem_span_singleton]
      refine ⟨b'.equivFun (ρ y' (b' k)) k, ?_⟩
      apply b'.ext_elem
      intro l
      by_cases hlk : l = k
      · subst hlk
        simp [Basis.repr_self]
      · have hc0 : b'.repr (ρ y' (b' k)) l = 0 := by
          simpa [Basis.equivFun_apply] using hcoord l hlk
        simp [Basis.repr_self, hlk, hc0]
    have hperf := perfect_trivial_on_section ρ hP (W' := ⊥) (W := Submodule.span K {b' k})
      bot_le (by rw [finrank_span_singleton (hb0 k)]; simp)
      (fun g w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        rw [map_smul]
        exact Submodule.smul_mem _ _ (hmem g))
      (fun g w hw => by
        rw [Submodule.mem_bot] at hw
        rw [hw, map_zero]
        exact Submodule.zero_mem _) y (b' k) (Submodule.mem_span_singleton_self _)
    simpa [sub_eq_zero] using hperf
  rcases hS1 k with h | h
  · have := htriv z₁
    rw [hε k, h, neg_smul, one_smul] at this
    exact hb0 k (eq_zero_of_neg_eq_self h2 this)
  · have := htriv z₂
    rw [hδ k, h, neg_smul, one_smul] at this
    exact hb0 k (eq_zero_of_neg_eq_self h2 this)

section Wrapper

theorem statedProj_three_no_klein {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (M : Subgroup (GL (Fin 3) K)) (x : StatedProj M) (hx1 : x ≠ 1)
    (Kb : Subgroup (StatedProj M)) [IsSimpleGroup Kb] (hKn : ∃ a b : Kb, a * b ≠ b * a)
    (V : Subgroup (StatedProj M)) (hVK : V ≤ Kb) (hV : IsElementaryAbelian 2 V)
    (hVc : Nat.card V = 4) (hcomm : ∀ k ∈ Kb, x * k = k * x) : False := by
  classical
  set Z : Subgroup M := (StatedScalars (Fin 3) K).subgroupOf M with hZ
  have hZc : Z ≤ Subgroup.center M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro m
    have hz' : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hz
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz' (m : GL (Fin 3) K))
  let mk : M →* StatedProj M := QuotientGroup.mk' Z
  have hKperf : Group.IsPerfect Kb := isPerfect_of_simple_nonabelian hKn
  set P₀ : Subgroup M := ⁅Kb.comap mk, Kb.comap mk⁆ with hP₀
  have hP₀perf : Group.IsPerfect P₀ :=
    CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap hZc Kb
  have hP₀map : P₀.map mk = Kb := CFSG.RankThree.SubgroupLists.map_commutator_comap Kb
  have hP₀K : ∀ y ∈ P₀, mk y ∈ Kb := fun y hy => hP₀map ▸ Subgroup.mem_map_of_mem mk hy
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective x
  have hmka : mk a = x := ha
  have hna : ∀ μ : Kˣ, (a : GL (Fin 3) K) ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
    intro μ hμ
    apply hx1
    rw [← hmka]
    change ((a : M) : StatedProj M) = 1
    rw [QuotientGroup.eq_one_iff]
    change (a : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K
    exact ⟨μ, hμ.symm⟩
  have : Group.IsPerfect P₀ := hP₀perf
  have hcommA : ∀ y : P₀, (y : M) * a = a * (y : M) := by
    intro y
    exact KFU.commute_of_central_commute (S := ↥P₀) (S' := ↥(Subgroup.zpowers a)) mk
      (by rw [QuotientGroup.ker_mk']; exact hZc) P₀.subtype (Subgroup.zpowers a).subtype
      (fun A B => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 B.2
        have hB : mk (B : M) = x ^ k := by
          rw [← hk, map_zpow, hmka]
        change mk (A : M) * mk (B : M) = mk (B : M) * mk (A : M)
        rw [hB]
        exact (Commute.zpow_right (show Commute (mk (A : M)) x from
          (hcomm _ (hP₀K _ A.2)).symm) k).eq)
      y ⟨a, Subgroup.mem_zpowers a⟩
  let σ : ↥P₀ →* GL (Fin 3) K := M.subtype.comp P₀.subtype
  let δ : ↥P₀ →* Kˣ := Matrix.GeneralLinearGroup.det.comp σ
  have hδ : ∀ g : ↥P₀, δ g = 1 := by
    intro g
    have hg : g ∈ commutator ↥P₀ := by
      rw [hP₀perf.commutator_eq_top]
      exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker δ hg)
  let e : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Module.End K (Fin 3 → K) := Matrix.toLinAlgEquiv'
  let ρ : ↥P₀ →* Module.End K (Fin 3 → K) :=
    (e.toRingEquiv.toMonoidHom).comp ((Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp σ)
  have hρ : ∀ y, ρ y = e ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun y => rfl
  have hρinj : Function.Injective ρ := by
    intro y y' h
    have h1 := e.injective h
    have h2 : σ y = σ y' := Units.ext h1
    exact Subtype.ext (Subtype.ext h2)
  have hdet : ∀ y, LinearMap.det (ρ y) = 1 := by
    intro y
    rw [hρ]
    show LinearMap.det (Matrix.toLin' ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 1
    rw [LinearMap.det_toLin']
    have h1 : ((Matrix.GeneralLinearGroup.det (σ y) : Kˣ) : K) = 1 := congrArg Units.val (hδ y)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
    exact h1
  have hu2 : ∀ u ∈ V, u ^ 2 = 1 := fun u hu =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) u hu
  have hVcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hV.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨u₁, hu₁V, hu₁1⟩ : ∃ u ∈ V, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 hcon
    rw [this, Subgroup.card_bot] at hVc
    omega
  obtain ⟨u₂, hu₂V, hu₂⟩ : ∃ u ∈ V, u ∉ Subgroup.zpowers u₁ := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ Subgroup.zpowers u₁ := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [hVc, Nat.card_zpowers] at h1
    have : orderOf u₁ ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hu2 u₁ hu₁V))
    omega
  have hu₂1 : u₂ ≠ 1 := fun h => hu₂ (h ▸ Subgroup.one_mem _)
  have hu₁₂ : u₁ ≠ u₂ := fun h => hu₂ (h ▸ Subgroup.mem_zpowers u₁)
  have hlift : ∀ u ∈ Kb, u ^ 2 = 1 → ∃ z : M, z ∈ P₀ ∧ mk z = u ∧ z * z = 1 := by
    intro u hu hu2'
    obtain ⟨y, hy, hyu⟩ : u ∈ P₀.map mk := hP₀map ▸ hu
    have hy2Z : y ^ 2 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      change mk (y ^ 2) = 1
      rw [map_pow, hyu, hu2']
    obtain ⟨c, hc⟩ : ((y ^ 2 : M) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
      Subgroup.mem_subgroupOf.1 hy2Z
    have hdy : Matrix.GeneralLinearGroup.det (y : GL (Fin 3) K) = 1 := hδ ⟨y, hy⟩
    have hc3 : c ^ 3 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hc
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
      rw [h1]
      show Matrix.GeneralLinearGroup.det ((y : GL (Fin 3) K) ^ 2) = 1
      rw [map_pow, hdy, one_pow]
    refine ⟨y ^ 3, P₀.pow_mem hy 3, ?_, ?_⟩
    · rw [map_pow, hyu]
      calc u ^ 3 = u ^ 2 * u := by rw [pow_succ]
        _ = u := by rw [hu2', one_mul]
    · apply Subtype.ext
      show ((y : GL (Fin 3) K) ^ 3) * (y : GL (Fin 3) K) ^ 3 = 1
      have h6 : (y : GL (Fin 3) K) ^ 3 * (y : GL (Fin 3) K) ^ 3 = ((y : GL (Fin 3) K) ^ 2) ^ 3 := by
        group
      rw [h6]
      have h7 : (y : GL (Fin 3) K) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
        rw [hc]
        rfl
      rw [h7, ← map_pow, hc3, map_one]
  obtain ⟨z₁, hz₁P, hz₁u, hz₁2⟩ := hlift u₁ (hVK hu₁V) (hu2 u₁ hu₁V)
  obtain ⟨z₂, hz₂P, hz₂u, hz₂2⟩ := hlift u₂ (hVK hu₂V) (hu2 u₂ hu₂V)
  have hcen : ∀ (ν : Kˣ) (g : GL (Fin 3) K), Matrix.GeneralLinearGroup.scalar (Fin 3) ν * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
    intro ν g
    have h : Matrix.GeneralLinearGroup.scalar (Fin 3) ν ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨ν, rfl⟩
    exact (Subgroup.mem_center_iff.1 h g).symm
  have hzc : z₁ * z₂ = z₂ * z₁ := by
    have hνZ : z₁ * z₂ * z₁⁻¹ * z₂⁻¹ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      change mk (z₁ * z₂ * z₁⁻¹ * z₂⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hz₁u, hz₂u, hVcomm u₁ hu₁V u₂ hu₂V]
      group
    obtain ⟨ν, hν⟩ : ((z₁ * z₂ * z₁⁻¹ * z₂⁻¹ : M) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
      Subgroup.mem_subgroupOf.1 hνZ
    set A : GL (Fin 3) K := (z₁ : GL (Fin 3) K) with hAdef
    set B : GL (Fin 3) K := (z₂ : GL (Fin 3) K) with hBdef
    have hA : A * A = 1 := congrArg (Subtype.val : M → GL (Fin 3) K) hz₁2
    have hB : B * B = 1 := congrArg (Subtype.val : M → GL (Fin 3) K) hz₂2
    have hcomm' : Matrix.GeneralLinearGroup.scalar (Fin 3) ν = A * B * A⁻¹ * B⁻¹ := hν
    have hsq : ν * ν = 1 := by
      have e1 : A * B * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B := by
        have : A * B * A⁻¹ = (A * B * A⁻¹ * B⁻¹) * B := by group
        rw [this, ← hcomm']
      have e2 : (A * B * A⁻¹) * (A * B * A⁻¹) = 1 := by
        calc (A * B * A⁻¹) * (A * B * A⁻¹) = A * (B * B) * A⁻¹ := by group
          _ = 1 := by rw [hB]; group
      rw [e1] at e2
      have e3 : Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ν * Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
            (B * B) := by
        calc Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B)
            = Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
              (B * Matrix.GeneralLinearGroup.scalar (Fin 3) ν) * B := by group
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
              (Matrix.GeneralLinearGroup.scalar (Fin 3) ν * B) * B := by rw [← hcen ν B]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ν *
              Matrix.GeneralLinearGroup.scalar (Fin 3) ν * (B * B) := by group
      rw [e3, hB, mul_one, ← map_mul] at e2
      have := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K) 0 0)) e2
      apply Units.ext
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
    have hcube : ν ^ 3 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hcomm'
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_mul, map_mul,
        map_inv, map_inv] at h1
      rw [h1, mul_comm (Matrix.GeneralLinearGroup.det A) (Matrix.GeneralLinearGroup.det B),
        mul_inv_cancel_right, mul_inv_cancel]
    have hν1 : ν = 1 := by
      calc ν = ν ^ 3 * (ν * ν)⁻¹ := by group
        _ = 1 := by rw [hcube, hsq]; simp
    rw [hν1, map_one] at hcomm'
    have hAB : A * B = B * A := by
      calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
        _ = B * A := by rw [← hcomm', one_mul]
    exact Subtype.ext hAB
  let z₁' : ↥P₀ := ⟨z₁, hz₁P⟩
  let z₂' : ↥P₀ := ⟨z₂, hz₂P⟩
  have hne1 : ρ z₁' ≠ 1 := by
    intro h
    have h1 : z₁' = 1 := hρinj (by rw [h, map_one])
    have h3 : z₁ = 1 := congrArg Subtype.val h1
    exact hu₁1 (by rw [← hz₁u, h3, map_one])
  have hne2 : ρ z₂' ≠ 1 := by
    intro h
    have h1 : z₂' = 1 := hρinj (by rw [h, map_one])
    have h3 : z₂ = 1 := congrArg Subtype.val h1
    exact hu₂1 (by rw [← hz₂u, h3, map_one])
  have hne12 : ρ z₁' ≠ ρ z₂' := by
    intro h
    have h1 : z₁' = z₂' := hρinj h
    have h3 : z₁ = z₂ := congrArg Subtype.val h1
    exact hu₁₂ (by rw [← hz₁u, ← hz₂u, h3])
  let fa : Module.End K (Fin 3 → K) := e ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hfa : ∀ y : ↥P₀, ρ y * fa = fa * ρ y := by
    intro y
    rw [hρ y]
    show e _ * e _ = e _ * e _
    rw [← map_mul, ← map_mul]
    congr 1
    have := congrArg (fun m : M => ((m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (hcommA y)
    exact this
  have hns : ∀ α : K, fa ≠ α • 1 := by
    intro α hα
    have hAα : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        α • (1 : Matrix (Fin 3) (Fin 3) K) :=
      e.injective (by rw [map_smul, map_one]; exact hα)
    have hα0 : α ≠ 0 := by
      intro hα0
      rw [hα0, zero_smul] at hAα
      have h1 : ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hAα, mul_zero] at h1
      exact zero_ne_one (congrFun (congrFun h1 0) 0)
    apply hna (Units.mk0 α hα0)
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one']
    simpa using hAα
  exact core_three_klein h2 ρ hP₀perf hdet (z₁ := z₁') (z₂ := z₂') (Subtype.ext hz₁2)
    (Subtype.ext hz₂2) (Subtype.ext hzc) hne1 hne2 hne12 fa hfa hns

end Wrapper

end CFSG.RankThree.PartOne.Q1327T
