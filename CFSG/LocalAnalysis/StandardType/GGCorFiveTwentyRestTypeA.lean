module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflTypeA
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Fix

variable {H : Type*} [Group H] [Finite H]

theorem card_fix_mul_of_le_zpowers {p : ℕ} (hp : p.Prime) (hc : ∀ a b : H, a * b = b * a)
    (f : MulAut H) {a₁ : H} (ha₁ : a₁ ^ p = 1) (hδ : ∀ a, ∃ e : ℕ, a * (f a)⁻¹ = a₁ ^ e)
    (h₁ : a₁ * (f a₁)⁻¹ ≠ 1) : Nat.card {a : H // f a = a} * p = Nat.card H := by
  have := Fact.mk hp
  let δ : H →* H :=
    { toFun := fun a => a * (f a)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv_rev]
        calc a * b * ((f b)⁻¹ * (f a)⁻¹) = a * (b * (f b)⁻¹ * (f a)⁻¹) := by group
          _ = a * ((f a)⁻¹ * (b * (f b)⁻¹)) := by rw [hc _ (f a)⁻¹]
          _ = a * (f a)⁻¹ * (b * (f b)⁻¹) := by group }
  have hδapp : ∀ a, δ a = a * (f a)⁻¹ := fun _ => rfl
  have hker : Nat.card δ.ker = Nat.card {a : H // f a = a} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      rw [MonoidHom.mem_ker, hδapp, mul_inv_eq_one, eq_comm])
  have ha₁1 : a₁ ≠ 1 := by
    rintro rfl
    exact h₁ (by simp)
  have hord : orderOf a₁ = p := orderOf_eq_prime ha₁ ha₁1
  have hle : δ.range ≤ Subgroup.zpowers a₁ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hδ a
    rw [hδapp, he]
    exact Subgroup.npow_mem_zpowers a₁ e
  have hdvd : Nat.card δ.range ∣ p := by
    rw [← hord, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hne : Nat.card δ.range ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    have hm : δ a₁ ∈ δ.range := ⟨a₁, rfl⟩
    rw [hbot, Subgroup.mem_bot, hδapp] at hm
    exact h₁ hm
  have hrange : Nat.card δ.range = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left hne
  have h := TableB.card_range_mul_card_ker δ
  rw [hrange, hker] at h
  rw [mul_comm]
  exact h

end Fix

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d p : ℕ} {K : Type} [Field K]

section PermConj

variable [CharP K 2]

theorem permConj_mul (A₀ : GL (Fin d) K) (σ τ : Equiv.Perm (Fin d)) :
    permConj A₀ (σ * τ) = permConj A₀ τ * permConj A₀ σ := by
  apply Subtype.ext
  change ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (σ * τ).permMatrix K *
      (A₀ : Matrix (Fin d) (Fin d) K) =
    ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * τ.permMatrix K *
        (A₀ : Matrix (Fin d) (Fin d) K) *
      (((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * σ.permMatrix K *
        (A₀ : Matrix (Fin d) (Fin d) K))
  rw [Matrix.permMatrix_mul]
  calc ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (τ.permMatrix K * σ.permMatrix K) *
        (A₀ : Matrix (Fin d) (Fin d) K)
      = ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * τ.permMatrix K *
          ((A₀ : Matrix (Fin d) (Fin d) K) * ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
          σ.permMatrix K * (A₀ : Matrix (Fin d) (Fin d) K) := by
        rw [mul_inv_GL, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem permConj_one (A₀ : GL (Fin d) K) : permConj A₀ 1 = 1 := by
  apply Subtype.ext
  change ((A₀⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      (1 : Equiv.Perm (Fin d)).permMatrix K * (A₀ : Matrix (Fin d) (Fin d) K) = 1
  rw [Matrix.permMatrix_one, Matrix.mul_one, inv_mul_GL]

theorem permConj_inv (A₀ : GL (Fin d) K) (τ : Equiv.Perm (Fin d)) :
    (permConj A₀ τ)⁻¹ = permConj A₀ τ⁻¹ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← permConj_mul, mul_inv_cancel, permConj_one]

end PermConj

section Cover

variable {L' : Type} [Group L'] {ψ : L' →* projectiveSL d K}
  {φ : SpecialLinearGroup (Fin d) K →* L'} (hφ : ∀ g, ψ (φ g) = proj d K g)

include hφ in
theorem conjAut_induces_conj (g : SpecialLinearGroup (Fin d) K) (l : L') :
    conjAut d K (SpecialLinearGroup.toGL g) (ψ l) = ψ (MulAut.conj (φ g) l) := by
  rw [conjAut_toGL, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hφ]

include hφ in
theorem eq_conj_of_induces (hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    (hker : ψ.ker ≤ Subgroup.center L') (hφs : Function.Surjective φ) {a : MulAut L'}
    {g : SpecialLinearGroup (Fin d) K}
    (hind : ∀ l, conjAut d K (SpecialLinearGroup.toGL g) (ψ l) = ψ (a l)) :
    a = MulAut.conj (φ g) := by
  ext l
  obtain ⟨s, rfl⟩ := hφs l
  rw [act_of_lift hperfSL hker hφ hind s, MulAut.conj_apply, map_mul, map_mul, map_inv]

include hφ in
theorem eq_of_conj_eq [Finite K] (hψ : Function.Surjective ψ) (hd : 0 < d)
    (hpd : Nat.Coprime p d) {g h : SpecialLinearGroup (Fin d) K} (hg : g ^ p = 1)
    (hh : h ^ p = 1) (he : MulAut.conj (φ g) = MulAut.conj (φ h)) : g = h := by
  refine eq_of_slLift hd hpd hg hh ?_
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [conjAut_induces_conj hφ, conjAut_induces_conj hφ, he]

end Cover

theorem exists_fin_avoid_three (hd : 4 ≤ d) (a b c : Fin d) :
    ∃ w : Fin d, w ≠ a ∧ w ≠ b ∧ w ≠ c := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {a, b, c} := fun w _ => by
    by_cases h1 : w = a
    · simp [h1]
    by_cases h2 : w = b
    · simp [h2]
    simp [h w h1 h2]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ({a, b, c} : Finset (Fin d)).card ≤ 3 := Finset.card_le_three
  omega

section Main

variable [Finite K] [CharP K 2]

theorem exists_weylModel_psl (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) {L' : Type} [Group L']
    [Finite L'] {ψ : L' →* projectiveSL d K} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : p ^ (d - 1) ≤ Nat.card A) :
    ∃ F : Equiv.Perm (Fin d) → MulAut ↥A, (∀ σ τ, F (σ * τ) = F τ * F σ) ∧ F 1 = 1 ∧
      (∀ i j : Fin d, i ≠ j → F (Equiv.swap i j) ∈ ggTorusPseudoReflSet p A) ∧
      (∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∃ π, v = F π) ∧
      (∀ π, F π ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∧
      Function.Injective F ∧ (∀ π, GGIsPseudoReflection p (F π) → π.IsSwap) := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hd0 : 0 < d := by omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian p X := isElemAbelian_inducedSub hψ hA
  have hXI : ∀ x ∈ X, ∃ B : GL (Fin d) K, conjAut d K B = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hXA hx hy
  have hXp : ∀ x ∈ X, x ^ p = 1 := hXA.2
  obtain ⟨A₀, hdiag, hle, hfull⟩ := exists_diagonalizing_slLift hp hpK hd0 hpd X hXc hXp hXI
  have hfull' := hfull (le_antisymm hle (by rw [hcardX]; exact hr))
  set Y := slLift hd0 hpd X hXc with hY
  have hTd : ∀ g ∈ Y, (∀ k, conjMat A₀ g k k ^ p = 1) ∧ ∏ k, conjMat A₀ g k k = 1 :=
    fun g hg => (conjMat_diag hg.1 (hdiag g hg)).2
  have hYA : ∀ g ∈ Y, MulAut.conj (φ g) ∈ A := by
    intro g hg
    obtain ⟨a, ha, hind⟩ := hg.2
    rw [← eq_conj_of_induces hφ hperfSL hker hφs hind]
    exact ha
  have hAY : ∀ a ∈ A, ∃ g ∈ Y, a = MulAut.conj (φ g) := by
    intro a ha
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    obtain ⟨g, hg, hgφ⟩ := exists_mem_slLift_of_mem hd0 hpd hXc hXp hXI
      (show φa ∈ X from ⟨a, ha, hφa⟩)
    exact ⟨g, hg, eq_conj_of_induces hφ hperfSL hker hφs fun l => by rw [hgφ, hφa]⟩
  have hinjY : ∀ g ∈ Y, ∀ h ∈ Y, MulAut.conj (φ g) = MulAut.conj (φ h) → g = h :=
    fun g hg h hh he => eq_of_conj_eq hφ hψ hd0 hpd hg.1 hh.1 he
  have hPY := fun τ g (hg : g ∈ Y) => permConj_conj_slLift hd0 hpd hXc hdiag hfull' τ hg
  have hconjP : ∀ (τ : Equiv.Perm (Fin d)) (g : SpecialLinearGroup (Fin d) K),
      MulAut.conj (φ (permConj A₀ τ)) * MulAut.conj (φ g) *
        (MulAut.conj (φ (permConj A₀ τ)))⁻¹ =
      MulAut.conj (φ (permConj A₀ τ * g * (permConj A₀ τ)⁻¹)) := by
    intro τ g
    simp only [map_mul, map_inv]
  have hPA : ∀ (τ : Equiv.Perm (Fin d)), ∀ a ∈ A, MulAut.conj (φ (permConj A₀ τ)) * a *
      (MulAut.conj (φ (permConj A₀ τ)))⁻¹ ∈ A := by
    intro τ a ha
    obtain ⟨g, hg, rfl⟩ := hAY a ha
    rw [hconjP]
    exact hYA _ (hPY τ g hg).1
  have hPN : ∀ τ : Equiv.Perm (Fin d),
      MulAut.conj (φ (permConj A₀ τ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro τ
    refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
    have h1 := hPA τ⁻¹ a ha
    simp only [← permConj_inv, map_inv, inv_inv] at h1
    exact h1
  obtain ⟨F, hF⟩ : ∃ F : Equiv.Perm (Fin d) → MulAut ↥A, ∀ τ, F τ = ggConjAut A (hPN τ) :=
    ⟨_, fun _ => rfl⟩
  have hFapp : ∀ (τ : Equiv.Perm (Fin d)) (a : ↥A), ((F τ a : ↥A) : MulAut L') =
      MulAut.conj (φ (permConj A₀ τ)) * a * (MulAut.conj (φ (permConj A₀ τ)))⁻¹ := by
    intro τ a
    rw [hF]
    exact ggConjAut_apply A (hPN τ) a
  have hFmul : ∀ σ τ : Equiv.Perm (Fin d), F (σ * τ) = F τ * F σ := by
    intro σ τ
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.mul_apply, hFapp (σ * τ), hFapp τ, hFapp σ, permConj_mul, map_mul, map_mul]
    group
  have hF1 : F 1 = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [hFapp, permConj_one, map_one, map_one, one_mul, inv_one, mul_one]
    rfl
  have hTδ : ∀ (τ : Equiv.Perm (Fin d)) (g : SpecialLinearGroup (Fin d) K) (hg : g ∈ Y) (k : Fin d),
      conjMat A₀ (g * (permConj A₀ τ * g * (permConj A₀ τ)⁻¹)⁻¹) k k =
        conjMat A₀ g k k * (conjMat A₀ g (τ k) (τ k))⁻¹ := by
    intro τ g hg k
    rw [conjMat_mul_apply hd0 hpd hXc hdiag hg, conjMat_inv_apply hd0 hpd hXc hdiag (hPY τ g hg).1,
      (hPY τ g hg).2 k]
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hAc : ∀ a b : ↥A, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2)
  have hFswap : ∀ i j : Fin d, i ≠ j → F (Equiv.swap i j) ∈ ggTorusPseudoReflSet p A := by
    intro i j hij
    refine ⟨φ (permConj A₀ (Equiv.swap i j)), hPN _, ?_, hF _, ?_⟩
    ·
      intro a ha
      obtain ⟨g, hg, rfl⟩ := hAY a ha
      have hmem : permConj A₀ (Equiv.swap i j) * g * (permConj A₀ (Equiv.swap i j))⁻¹ * g⁻¹ ∈ Y :=
        Y.mul_mem (hPY _ g hg).1 (Y.inv_mem hg)
      have e : φ (permConj A₀ (Equiv.swap i j)) *
          (MulAut.conj (φ g) (φ (permConj A₀ (Equiv.swap i j))))⁻¹ =
          φ (permConj A₀ (Equiv.swap i j) * g * (permConj A₀ (Equiv.swap i j))⁻¹ * g⁻¹) := by
        rw [MulAut.conj_apply]
        simp only [map_mul, map_inv]
        group
      refine ⟨by rw [e, ← map_pow, hmem.1, map_one], fun a' ha' => ?_⟩
      obtain ⟨g', hg', rfl⟩ := hAY a' ha'
      rw [e, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
        slLift_comm hd0 hpd X hXc hg' hmem, mul_inv_cancel_right]
    ·
      have hsq : F (Equiv.swap i j) * F (Equiv.swap i j) = 1 := by
        rw [← hFmul, Equiv.swap_mul_self, hF1]
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        rw [show p - 1 = 2 * k by omega, pow_mul, sq, hsq, one_pow]
      · obtain ⟨g₁, hg₁, hg₁t⟩ := hfull' (rootT ζ i j) (rootT_pow hζ.pow_eq_one i j)
          (prod_rootT hζ0 hij)
        have hT1 : ∀ k, conjMat A₀ g₁ k k = rootT ζ i j k := fun k => by
          rw [hg₁t, diagonal_apply_eq]
        have hτi : Equiv.swap i j i = j := Equiv.swap_apply_left i j
        have hτj : Equiv.swap i j j = i := Equiv.swap_apply_right i j
        have hτk : ∀ k, k ≠ i → k ≠ j → Equiv.swap i j k = k := fun k hki hkj =>
          Equiv.swap_apply_of_ne_of_ne hki hkj
        have hδcoe : ∀ (g : SpecialLinearGroup (Fin d) K) (hg : g ∈ Y),
            (((⟨MulAut.conj (φ g), hYA g hg⟩ : ↥A) *
              (F (Equiv.swap i j) ⟨MulAut.conj (φ g), hYA g hg⟩)⁻¹ : ↥A) : MulAut L') =
              MulAut.conj (φ (g * (permConj A₀ (Equiv.swap i j) * g *
                (permConj A₀ (Equiv.swap i j))⁻¹)⁻¹)) := by
          intro g hg
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hFapp]
          simp only [map_mul, map_inv]
        refine card_fix_mul_of_le_zpowers hp hAc (F (Equiv.swap i j))
          (a₁ := ⟨MulAut.conj (φ g₁), hYA g₁ hg₁⟩)
          (Subtype.ext (by simpa using hA.2 _ (hYA g₁ hg₁))) (fun a => ?_) ?_
        · obtain ⟨g, hg, hga⟩ := hAY a a.2
          have ha : a = ⟨MulAut.conj (φ g), hYA g hg⟩ := Subtype.ext hga
          obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one
            (ξ := conjMat A₀ g i i * (conjMat A₀ g j j)⁻¹)
            (by rw [mul_pow, inv_pow, (hTd g hg).1 i, (hTd g hg).1 j, inv_one, mul_one])
          refine ⟨e, Subtype.ext ?_⟩
          have hmemδ : g * (permConj A₀ (Equiv.swap i j) * g *
              (permConj A₀ (Equiv.swap i j))⁻¹)⁻¹ ∈ Y :=
            Y.mul_mem hg (Y.inv_mem (hPY _ g hg).1)
          have heq : g * (permConj A₀ (Equiv.swap i j) * g *
              (permConj A₀ (Equiv.swap i j))⁻¹)⁻¹ = g₁ ^ e := by
            refine eq_of_conjMat_apply hd0 hpd hXc hdiag hmemδ (Y.pow_mem hg₁ e) fun k => ?_
            rw [hTδ _ g hg k, conjMat_pow_apply hd0 hpd hXc hdiag hg₁, hT1]
            by_cases hki : k = i
            · rw [hki, hτi, rootT_left, he]
            by_cases hkj : k = j
            · rw [hkj, hτj, rootT_right ζ hij, inv_pow, he, _root_.mul_inv_rev, inv_inv]
            · rw [hτk k hki hkj, rootT_other ζ hki hkj, one_pow]
              have hk0 : conjMat A₀ g k k ≠ 0 := by
                intro h0
                have h1 := (hTd g hg).1 k
                rw [h0, zero_pow hp.ne_zero] at h1
                exact zero_ne_one h1
              exact mul_inv_cancel₀ hk0
          rw [ha, hδcoe g hg, heq, map_pow, map_pow, Subgroup.coe_pow]
        · intro h1
          have h2 := congrArg Subtype.val h1
          rw [hδcoe g₁ hg₁] at h2
          have h3 := hinjY _ (Y.mul_mem hg₁ (Y.inv_mem (hPY _ g₁ hg₁).1)) 1 Y.one_mem
            (h2.trans (by rw [map_one, map_one]; rfl))
          have h4 : g₁ = permConj A₀ (Equiv.swap i j) * g₁ * (permConj A₀ (Equiv.swap i j))⁻¹ :=
            mul_inv_eq_one.mp h3
          have h5 := congrArg (fun g => conjMat A₀ g i i) h4
          rw [(hPY _ g₁ hg₁).2 i, hτi, hT1, hT1, rootT_left, rootT_right ζ hij] at h5
          exact hζinv h5
  have hFW : ∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∃ π, v = F π := by
    intro v hv
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
    obtain ⟨s₀, rfl⟩ := hφs n
    have hβinv : ∀ l, (conjAut d K (SpecialLinearGroup.toGL s₀))⁻¹ (ψ l) =
        ψ ((MulAut.conj (φ s₀))⁻¹ l) := by
      intro l
      apply (conjAut d K (SpecialLinearGroup.toGL s₀)).injective
      rw [MulAut.apply_inv_self, conjAut_induces_conj hφ, MulAut.apply_inv_self]
    have hNX : ∀ x ∈ X, conjAut d K (SpecialLinearGroup.toGL s₀) * fieldAut d K 1 * x *
        (conjAut d K (SpecialLinearGroup.toGL s₀) * fieldAut d K 1)⁻¹ ∈ X := by
      rintro x ⟨a, ha, hxa⟩
      rw [map_one, mul_one]
      refine ⟨MulAut.conj (φ s₀) * a * (MulAut.conj (φ s₀))⁻¹,
        (Subgroup.mem_normalizer_iff.mp hcN a).mp ha, fun l => ?_⟩
      simp only [MulAut.mul_apply]
      rw [hβinv, hxa, conjAut_induces_conj hφ]
    obtain ⟨π, -, hform⟩ := semilinear_normal_form hd0 hpd hXc hp hp2 hpK hXp hXI hdiag hfull'
      (SpecialLinearGroup.toGL s₀) 1 hNX
    have hvF : v = F π := by
      refine MulEquiv.ext fun a => Subtype.ext ?_
      rw [hvc a, hFapp π a]
      obtain ⟨g, hg, hga⟩ := hAY a a.2
      rw [hga, hconjP]
      have hmem := (Subgroup.mem_normalizer_iff.mp hcN _).mp (hYA g hg)
      obtain ⟨g'', hg'', hg''a⟩ := hAY _ hmem
      rw [hg''a]
      congr 2
      refine eq_of_conjMat_apply hd0 hpd hXc hdiag hg'' (hPY π g hg).1 fun k => ?_
      rw [(hPY π g hg).2 k]
      refine (hform g hg g'' hg'' ?_ k).trans rfl
      rw [map_one, mul_one]
      ext x
      obtain ⟨l, rfl⟩ := hψ x
      rw [conjAut_induces_conj hφ, ← hg''a]
      simp only [MulAut.mul_apply]
      rw [hβinv, conjAut_induces_conj hφ, conjAut_induces_conj hφ]
    exact ⟨π, hvF⟩
  have hFA : ∀ π, F π ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    intro π
    rw [hF]
    exact ggConjAut_mem_ggAutomizer
      (show MulAut.conj (φ (permConj A₀ π)) ∈ (MulAut.conj : L' →* MulAut L').range from ⟨_, rfl⟩)
      (hPN π)
  have hfixT : ∀ (π : Equiv.Perm (Fin d)) (g : SpecialLinearGroup (Fin d) K), g ∈ Y →
      MulAut.conj (φ (permConj A₀ π)) * MulAut.conj (φ g) *
          (MulAut.conj (φ (permConj A₀ π)))⁻¹ = MulAut.conj (φ g) →
        ∀ k, conjMat A₀ g (π k) (π k) = conjMat A₀ g k k := by
    intro π g hg h k
    rw [hconjP] at h
    rw [← (hPY π g hg).2 k, hinjY _ (hPY π g hg).1 g hg h]
  have hroot : ∀ a b : Fin d, a ≠ b → ∃ g ∈ Y, ∀ k, conjMat A₀ g k k = rootT ζ a b k := by
    intro a b hab
    obtain ⟨g, hg, hgt⟩ := hfull' (rootT ζ a b) (rootT_pow hζ.pow_eq_one a b) (prod_rootT hζ0 hab)
    exact ⟨g, hg, fun k => by rw [hgt, diagonal_apply_eq]⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hFker : ∀ π, F π = 1 → π = 1 := by
    intro π h1
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨g₁, hg₁, hT₁⟩ := hroot i (π i) (Ne.symm hi)
    have hfix : MulAut.conj (φ (permConj A₀ π)) * MulAut.conj (φ g₁) *
        (MulAut.conj (φ (permConj A₀ π)))⁻¹ = MulAut.conj (φ g₁) := by
      rw [← hFapp π ⟨_, hYA g₁ hg₁⟩, h1]
      rfl
    have h2 := hfixT π g₁ hg₁ hfix i
    rw [hT₁, hT₁, rootT_left, rootT_right ζ (Ne.symm hi)] at h2
    exact hζinv h2.symm
  have hFinj : Function.Injective F := by
    intro σ τ h
    have h1 : F (σ * τ⁻¹) = 1 := by
      rw [hFmul, h, ← hFmul, mul_inv_cancel, hF1]
    exact mul_inv_eq_one.mp (hFker _ h1)
  have hTpm : ∀ (g₁ g₂ : SpecialLinearGroup (Fin d) K), g₁ ∈ Y → g₂ ∈ Y → ∀ (e : ℕ) (k : Fin d),
      conjMat A₀ (g₁ ^ e * g₂⁻¹) k k = conjMat A₀ g₁ k k ^ e * (conjMat A₀ g₂ k k)⁻¹ := by
    intro g₁ g₂ hg₁ hg₂ e k
    rw [conjMat_mul_apply hd0 hpd hXc hdiag (Y.pow_mem hg₁ e),
      conjMat_pow_apply hd0 hpd hXc hdiag hg₁, conjMat_inv_apply hd0 hpd hXc hdiag hg₂]
  have hconjpow : ∀ (g₁ g₂ : SpecialLinearGroup (Fin d) K) (e : ℕ),
      MulAut.conj (φ g₁) ^ e * (MulAut.conj (φ g₂))⁻¹ = MulAut.conj (φ (g₁ ^ e * g₂⁻¹)) := by
    intro g₁ g₂ e
    simp only [map_mul, map_pow, map_inv]
  have hFsw : ∀ π, GGIsPseudoReflection p (F π) → π.IsSwap := by
    intro π hπ
    have hfixβ : Nat.card {a : A // MulAut.conj (φ (permConj A₀ π)) * (a : MulAut L') *
        (MulAut.conj (φ (permConj A₀ π)))⁻¹ = a} * p = Nat.card A := by
      rw [← hπ.2]
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [Subtype.ext_iff, hFapp])
    have hrank : ∀ (g₁ g₂ : SpecialLinearGroup (Fin d) K), g₁ ∈ Y → g₂ ∈ Y →
        MulAut.conj (φ (permConj A₀ π)) * MulAut.conj (φ g₁) *
            (MulAut.conj (φ (permConj A₀ π)))⁻¹ = MulAut.conj (φ g₁) ∨
          ∃ e : ℕ, MulAut.conj (φ (permConj A₀ π)) * MulAut.conj (φ (g₁ ^ e * g₂⁻¹)) *
            (MulAut.conj (φ (permConj A₀ π)))⁻¹ = MulAut.conj (φ (g₁ ^ e * g₂⁻¹)) := by
      intro g₁ g₂ hg₁ hg₂
      rcases pseudoRefl_rank_one hp (fun x hx y hy => TableB.IsElemAbelian.comm hA hx hy)
        (hPA π) hfixβ (hYA g₁ hg₁) (hYA g₂ hg₂) with h | ⟨e, he⟩
      · exact Or.inl h
      · rw [hconjpow] at he
        exact Or.inr ⟨e, he⟩
    by_contra hns
    have hne1 : π ≠ 1 := by
      rintro rfl
      have h1 := hπ.2
      rw [hF1] at h1
      have h2 : Nat.card {a : ↥A // (1 : MulAut ↥A) a = a} = Nat.card ↥A :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun a => rfl)
      rw [h2] at h1
      have hpos : 0 < Nat.card ↥A := Nat.card_pos
      have := hp.two_le
      nlinarith
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
      by_contra h
      push Not at h
      exact hne1 (Equiv.ext h)
    obtain ⟨g₁, hg₁, hT₁⟩ := hroot i (π i) (Ne.symm hi)
    by_cases hj : π (π i) = i
    ·
      obtain ⟨m, hmi, hmj, hm⟩ : ∃ m, m ≠ i ∧ m ≠ π i ∧ π m ≠ m := by
        by_contra h
        push Not at h
        apply hns
        refine ⟨i, π i, Ne.symm hi, Equiv.ext fun x => ?_⟩
        by_cases hxi : x = i
        · rw [hxi, Equiv.swap_apply_left]
        by_cases hxj : x = π i
        · rw [hxj, hj, Equiv.swap_apply_right]
        · rw [h x hxi hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]
      have hn_i : π m ≠ i := fun h => hmj (π.injective (h.trans hj.symm))
      have hn_j : π m ≠ π i := fun h => hmi (π.injective h)
      obtain ⟨g₂, hg₂, hT₂⟩ := hroot m (π m) (Ne.symm hm)
      rcases hrank g₁ g₂ hg₁ hg₂ with h | ⟨e, he⟩
      · have h2 := hfixT π g₁ hg₁ h i
        rw [hT₁, hT₁, rootT_left, rootT_right ζ (Ne.symm hi)] at h2
        exact hζinv h2.symm
      · have h2 := hfixT π _ (Y.mul_mem (Y.pow_mem hg₁ e) (Y.inv_mem hg₂)) he m
        rw [hTpm _ _ hg₁ hg₂, hTpm _ _ hg₁ hg₂, hT₁, hT₁, hT₂, hT₂, rootT_other ζ hn_i hn_j,
          rootT_right ζ (Ne.symm hm), rootT_other ζ hmi hmj, rootT_left, one_pow, one_mul,
          one_mul, inv_inv] at h2
        exact hζinv h2
    ·
      have hk_j : π (π i) ≠ π i := fun h => hi (π.injective h)
      obtain ⟨l, hli, hlj, hlk⟩ := exists_fin_avoid_three hd i (π i) (π (π i))
      obtain ⟨g₂, hg₂, hT₂⟩ := hroot (π i) l (Ne.symm hlj)
      rcases hrank g₁ g₂ hg₁ hg₂ with h | ⟨e, he⟩
      · have h2 := hfixT π g₁ hg₁ h i
        rw [hT₁, hT₁, rootT_left, rootT_right ζ (Ne.symm hi)] at h2
        exact hζinv h2.symm
      · have hY12 := Y.mul_mem (Y.pow_mem hg₁ e) (Y.inv_mem hg₂)
        have h_i := hfixT π _ hY12 he i
        have h_j := hfixT π _ hY12 he (π i)
        rw [hTpm _ _ hg₁ hg₂, hTpm _ _ hg₁ hg₂, hT₁, hT₁, hT₂, hT₂, rootT_left, rootT_left,
          rootT_right ζ (Ne.symm hi), rootT_other ζ (Ne.symm hi) (Ne.symm hli)] at h_i
        rw [hTpm _ _ hg₁ hg₂, hTpm _ _ hg₁ hg₂, hT₁, hT₁, hT₂, hT₂, rootT_left,
          rootT_right ζ (Ne.symm hi), rootT_other ζ hj hk_j, rootT_other ζ hk_j (Ne.symm hlk),
          one_pow, inv_one, mul_one] at h_j
        rw [inv_one, mul_one, ← h_j] at h_i
        rw [inv_pow, ← h_i, inv_one, one_mul] at h_j
        exact hζ1 (inv_eq_one.mp h_j.symm)
  exact ⟨F, hFmul, hF1, hFswap, hFW, hFA, hFinj, hFsw⟩

theorem ggTorusPseudoReflGen_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) :
    GGTorusPseudoReflGen p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ v hv
  obtain ⟨F, hFmul, hF1, hFswap, hFW, -, -, -⟩ :=
    exists_weylModel_psl hp hp2 hpK hd hpd hsec hψ hker hperf hA hAI hr
  have hFcl : ∀ π : Equiv.Perm (Fin d), F π ∈ Subgroup.closure (ggTorusPseudoReflSet p A) := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one =>
      rw [hF1]
      exact one_mem _
    | swap_mul π x y hxy ih =>
      rw [hFmul]
      exact mul_mem ih (Subgroup.subset_closure (hFswap x y hxy))
  obtain ⟨π, rfl⟩ := hFW v hv
  exact hFcl π

omit [CharP K 2] in
theorem ggTorusPseudoReflGen_small (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) :
    GGTorusPseudoReflGen p 0 (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

end Main

theorem recipeLinear_pseudoReflGen {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggTorusPseudoReflGen_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusPseudoReflGen_small hp hpK (by omega) hd3 hpd')⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggTorusPseudoReflGen_of_mulEquiv (recipeEquiv d K) hI
        (ggTorusPseudoReflGen_coprime hp hp2 hpK hd4 hpd' hsec)⟩

theorem largeEvenLabelAll_pseudoReflGen_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_pseudoReflGen hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_pseudoReflGen hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_pseudoReflGen hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end TypeA

theorem ggWeylPseudoReflGenInputOn_typeA : GGWeylPseudoReflGenInputOn GGTypeALabel :=
  ggWeylPseudoReflGenInputOn_of_labels fun _ _ hp hlab h =>
    TypeA.largeEvenLabelAll_pseudoReflGen_typeA hp hlab h

theorem ggWeylPseudoReflGenInput_of_rest
    (h : GGWeylPseudoReflGenInputOn fun p lab => ¬ GGTypeALabel p lab) :
    GGWeylPseudoReflGenInput :=
  ggWeylPseudoReflGenInput_of_on ggWeylPseudoReflGenInputOn_typeA h

end CFSG.StandardType

end
